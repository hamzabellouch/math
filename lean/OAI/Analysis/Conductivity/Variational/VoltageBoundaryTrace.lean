import Mathlib
import OAI.Analysis.Conductivity.Variational.PhysicalOpenVoltage

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

def voltageOriginalProjectedH1 {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2) :
    VoltageJetSpace volume U →L[ℝ] H1 :=
  H1Space.orthogonalProjectionOnto.comp (voltageOriginalJetCLM hU j)

lemma voltageOriginalProjectedH1_eq {U : Set Coord3} (hU : MeasurableSet U) (j : Fin 2)
    (Z : VoltageJetSpace volume U) (u : H1) (hu : u.val=voltageOriginalJetCLM hU j Z) :
    voltageOriginalProjectedH1 hU j Z=u := by
  change H1Space.orthogonalProjectionOnto (voltageOriginalJetCLM hU j Z)=u
  rw [←hu]
  exact H1Space.orthogonalProjectionOnto_mem_subspace_eq_self u

lemma voltageOriginalJetCLM_smooth_compact {U : Set Coord3} (hU : MeasurableSet U)
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ (↑(⊤:ℕ∞)) v)
    (hvs : tsupport v⊆U) (hm : MemLp v 2 (volume.restrict U))
    (hg : MemLp (voltageGradient v) 2 (volume.restrict U)) (j : Fin 2) :
    voltageOriginalJetCLM hU j (hm.toLp _,hg.toLp _)=
      (piSmoothH1 ((contDiff_apply ℝ ℝ j).comp hv)).val := by
  have hp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hm.coeFn_toLp)
  have hgp := (PiLp.volume_preserving_ofLp (Fin 3)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' hU).1 hg.coeFn_toLp)
  apply Lp.ext
  filter_upwards [voltageOriginalJetCLM_ae hU j (hm.toLp _,hg.toLp _),
    ae_restrict_of_ae hp,ae_restrict_of_ae hgp,
    piSmoothH1_jet ((contDiff_apply ℝ ℝ j).comp hv)] with x hx hp hgp hf
  rw [hx,hf]
  by_cases hu : WithLp.ofLp x∈U
  · rw [ite_eq_left hu,hp hu,hgp hu]
    ext k
    refine Fin.cases rfl (fun i => ?_) k
    exact voltageGradient_component (hv.differentiable (by simp) _) i j
  · rw [ite_eq_right hu]
    have hn : WithLp.ofLp x∉tsupport (fun y => v y j) := by
      intro h
      exact hu (hvs ((tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v) h))
    ext k
    refine Fin.cases ?_ (fun i => ?_) k
    · exact (image_eq_zero_of_notMem_tsupport hn).symm
    · change 0=fderiv ℝ (fun y => v y j) (WithLp.ofLp x) (Pi.single i 1)
      rw [fderiv_of_notMem_tsupport ℝ hn]
      rfl

theorem voltageOriginal_outer_trace_zero (j : Fin 2)
    {Z : VoltageJetSpace volume physicalOpenBlock}
    (hZ : Z∈zeroVoltageJets volume physicalOpenBlock) (u : H1)
    (hu : u.val=voltageOriginalJetCLM physicalOpenBlock_open.measurableSet j Z) (i : Fin 3) :
    physicalOuterTraceCLM i u=0 := by
  let T : VoltageJetSpace volume physicalOpenBlock →L[ℝ] SpectralL2 TorusModes :=
    (physicalOuterTraceCLM i).comp (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j)
  have hz : T Z=0 := by
    apply closure_minimal (t:={Z | T Z=0}) ?_ (isClosed_eq T.continuous continuous_const) hZ
    intro a ha
    obtain ⟨v,hv,hvc,hvs,hm,hg,rfl⟩ := ha
    have he := voltageOriginalJetCLM_smooth_compact physicalOpenBlock_open.measurableSet hv hvs hm hg j
    change physicalOuterTraceCLM i (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j
      (hm.toLp _,hg.toLp _))=0
    rw [voltageOriginalProjectedH1_eq _ _ _ _ he.symm,physicalOuterTrace_smooth i _ (fun _ => 1),
      physicalSmoothOuterTrace_compact_zero (fun _ => 1) _ ?_]
    rfl
    exact (tsupport_comp_subset (g:=fun w : Fin 2 → ℝ => w j) rfl v).trans hvs
  change physicalOuterTraceCLM i (voltageOriginalProjectedH1 physicalOpenBlock_open.measurableSet j Z)=0 at hz
  rw [voltageOriginalProjectedH1_eq _ _ _ _ hu] at hz
  exact hz

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped Convolution ENNReal NNReal
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma mollifyReal_congr_ae (φ : SpatialBump) {f g : R3 → ℝ}
    (h : f=ᵐ[volume] g) : mollifyReal φ f=mollifyReal φ g := by
  funext x
  unfold mollifyReal
  rw [convolution_eq_swap,convolution_eq_swap]
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

lemma mollifyReal_lipschitz_bound {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (φ : SpatialBump) (x : R3) :
    ‖mollifyReal φ f x-f x‖≤C*φ.rOut := by
  have hi : Integrable (fun y => f (x-y)) (bumpProbability φ) := by
    apply Integrable.mono' (integrable_const (‖f x‖+C*φ.rOut))
      (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    filter_upwards [bumpProbability_ball φ] with y hy
    have hh := hf.norm_sub_le (x-y) x
    have hn : ‖x-y-x‖=‖y‖ := by rw [sub_sub_cancel_left,norm_neg]
    rw [hn] at hh
    exact (norm_le_insert' (f (x-y)) (f x)).trans (by nlinarith [C.coe_nonneg])
  have hc : (∫ _ : R3,f x ∂bumpProbability φ)=f x := by simp
  rw [mollifyReal_eq_average,←hc,←integral_sub hi (integrable_const _)]
  have hh := norm_integral_le_of_norm_le_const (μ:=bumpProbability φ)
    (f:=fun y => f (x-y)-f x) (C:=(C:ℝ)*φ.rOut) (by
      filter_upwards [bumpProbability_ball φ] with y hy
      have hb := hf.norm_sub_le (x-y) x
      have hn : ‖x-y-x‖=‖y‖ := by rw [sub_sub_cancel_left,norm_neg]
      rw [hn] at hb
      exact hb.trans (mul_le_mul_of_nonneg_left hy.le C.coe_nonneg))
  simpa using hh

def continuousOuterMap (i : Fin 3) {f : R3 → ℝ} (hf : Continuous f) :
    C(UnitAddTorus (Fin 2),ℂ) :=
  ⟨fun θ => (f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ),
    Complex.continuous_ofReal.comp (hf.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous.comp
        (physicalOuterBoundary_continuous i)))⟩

def continuousOuterFourier (i : Fin 3) {f : R3 → ℝ} (hf : Continuous f) : SpectralL2 TorusModes :=
  (mFourierBasis (d:=Fin 2)).repr (ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf))

lemma smoothOuterFourier_original (i : Fin 3) {f : R3 → ℝ}
    (hf : ContDiff ℝ (↑(⊤:ℕ∞)) f) :
    physicalOuterTraceCLM i (smoothH1 f hf)=continuousOuterFourier i hf.continuous := by
  let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have hp : ContDiff ℝ (↑(⊤:ℕ∞)) (f ∘ e) := hf.comp e.contDiff
  have he : piSmoothH1 hp=smoothH1 f hf := by
    unfold piSmoothH1
    congr 1
  rw [←he]
  have hh := (dense_linear_observable_extension smoothPiH1L (smoothOuterFourierL i)
    smoothPiH1L_dense (smoothOuterFourierL_bound i)).choose_spec ⟨f ∘ e,hp⟩
  exact hh

lemma continuousOuterMap_mollify_tendsto {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (i : Fin 3) :
    Tendsto (fun n => continuousOuterMap i (mollifyReal_smooth (dyadicBump n)
      hf.continuous.locallyIntegrable).continuous) atTop (𝓝 (continuousOuterMap i hf.continuous)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (g:=fun n => (C:ℝ)*(dyadicBump n).rOut) (fun _ => norm_nonneg _) ?_ ?_
  · intro n
    apply (ContinuousMap.norm_le _ (mul_nonneg C.coe_nonneg (by change 0≤(1/2:ℝ)^n; positivity))).mpr
    intro θ
    change ‖(mollifyReal (dyadicBump n) f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ)-
      (f (WithLp.toLp 2 (physicalOuterBoundary i θ)):ℂ)‖≤_
    rw [←Complex.ofReal_sub,Complex.norm_real]
    exact mollifyReal_lipschitz_bound hf _ _
  · simpa using (tendsto_const_nhds.mul dyadicBump_radius :
      Tendsto (fun n => (C:ℝ)*(dyadicBump n).rOut) atTop (𝓝 ((C:ℝ)*0)))

theorem physicalOuterTrace_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) (F : Fin 4 → WholeL2)
    (hv : (F 0 : R3 → ℝ)=ᵐ[volume] f)
    (hw : ∀ i : Fin 3,WeakL2Direction (F 0) (F i.succ) (EuclideanSpace.single i 1))
    (u : H1) (hu : u.val=ballJet F) (i : Fin 3) :
    physicalOuterTraceCLM i u=continuousOuterFourier i hf.continuous := by
  let P := H1Space.orthogonalProjectionOnto
  have hp : P (ballJet F)=u := by
    rw [←hu]
    exact H1Space.orthogonalProjectionOnto_mem_subspace_eq_self u
  have hlim := ((physicalOuterTraceCLM i).continuous.comp P.continuous).continuousAt.tendsto.comp
    (ballJet_mollify_tendsto F)
  change Tendsto (fun n => physicalOuterTraceCLM i
    (H1Space.orthogonalProjectionOnto (ballJet (fun j => mollifyL2 (dyadicBump n) (F j)))))
    atTop (𝓝 (physicalOuterTraceCLM i (P (ballJet F)))) at hlim
  simp only [mollifiedJet_eq F hw,
    H1Space.orthogonalProjectionOnto_mem_subspace_eq_self,smoothOuterFourier_original] at hlim
  change Tendsto _ atTop (𝓝 (physicalOuterTraceCLM i (P (ballJet F)))) at hlim
  rw [hp] at hlim
  have hlim' := (mFourierBasis (d:=Fin 2)).repr.continuous.continuousAt.tendsto.comp
    ((ContinuousMap.toLp 2 volume ℂ).continuous.continuousAt.tendsto.comp
      (continuousOuterMap_mollify_tendsto hf i))
  apply tendsto_nhds_unique hlim
  convert hlim' using 1
  · funext n
    unfold continuousOuterFourier continuousOuterMap
    congr 3
    ext θ
    rw [mollifyReal_congr_ae _ hv]
  · rfl

end ScalarConductivity

end
end

end OAI
