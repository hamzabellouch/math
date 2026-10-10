import Mathlib
import OAI.Analysis.Conductivity.Sobolev.OriginalSmoothMultiplier
import OAI.Analysis.Conductivity.Sources.PhysicalGradient
import OAI.Analysis.Conductivity.Variational.PhysicalRealTrace

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance sourcePhysicalTraceMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourcePhysicalTraceIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma physicalOuterTrace_compact_mul {χ : R3 → ℝ}
    (hχ : ContDiff ℝ (↑(⊤:ℕ∞)) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ⊆(WithLp.ofLp) ⁻¹' physicalOpenBlock) (u v : H1)
    (hv : weakValue v=ᵐ[ballMeasure] fun x => χ x*weakValue u x) (i : Fin 3) :
    physicalOuterTraceCLM i v=0 := by
  let P := H1Space.orthogonalProjectionOnto
  let T : H1 →L[ℝ] SpectralL2 TorusModes :=
    (physicalOuterTraceCLM i).comp (P.comp (originalMulJetCLM hχ hc))
  have hz : T u=0 := by
    apply (closure_minimal (s:={u : H1 | u.val∈smoothJets}) ?_
      (isClosed_eq T.continuous continuous_const)) (smoothH1_dense u)
    rintro w ⟨f,hf,hm,he⟩
    have hw : w=smoothH1 f hf := Subtype.ext he
    change T w=0
    rw [hw]
    change physicalOuterTraceCLM i (P (originalMulJetCLM hχ hc (smoothH1 f hf)))=0
    rw [originalMulJetCLM_smooth]
    simp only [P,H1Space.orthogonalProjectionOnto_mem_subspace_eq_self]
    let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
    have hd : ContDiff ℝ (↑(⊤:ℕ∞)) ((χ*f) ∘ E) := (hχ.mul hf).comp E.contDiff
    have hev : piSmoothH1 hd=smoothH1 (χ*f) (hχ.mul hf) := by
      unfold piSmoothH1
      congr 1
    rw [←hev,physicalOuterTrace_smooth i hd (fun _ => 1),
      physicalSmoothOuterTrace_compact_zero (fun _ => 1) hd ?_]
    rfl
    have hss : tsupport ((χ*f) ∘ E)⊆E ⁻¹' tsupport χ :=
      closure_minimal (fun x hx => tsupport_mul_subset_left (subset_tsupport (χ*f) hx))
        ((isClosed_tsupport χ).preimage E.continuous)
    intro y hy
    exact hs (hss hy)
  have hm := originalMulJetCLM_mem_zero hχ hc (fun x hx => physicalOpenBlock_subset_ball (hs hx)) u
  let a : H1 := ⟨originalMulJetCLM hχ hc u,zeroTraceAmbient_le_H1Space hm⟩
  have ha : a=v := by
    apply H1_eq_of_value_ae
    filter_upwards [originalMulJetCLM_ae hχ hc u,hv] with x hx hv
    exact (congrArg (fun z : JetFiber => z 0) hx).trans hv.symm
  change physicalOuterTraceCLM i (P a.val)=0 at hz
  rw [H1Space.orthogonalProjectionOnto_mem_subspace_eq_self,ha] at hz
  exact hz

lemma physicalOuterTrace_compact_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → f x=0)
    (u : H1) (hu : weakValue u=ᵐ[ballMeasure] f) (i : Fin 3) :
    physicalOuterTraceCLM i u=continuousOuterFourier i hf.continuous := by
  have hm : MemLp f 2 volume := hf.continuous.memLp_of_hasCompactSupport (bounded_support_compact hs)
  have hd (j : Fin 3) := lipschitz_lineDeriv_memLp hf hs (EuclideanSpace.single j 1)
  let F : Fin 4 → WholeL2 := Fin.cases (hm.toLp f)
    (fun j => (hd j).toLp (fun x => lineDeriv ℝ f x (EuclideanSpace.single j 1)))
  have hv : (F 0 : R3 → ℝ)=ᵐ[volume] f := hm.coeFn_toLp
  have hw (j : Fin 3) : WeakL2Direction (F 0) (F j.succ) (EuclideanSpace.single j 1) :=
    (lipschitz_weakDirection hf _).congr hv ((hd j).coeFn_toLp)
  have hz := compact_weakJet_mem_zeroTrace F hw hR (by
    filter_upwards [hv] with x hx hn; exact hx.trans (hs x hn))
  let v : H1 := ⟨ballJet F,zeroTraceAmbient_le_H1Space hz⟩
  have he : u=v := by
    apply H1_eq_of_value_ae
    filter_upwards [hu,ae_restrict_of_ae (s:=ball) hv,ballJet_ae F] with x hu hx hb
    exact hu.trans (hx.symm.trans (hb 0).symm)
  rw [he]
  exact physicalOuterTrace_lipschitz hf F hv hw v rfl i

lemma physicalRealTrace_compact_lipschitz {C : ℝ≥0} {f : R3 → ℝ}
    (hf : LipschitzWith C f) {R : ℝ} (hR : R<3) (hs : ∀ x,R<‖x‖ → f x=0)
    (u : H1) (hu : weakValue u=ᵐ[ballMeasure] f) (i : Fin 3) :
    physicalRealTraceCLM i u=ᵐ[volume] fun θ => f (WithLp.toLp 2 (physicalOuterBoundary i θ)) := by
  have he : physicalComplexTraceCLM i u=ContinuousMap.toLp 2 volume ℂ (continuousOuterMap i hf.continuous) := by
    change (mFourierBasis (d:=Fin 2)).repr.symm (physicalOuterTraceCLM i u)=_
    rw [physicalOuterTrace_compact_lipschitz hf hR hs u hu]
    exact (mFourierBasis (d:=Fin 2)).repr.symm_apply_apply _
  have hh := Complex.reCLM.coeFn_compLpL (p:=2) (μ:=volume) (physicalComplexTraceCLM i u)
  change physicalRealTraceCLM i u=ᵐ[volume] _ at hh
  rw [he] at hh
  filter_upwards [hh,ContinuousMap.coeFn_toLp (continuousOuterMap i hf.continuous) (p:=2) (μ:=volume) (𝕜:=ℂ)]
    with θ hθ hfv
  rw [hθ,hfv]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma terminalTime_outer (i : Fin 3) (θ : UnitAddTorus (Fin 2)) :
    terminalTime i (physicalOuterBoundary i θ)=0 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · change sourceCollarTime (sourceAngularCollar 0 θ)=0
    exact sourceAngular_time (by norm_num) θ
  · change sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm
      ((sourceChildHomeomorph (actualChildSign k)) (sourceAngularCollar 0 θ)))=0
    rw [Homeomorph.symm_apply_apply,sourceAngular_time (by norm_num)]

lemma terminalProfile_boundary {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (j : Fin 2) (i : Fin 3) (θ : UnitAddTorus (Fin 2)) :
    z.terminalProfile η j (physicalOuterBoundary i θ)=z.terminalValue i j-z.terminalValue 0 j := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [z.terminalProfile_zero_outside hη hηc j (terminalTime_outer 0 θ).le,sub_self]
  · rw [z.terminalProfile_child_band hη hηc j k (by rw [terminalTime_outer]; linarith),terminalTime_outer]
    simp

lemma terminalProfile_trace {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (j : Fin 2) (f : H1)
    (hf : weakValue f=ᵐ[ballMeasure] fun x => z.terminalProfile η j (WithLp.ofLp x)) (i : Fin 3) :
    physicalRealTraceCLM i f=ᵐ[volume] fun _ => z.terminalValue i j-z.terminalValue 0 j := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  have hh (x : R3) : LocalLipAt (z.terminalProfile η j ∘ E) x :=
    (z.terminalProfile_localLip η j (E x)).comp
      (E.toContinuousLinearMap.lipschitzWith.locallyLipschitz x)
  have hz (x : R3) (hx : 5/2<‖x‖) : (z.terminalProfile η j ∘ E) x=0 := by
    apply z.terminalProfile_zero_outside hη hηc j
    by_contra hn
    have hd := (sourceCollarTime_pos_iff_domain (E x)).mp (lt_of_not_ge hn)
    have hb := sourceClosure_subset_ball (subset_closure hd)
    change x∈Metric.ball 0 (5/2) at hb
    simp only [Metric.mem_ball,dist_zero_right] at hb
    linarith
  obtain ⟨K,hK⟩ := compact_locallyLipschitz hh (bounded_support_compact hz)
  have ht := physicalRealTrace_compact_lipschitz hK (by norm_num : (5/2:ℝ)<3) hz f hf i
  exact ht.mono (fun θ h => h.trans (z.terminalProfile_boundary hη hηc j i θ))

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
attribute [local instance] Classical.propDecidable

lemma patch_energy_eq (a : R3 → ℝ) (σ : Coord3 → ℝ) (q W h : H1)
    (ha : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y)
    (hW : ∀ᵐ x∂ballMeasure,weakGradient W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakGradient q x else 0) :
    (∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      ∫ y in physicalOpenBlock,σ y*(originalPiGradient q y ⬝ᵥ originalPiGradient h y) := by
  let E : R3 ≃L[ℝ] Coord3 := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)
  let U := E ⁻¹' physicalOpenBlock
  let f : R3 → ℝ := fun x => a x*inner ℝ (weakGradient q x) (weakGradient h x)
  have hU : MeasurableSet U := physicalOpenBlock_open.measurableSet.preimage E.continuous.measurable
  have hUb : U⊆ball := fun _ hx => physicalOpenBlock_subset_ball hx
  have hi : (∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      ∫ x,f x ∂volume.restrict U := by
    calc
      _ = ∫ x,U.indicator f x ∂ballMeasure := integral_congr_ae (by
        filter_upwards [hW] with x hx
        rw [hx]
        by_cases hb : WithLp.ofLp x∈physicalOpenBlock
        · rw [ite_eq_left hb,Set.indicator_of_mem (show x∈U from hb)]
        · rw [ite_eq_right hb,Set.indicator_of_notMem (show x∉U from hb),inner_zero_left,mul_zero])
      _ = ∫ x in U,f x ∂ballMeasure := integral_indicator hU
      _ = _ := by rw [ballMeasure,Measure.restrict_restrict hU,inter_eq_left.mpr hUb]
  rw [hi]
  have ht := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb
    E.toHomeomorph.measurableEmbedding (fun y => f (WithLp.toLp 2 y)) physicalOpenBlock
  change (∫ x in U,f x)=_ at ht
  rw [ht]
  apply integral_congr_ae
  filter_upwards [ha] with y hy
  change a (WithLp.toLp 2 y)*inner ℝ (weakGradient q (WithLp.toLp 2 y))
    (weakGradient h (WithLp.toLp 2 y))=_
  rw [hy]
  congr 1
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  exact dotProduct_comm _ _

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

theorem source_patch_green {η : ℝ} (hη : 0<η) (hηc : 2*η<centralThickness)
    (a : R3 → ℝ) (σ : Coord3 → ℝ) (q W : H1) (j : Fin 2)
    (ha : ∀ᵐ y∂volume.restrict physicalOpenBlock,a (WithLp.toLp 2 y)=σ y)
    (hv : ∀ᵐ x∂ballMeasure,weakValue W x=
      if WithLp.ofLp x∈physicalOpenBlock then weakValue q x-z.terminalValue 0 j
      else z.terminalProfile η j (WithLp.ofLp x))
    (hg : ∀ h : H1,(∫ y in physicalOpenBlock,σ y*(originalPiGradient q y ⬝ᵥ
      originalPiGradient h y))=constantTerminalFluxCLM (centralBasisSlopes j) h) :
    ∀ h : H1,(∫ x,a x*inner ℝ (weakGradient W x) (weakGradient h x) ∂ballMeasure)=
      constantTerminalFluxCLM (centralBasisSlopes j) h := by
  intro h
  exact (patch_energy_eq a σ q W h ha (z.source_patch_gradient hη hηc q W j hv)).trans (hg h)

end PhysicalFiniteEndingData
end ScalarConductivity

end
end

end OAI
