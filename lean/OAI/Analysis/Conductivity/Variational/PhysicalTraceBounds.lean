import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergy
import OAI.Analysis.Conductivity.Variational.PhysicalSmoothTest

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology
open scoped ENNReal

lemma sourcePhysicalEnergy_jet_le (φ : (Fin 3 → ℝ) → ℝ) (y : Fin 3 → ℝ) :
    sourcePhysicalEnergy φ y ≤ 192*‖piSmoothJet φ y‖^2 := by
  have hb := linear_three_bound (fderiv ℝ φ y)
  have hsingle (i : Fin 3) : (Pi.single i (1:ℝ) : Fin 3 → ℝ)=
      ![![1,0,0],![0,1,0],![0,0,1]] i := by
    fin_cases i <;> ext j <;> fin_cases j <;> simp
  rw [piSmoothJet,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_succ,Fin.sum_univ_three]
  simp only [Fin.cases_zero,Fin.cases_succ,Real.norm_eq_abs,sq_abs,
    hsingle,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  dsimp [sourcePhysicalEnergy]
  change 64*‖fderiv ℝ φ y‖^2+2*(φ y)^2 ≤
    192*((φ y)^2+((fderiv ℝ φ y ![1,0,0])^2+
      (fderiv ℝ φ y ![0,1,0])^2+(fderiv ℝ φ y ![0,0,1])^2))
  nlinarith [sq_nonneg (φ y)]

def physicalRestrictedJetCLM (D : Set (Fin 3 → ℝ)) :
    H1 →L[ℝ] Lp JetFiber 2 (volume.restrict D) :=
  ((lpRestrictionCLM D).comp ballWholePiJetCLM).comp H1Space.subtypeL

lemma physicalRestrictedJet_smooth_ae {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {D : Set (Fin 3 → ℝ)}
    (hD : MeasurableSet D) (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    physicalRestrictedJetCLM D (piSmoothH1 hφ)=ᵐ[volume.restrict D] piSmoothJet φ := by
  filter_upwards [lpRestrictionCLM_ae D (ballWholePiJetCLM (piSmoothH1 hφ).val),
    ae_restrict_of_ae (ballWholePiJetCLM_ae_of_ae (piSmoothH1 hφ).val _ (piSmoothH1_jet hφ)),
    ae_restrict_mem hD] with y hr he hy
  exact hr.trans (he.trans (ite_eq_left (hb y hy)))

lemma physical_smooth_energy_bound {φ : (Fin 3 → ℝ) → ℝ}
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) {D : Set (Fin 3 → ℝ)}
    (hD : IsCompact D) (hb : ∀ y∈D,WithLp.toLp 2 y∈ball) :
    (∫ y in D,sourcePhysicalEnergy φ y) ≤
      (192*‖physicalRestrictedJetCLM D‖^2)*‖piSmoothH1 hφ‖^2 := by
  let z := physicalRestrictedJetCLM D (piSmoothH1 hφ)
  have he : (∫ y in D,‖piSmoothJet φ y‖^2)=‖z‖^2 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [physicalRestrictedJet_smooth_ae hφ hD.measurableSet hb] with y hy
    rw [hy,real_inner_self_eq_norm_sq]
  have hi : Integrable (fun y => ‖piSmoothJet φ y‖^2) (volume.restrict D) := by
    apply Integrable.congr (L2.integrable_inner z z)
    filter_upwards [physicalRestrictedJet_smooth_ae hφ hD.measurableSet hb] with y hy
    rw [hy,real_inner_self_eq_norm_sq]
  have hh := integral_mono
    ((continuous_sourcePhysicalEnergy hφ).continuousOn.integrableOn_compact hD)
    (hi.const_mul 192) (sourcePhysicalEnergy_jet_le φ)
  rw [integral_const_mul,he] at hh
  have hn := (physicalRestrictedJetCLM D).le_opNorm (piSmoothH1 hφ)
  exact hh.trans (by nlinarith [sq_nonneg (‖physicalRestrictedJetCLM D‖*‖piSmoothH1 hφ‖-‖z‖),
    mul_self_le_mul_self (norm_nonneg z) hn])

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology

theorem dense_linear_observable_extension
    {E H V : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (J : E →ₗ[ℝ] H) (T : E →ₗ[ℝ] V) (hJ : DenseRange J)
    (hB : ∃ C : ℝ, ∀ f, ‖T f‖ ≤ C*‖J f‖) :
    ∃ L : H →L[ℝ] V, ∀ f, L (J f)=T f := by
  obtain ⟨C,hC⟩ := hB
  have hk : J.ker ≤ T.ker := by
    intro f hf
    apply LinearMap.mem_ker.mpr
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    simpa only [LinearMap.mem_ker.mp hf,norm_zero,mul_zero] using hC f
  let Q : J.range →ₗ[ℝ] V := (J.ker.liftQ T hk).comp J.quotKerEquivRange.symm.toLinearMap
  have hQ (f : E) : Q (J.rangeRestrict f)=T f := by
    have hh : J.quotKerEquivRange (Submodule.Quotient.mk f)=J.rangeRestrict f := rfl
    rw [←hh]
    change (J.ker.liftQ T hk) (J.quotKerEquivRange.symm
      (J.quotKerEquivRange (Submodule.Quotient.mk f)))=_
    rw [LinearEquiv.symm_apply_apply,Submodule.liftQ_apply]
  have hQB (x : J.range) : ‖Q x‖≤C*‖x‖ := by
    obtain ⟨f,hf⟩ := x.property
    have hx : x=J.rangeRestrict f := Subtype.ext hf.symm
    rw [hx,hQ]
    exact hC f
  let Qc := Q.mkContinuous C hQB
  have hd : DenseRange J.range.subtypeL := by
    intro x
    apply closure_mono (s := Set.range J) ?_ (hJ x)
    rintro _ ⟨f,rfl⟩
    exact ⟨J.rangeRestrict f,rfl⟩
  refine ⟨Qc.extend J.range.subtypeL,fun f => ?_⟩
  have hi : Isometry J.range.subtypeL := fun _ _ => rfl
  exact (Qc.extend_eq hd hi.isUniformInducing (J.rangeRestrict f)).trans (hQ f)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def physicalOuterBoundary (i : Fin 3) (θ : UnitAddTorus (Fin 2)) : Fin 3 → ℝ :=
  Fin.cases (sourceAngularCollar 0 θ)
    (fun k => sourceChildCoordinates (actualChildSign k) (sourceAngularCollar 0 θ)) i

lemma physicalOuterBoundary_continuous (i : Fin 3) : Continuous (physicalOuterBoundary i) := by
  refine Fin.cases (continuous_sourceAngularCollar 0) (fun k => ?_) i
  exact (sourceChildCoordinates_contDiff _).continuous.comp (continuous_sourceAngularCollar 0)

lemma physicalOuter_smooth_sq_bound (i : Fin 3) :
    ∃ C : ℝ, 0≤C ∧ ∀ (φ : (Fin 3 → ℝ) → ℝ)
      (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ),
      (∫ θ : UnitAddTorus (Fin 2), (φ (physicalOuterBoundary i θ))^2)≤C*‖piSmoothH1 hφ‖^2 := by
  let A : ℝ := (1+1/centralThickness)*physicalRayConstant
  have hA : 0≤A := by have := physicalRayConstant_pos; dsimp [A,centralThickness]; positivity
  refine Fin.cases ?_ (fun k => ?_) i
  · refine ⟨A*(192*‖physicalRestrictedJetCLM (physicalEndRegion 0)‖^2),by positivity,fun φ hφ => ?_⟩
    have ht := sourceAngular_physical_trace_forward hφ (physicalEndRegion_compact 0) 0
      (η:=centralThickness) (by norm_num [centralThickness]) (by norm_num)
      (by norm_num [centralThickness]) (fun i j => by
        simpa only [zero_add, physicalEndRegion, Fin.cases_zero] using sourceCollarClosedPiece_subset
          (by norm_num : -(1:ℝ)/100≤0) (by norm_num [centralThickness] : centralThickness≤1/100) i j)
    have he := physical_smooth_energy_bound hφ (physicalEndRegion_compact 0)
      (fun _ => physicalEndRegion_subset_ball 0)
    change (∫ θ : UnitAddTorus (Fin 2), (φ (sourceAngularCollar 0 θ))^2) ≤ _
    calc
      _ ≤ A * (∫ y in physicalEndRegion 0, sourcePhysicalEnergy φ y) := ht
      _ ≤ A * (192*‖physicalRestrictedJetCLM (physicalEndRegion 0)‖^2*‖piSmoothH1 hφ‖^2) :=
        mul_le_mul_of_nonneg_left he hA
      _ = _ := by ring
  · let σ := actualChildSign k
    let D := sourceClosedCollarBand (-centralThickness) 0
    have hD : IsCompact D := isCompact_sourceClosedCollarBand
      (by norm_num [centralThickness]) (by norm_num)
    have hσ : 0<sourceScale^3 := by norm_num [sourceScale]
    refine ⟨A*((sourceScale^3)⁻¹*(192*‖physicalRestrictedJetCLM (physicalEndRegion k.succ)‖^2)),
      by positivity,fun φ hφ => ?_⟩
    have hfc := hφ.comp (sourceChildCoordinates_contDiff σ)
    have ht := sourceAngular_physical_trace_backward hfc hD 0
      (η:=centralThickness) (by norm_num [centralThickness])
      (by norm_num [centralThickness]) (by norm_num) (fun i j => by
        simpa only [zero_sub] using sourceCollarClosedPiece_subset
          (by norm_num [centralThickness] : -(1:ℝ)/100≤ -centralThickness)
          (by norm_num : (0:ℝ)≤1/100) i j)
    have hm : (∫ y in D, sourcePhysicalEnergy (φ ∘ sourceChildCoordinates σ) y)≤
        ∫ y in D,sourcePhysicalEnergy φ (sourceChildCoordinates σ y) := by
      apply integral_mono
        ((continuous_sourcePhysicalEnergy hfc).continuousOn.integrableOn_compact hD)
        (((continuous_sourcePhysicalEnergy hφ).comp (sourceChildCoordinates_contDiff σ).continuous).continuousOn.integrableOn_compact hD)
        (sourceChild_energy hφ σ)
    have hp : sourceChildCoordinates σ ⁻¹' physicalEndRegion k.succ=D := by
      ext y
      change ((sourceChildHomeomorph σ).symm (sourceChildHomeomorph σ y)∈D)↔y∈D
      rw [Homeomorph.symm_apply_apply]
    have hh := integral_sourceChild_preimage σ (physicalEndRegion_compact k.succ) (sourcePhysicalEnergy φ)
    rw [hp] at hh
    rw [hh] at hm
    have he := physical_smooth_energy_bound hφ (physicalEndRegion_compact k.succ)
      (fun _ => physicalEndRegion_subset_ball k.succ)
    have he' := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hσ.le)
    change (∫ θ : UnitAddTorus (Fin 2), ((φ ∘ sourceChildCoordinates σ) (sourceAngularCollar 0 θ))^2) ≤ _
    calc
      _ ≤ A * (∫ y in D, sourcePhysicalEnergy (φ ∘ sourceChildCoordinates σ) y) := ht
      _ ≤ A * ((sourceScale^3)⁻¹*(192*‖physicalRestrictedJetCLM (physicalEndRegion k.succ)‖^2*‖piSmoothH1 hφ‖^2)) :=
        mul_le_mul_of_nonneg_left (hm.trans he') hA
      _ = _ := by ring

def smoothPiH1L : SmoothScalar (Fin 3 → ℝ) →ₗ[ℝ] H1 where
  toFun f := piSmoothH1 (smoothScalar_contDiff f)
  map_add' f g := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [piSmoothH1_jet (smoothScalar_contDiff (f+g)),
      piSmoothH1_jet (smoothScalar_contDiff f),piSmoothH1_jet (smoothScalar_contDiff g),
      Lp.coeFn_add (piSmoothH1 (smoothScalar_contDiff f)).val (piSmoothH1 (smoothScalar_contDiff g)).val]
      with x hfg hf hg ha
    change (piSmoothH1 (smoothScalar_contDiff (f+g))).val x =
      ((piSmoothH1 (smoothScalar_contDiff f)).val + (piSmoothH1 (smoothScalar_contDiff g)).val) x
    rw [ha,hfg]
    simp only [Pi.add_apply]
    rw [hf,hg]
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    change fderiv ℝ (f.val+g.val) _ (Pi.single j 1)=_
    rw [fderiv_add ((smoothScalar_contDiff f).differentiable (by simp) _)
      ((smoothScalar_contDiff g).differentiable (by simp) _)]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [piSmoothH1_jet (smoothScalar_contDiff (c•f)),
      piSmoothH1_jet (smoothScalar_contDiff f),
      Lp.coeFn_smul c (piSmoothH1 (smoothScalar_contDiff f)).val] with x hcf hf ha
    change (piSmoothH1 (smoothScalar_contDiff (c•f))).val x =
      (c • (piSmoothH1 (smoothScalar_contDiff f)).val) x
    rw [ha,hcf]
    simp only [Pi.smul_apply]
    rw [hf]
    ext i
    refine Fin.cases rfl (fun j => ?_) i
    change fderiv ℝ (c•f.val) _ (Pi.single j 1)=_
    rw [fderiv_const_smul ((smoothScalar_contDiff f).differentiable (by simp) _) c]
    rfl

lemma smoothPiH1L_dense : DenseRange smoothPiH1L := by
  apply smoothH1_dense.mono
  rintro u ⟨f,hf,hm,he⟩
  let q : SmoothScalar (Fin 3 → ℝ) := ⟨f ∘ (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm,
    hf.comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff⟩
  refine ⟨q,?_⟩
  apply Subtype.ext
  change (smoothJet_memLp ((smoothScalar_contDiff q).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).toLp _=u.val
  rw [he]
  apply Lp.ext
  filter_upwards [(smoothJet_memLp ((smoothScalar_contDiff q).comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff)).coeFn_toLp,hm.coeFn_toLp] with x hq hf'
  rw [hq,hf']
  congr 1

end ScalarConductivity

end

end OAI
