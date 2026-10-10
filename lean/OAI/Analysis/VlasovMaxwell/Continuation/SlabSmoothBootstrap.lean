import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.SpatialJets
import OAI.Analysis.VlasovMaxwell.Regularity.WithinPartial

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u
variable {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]

lemma iterated_spatial_time_derivative (j : ℕ) {T : ℝ} (hT : 0<T) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F G : ℝ × U → W}, SpatialJetRegular 0 (Icc 0 T) F → SpatialJetRegular 0 (Icc 0 T) G →
      (∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t) →
      ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt
        (fun r => iteratedFDeriv ℝ j (fun y => F (r,y)) x)
        (iteratedFDeriv ℝ j (fun y => G (t,y)) x) (Icc 0 T) t := by
  induction j with
  | zero =>
    intro W _ _ _ F G hF hG htime t ht x
    let A : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      A.hasFDerivAt.comp_hasDerivWithinAt t (htime t ht x)
  | succ j ih =>
    intro W _ _ _ F G hF hG htime t ht x
    have hdtime := fun (t : ℝ) (ht : t ∈ Icc 0 T) (x : U) => space_time_derivative_slab hT hF hG htime ht x
    have hd := ih hF.deriv hG.deriv hdtime t ht x
    let A : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    convert! A.hasFDerivAt.comp_hasDerivWithinAt t hd using 1 <;>
      simp only [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]

omit [ProperSpace U] in
lemma contDiffOn_assembleDerivative {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ∞ω} {S : Set X}
    {G : X → W} {D : X → (U →L[ℝ] W)} (hG : ContDiffOn ℝ n G S) (hD : ContDiffOn ℝ n D S) :
    ContDiffOn ℝ n (fun p => assembleDerivative (G p) (D p)) S := by
  let A : W →L[ℝ] ((ℝ × U) →L[ℝ] W) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × U) W (ContinuousLinearMap.fst ℝ ℝ U)
  exact (A.contDiff.comp_contDiffOn hG).add (hD.clm_comp contDiffOn_const)

lemma spatialJetRegular_succ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F G : ℝ × U → W} {T : ℝ} (hT : 0<T) (n : ℕ)
    (hF : SpatialJetRegular n (Icc 0 T) F) (hG : SpatialJetRegular n (Icc 0 T) G)
    (htime : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t) :
    SpatialJetRegular (n+1) (Icc 0 T) F := by
  have hu : UniqueDiffOn ℝ {p : ℝ × U | p.1∈Icc 0 T} := by
    have he : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
    rw [he]
    exact (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine ⟨hF.1,fun j => ?_⟩
  let Fj := fun p : ℝ × U => iteratedFDeriv ℝ j (fun y => F (p.1,y)) p.2
  let Gj := fun p : ℝ × U => iteratedFDeriv ℝ j (fun y => G (p.1,y)) p.2
  let Dj := fun p : ℝ × U => fderiv ℝ (fun y => Fj (p.1,y)) p.2
  have hFj : SpatialJetRegular n (Icc 0 T) Fj := spatialJetRegular_iterated j hF
  have hGj : ContDiffOn ℝ n Gj {p | p.1∈Icc 0 T} := hG.2 j
  have hDj : ContDiffOn ℝ n Dj {p | p.1∈Icc 0 T} := hFj.deriv.regular
  have htimej := iterated_spatial_time_derivative j hT
    (hF.mono_order (by simp)) (hG.mono_order (by simp)) htime
  have hd (p : ℝ × U) (hp : p.1∈Icc 0 T) : HasFDerivWithinAt Fj
      (assembleDerivative (Gj p) (Dj p)) {p | p.1∈Icc 0 T} p := by
    apply hasFDerivWithinAt_of_time_space hp _ hDj.continuousOn (htimej p.1 hp p.2)
    intro r hr y
    exact ((hFj.1 r hr).differentiable (by simp) y).hasFDerivAt
  have he (p : ℝ × U) (hp : p.1∈Icc 0 T) :
      fderivWithin ℝ Fj {p | p.1∈Icc 0 T} p=assembleDerivative (Gj p) (Dj p) :=
    (hd p hp).fderivWithin (hu p hp)
  have hn : ((n+1:ℕ∞):ℕ∞ω)=(n:ℕ∞ω)+1 := by simp
  rw [hn,contDiffOn_succ_iff_fderivWithin hu]
  refine ⟨fun p hp => (hd p hp).differentiableWithinAt,by simp,?_⟩
  exact (contDiffOn_assembleDerivative hGj hDj).congr he

end RVM
end

end OAI
