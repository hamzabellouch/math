import Mathlib
import OAI.Analysis.AffineBernstein.PositiveMatrixTraceBound
import OAI.Analysis.AffineBernstein.LogCaccioppoli

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section LogVariance

lemma inverseHessianPair_le_trace_gradientSquared {n : ℕ} {u f : Space n → ℝ}
    {x : Space n} (hp : (hessian u x).PosDef) :
    inverseHessianPair u f f x ≤ (hessian u x)⁻¹.trace * gradientSquared f x := by
  have hh := posSemidef_quadratic_le_trace_mul_sq hp.inv.posSemidef
    (fun i => dirDeriv (coordinateVector n i) f x)
  change _ ≤ _ * gradientSquared f x at hh
  convert hh using 1
  unfold inverseHessianPair Matrix.mulVec dotProduct
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inverseHessianPair_eq_zero_outside_tsupport {n : ℕ} (u f g : Space n → ℝ)
    {x : Space n} (hx : x ∉ tsupport g) : inverseHessianPair u f g x = 0 := by
  have hd (i : Fin n) : dirDeriv (coordinateVector n i) g x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_apply_subset ℝ _ hh))
  simp [inverseHessianPair,hd]

lemma continuous_cofactor_trace {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef) :
    Continuous (fun x => (hessian u x).det * (hessian u x)⁻¹.trace) := by
  have he : (fun x => (hessian u x).det * (hessian u x)⁻¹.trace) =
      (fun x => ∑ i, cofactorHessian u x i i) := by
    funext x
    simp [Matrix.trace,cofactorHessian,Finset.mul_sum]
  rw [he]
  exact continuous_finsetSum _ (fun i _ => (contDiff_cofactorHessian_entry_global hu hp i i).continuous)

lemma integral_cofactor_trace_le_ball {n : ℕ} {u : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    {D : Set (Space n)} (hD : IsCompact D) {G R : ℝ}
    (hG : ∀ x ∈ D, ‖gradient u x‖ ≤ G) (hR : ∀ x ∈ D, ‖x‖ ≤ R) :
    (∫ x in D, (hessian u x).det * (hessian u x)⁻¹.trace) ≤
      ((n:ℝ)+1)*(volume (Metric.closedBall (0:Space n) (G+R))).toReal := by
  have hi : IntegrableOn (fun x => (hessian u x).det*(hessian u x)⁻¹.trace) D volume :=
    ContinuousOn.integrableOn_compact hD (continuous_cofactor_trace hu hp).continuousOn
  have hnon (x : Space n) : 0 ≤ (hessian u x).det*(hessian u x)⁻¹.trace :=
    mul_nonneg (hp x).det_pos.le (hp x).inv.posSemidef.trace_nonneg
  have hlin := lintegral_hessian_minors_le_ball convex_univ (fun _ _ => hu.contDiffAt)
    (fun x _ => hp x) hD.measurableSet (fun x _ => mem_univ x) hG hR
  have hh : (∫⁻ x in D, ENNReal.ofReal ((hessian u x).det*(hessian u x)⁻¹.trace)) ≤
      ((n:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space n) (G+R)) := by
    apply le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hlin
    have hd := (hp x).det_pos
    nlinarith
  have hfin : ((n:ℝ≥0∞)+1)*volume (Metric.closedBall (0:Space n) (G+R)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (isCompact_closedBall (0:Space n) (G+R)).measure_lt_top.ne
  have HH := ENNReal.toReal_mono hfin hh
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnon),
    ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg hnon), ENNReal.toReal_mul] at HH
  simpa [ENNReal.toReal_add (a := (n:ℝ≥0∞)) (b := 1) (by simp) (by simp)] using HH

lemma log_energy_le_cutoff {n : ℕ} {u s η : Space n → ℝ}
    (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hs : ContDiff ℝ ∞ s) (hpos : ∀ x, 0 < s x)
    (hL : ∀ x, inverseHessianTrace u s x ≤ 0)
    (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    {K B : Set (Space n)} (hK : IsCompact K) (hB : IsCompact B)
    (hηB : tsupport η ⊆ B) (hηK : ∀ x ∈ K, η x = 1)
    {c M J : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    (hdet : ∀ x ∈ K, c ≤ (hessian u x).det)
    (hgrad : ∀ x ∈ B, gradientSquared η x ≤ M)
    (hcof : (∫ x in B, (hessian u x).det*(hessian u x)⁻¹.trace) ≤ J) :
    (∫ x in K, inverseHessianPair u (fun y => Real.log (s y)) (fun y => Real.log (s y)) x) ≤ 4*M*J/c := by
  let f := fun y => Real.log (s y)
  have hf : ContDiff ℝ ∞ f := hs.log (fun x => (hpos x).ne')
  have hQ : Continuous (inverseHessianPair u f f) := (contDiff_inverseHessianPair_global hu hp hf hf).continuous
  have hdt : Continuous (fun x => (hessian u x).det) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact (contDiffAt_det_hessian hu.contDiffAt).continuousAt
  have hEn : ∀ x, 0 ≤ (hessian u x).det*(η x)^2*inverseHessianPair u f f x :=
    fun x => mul_nonneg (mul_nonneg (hp x).det_pos.le (sq_nonneg _)) (inverseHessianPair_self_nonneg (hp x) f)
  have hEc : HasCompactSupport (fun x => (hessian u x).det*(η x)^2*inverseHessianPair u f f x) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc.isCompact
    intro x hx
    by_contra hxn
    have hz := image_eq_zero_of_notMem_tsupport hxn
    apply hx
    simp [hz]
  have hEi : Integrable (fun x => (hessian u x).det*(η x)^2*inverseHessianPair u f f x) :=
    ((hdt.mul (hη.continuous.pow 2)).mul hQ).integrable_of_hasCompactSupport hEc
  have hlow : c*(∫ x in K, inverseHessianPair u f f x) ≤
      ∫ x, (hessian u x).det*(η x)^2*inverseHessianPair u f f x := by
    rw [← integral_const_mul]
    apply le_trans (setIntegral_mono_on
      ((ContinuousOn.integrableOn_compact hK hQ.continuousOn).const_mul c)
      hEi.integrableOn hK.measurableSet ?_) (setIntegral_le_integral hEi (Filter.Eventually.of_forall hEn))
    intro x hx
    rw [hηK x hx,one_pow,mul_one]
    exact mul_le_mul_of_nonneg_right (hdet x hx) (inverseHessianPair_self_nonneg (hp x) f)
  have hcut : (∫ x, (hessian u x).det*inverseHessianPair u η η x) ≤ M*J := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := B) (fun x hx => by
      rw [inverseHessianPair_eq_zero_outside_tsupport u η η (fun hh => hx (hηB hh)),mul_zero])]
    have hi : (∫ x in B, (hessian u x).det*inverseHessianPair u η η x) ≤
        ∫ x in B, M*((hessian u x).det*(hessian u x)⁻¹.trace) := by
      apply setIntegral_mono_on
        (ContinuousOn.integrableOn_compact hB (hdt.mul (contDiff_inverseHessianPair_global hu hp hη hη).continuous).continuousOn)
        ((ContinuousOn.integrableOn_compact hB (continuous_cofactor_trace hu hp).continuousOn).const_mul M)
        hB.measurableSet
      intro x hx
      have hh := (inverseHessianPair_le_trace_gradientSquared (u := u) (f := η) (hp x)).trans
        (mul_le_mul_of_nonneg_left (hgrad x hx) (hp x).inv.posSemidef.trace_nonneg)
      calc
        (hessian u x).det * inverseHessianPair u η η x ≤
            (hessian u x).det * ((hessian u x)⁻¹.trace * M) :=
          mul_le_mul_of_nonneg_left hh (hp x).det_pos.le
        _ = M * ((hessian u x).det * (hessian u x)⁻¹.trace) := by ring
    rw [integral_const_mul] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left hcof hM)
  have hC := linearizedMA_log_caccioppoli hu hp hs hpos hL hη hηc
  change _ ≤ 4*(∫ x, (hessian u x).det*inverseHessianPair u η η x) at hC
  apply (le_div_iff₀ hc).mpr
  nlinarith

end LogVariance


end
end AffineBernstein
end

end OAI
