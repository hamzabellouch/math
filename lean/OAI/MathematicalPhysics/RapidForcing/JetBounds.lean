import OAI.MathematicalPhysics.RapidForcing.FieldExpressions

namespace OAI

open scoped BigOperators Topology ENNReal ContDiff
open Set Filter
namespace RapidForcing

lemma finite_order (k : ℕ) : (k : ℕ∞ω) ≤ (⊤ : ℕ∞) := by
  exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤)

section JetEstimates
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
lemma jet_sum_le {ι : Type} (s : Finset ι) (f : ι → E → F)
    (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i)) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i ∈ s, f i y) x‖ ≤
      ∑ i ∈ s, ‖iteratedFDeriv ℝ k (f i) x‖ := by
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => ((hf i hi).of_le (finite_order k)).contDiffAt)]
  exact norm_sum_le _ _
lemma jet_postcomp_le (L : F →L[ℝ] G) {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (x : E) (C : ℝ) (hC : ‖L‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => L (f y)) x‖ ≤ C * ‖iteratedFDeriv ℝ k f x‖ :=
  (L.norm_iteratedFDeriv_comp_left hf.contDiffAt (finite_order k)).trans
    (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
lemma jet_smul_const_le {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v : F) (k : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => f y • v) x‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ k f x‖ := by
  exact jet_postcomp_le (ContinuousLinearMap.toSpanSingleton ℝ v) hf k x ‖v‖
    (by rw [ContinuousLinearMap.norm_toSpanSingleton])
end JetEstimates

namespace EffectiveProfile.Formula
variable {d : ℕ}
lemma fderiv_eq_sum (a : Formula d) (x : Fin d → ℝ) :
    fderiv ℝ a.value x = ∑ i : Fin d, (a.diff i).value x • ContinuousLinearMap.proj i := by
  ext v
  have he : v = ∑ i : Fin d, (v i) • Pi.single i (1 : ℝ) := by
    simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using (Finset.univ_sum_single v).symm
  calc
    _ = ∑ i : Fin d, v i * (a.diff i).value x := by
      rw [he, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [map_smul, fderiv_apply_single, smul_eq_mul]
      congr 1
      exact congrFun he i
    _ = _ := by simp [mul_comm]

lemma jet_succ_le (a : Formula d) (k : ℕ) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ (k+1) a.value x‖ ≤
      ∑ i : Fin d, ‖iteratedFDeriv ℝ k (a.diff i).value x‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ a.value = fun y => ∑ i : Fin d,
      (a.diff i).value y • ContinuousLinearMap.proj i := funext (a.fderiv_eq_sum)
  rw [he]
  apply (jet_sum_le _ _ (fun i _ => (a.diff i).contDiff.smul contDiff_const) _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hp : ‖(ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by simpa using norm_le_pi_norm v i)
  exact (jet_smul_const_le (a.diff i).contDiff _ k x).trans (by
    simpa using mul_le_mul_of_nonneg_right hp (norm_nonneg (iteratedFDeriv ℝ k (a.diff i).value x)))

def allDiff (as : List (Formula d)) : List (Formula d) :=
  as.flatMap fun a => (List.finRange d).map (fun i => a.diff i)

def jetBound (R : ℚ) (k : ℕ) (a : Formula d) : ℚ :=
  ((allDiff^[k] [a]).map (fun e => e.bound R)).sum

lemma jetBound_nonneg (R : ℚ) (k : ℕ) (a : Formula d) : 0 ≤ a.jetBound R k := by
  apply List.sum_nonneg
  intro r hr
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp hr
  exact e.bound_nonneg R

lemma jet_list_le (R : ℚ) (k : ℕ) (as : List (Formula d)) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ |(R : ℝ)|) :
    (as.map fun a => ‖iteratedFDeriv ℝ k a.value x‖).sum ≤
      (((allDiff^[k] as).map fun a => a.bound R).sum : ℚ) := by
  induction k generalizing as with
  | zero =>
    simp only [Function.iterate_zero_apply, norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    induction as with
    | nil => simp
    | cons a as ih =>
      simpa only [List.map_cons, List.sum_cons, Rat.cast_add] using add_le_add (a.abs_value_le R x hx) ih
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    apply le_trans _ (ih (allDiff as))
    induction as with
    | nil => simp [allDiff]
    | cons a as ih' =>
      simp only [List.map_cons, List.sum_cons, allDiff, List.flatMap_cons, List.map_append, List.sum_append] at ih' ⊢
      apply add_le_add _ ih'
      simpa only [List.map_map, Function.comp_def, ← List.ofFn_eq_map, List.map_ofFn, List.sum_ofFn] using a.jet_succ_le k x

lemma norm_jet_le (R : ℚ) (k : ℕ) (a : Formula d) (x : Fin d → ℝ)
    (hx : ∀ i, |x i| ≤ |(R : ℝ)|) :
    ‖iteratedFDeriv ℝ k a.value x‖ ≤ (a.jetBound R k : ℝ) := by
  simpa only [List.map_singleton, List.sum_singleton, jetBound] using jet_list_le R k [a] x hx
end EffectiveProfile.Formula
end RapidForcing

end OAI
