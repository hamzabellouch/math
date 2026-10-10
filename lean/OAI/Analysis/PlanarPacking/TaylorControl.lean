import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

namespace SharpPlanar
open scoped BigOperators
open Set
lemma jet_iteratedDeriv {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) (ell : ℕ) :
    iteratedDeriv ell (J 0)=J ell := by
  induction ell with
  | zero => rfl
  | succ ell ih =>
    rw [iteratedDeriv_succ,ih]
    funext s
    exact (hJ ell s).deriv
lemma jet_contDiff {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s) : ContDiff ℝ (⊤ : ℕ∞) (J 0) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro ell _
  rw [jet_iteratedDeriv hJ]
  exact fun s => (hJ ell s).differentiableAt
noncomputable def jetTaylor (J : ℕ → ℝ → ℝ) (n : ℕ) (m u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n+1), J k m/(k.factorial:ℝ)*u^k
lemma jetTaylor_zero (J : ℕ → ℝ → ℝ) (m u : ℝ) : jetTaylor J 0 m u=J 0 m := by
  simp [jetTaylor]
lemma jetTaylor_at_zero (J : ℕ → ℝ → ℝ) (n : ℕ) (m : ℝ) : jetTaylor J n m 0=J 0 m := by
  unfold jetTaylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0; simp [zero_pow hb0]
  · simp
lemma jetTaylor_eq_within {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    {m u : ℝ} (hu : u≠0) (n : ℕ) :
    taylorWithinEval (J 0) n (uIcc m (m+u)) m (m+u)=jetTaylor J n m u := by
  rw [taylor_within_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc (by intro he; apply hu; linarith))
    ((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤))).contDiffAt (left_mem_uIcc),jet_iteratedDeriv hJ]
  simp only [add_sub_cancel_left,smul_eq_mul]
  ring

lemma jetTaylor_error {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (n : ℕ) (m u M : ℝ)
    (hM : ∀ s ∈ uIcc m (m+u), |J (n+1) s| ≤ M) :
    |J 0 (m+u)-jetTaylor J n m u| ≤ M*|u|^(n+1)/((n+1).factorial:ℝ) := by
  by_cases hu : u=0
  · subst u; simp [jetTaylor_at_zero]
  obtain ⟨s,hs,he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := J 0) (n := n) (x₀ := m) (x := m+u) (by intro he; apply hu; linarith : m≠m+u)
    (((jet_contDiff hJ).of_le (by exact_mod_cast (le_top : ((n+1):ℕ∞) ≤ ⊤))).contDiffOn)
  rw [jetTaylor_eq_within hJ hu,jet_iteratedDeriv hJ,add_sub_cancel_left] at he
  rw [he,abs_div,abs_mul,abs_pow,abs_of_pos (show 0 < ((n+1).factorial:ℝ) from Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hM s ⟨hs.1.le,hs.2.le⟩)
    (pow_nonneg (abs_nonneg u) _)) (Nat.cast_nonneg _)
noncomputable def jetPartial (J : ℕ → ℝ → ℝ) (q : ℕ) (m u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range q, J k m/(k.factorial:ℝ)*u^k
lemma jetPartial_succ (J : ℕ → ℝ → ℝ) (n : ℕ) (m u : ℝ) :
    jetPartial J (n+1) m u=jetTaylor J n m u := rfl
lemma jetPartial_error {J : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (q : ℕ) (m u M : ℝ)
    (hM : ∀ s ∈ uIcc m (m+u), |J q s| ≤ M) :
    |J 0 (m+u)-jetPartial J q m u| ≤ M*|u|^q/(q.factorial:ℝ) := by
  cases q with
  | zero => simpa [jetPartial] using hM (m+u) right_mem_uIcc
  | succ n => exact jetTaylor_error hJ n m u M hM
noncomputable def deletedPolynomial (T : ℕ → ℝ → ℝ) (ν d : ℕ) (m u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (d+1), T (r+ν) m/((r+ν).factorial:ℝ)*u^r
lemma jetPartial_split (T : ℕ → ℝ → ℝ) (ν d : ℕ) (m u : ℝ) :
    jetPartial T (ν+(d+1)) m u=jetPartial T ν m u+u^ν*deletedPolynomial T ν d m u := by
  unfold jetPartial deletedPolynomial
  rw [Finset.sum_range_add,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Nat.add_comm ν r,pow_add]
  ring
lemma jetPartial_sub (J T : ℕ → ℝ → ℝ) (q : ℕ) (m u : ℝ) :
    jetPartial (fun ell s => J ell s-T ell s) q m u=
      jetPartial J q m u-jetPartial T q m u := by
  simp only [jetPartial,sub_div,sub_mul,Finset.sum_sub_distrib]

lemma deletedPolynomial_error {J T : ℕ → ℝ → ℝ}
    (hJ : ∀ ell s, HasDerivAt (J ell) (J (ell+1) s) s)
    (hT : ∀ ell s, HasDerivAt (T ell) (T (ell+1) s) s)
    (ν d : ℕ) (m u E R : ℝ)
    (hj : ∀ k<ν, J k m=0)
    (hE : ∀ s ∈ uIcc m (m+u), |J ν s-T ν s|≤E)
    (hR : ∀ s ∈ uIcc m (m+u), |T (ν+(d+1)) s|≤R) :
    |J 0 (m+u)-u^ν*deletedPolynomial T ν d m u| ≤
      E*|u|^ν/(ν.factorial:ℝ)+R*|u|^(ν+(d+1))/((ν+(d+1)).factorial:ℝ) := by
  have hp : jetPartial J ν m u=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [hj k (Finset.mem_range.mp hk)]
  have hd := jetPartial_error (fun ell s => (hJ ell s).sub (hT ell s)) ν m u E hE
  have ht := jetPartial_error hT (ν+(d+1)) m u R hR
  change |J 0 (m+u)-T 0 (m+u)-jetPartial (fun ell s => J ell s-T ell s) ν m u| ≤ _ at hd
  rw [jetPartial_sub,hp,zero_sub] at hd
  rw [jetPartial_split] at ht
  calc
    _ = |((J 0 (m+u)-T 0 (m+u))- -jetPartial T ν m u)+
        (T 0 (m+u)-(jetPartial T ν m u+u^ν*deletedPolynomial T ν d m u))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add hd ht)
end SharpPlanar

end OAI
