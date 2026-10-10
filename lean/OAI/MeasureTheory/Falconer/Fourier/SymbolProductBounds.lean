import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

 theorem iteratedDeriv_tsupport {f : ℝ → ℝ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

 theorem product_iteratedDeriv_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) {b : ι} (hb : b ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (fun x => ∏ i ∈ S, f i x)) ⊆ tsupport (f b) := by
  apply (iteratedDeriv_tsupport j).trans
  have he : (fun x => ∏ i ∈ S, f i x) =
      fun x => f b x * ∏ i ∈ S.erase b, f i x := by
    funext x
    exact (Finset.mul_prod_erase S (fun i => f i x) hb).symm
  rw [he]
  exact tsupport_mul_subset_left

 theorem iteratedDeriv_product_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) (c : ι → ℝ) (d : ℝ) (hd : 0 ≤ d)
    (J : ℕ) (hc : ∀ i ∈ S, 0 ≤ c i)
    (hf : ∀ i ∈ S, ContDiff ℝ ∞ (f i))
    (hb : ∀ i ∈ S, ∀ n ≤ J, ∀ x, ‖iteratedDeriv n (f i) x‖ ≤ c i * d^n) :
    ∀ j ≤ J, ∀ x, ‖iteratedDeriv j (fun x => ∏ i ∈ S, f i x) x‖ ≤
      (∏ i ∈ S, c i) * ((S.card:ℝ)*d)^j := by
  induction S using Finset.induction_on with
  | empty =>
    intro j hj x
    cases j with
    | zero => simp
    | succ j => simp [iteratedDeriv_const]
  | @insert a S ha ih =>
    have hcS : ∀ i ∈ S, 0 ≤ c i := fun i hi => hc i (Finset.mem_insert_of_mem hi)
    have hfS : ∀ i ∈ S, ContDiff ℝ ∞ (f i) := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hbS := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have ih := ih hcS hfS hbS
    intro j hj x
    have hfa : ContDiffAt ℝ j (f a) x :=
      ((hf a (Finset.mem_insert_self _ _)).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    have hfp : ContDiffAt ℝ j (fun x => ∏ i ∈ S, f i x) x :=
      ((contDiff_prod fun i hi => hfS i hi).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))).contDiffAt
    simp only [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.cast_add, Nat.cast_one]
    rw [iteratedDeriv_fun_mul hfa hfp]
    calc
      _ ≤ ∑ k ∈ Finset.range (j+1),
          (j.choose k:ℝ) * (c a*d^k) * ((∏ i ∈ S, c i)*((S.card:ℝ)*d)^(j-k)) := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro k hk
        have hk : k ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        simp only [norm_mul, Real.norm_natCast]
        have hca := hc a (Finset.mem_insert_self _ _)
        gcongr
        · exact hb a (Finset.mem_insert_self _ _) k (hk.trans hj) x
        · exact ih (j-k) ((Nat.sub_le _ _).trans hj) x
      _ = (c a * ∏ i ∈ S, c i) * (d+(S.card:ℝ)*d)^j := by
        rw [add_pow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = _ := by congr 2; ring

end PlanarFalconer

end OAI
