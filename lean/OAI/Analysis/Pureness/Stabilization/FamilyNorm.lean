import OAI.Analysis.Pureness.Stabilization.FamilyQuotient

namespace OAI
noncomputable section
open scoped ENNReal Topology
open Filter
namespace CuntzTrace
variable {A : ℕ → Type*} [∀ n, NonUnitalCStarAlgebra (A n)]
namespace BoundedFamilies
lemma norm_bounded (x : BoundedFamilies A) :
    IsBoundedUnder (· ≤ ·) atTop (fun n => ‖x n‖) :=
  isBoundedUnder_of ⟨‖x‖, norm_coordinate_le x⟩
lemma norm_cobounded (x : BoundedFamilies A) :
    IsCoboundedUnder (· ≤ ·) atTop (fun n => ‖x n‖) :=
  (isBoundedUnder_of ⟨0, fun n => norm_nonneg (x n)⟩ :
    IsBoundedUnder (· ≥ ·) atTop (fun n => ‖x n‖)).isCoboundedUnder_le
lemma limsup_norm_nonneg (x : BoundedFamilies A) :
    0 ≤ limsup (fun n => ‖x n‖) atTop :=
  le_limsup_of_frequently_le (Eventually.of_forall (fun n => norm_nonneg (x n))).frequently (norm_bounded x)

lemma limsup_norm_le_of_vanishing_sub (x y : BoundedFamilies A)
    (h : x-y ∈ vanishing (A := A)) : limsup (fun n => ‖x n‖) atTop ≤ ‖y‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (norm_cobounded x)
  have he : ∀ᶠ n in atTop, ‖x n-y n‖ < ε := by
    have h0 := h
    have h0' : Tendsto (fun n => ‖x n-y n‖) atTop (𝓝 0) := h0
    exact (tendsto_order.mp h0').2 ε hε
  filter_upwards [he] with n hn
  have ht := norm_le_norm_sub_add (x n) (y n)
  have hy := norm_coordinate_le y n
  linarith

def tail (x : BoundedFamilies A) (N : ℕ) : BoundedFamilies A :=
  ⟨fun n => if N ≤ n then x n else 0, memℓp_infty ⟨‖x‖, by
    rintro _ ⟨n,rfl⟩
    change ‖if N ≤ n then x n else 0‖ ≤ ‖x‖
    split_ifs
    · exact norm_coordinate_le x n
    · simpa only [norm_zero] using norm_nonneg x⟩⟩
lemma tail_sub_mem (x : BoundedFamilies A) (N : ℕ) : tail x N-x ∈ vanishing (A := A) := by
  change Tendsto (fun n => ‖(tail x N) n-x n‖) atTop (𝓝 0)
  apply (tendsto_congr' (show (fun n => ‖(tail x N) n-x n‖) =ᶠ[atTop] fun _ => (0 : ℝ) from ?_)).mpr
    tendsto_const_nhds
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [tail, hn]
lemma norm_tail_le (x : BoundedFamilies A) (N : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ n, N ≤ n → ‖x n‖ ≤ C) : ‖tail x N‖ ≤ C := by
  apply lp.norm_le_of_forall_le hC
  intro n
  change ‖if N ≤ n then x n else 0‖ ≤ C
  split_ifs with hn
  · exact h n hn
  · simpa using hC
end BoundedFamilies
namespace FamilyQuotient
open BoundedFamilies

theorem norm_mk_eq_limsup (x : BoundedFamilies A) :
    ‖mk x‖ = limsup (fun n => ‖x n‖) atTop := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_lt_of_limsup_lt
      (lt_add_of_pos_right (limsup (fun n => ‖x n‖) atTop) hε) (norm_bounded x))
    have heq : mk (tail x N) = mk x := (mk_eq_mk_iff _ _).mpr (tail_sub_mem x N)
    rw [← heq]
    exact (norm_mk_le _).trans (norm_tail_le x N _ (by linarith [limsup_norm_nonneg x])
      (fun n hn => (hN n hn).le))
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨y,hy,hn⟩ := exists_norm_mk_lt (mk x) hε
    have hxy : x-y ∈ vanishing (A := A) := (mk_eq_mk_iff _ _).mp hy.symm
    exact (limsup_norm_le_of_vanishing_sub x y hxy).trans hn.le

lemma norm_star_mul_self_eq (x : FamilyQuotient A) : ‖star x*x‖ = ‖x‖*‖x‖ := by
  obtain ⟨x,rfl⟩ := mk_surjective x
  rw [← mk_star, ← mk_mul, norm_mk_eq_limsup, norm_mk_eq_limsup]
  let f : ℝ → ℝ := fun t => max t 0 * max t 0
  have hf : Monotone f := by
    intro a b hab
    exact mul_self_le_mul_self (le_max_right _ _) (max_le_max hab le_rfl)
  have hc : Continuous f := (continuous_id.max continuous_const).mul (continuous_id.max continuous_const)
  have h := hf.map_limsup_of_continuousAt (fun n => ‖x n‖) hc.continuousAt
    (norm_bounded x) (norm_cobounded x)
  have he : f ∘ (fun n => ‖x n‖) = fun n => ‖star (x n)*x n‖ := by
    funext n
    simp only [Function.comp_apply, f, max_eq_left (norm_nonneg (x n)), CStarRing.norm_star_mul_self]
  rw [he] at h
  dsimp [f] at h
  rw [max_eq_left (limsup_norm_nonneg x)] at h
  exact h.symm

instance : CStarRing (FamilyQuotient A) where
  norm_mul_self_le x := (norm_star_mul_self_eq x).symm.le

instance : NonUnitalCStarAlgebra (FamilyQuotient A) where
end FamilyQuotient
end CuntzTrace

end

end OAI
