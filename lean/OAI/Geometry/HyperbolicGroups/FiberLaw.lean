import Mathlib
import OAI.Geometry.HyperbolicGroups.Normalization

namespace OAI

section
section


noncomputable section
open scoped BigOperators
namespace HyperbolicObstruction
namespace FiniteLaw
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]

lemma uniform_map_mass [Nonempty α] (f : α → β) (b : β) :
    ((uniform : FiniteLaw α).map f).mass b = (Fintype.card {a // f a = b} : ℝ) / Fintype.card α := by
  classical
  unfold map uniform
  simp only
  have hi (a : α) : (if f a = b then 1 / (Fintype.card α : ℝ) else 0) =
      (if f a = b then (1 : ℝ) else 0) / Fintype.card α := by split_ifs <;> simp
  simp_rw [hi]
  rw [← Finset.sum_div]
  congr 1
  simp [Fintype.card_subtype]

lemma card_fibers (f : α → β) : ∑ b, Fintype.card {a // f a = b} = Fintype.card α := by
  classical
  simpa only [Fintype.card_sigma] using
    (Fintype.card_congr (Equiv.sigmaFiberEquiv f))

lemma uniform_map_eq_normalize [Nonempty α] (f : α → β) :
    (uniform : FiniteLaw α).map f =
      normalize (fun b => (Fintype.card {a // f a = b} : ℝ)) (fun _ => Nat.cast_nonneg _)
        (by rw [← Nat.cast_sum,card_fibers]; exact_mod_cast Fintype.card_pos (α := α)) := by
  apply ext
  funext b
  simp only [uniform_map_mass,normalize,← Nat.cast_sum,card_fibers]

lemma uniform_map_bound [Nonempty α] [Nonempty β] (f : α → β) (c : ℝ) :
    ((uniform : FiniteLaw α).map f).totalVariation uniform ≤
      (∑ b, |(Fintype.card {a // f a = b} : ℝ) - c|) / Fintype.card α := by
  rw [uniform_map_eq_normalize]
  simpa only [← Nat.cast_sum,card_fibers] using
    normalize_uniform_bound (fun b => (Fintype.card {a // f a = b} : ℝ)) (fun _ => Nat.cast_nonneg _)
      (by rw [← Nat.cast_sum,card_fibers]; exact_mod_cast Fintype.card_pos (α := α)) c

/-- The uniform law on a subset, included in the ambient finite set, differs
from the ambient uniform law by exactly the proportion excluded. -/
lemma uniform_subtype_tv [Nonempty α] (P : α → Prop) [DecidablePred P] [Nonempty {a // P a}] :
    ((uniform : FiniteLaw {a // P a}).map Subtype.val).totalVariation (uniform : FiniteLaw α) =
      1 - (Fintype.card {a // P a} : ℝ) / Fintype.card α := by
  classical
  let m : ℝ := Fintype.card {a // P a}
  let n : ℝ := Fintype.card α
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hmn : m ≤ n := by dsimp [m,n]; exact_mod_cast Fintype.card_subtype_le P
  have hrec : 1 / n ≤ 1 / m := one_div_le_one_div_of_le hm hmn
  have hmass (a : α) : ((uniform : FiniteLaw {a // P a}).map Subtype.val).mass a =
      if P a then 1 / m else 0 := by
    unfold map uniform
    dsimp only
    by_cases ha : P a
    · rw [Finset.sum_eq_single ⟨a,ha⟩]
      · simp [ha,m]
      · intro b _ hb; simp [show b.val ≠ a by intro hh; exact hb (Subtype.ext hh)]
      · simp
    · simp [ha,show ∀ b : {a // P a}, b.val ≠ a by intro b h; exact ha (h ▸ b.property)]
  unfold totalVariation
  simp_rw [hmass]
  change (∑ a, |(if P a then 1 / m else 0) - 1 / n|) / 2 = _
  have hi (a : α) : |(if P a then 1 / m else 0) - 1 / n| =
      (if P a then 1 / m - 2 / n else 0) + 1 / n := by
    split_ifs
    · rw [abs_of_nonneg (sub_nonneg.mpr hrec)]; ring
    · rw [zero_sub,abs_neg,abs_of_pos (one_div_pos.mpr hn)]; ring
  simp_rw [hi]
  rw [Finset.sum_add_distrib]
  have hs : (∑ a : α, if P a then 1 / m - 2 / n else 0) = m * (1 / m - 2 / n) := by
    simp [← Finset.sum_filter,Fintype.card_subtype,m]
    ring
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  change (m * (1 / m - 2 / n) + n * (1 / n)) / 2 = 1 - m / n
  field_simp
  ring

end FiniteLaw
end HyperbolicObstruction
end
end

section

end
end

end OAI
