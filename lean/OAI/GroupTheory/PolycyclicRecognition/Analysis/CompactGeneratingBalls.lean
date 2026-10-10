import Mathlib.Geometry.Group.WordMetric
import Mathlib.Topology.Algebra.Group.Compact

namespace OAI

/-! # Compact bounds for words in a compact symmetric generating set -/

noncomputable section
namespace PolycyclicRecognition

open Set
open scoped Pointwise

variable {G : Type*} [Group G] (K : Set G) (hK : Subgroup.closure K = ⊤)
  (hsymm : ∀ g : G, g⁻¹ ∈ K ↔ g ∈ K)

include hsymm in
theorem generator_wordProd_mem_pow (l : List (K × Bool)) :
    (Group.Generators.ofSet hK).wordProd l ∈ K ^ l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.length_cons, pow_succ', Group.Generators.wordProd_cons]
    apply Set.mul_mem_mul ?_ ih
    obtain ⟨k, b⟩ := b
    cases b with
    | false => exact (hsymm k).mpr k.property
    | true => exact k.property

include hsymm in
theorem wordLength_ball_subset_pow (hone : (1 : G) ∈ K) (n : ℕ) :
    {g | (Group.Generators.ofSet hK).wordLength g ≤ n} ⊆ K ^ n := by
  intro g hg
  obtain ⟨l, hl, he⟩ := (Group.Generators.ofSet hK).wordLength_le_iff g |>.mp hg
  rw [← he]
  exact Set.pow_right_monotone hone hl (generator_wordProd_mem_pow K hK hsymm l)

theorem isCompact_set_pow [TopologicalSpace G] [ContinuousMul G]
    (hcompact : IsCompact K) (n : ℕ) : IsCompact (K ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simpa only [pow_succ] using ih.mul hcompact

end PolycyclicRecognition

end

end OAI
