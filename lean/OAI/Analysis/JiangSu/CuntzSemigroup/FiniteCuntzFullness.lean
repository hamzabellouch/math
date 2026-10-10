import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.FiniteCuntzSums
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixSimplicity

namespace OAI


noncomputable section
namespace Pureness
open TraceCone
open scoped CStarAlgebra ENNReal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma finitePositiveClass_eq_zero_iff (n : ℕ) (M : Positive (FinMatrix A n)) :
    finitePositiveClass n M = 0 ↔ M.1 = 0 := by
  constructor
  · intro h
    have ho : finitePositiveClass n M ≤ finitePositiveClass n Positive.zero := by
      rw [h, finitePositiveClass_zero]
    exact (cuntzSubequiv_zero_iff M.1).mp ((finitePositiveClass_le_iff n M Positive.zero).mp ho)
  · intro h
    have he : M = Positive.zero := Subtype.ext h
    rw [he, finitePositiveClass_zero]

private theorem positive_le_norm_smul_one {B : Type*} [CStarAlgebra B]
    [PartialOrder B] [StarOrderedRing B] (b : Positive B) : b.1 ≤ ‖b.1‖ • (1 : B) := by
  simpa only [← Algebra.algebraMap_eq_smul_one] using b.2.isSelfAdjoint.le_algebraMap_norm_self

theorem finitePositiveClass_dominated (hsimple : TopologicallySimple A)
    (L : ℕ) (M N : Positive (FinMatrix A L)) (hN : N.1 ≠ 0) :
    ∃ q : ℕ, finitePositiveClass L M ≤ q • finitePositiveClass L N := by
  have hL : 0 < L := by
    by_contra h
    have he : L = 0 := Nat.eq_zero_of_not_pos h
    subst L
    apply hN
    ext i j
    exact Fin.elim0 i
  let : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  obtain ⟨q,s,hs⟩ := fullness (matrix_topologicallySimple hsimple) N.1 N.2 hN
  let C : Fin q → Positive (FinMatrix A L) := fun i =>
    ⟨star (s i)*N.1*s i, star_left_conjugate_nonneg N.2 (s i)⟩
  have hC : ∀ i ∈ (Finset.univ : Finset (Fin q)), finitePositiveClass L (C i) ≤ finitePositiveClass L N := by
    intro i _
    exact (finitePositiveClass_le_iff L _ _).mpr (cuntzSubequiv_conjugate N.1 (s i))
  have hsum := finitePositiveClass_sum_bound L Finset.univ C (finitePositiveClass L N) hC
  have he : (⟨∑ i, (C i).1, Finset.sum_nonneg fun i _ => (C i).2⟩ : Positive (FinMatrix A L)) =
      ⟨1,zero_le_one⟩ := Subtype.ext hs
  have hunit : finitePositiveClass (A := A) L ⟨1,zero_le_one⟩ ≤ q • finitePositiveClass L N := by
    simpa only [he, Finset.card_univ, Fintype.card_fin] using hsum
  refine ⟨q, ?_⟩
  apply le_trans _ hunit
  apply (finitePositiveClass_le_iff L _ _).mpr
  apply (cuntzSubequiv_iff_shared _ _).mpr
  apply TraceCone.CuntzBelow.of_le_smul M ⟨1,zero_le_one⟩ ‖M.1‖ (norm_nonneg _)
  exact positive_le_norm_smul_one M

theorem finiteCuntz_nonzero_orderUnit (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0)
    (x : finiteCuntzSubmonoid (A := A)) : ∃ q : ℕ, x ≤ q • y := by
  obtain ⟨n,M,hM⟩ := x.2
  obtain ⟨m,N,hN⟩ := y.2
  have hx : finitePositiveClass n M = x := Subtype.ext hM.symm
  have hyEq : finitePositiveClass m N = y := Subtype.ext hN.symm
  rw [← hx, ← hyEq]
  rw [← hyEq] at hy
  let M' := Positive.map (matrixInclusion (le_max_left n m)) M
  let N' := Positive.map (matrixInclusion (le_max_right n m)) N
  have hn : N'.1 ≠ 0 := by
    intro h
    apply hy
    rw [← finitePositiveClass_inclusion (le_max_right n m) N]
    exact (finitePositiveClass_eq_zero_iff _ N').mpr h
  obtain ⟨q,hq⟩ := finitePositiveClass_dominated hsimple (max n m) M' N' hn
  exact ⟨q, by simpa only [M',N',finitePositiveClass_inclusion] using hq⟩

theorem finiteCuntz_state_finite (hsimple : TopologicallySimple A)
    (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0)
    (f : OrderedSemigroup.StateSpace y) (x : finiteCuntzSubmonoid (A := A)) : f.1 x ≠ ⊤ :=
  OrderedSemigroup.state_finite_on_principalIdeal f (finiteCuntz_nonzero_orderUnit hsimple y hy x)

end Pureness
end

end OAI
