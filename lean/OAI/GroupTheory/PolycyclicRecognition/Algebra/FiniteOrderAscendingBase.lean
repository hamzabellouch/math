import OAI.GroupTheory.PolycyclicRecognition.Analysis.AscendingBaseTransport
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentAbelianizationGenerators

namespace OAI

/-! # A finite-order ascending action forces finite generation -/

noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem finitelyGenerated_of_ascending_base_pow_eq_one (α : MulAut G)
    (r : ℕ) (hr : 0 < r) (hpow : α ^ r = 1)
    (hbase : HasFinitelyGeneratedAscendingBase α) : Group.FG G := by
  obtain ⟨P, hPfg, hPstable, hPcover⟩ := hbase
  have htop : P = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨n, hn⟩ := hPcover g
    have hgn := (mem_automorphismStage_iff _ _ _ _).mp hn
    have he : (α ^ ((r - 1) * n)) ((α ^ n) g) = g := by
      have hm : (r - 1) * n + n = r * n := by
        calc
          (r - 1) * n + n = ((r - 1) + 1) * n := by rw [add_mul, one_mul]
          _ = r * n := by rw [Nat.sub_add_cancel (by omega)]
      rw [← MulAut.mul_apply, ← pow_add, hm, pow_mul, hpow, one_pow]
      rfl
    exact he ▸ automorphism_pow_mem_of_stable α P hPstable ((r - 1) * n) hgn
  exact Group.fg_def.mpr (htop ▸ hPfg)

theorem quotient_conjugation_pow_eq_one
    (N : Subgroup G) [N.Normal] (t : G) (r : ℕ) (ht : t ^ r ∈ N) :
    (characteristicQuotientAut (commutator N) (MulAut.conjNormal (H := N) t)) ^ r = 1 := by
  rw [← map_pow, ← map_pow]
  apply MulEquiv.ext
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (commutator N) x
  let b : N := ⟨t ^ r, ht⟩
  have he : MulAut.conjNormal (H := N) (t ^ r) a = b * a * b⁻¹ := rfl
  change (QuotientGroup.mk' (commutator N)) (MulAut.conjNormal (H := N) (t ^ r) a) =
    (QuotientGroup.mk' (commutator N)) a
  rw [he, map_mul, map_mul, map_inv]
  rw [mul_comm' ((QuotientGroup.mk' (commutator N)) b), mul_assoc, mul_inv_cancel, mul_one]

end PolycyclicRecognition

end

end OAI
