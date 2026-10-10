import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace OAI
noncomputable section
namespace CuntzPureness.OrderedSemigroup
variable (G : Type*) [AddCommGroup G]

abbrev RationalGroup := LocalizedModule (nonZeroDivisors ℤ) G
instance rationalGroupModule : Module ℚ (RationalGroup G) :=
  LocalizedModule.moduleOfIsLocalization (S := nonZeroDivisors ℤ) (M := G) (T := ℚ)

abbrev toRationalGroup : G →ₗ[ℤ] RationalGroup G :=
  LocalizedModule.mkLinearMap (nonZeroDivisors ℤ) G

theorem rationalGroup_eq_iff (g h : G) :
    toRationalGroup G g = toRationalGroup G h ↔
      ∃ n : ℕ, 0 < n ∧ n • g = n • h := by
  change LocalizedModule.mk g 1 = LocalizedModule.mk h 1 ↔ _
  rw [LocalizedModule.mk_eq]
  simp only [one_smul]
  constructor
  · rintro ⟨⟨k,hk⟩,he⟩
    have hk0 := nonZeroDivisors.ne_zero hk
    change k • g = k • h at he
    cases k with
    | ofNat n =>
      exact ⟨n, by
        apply Nat.pos_of_ne_zero
        intro hn
        apply hk0
        simp [hn], by simpa using he⟩
    | negSucc n =>
      refine ⟨n+1, Nat.succ_pos n, ?_⟩
      change (-((n+1 : ℕ) : ℤ)) • g = (-((n+1 : ℕ) : ℤ)) • h at he
      simpa only [neg_smul, neg_inj, natCast_zsmul] using he
  · rintro ⟨n,hn,he⟩
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    simpa using he

theorem rationalGroup_denominator (z : RationalGroup G) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : G, (n : ℚ) • z = toRationalGroup G g := by
  induction z using LocalizedModule.induction_on with
  | h g s =>
   obtain ⟨k,hk⟩ := s
   have he : (k : ℚ) • (LocalizedModule.mk g ⟨k,hk⟩ : RationalGroup G) = toRationalGroup G g := by
     have heq : (k : ℚ) = IsLocalization.mk' ℚ k (1 : nonZeroDivisors ℤ) := by simp
     rw [heq, LocalizedModule.mk'_smul_mk, one_mul]
     exact LocalizedModule.mk_cancel ⟨k,hk⟩ g
   have hk0 := nonZeroDivisors.ne_zero hk
   cases k with
   | ofNat n =>
     refine ⟨n, ?_, g, by simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using he⟩
     apply Nat.pos_of_ne_zero
     intro hn
     apply hk0
     simp [hn]
   | negSucc n =>
    refine ⟨n+1, Nat.succ_pos n, -g, ?_⟩
    change (-((n+1 : ℕ) : ℚ)) • _ = _ at he
    rw [neg_smul] at he
    have h := congrArg Neg.neg he
    simpa only [neg_neg, map_neg] using h
end CuntzPureness.OrderedSemigroup

end

end OAI
