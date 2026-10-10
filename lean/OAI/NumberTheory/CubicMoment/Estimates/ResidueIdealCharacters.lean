import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveConductor
import OAI.NumberTheory.CubicMoment.Estimates.PrimeToThreeIdeals
import Mathlib.NumberTheory.MulChar.Lemmas

namespace OAI

/-! The finite residue character as an actual complete ideal character,
and exact restoration of Euler factors after primitive reduction. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def residueIdealChar (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν : EisensteinIdealExponent) : ℂ :=
  χ (Ideal.Quotient.mk (modulus q) (idealExponentGenerator ν))

lemma residueIdealChar_add (q : Eisenstein) (χ : MulChar (Residues q) ℂ)
    (ν κ : EisensteinIdealExponent) :
    residueIdealChar q χ (ν+κ) = residueIdealChar q χ ν*residueIdealChar q χ κ := by
  simp only [residueIdealChar,idealExponentGenerator_add,map_mul]

lemma residueChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (x : Residues q) : ‖χ x‖ ≤ 1 := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  by_cases hx : IsUnit x
  · obtain ⟨u,rfl⟩ := hx
    have he : ‖χ (u : Residues q)‖ = 1 :=
      Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
    exact he.le
  · rw [MulChar.map_nonunit χ hx,norm_zero]
    exact zero_le_one

lemma residueIdealChar_norm_le_one {q : Eisenstein} (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (ν : EisensteinIdealExponent) :
    ‖residueIdealChar q χ ν‖ ≤ 1 := residueChar_norm_le_one hq χ _

lemma residueIdealChar_primaryMixed {a b : Eisenstein}
    (ha : primary a) (hb : primary b) (ν : EisensteinIdealExponent) :
    residueIdealChar (3*(a*b)) (primaryMixedResidueChar a b ha hb) ν =
      primaryMixedIdealChar a b ν := primaryMixedResidueChar_mk ha hb _

lemma ideal_coprime_support {q : Eisenstein} (hq : q ≠ 0)
    (ν : EisensteinIdealExponent) :
    IsCoprime q (idealExponentGenerator ν) ↔
      ∀ p ∈ (idealExponentOf q).support, ν p = 0 := by
  rw [isCoprime_comm,isCoprime_iff_idealExponent_disjoint (idealExponentGenerator_ne_zero ν) hq,
    idealExponentOf_generator]
  constructor
  · intro h p hp
    rcases h p with hn | hq
    · exact hn
    · exact False.elim ((Finsupp.mem_support_iff.mp hp) hq)
  · intro h p
    by_cases hp : p ∈ (idealExponentOf q).support
    · exact Or.inl (h p hp)
    · exact Or.inr (Finsupp.notMem_support_iff.mp hp)

lemma induced_residueIdealChar {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (ν : EisensteinIdealExponent) :
    residueIdealChar q χ ν =
      if ∀ p ∈ (idealExponentOf q).support, ν p = 0 then residueIdealChar d ψ ν else 0 := by
  simpa only [residueIdealChar,ideal_coprime_support hq] using
    h.restriction (idealExponentGenerator ν)

/-- Primitive reduction gives an exact finite Euler inclusion-exclusion
for the original complete smooth sum, with every rescaling retained. -/
theorem induced_residue_smooth_euler {q d : Eisenstein} (hq : q ≠ 0)
    {χ : MulChar (Residues q) ℂ} {ψ : MulChar (Residues d) ℂ}
    (h : ResidueCharacterInduces q d χ ψ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) {Z : ℝ} (hZ : 0 < Z) :
    (∑' ν, residueIdealChar q χ ν*W (idealExponentNorm ν/Z)) =
      ∑ T ∈ (idealExponentOf q).support.powerset,
        (-1:ℂ)^T.card*residueIdealChar d ψ (primeSetExponent T)*
          ∑' κ, residueIdealChar d ψ κ*
            W (idealExponentNorm κ/(Z/idealExponentNorm (primeSetExponent T))) := by
  have he := smooth_ideal_euler_exclusion (idealExponentOf q).support (residueIdealChar d ψ)
    (residueIdealChar_add d ψ) W hW hZ
  rw [← he]
  apply tsum_congr
  intro ν
  rw [induced_residueIdealChar hq h]
  split <;> simp

end CubicFirstMoment

end

end OAI
