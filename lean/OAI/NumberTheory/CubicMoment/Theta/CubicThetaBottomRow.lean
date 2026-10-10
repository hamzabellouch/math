import OAI.NumberTheory.CubicMoment.Theta.CubicThetaKubotaCharacter

namespace OAI

/-! The actual primitive bottom rows for the cubic Eisenstein series.
Every admissible row is completed inside the principal level-three group,
using Bezout with 3c rather than an unproved choice of congruences. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

lemma cubicThetaPrincipalGroup_mem_iff (g : SL(2,Eisenstein)) :
    g ∈ cubicThetaPrincipalGroup ↔
      primary (g 0 0) ∧ (3:Eisenstein) ∣ g 0 1 ∧
      (3:Eisenstein) ∣ g 1 0 ∧ primary (g 1 1) := by
  constructor
  · intro hg
    have hdiag := cubicThetaPrincipalGroup_diagonal_primary ⟨g,hg⟩
    have hoff := cubicThetaPrincipalGroup_offDiagonal ⟨g,hg⟩
    exact ⟨hdiag.1,hoff.1,hoff.2,hdiag.2⟩
  · rintro ⟨ha,hb,hc,hd⟩
    let q := Ideal.Quotient.mk (modulus (3:Eisenstein))
    have hz {z : Eisenstein} (h : (3:Eisenstein) ∣ z) : q z = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr h
    have hqa : q (g 0 0) = 1 := by
      have he := hz ha
      rw [map_sub,map_one] at he
      exact sub_eq_zero.mp he
    have hqd : q (g 1 1) = 1 := by
      have he := hz hd
      rw [map_sub,map_one] at he
      exact sub_eq_zero.mp he
    change Matrix.SpecialLinearGroup.map q g = 1
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hqa
    · exact hz hb
    · exact hz hc
    · exact hqd

@[ext] structure CubicThetaBottomRow where
  c : Eisenstein
  d : Eisenstein
  c_three : (3:Eisenstein) ∣ c
  d_primary : primary d
  coprime : IsCoprime c d

def cubicThetaBottomRow (g : cubicThetaPrincipalGroup) : CubicThetaBottomRow where
  c := g.val 1 0
  d := g.val 1 1
  c_three := (cubicThetaPrincipalGroup_offDiagonal g).2
  d_primary := (cubicThetaPrincipalGroup_diagonal_primary g).2
  coprime := by
    refine ⟨-g.val 0 1,g.val 0 0,?_⟩
    linear_combination cubicThetaPrincipalGroup_det g

theorem cubicThetaBottomRow_surjective : Function.Surjective cubicThetaBottomRow := by
  intro r
  obtain ⟨a,k,h⟩ := (primary_coprime_three r.d_primary).mul_right r.coprime.symm
  have ha : primary a := by
    obtain ⟨t,ht⟩ := r.d_primary
    refine ⟨-a*t-k*r.c,?_⟩
    linear_combination h-a*ht
  let g : SL(2,Eisenstein) := ⟨!![a,-3*k;r.c,r.d],by
    rw [Matrix.det_fin_two_of]
    linear_combination h⟩
  have hg : g ∈ cubicThetaPrincipalGroup := by
    apply (cubicThetaPrincipalGroup_mem_iff g).mpr
    change primary a ∧ (3:Eisenstein) ∣ -3*k ∧ (3:Eisenstein) ∣ r.c ∧ primary r.d
    exact ⟨ha,⟨-k,by ring⟩,r.c_three,r.d_primary⟩
  refine ⟨⟨g,hg⟩,?_⟩
  ext <;> rfl

/-- A completion of the bottom row, with its existence proved above. -/
def CubicThetaBottomRow.completion (r : CubicThetaBottomRow) : cubicThetaPrincipalGroup :=
  Classical.choose (cubicThetaBottomRow_surjective r)

@[simp] lemma CubicThetaBottomRow.completion_row (r : CubicThetaBottomRow) :
    cubicThetaBottomRow r.completion = r :=
  Classical.choose_spec (cubicThetaBottomRow_surjective r)

end CubicFirstMoment

end

end OAI
