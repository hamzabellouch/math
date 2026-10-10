import OAI.NumberTheory.CubicMoment.Theta.CubicThetaEisensteinConvergence

namespace OAI

/-! The actual cusp stabilizer and the distinguished zero lower-left
row of the cubic Eisenstein series. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped MatrixGroups Matrix
namespace CubicFirstMoment

def cubicThetaZeroRow : CubicThetaBottomRow where
  c := 0
  d := 1
  c_three := dvd_zero _
  d_primary := primary_one
  coprime := ⟨0,1,by ring⟩

lemma CubicThetaBottomRow.c_zero_iff (r : CubicThetaBottomRow) :
    r.c = 0 ↔ r = cubicThetaZeroRow := by
  constructor
  · intro hc
    have hunit : IsUnit r.d := isCoprime_zero_left.mp (hc ▸ r.coprime)
    apply CubicThetaBottomRow.ext hc
    exact primary_unit_eq_one hunit r.d_primary
  · rintro rfl
    rfl

lemma cubicThetaEisensteinTerm_zeroRow (p : ℂ × ℝ) (s : ℂ) :
    cubicThetaEisensteinTerm cubicThetaZeroRow p s = (p.2:ℂ)^s := by
  simp [cubicThetaEisensteinTerm,CubicThetaBottomRow.phase,CubicThetaBottomRow.height,
    cubicThetaZeroRow,norm,cubicSymbol_one_lower]

theorem cubicThetaEisenstein_split_cusp {p : ℂ × ℝ} (hp : 0 < p.2)
    {s : ℂ} (hs : 2 < s.re) :
    cubicThetaEisenstein p s = (p.2:ℂ)^s+
      ∑' r : CubicThetaBottomRow, if r.c = 0 then 0 else cubicThetaEisensteinTerm r p s := by
  have he := (cubicThetaEisenstein_summable hp hs).tsum_eq_add_tsum_ite cubicThetaZeroRow
  rw [cubicThetaEisensteinTerm_zeroRow] at he
  simpa only [cubicThetaEisenstein,CubicThetaBottomRow.c_zero_iff] using he

def cubicThetaPrincipalTranslation (m : Eisenstein) : cubicThetaPrincipalGroup :=
  let g : SL(2,Eisenstein) := ⟨!![1,3*m;0,1],by simp [Matrix.det_fin_two]⟩
  ⟨g,(cubicThetaPrincipalGroup_mem_iff g).mpr
    ⟨primary_one,⟨m,rfl⟩,dvd_zero _,primary_one⟩⟩

@[simp] lemma cubicThetaPrincipalTranslation_value (m : Eisenstein) :
    cubicThetaKubotaValue (cubicThetaPrincipalTranslation m) = 1 := by
  simp [cubicThetaKubotaValue,cubicThetaPrincipalTranslation]

lemma cubicThetaPrincipalTranslation_complex (m : Eisenstein) :
    cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation m) =
      cubicThetaTranslationMatrix ((3*m:Eisenstein):ℂ) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cubicThetaEisenstein_three_periodic (m : Eisenstein)
    {p : ℂ × ℝ} (hp : 0 < p.2) (s : ℂ) :
    cubicThetaEisenstein (p.1+((3*m:Eisenstein):ℂ),p.2) s = cubicThetaEisenstein p s := by
  have he := cubicThetaEisenstein_automorphy (cubicThetaPrincipalTranslation m) hp s
  rw [cubicThetaPrincipalTranslation_complex,cubicThetaMobius_translation,
    cubicThetaPrincipalTranslation_value,one_mul] at he
  exact he

end CubicFirstMoment

end

end OAI
