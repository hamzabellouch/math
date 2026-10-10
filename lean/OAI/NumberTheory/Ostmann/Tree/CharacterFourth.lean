import OAI.NumberTheory.Ostmann.Tree.Mellin
import OAI.NumberTheory.Ostmann.Tree.QuarticWeighted

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
local instance characterFourthFintype : Fintype (MulChar F ℂ) := Fintype.ofFinite _

theorem sum_mulChar_field_kernel (x y : F) :
    (∑ χ : MulChar F ℂ, χ x*conj (χ y)) =
      if x=y ∧ x≠0 then (Fintype.card Fˣ:ℂ) else 0 := by
  classical
  by_cases hx : x=0
  · simp [hx,MulChar.map_zero]
  by_cases hy : y=0
  · simp [hy,MulChar.map_zero]
  let u : Fˣ := Units.mk0 y hy
  let v : Fˣ := Units.mk0 x hx
  calc
    _ = ∑ χ : MulChar F ℂ, conj (χ u)*χ v := by
      apply Finset.sum_congr rfl
      intro χ _
      exact mul_comm _ _
    _ = if u=v then (Fintype.card Fˣ:ℂ) else 0 := sum_mulChar_kernel u v
    _ = _ := by
      by_cases he : x=y
      · have huv : u=v := Units.ext he.symm
        simp [he,huv,hy]
      · have huv : u≠v := fun h => he (congrArg (fun t : Fˣ => (t:F)) h).symm
        simp [he,huv]

omit [Field F] [DecidableEq F] in
theorem norm_sum_fourth_expansion (z : F → ℂ) :
    (‖∑ b, z b‖^4:ℂ) = ∑ b : Quartet F, z b.1.1*z b.1.2*conj (z b.2.1)*conj (z b.2.2) := by
  calc
    _ = ((‖∑ b,z b‖:ℂ)^2)^2 := by ring
    _ = ((∑ b,z b)*conj (∑ b,z b))^2 := by rw [Complex.mul_conj']
    _ = _ := by
      simp only [Fintype.sum_prod_type,map_sum,← Finset.mul_sum,← Finset.sum_mul]
      ring

def weightedCharacterSum (w : F → ℝ) (χ : MulChar F ℂ) (a : F) : ℂ :=
  ∑ b, (w b:ℂ)*χ (a-b)

theorem weightedCharacterSum_fourth_identity (w : F → ℝ) (a : F) :
    (∑ χ : MulChar F ℂ, ‖weightedCharacterSum w χ a‖^4) =
      (Fintype.card Fˣ:ℝ) * ∑ b : Quartet F,
        if quartetCollision a b ∧ (a-b.1.1)*(a-b.1.2)≠0 then quartetWeight w b else 0 := by
  classical
  apply Complex.ofReal_injective
  push_cast
  have he (χ : MulChar F ℂ) :
      (‖weightedCharacterSum w χ a‖:ℂ)^4 = ∑ b : Quartet F,
        (quartetWeight w b:ℂ) * (χ ((a-b.1.1)*(a-b.1.2))*conj (χ ((a-b.2.1)*(a-b.2.2)))) := by
    rw [weightedCharacterSum,norm_sum_fourth_expansion]
    apply Finset.sum_congr rfl
    intro b _
    simp only [quartetWeight,map_mul,Complex.conj_ofReal]
    push_cast
    ring
  simp_rw [he]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [← Finset.mul_sum,sum_mulChar_field_kernel]
  split_ifs <;> simp_all
  ring

theorem weightedCharacterSum_fourth_bound (w : F → ℝ) (hw : ∀ x,0≤w x) :
    (∑ χ : MulChar F ℂ, ∑ a : F, ‖weightedCharacterSum w χ a‖^4) ≤
      (Fintype.card Fˣ:ℝ) *
        (2*(Fintype.card F:ℝ)*(∑ x,w x^2)^2+(∑ x,w x)^4) := by
  classical
  rw [Finset.sum_comm]
  simp_rw [weightedCharacterSum_fourth_identity]
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply le_trans _ (quartetCollision_weighted_bound w hw)
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  have hW := quartetWeight_nonneg w hw b
  split_ifs <;> simp_all

end
end Ostmann.FiniteField

end OAI
