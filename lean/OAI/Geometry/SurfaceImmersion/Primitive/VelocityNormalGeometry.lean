import OAI.Geometry.SurfaceImmersion.Primitive.VelocityNormalBounds

namespace OAI

/-! The angular derivative contributes only to the complementary normal component. -/
noncomputable section
open scoped Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame RealModes

def direction (e₁ e₂ : Vec) (α : ℝ) : Vec := Real.cos α • e₁ + Real.sin α • e₂
def angularDirection (e₁ e₂ : Vec) (α : ℝ) : Vec := -Real.sin α • e₁ + Real.cos α • e₂

lemma direction_unit {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) : direction e₁ e₂ α ⬝ᵥ direction e₁ e₂ α = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [direction, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq α]

lemma angularDirection_unit {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) :
    angularDirection e₁ e₂ α ⬝ᵥ angularDirection e₁ e₂ α = 1 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [angularDirection, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  nlinarith [Real.sin_sq_add_cos_sq α]

lemma direction_angular_perp {e₁ e₂ : Vec} (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1)
    (horth : e₁ ⬝ᵥ e₂ = 0) (α : ℝ) :
    direction e₁ e₂ α ⬝ᵥ angularDirection e₁ e₂ α = 0 := by
  have horth' : e₂ ⬝ᵥ e₁ = 0 := (dotProduct_comm _ _).trans horth
  simp only [direction, angularDirection, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h₁, h₂, horth, horth', mul_zero, mul_one, zero_add, add_zero]
  ring

lemma angularDirection_perp {e₁ e₂ w : Vec} (h₁ : w ⬝ᵥ e₁ = 0) (h₂ : w ⬝ᵥ e₂ = 0) (α : ℝ) :
    w ⬝ᵥ angularDirection e₁ e₂ α = 0 := by
  simp [angularDirection, dotProduct_add, dotProduct_smul, h₁, h₂]

lemma dot_normalPart_eq {X Y w m : Vec} (hX : m ⬝ᵥ X = 0) (hY : m ⬝ᵥ Y = 0) :
    m ⬝ᵥ realNormalPart X Y w = m ⬝ᵥ w := by
  simp [realNormalPart, dotProduct_sub, dotProduct_smul, hX, hY]

lemma dot_leadingTangent_zero {X Y C V m : Vec}
    (hY : m ⬝ᵥ Y = 0) (hC : m ⬝ᵥ C = 0) (hV : m ⬝ᵥ V = 0) :
    m ⬝ᵥ leadingTangent X Y C V = 0 := by
  simp only [leadingTangent, dotProduct_add, dotProduct_sub, dot_normalPart_eq hY hC,
    sub_self, hV, add_zero]

lemma angularDirection_normal_perp {X Y C e₁ e₂ : Vec} (R α : ℝ)
    (h₁ : e₁ ⬝ᵥ e₁ = 1) (h₂ : e₂ ⬝ᵥ e₂ = 1) (horth : e₁ ⬝ᵥ e₂ = 0)
    (hY₁ : Y ⬝ᵥ e₁ = 0) (hY₂ : Y ⬝ᵥ e₂ = 0)
    (hC₁ : C ⬝ᵥ e₁ = 0) (hC₂ : C ⬝ᵥ e₂ = 0) :
    angularDirection e₁ e₂ α ⬝ᵥ normalize (leadingNormal X Y C (R • direction e₁ e₂ α)) = 0 := by
  have hY : angularDirection e₁ e₂ α ⬝ᵥ Y = 0 :=
    (dotProduct_comm _ _).trans (angularDirection_perp hY₁ hY₂ α)
  have hC : angularDirection e₁ e₂ α ⬝ᵥ C = 0 :=
    (dotProduct_comm _ _).trans (angularDirection_perp hC₁ hC₂ α)
  have hV : angularDirection e₁ e₂ α ⬝ᵥ (R • direction e₁ e₂ α) = 0 := by
    rw [dotProduct_smul, dotProduct_comm (angularDirection _ _ _) (direction _ _ _),
      direction_angular_perp h₁ h₂ horth, smul_zero]
  have hT := dot_leadingTangent_zero (X := X) hY hC hV
  apply dot_normalize_zero
  change angularDirection e₁ e₂ α ⬝ᵥ realNormalPart
    (leadingTangent X Y C (R • direction e₁ e₂ α)) Y C = 0
  rw [dot_normalPart_eq hT hY, hC]

/-- The first normal coefficient does not contain the angular derivative. -/
lemma first_normal_derivative_independent {W m n : Vec} (hmn : m ⬝ᵥ n = 0) (R d : ℝ) :
    (W + (R * d) • m) ⬝ᵥ n = W ⬝ᵥ n := by
  simp [add_dotProduct, smul_dotProduct, hmn]

/-- The complementary normal coefficient contains that derivative with coefficient `R`. -/
lemma second_normal_derivative {W m : Vec} (hm : m ⬝ᵥ m = 1) (R d : ℝ) :
    (W + (R * d) • m) ⬝ᵥ m = R * d + W ⬝ᵥ m := by
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul, hm, mul_one]
  ring

end ClosedSurfaceR4.VelocityFrame

end

end OAI
