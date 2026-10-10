import OAI.Geometry.Relativity.CKS.MixedJetCalculus

namespace OAI

noncomputable section
namespace CKSEnd
noncomputable section

def mass (r u v : ℝ) : ℝ := r / 2 * (1 + v ^ 2 - u ^ 2)

def normalMass (r U u v du dv : ℝ) : ℝ :=
  U / 2 * (1 + v ^ 2 - u ^ 2) + r * (v * dv - u * du)

structure ConstraintJet where
  r : ℝ
  U : ℝ
  u : ℝ
  v : ℝ
  du : ℝ
  dv : ℝ
  leafScalar : ℝ
  normalEntry : ℝ
  lapseLaplacian : ℝ
  shearSq : ℝ
  tensorSq : ℝ
  mixedSq : ℝ
  shearTensor : ℝ
  mixedDivergence : ℝ
  mixedAcceleration : ℝ

namespace ConstraintJet

def H (j : ConstraintJet) : ℝ := 2 * j.u / j.r
def p (j : ConstraintJet) : ℝ := 2 * j.v / j.r

def NH (j : ConstraintJet) : ℝ :=
  2 * j.du / j.r - 2 * j.u * j.U / j.r ^ 2

def Np (j : ConstraintJet) : ℝ :=
  2 * j.dv / j.r - 2 * j.v * j.U / j.r ^ 2

def C (j : ConstraintJet) : ℝ :=
  j.leafScalar / 2 - j.NH - j.lapseLaplacian - 3 / 4 * j.H ^ 2 -
  1 / 2 * j.shearSq + j.normalEntry * j.p + 1 / 4 * j.p ^ 2 -
  1 / 2 * j.tensorSq - j.mixedSq

def Q (j : ConstraintJet) : ℝ :=
  j.H * (j.normalEntry - j.p / 2) - j.shearTensor - j.Np +
  j.mixedDivergence - 2 * j.mixedAcceleration

def massIdentityRHS (j : ConstraintJet) : ℝ :=
  2 * normalMass j.r j.U j.u j.v j.du j.dv / (j.u * j.r ^ 2) +
  (j.leafScalar / 2 - 1 / j.r ^ 2) +
  (j.U / j.u - 1) * (2 - 6 * mass j.r j.u j.v / j.r) / j.r ^ 2 -
  j.lapseLaplacian - 1 / 2 * (j.shearSq + j.tensorSq) +
  j.v / j.u * j.shearTensor - j.mixedSq -
  j.v / j.u * (j.mixedDivergence - 2 * j.mixedAcceleration)

theorem mass_identity (j : ConstraintJet) (hr : j.r ≠ 0) (hu : j.u ≠ 0) :
    j.C - j.v / j.u * j.Q = j.massIdentityRHS := by
  unfold C Q H p NH Np massIdentityRHS mass normalMass
  field_simp
  ring

end ConstraintJet

section Cone

variable {E E₀ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]

def DEC (C Q : ℝ) (Z : E) : Prop := Real.sqrt (Q ^ 2 + ‖Z‖ ^ 2) ≤ C

omit [NormedSpace ℝ E] in
lemma momentum_norm [NormedSpace ℝ E] (Q : ℝ) (Z : E) :
    ‖(WithLp.toLp 2 (Q, Z) : WithLp 2 (ℝ × E))‖ =
      Real.sqrt (Q ^ 2 + ‖Z‖ ^ 2) := by
  simp [WithLp.prod_norm_eq_of_L2, Real.norm_eq_abs]

lemma DEC.add {C₀ Q₀ C₁ Q₁ : ℝ} {Z₀ Z₁ : E}
    (h₀ : DEC C₀ Q₀ Z₀) (h₁ : DEC C₁ Q₁ Z₁) :
    DEC (C₀ + C₁) (Q₀ + Q₁) (Z₀ + Z₁) := by
  let V₀ : WithLp 2 (ℝ × E) := WithLp.toLp 2 (Q₀, Z₀)
  let V₁ : WithLp 2 (ℝ × E) := WithLp.toLp 2 (Q₁, Z₁)
  have hn := norm_add_le V₀ V₁
  change ‖(WithLp.toLp 2 (Q₀ + Q₁, Z₀ + Z₁) : WithLp 2 (ℝ × E))‖ ≤
    ‖V₀‖ + ‖V₁‖ at hn
  rw [momentum_norm, momentum_norm, momentum_norm] at hn
  exact hn.trans (add_le_add h₀ h₁)

omit [NormedSpace ℝ E] in
lemma DEC.of_null_margins [NormedSpace ℝ E] {C Q a b : ℝ} {Z : E}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hm : a ≤ C - Q) (hp : b ≤ C + Q)
    (hz : ‖Z‖ ^ 2 ≤ a * b) : DEC C Q Z := by
  have hC : 0 ≤ C := by linarith
  have hmul := mul_le_mul hm hp hb (ha.trans hm)
  apply (Real.sqrt_le_iff).2
  constructor
  · exact hC
  · nlinarith

lemma DEC.after_common_norm {C Q C₀ Q₀ a b : ℝ} {Z : E} {Z₀ : E₀}
    (I : E₀ →ₗᵢ[ℝ] E) (h₀ : DEC C₀ Q₀ Z₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : a ≤ (C - C₀) - (Q - Q₀))
    (hp : b ≤ (C - C₀) + (Q - Q₀))
    (hz : ‖Z - I Z₀‖ ^ 2 ≤ a * b) : DEC C Q Z := by
  have h₀' : DEC C₀ Q₀ (I Z₀) := by simpa [DEC] using h₀
  have hδ := DEC.of_null_margins ha hb hm hp hz
  have h := h₀'.add hδ
  simpa using h

def smallMargin (r w : ℝ) : ℝ := w / (r ^ 3 * Real.sqrt r)

def largeMargin (r w : ℝ) : ℝ := w / r ^ 2

lemma smallMargin_eq_rpow {r w : ℝ} (hr : 0 < r) :
    smallMargin r w = w * r ^ (-(7 / 2 : ℝ)) := by
  rw [Real.rpow_neg hr.le, ← div_eq_mul_inv]
  unfold smallMargin
  congr 1
  rw [show (7 / 2 : ℝ) = 3 + 1 / 2 by norm_num,
    Real.rpow_add hr, ← Real.sqrt_eq_rpow]
  norm_num

theorem collar_DEC_of_weighted_errors
    {C Q C₀ Q₀ r w A B C₁ : ℝ} {Z : E} {Z₀ : E₀}
    (I : E₀ →ₗᵢ[ℝ] E) (h₀ : DEC C₀ Q₀ Z₀)
    (hr : 1 ≤ r) (hw : 0 ≤ w) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC₁ : 0 ≤ C₁)
    (hAr : A ^ 2 ≤ r) (hBr : B ≤ r) (hC₁r : C₁ ^ 4 ≤ r)
    (hsmall : |((C - C₀) - (Q - Q₀)) - 2 * smallMargin r w| ≤ A * w / r ^ 4)
    (hlarge : |(Q - Q₀) - 2 * largeMargin r w| ≤ B * w / r ^ 3)
    (htan : ‖Z - I Z₀‖ ≤ C₁ * w / r ^ 3) :
    DEC C Q Z := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
  have hAs : A ≤ Real.sqrt r := by nlinarith
  have hCs : C₁ ^ 2 ≤ Real.sqrt r := by nlinarith [sq_nonneg (C₁ ^ 2 - Real.sqrt r)]
  have hsmallerr : A * w / r ^ 4 ≤ smallMargin r w := by
    calc
      A * w / r ^ 4 ≤ Real.sqrt r * w / r ^ 4 := by gcongr
      _ = smallMargin r w := by
        unfold smallMargin
        field_simp
        nlinarith [hs2]
  have hlargeerr : B * w / r ^ 3 ≤ largeMargin r w := by
    calc
      B * w / r ^ 3 ≤ r * w / r ^ 3 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBr hw)
          (pow_nonneg (hB.trans hBr) 3)
      _ = largeMargin r w := by unfold largeMargin; field_simp
  have ha : 0 ≤ smallMargin r w := by unfold smallMargin; positivity
  have hb : 0 ≤ largeMargin r w := by unfold largeMargin; positivity
  have hm : smallMargin r w ≤ (C - C₀) - (Q - Q₀) := by
    have := (abs_le.mp hsmall).1
    linarith
  have hq : largeMargin r w ≤ Q - Q₀ := by
    have := (abs_le.mp hlarge).1
    linarith
  have hp : largeMargin r w ≤ (C - C₀) + (Q - Q₀) := by linarith
  have hz : ‖Z - I Z₀‖ ^ 2 ≤ smallMargin r w * largeMargin r w := by
    calc
      ‖Z - I Z₀‖ ^ 2 ≤ (C₁ * w / r ^ 3) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (div_nonneg (mul_nonneg hC₁ hw) (pow_nonneg hr0.le 3))).2 htan
      _ = C₁ ^ 2 * w ^ 2 / r ^ 6 := by ring
      _ ≤ Real.sqrt r * w ^ 2 / r ^ 6 := by gcongr
      _ = smallMargin r w * largeMargin r w := by
        unfold smallMargin largeMargin
        field_simp
        nlinarith [hs2]
  exact DEC.after_common_norm I h₀ ha hb hm hp hz

end Cone

end
end CKSEnd

end

end OAI
