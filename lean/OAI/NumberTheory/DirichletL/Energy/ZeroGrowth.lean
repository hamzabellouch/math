import OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowth
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceLowBands QuadraticInitialBound
local notation "O" => HeckeFamily.O

def ZeroGrowthAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) : Prop :=
  ∀ s : NaturalState Z Bmask bΦ, s.fixedModulus = Q → s.width ≤ M →
  ∀ p : Profiles a b, ∀ t X₁ X₂ : ℝ,
    0 < X₁ → 0 < X₂ → X₁ ≤ Z ^ L → X₂ ≤ Z ^ L →
    s.plainEnergy p t X₁ X₂ ≤
      C * diagonalControl s.radial.profile * (p.control S) ^ 2 *
        (1 + ‖t‖) ^ degree *
        Z ^ (max s.width (length Z X₁ + length Z X₂) + ε)

lemma zeroGrowth_of_zeroAt (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ) (hC : 0 ≤ C)
    (h : ZeroAt Q a b bΦ Bmask L M ε Z degree S C) :
    ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C := by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂
  apply (h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂).trans
  have he : s.width + ε ≤ max s.width (length Z X₁ + length Z X₂) + ε := by
    linarith [le_max_left s.width (length Z X₁ + length Z X₂)]
  apply mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le s.base_ge_one he)
  exact mul_nonneg (mul_nonneg (mul_nonneg hC
    (diagonalControl_nonneg _)) (sq_nonneg _)) (pow_nonneg (by positivity) _)

lemma zeroGrowth_on_capacity (Q : Ideal O) (a b bΦ Bmask L M ε Z : ℝ)
    (degree : ℕ) (S : Finset (ℕ × ℕ)) (C : ℝ)
    (h : ZeroGrowthAt Q a b bΦ Bmask L M ε Z degree S C)
    (s : NaturalState Z Bmask bΦ) (hQ : s.fixedModulus = Q) (hs : s.width ≤ M)
    (p : Profiles a b) (t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hc₁ : X₁ ≤ Z ^ L) (hc₂ : X₂ ≤ Z ^ L)
    (hcapacity : length Z X₁ + length Z X₂ ≤ s.width) :
    s.plainEnergy p t X₁ X₂ ≤ C * diagonalControl s.radial.profile *
      (p.control S) ^ 2 * (1 + ‖t‖) ^ degree * Z ^ (s.width + ε) := by
  simpa only [max_eq_left hcapacity] using
    h s hQ hs p t X₁ X₂ hX₁ hX₂ hc₁ hc₂

theorem exists_zero_growth_floor (a b bΦ Bmask L ε : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hbΦ : 0 < bΦ) (hmask : 0 ≤ Bmask)
    (hε : 0 < ε) :
    ∃ degree : ℕ, ∃ S : Finset (ℕ × ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ Q : Ideal O, ∀ Z : ℝ, 1 ≤ Z →
        ZeroGrowthAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C := by
  obtain ⟨degree, S, C, hC, hf⟩ := exists_zero_floor a b bΦ Bmask ε ha hb hbΦ hmask hε
  refine ⟨degree, S, C, hC, ?_⟩
  intro Q Z hZ
  exact zeroGrowth_of_zeroAt Q a b bΦ Bmask L (ε / 16) ε Z degree S C hC.le
    (zeroAt_of_zeroBound Q a b bΦ Bmask L (ε / 16) ε Z 1 degree S C (hf Q) hZ)

end SevenEighths.CenteredMomentEnergyZeroGrowth

end

end OAI
