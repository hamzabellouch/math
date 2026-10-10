import OAI.NumberTheory.CubicMoment.Estimates.UniformNoncubeGap

namespace OAI

/-! Exact normalization of the three numerical sieve bounds, and a quantitative
uniform power saving away from the exceptional configurations. -/

noncomputable section
namespace CubicFirstMoment

/-- The actual cubic-sieve bound, divided by the dispersion benchmark. -/
def pSieveRatio (B P Q : ℝ) : ℝ :=
  Q*(P+B+(P*B)^(2/3:ℝ))/(B*(P*Q^2)^(1/3:ℝ))

def qSieveRatio (B P Q : ℝ) : ℝ :=
  P*(Q+B+(Q*B)^(2/3:ℝ))/(B*(P*Q^2)^(1/3:ℝ))

def ordinarySieveRatio (B P Q : ℝ) : ℝ :=
  (B+(P*Q)^2)/(B*(P*Q^2)^(1/3:ℝ))

private lemma sieve_power_mul_div {B : ℝ} (hB : 0 < B) (a b c : ℝ) :
    B^a*B^b/B^c = B^(a+b-c) := by
  rw [← Real.rpow_add hB,← Real.rpow_sub hB]

private lemma sieve_power_denominator {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    B*(B^p*(B^q)^2)^(1/3:ℝ) = B^(1+(p+2*q)/3) := by
  have hq : (B^q)^2 = B^(2*q) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hB.le]
    congr 1
    ring
  rw [hq,← Real.rpow_add hB,← Real.rpow_mul hB.le]
  calc
    _ = B^(1:ℝ)*B^((p+2*q)/3) := by rw [Real.rpow_one]; congr 2; ring
    _ = _ := by rw [← Real.rpow_add hB]

lemma pSieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    pSieveRatio B (B^p) (B^q) =
      B^((2*p+q)/3-1)+B^((q-p)/3)+B^((p+q-1)/3) := by
  have hpb : (B^p*B)^(2/3:ℝ) = B^((p+1)*(2/3)) := by
    conv_lhs => arg 1; rhs; rw [← Real.rpow_one B]
    rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  unfold pSieveRatio
  rw [sieve_power_denominator hB,hpb]
  have h₁ : B^q*B^p/B^(1+(p+2*q)/3) = B^((2*p+q)/3-1) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  have h₂ : B^q*B/B^(1+(p+2*q)/3) = B^((q-p)/3) := by
    calc
      _ = B^q*B^(1:ℝ)/B^(1+(p+2*q)/3) := by rw [Real.rpow_one]
      _ = _ := by rw [sieve_power_mul_div hB]; congr 1; ring
  have h₃ : B^q*B^((p+1)*(2/3))/B^(1+(p+2*q)/3) = B^((p+q-1)/3) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  calc
    _ = B^q*B^p/B^(1+(p+2*q)/3)+B^q*B/B^(1+(p+2*q)/3)+
        B^q*B^((p+1)*(2/3))/B^(1+(p+2*q)/3) := by ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma qSieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    qSieveRatio B (B^p) (B^q) =
      B^((2*p+q)/3-1)+B^(2*(p-q)/3)+B^((2*p-1)/3) := by
  have hqb : (B^q*B)^(2/3:ℝ) = B^((q+1)*(2/3)) := by
    conv_lhs => arg 1; rhs; rw [← Real.rpow_one B]
    rw [← Real.rpow_add hB,← Real.rpow_mul hB.le]
  unfold qSieveRatio
  rw [sieve_power_denominator hB,hqb]
  have h₁ : B^p*B^q/B^(1+(p+2*q)/3) = B^((2*p+q)/3-1) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  have h₂ : B^p*B/B^(1+(p+2*q)/3) = B^(2*(p-q)/3) := by
    calc
      _ = B^p*B^(1:ℝ)/B^(1+(p+2*q)/3) := by rw [Real.rpow_one]
      _ = _ := by rw [sieve_power_mul_div hB]; congr 1; ring
  have h₃ : B^p*B^((q+1)*(2/3))/B^(1+(p+2*q)/3) = B^((2*p-1)/3) := by
    rw [sieve_power_mul_div hB]
    congr 1
    ring
  calc
    _ = B^p*B^q/B^(1+(p+2*q)/3)+B^p*B/B^(1+(p+2*q)/3)+
        B^p*B^((q+1)*(2/3))/B^(1+(p+2*q)/3) := by ring
    _ = _ := by rw [h₁,h₂,h₃]

lemma ordinarySieveRatio_eq_powers {B : ℝ} (hB : 0 < B) (p q : ℝ) :
    ordinarySieveRatio B (B^p) (B^q) =
      B^(-(p+2*q)/3)+B^((5*p+4*q)/3-1) := by
  have hpq : (B^p*B^q)^2 = B^(2*(p+q)) := by
    rw [← Real.rpow_add hB,← Real.rpow_natCast,← Real.rpow_mul hB.le]
    congr 1
    ring
  unfold ordinarySieveRatio
  rw [sieve_power_denominator hB,hpq,add_div]
  congr 1
  · calc
      _ = B^(1-(1+(p+2*q)/3)) := by rw [Real.rpow_sub hB,Real.rpow_one]
      _ = _ := by congr 1; ring
  · rw [← Real.rpow_sub hB]
    congr 1
    ring

private lemma sieve_three_power_le {B : ℝ} (hB : 1 ≤ B) (a b c : ℝ) :
    B^a+B^b+B^c ≤ 3*B^(max a (max b c)) := by
  have ha := Real.rpow_le_rpow_of_exponent_le hB (le_max_left a (max b c))
  have hb := Real.rpow_le_rpow_of_exponent_le hB
    ((le_max_left b c).trans (le_max_right a (max b c)))
  have hc := Real.rpow_le_rpow_of_exponent_le hB
    ((le_max_right b c).trans (le_max_right a (max b c)))
  linarith

lemma pSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    pSieveRatio B (B^p) (B^q) ≤ 3*B^(pSieveExponent p q) := by
  rw [pSieveRatio_eq_powers (by linarith)]
  exact sieve_three_power_le hB _ _ _

lemma qSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    qSieveRatio B (B^p) (B^q) ≤ 3*B^(qSieveExponent p q) := by
  rw [qSieveRatio_eq_powers (by linarith)]
  exact sieve_three_power_le hB _ _ _

lemma ordinarySieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    ordinarySieveRatio B (B^p) (B^q) ≤ 3*B^(ordinarySieveExponent p q) := by
  rw [ordinarySieveRatio_eq_powers (by linarith)]
  have h₁ := Real.rpow_le_rpow_of_exponent_le hB
    (le_max_left (-(p+2*q)/3) ((5*p+4*q)/3-1))
  have h₂ := Real.rpow_le_rpow_of_exponent_le hB
    (le_max_right (-(p+2*q)/3) ((5*p+4*q)/3-1))
  have hp := Real.rpow_nonneg (by linarith : 0 ≤ B) (ordinarySieveExponent p q)
  change _ ≤ 3*B^(max (-(p+2*q)/3) ((5*p+4*q)/3-1))
  unfold ordinarySieveExponent at hp
  linarith

/-- This is the numerical bound used after normalizing the concrete sieve
estimates; the exponent is the limiting exponent. -/
theorem noncubeSieveRatio_le {B : ℝ} (hB : 1 ≤ B) (p q : ℝ) :
    min (pSieveRatio B (B^p) (B^q))
      (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q))) ≤
      3*B^(noncubeSieveExponent p q) := by
  unfold noncubeSieveExponent
  by_cases h : pSieveExponent p q ≤ min (qSieveExponent p q) (ordinarySieveExponent p q)
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans (pSieveRatio_le hB p q)
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hq : qSieveExponent p q ≤ ordinarySieveExponent p q
    · rw [min_eq_left hq]
      exact ((min_le_right _ _).trans (min_le_left _ _)).trans (qSieveRatio_le hB p q)
    · rw [min_eq_right (le_of_not_ge hq)]
      exact ((min_le_right _ _).trans (min_le_right _ _)).trans (ordinarySieveRatio_le hB p q)

/-- A uniform power saving survives all additional losses with exponent at
most half the compactness gap. -/
theorem uniform_noncube_ratio_saving {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (B p q η : ℝ), 1 ≤ B →
      0 ≤ p → 0 ≤ q → p+2*q ≤ 1 → κ ≤ p+2*q →
      δ ≤ |p-1|+|q| → δ ≤ |p-1/3|+|q-1/3| → η ≤ γ/2 →
      B^η * min (pSieveRatio B (B^p) (B^q))
        (min (qSieveRatio B (B^p) (B^q)) (ordinarySieveRatio B (B^p) (B^q))) ≤
          3*B^(-γ/2) := by
  obtain ⟨γ,hγ,hgap⟩ := uniform_noncube_exponent_gap hκ hδ
  refine ⟨γ,hγ,?_⟩
  intro B p q η hB hp hq hsize hlarge hfirst hbalanced hη
  have hg := hgap p q hp hq hsize hlarge hfirst hbalanced
  calc
    _ ≤ B^η*(3*B^(noncubeSieveExponent p q)) :=
      mul_le_mul_of_nonneg_left (noncubeSieveRatio_le hB p q)
        (Real.rpow_nonneg (by linarith) _)
    _ = 3*B^(η+noncubeSieveExponent p q) := by
      rw [Real.rpow_add (by linarith : 0 < B)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hB (by linarith)) (by norm_num)

end CubicFirstMoment

end

end OAI
