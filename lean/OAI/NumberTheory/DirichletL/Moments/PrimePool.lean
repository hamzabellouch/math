import OAI.NumberTheory.DirichletL.RayPrimeNormalizer
import OAI.NumberTheory.DirichletL.Moments.AmplificationCount

namespace OAI

noncomputable section
open scoped BigOperators Classical Topology ContDiff
open Filter
namespace SevenEighths.CenteredMomentPrimePool
open HeckeFamily PNT.AnnularPrimeMass CenteredMomentAmplificationCount

def primePool (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  annularPrimeIdeals (RayQuotient.identityClass M H) a b x \ S

theorem annular_weighted_card_bound (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (a b B x : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 ≤ B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hW : ∀ y, W y ≤ B) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x ≤
      ((annularPrimeIdeals C a b x \ S).card : ℝ) * (B * a^(-5/6 : ℝ)) * x^(-5/6 : ℝ) := by
  rw [weightedPrimeSumDeleted_eq_annular C S W ha hab hsupp hx]
  calc
    _ ≤ ∑ _P ∈ annularPrimeIdeals C a b x \ S, B*(a*x)^(-5/6 : ℝ) := by
      apply Finset.sum_le_sum
      intro P hP
      have hn := (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx (Finset.mem_sdiff.mp hP).1).1
      apply mul_le_mul (hW _) _ (Real.rpow_nonneg (Nat.cast_nonneg _) _) hB
      exact Real.rpow_le_rpow_of_nonpos (mul_pos ha hx) (by nlinarith) (by norm_num)
    _ = _ := by
      rw [Finset.sum_const,nsmul_eq_mul,Real.mul_rpow ha.le hx.le]
      ring

section FixedRay
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)

include hH

theorem eventually_primePool_card (S : Finset (Ideal O)) (W : ℝ → ℝ)
    (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0)
    (a b B : ℝ) (ha : 0 < a) (hab : a ≤ b) (hB : 0 < B)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hbound : ∀ y, W y ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c*x/Real.log x ≤ (primePool M H S a b x).card := by
  obtain ⟨c,hcpos,hlower⟩ := RayPrimeNormalizer.eventually_lower_bound M H hH S W hW hc hp hW0 hWne
  let D : ℝ := B*a^(-5/6 : ℝ)
  have hD : 0 < D := mul_pos hB (Real.rpow_pos_of_pos ha _)
  refine ⟨c/D,div_pos hcpos hD,?_⟩
  filter_upwards [hlower,eventually_gt_atTop (1 : ℝ)] with x hlow hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hu := annular_weighted_card_bound (RayQuotient.identityClass M H) S W a b B x
    ha hab hB.le hsupp hbound hx0
  change weightedPrimeSumDeleted _ S W x ≤ (primePool M H S a b x).card * D * x^(-5/6 : ℝ) at hu
  change c*x^(1/6 : ℝ)/Real.log x ≤ weightedPrimeSumDeleted _ S W x at hlow
  have hpower : x*x^(-5/6 : ℝ) = x^(1/6 : ℝ) := by
    calc
      _ = x^(1 : ℝ)*x^(-5/6 : ℝ) := by rw [Real.rpow_one]
      _ = x^((1 : ℝ)+(-5/6)) := (Real.rpow_add hx0 _ _).symm
      _ = _ := by norm_num
  have hmul : (c*x/Real.log x)*x^(-5/6 : ℝ) ≤
      ((primePool M H S a b x).card * D)*x^(-5/6 : ℝ) := by
    calc
      _ = c*(x*x^(-5/6 : ℝ))/Real.log x := by ring
      _ = _ := by rw [hpower]
      _ ≤ _ := hlow.trans hu
  have hcancel := le_of_mul_le_mul_right hmul (Real.rpow_pos_of_pos hx0 (-5/6 : ℝ))
  convert (div_le_iff₀ hD).mpr hcancel using 1 ; ring

end FixedRay

def eligiblePool (P : Finset (Ideal O)) (R : Ideal O) : Finset (Ideal O) :=
  P.filter (fun Q => ¬Q ∣ R)

theorem eligiblePool_card_lower (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) :
    (P.card : ℝ) - B/ℓ ≤ (eligiblePool P R).card := by
  have hbad := large_prime_divisor_count (P.filter (fun Q => Q ∣ R))
    (fun Q hQ => hp Q (Finset.mem_filter.mp hQ).1) R hR
    (fun Q hQ => (Finset.mem_filter.mp hQ).2) Z ℓ B hZ hℓ
    (fun Q hQ => hlower Q (Finset.mem_filter.mp hQ).1) hupper
  have he := Finset.card_filter_add_card_filter_not (s := P) (fun Q => Q ∣ R)
  have her : ((P.filter (fun Q => Q ∣ R)).card : ℝ) + (eligiblePool P R).card = P.card := by
    exact_mod_cast he
  linarith

theorem eligiblePool_half (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q)
    (R : Ideal O) (hR : R ≠ 0) (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ Q ∈ P, Z^ℓ ≤ (Ideal.absNorm Q : ℝ))
    (hupper : (Ideal.absNorm R : ℝ) ≤ Z^B) (hsize : 2*(B/ℓ) ≤ P.card) :
    (P.card : ℝ)/2 ≤ (eligiblePool P R).card := by
  have h := eligiblePool_card_lower P hp R hR Z ℓ B hZ hℓ hlower hupper
  linarith

end SevenEighths.CenteredMomentPrimePool

end

end OAI
