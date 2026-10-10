import OAI.NumberTheory.EgyptianFractions.CubeFreeRationalSupply
import OAI.NumberTheory.EgyptianFractions.CubeFreeDensity

namespace OAI
noncomputable section

namespace Problem337

/-- The actual exceptional moduli: multiples of a bad divisor coprime to the
fixed supply. The unit divisor is excluded, as in the Fourier collision API. -/
def badCoprimeDivisorMultiples (N P : ℕ) (Q : ℕ → Prop) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun q => ∃ d : ℕ,
    2 ≤ d ∧ d ∣ q ∧ Nat.Coprime d P ∧ ¬Q d)

@[simp] theorem mem_badCoprimeDivisorMultiples {N P q : ℕ} {Q : ℕ → Prop} :
    q ∈ badCoprimeDivisorMultiples N P Q ↔
      1 ≤ q ∧ q ≤ N ∧ ∃ d : ℕ, 2 ≤ d ∧ d ∣ q ∧ Nat.Coprime d P ∧ ¬Q d := by
  classical
  simp only [badCoprimeDivisorMultiples, Finset.mem_filter, Finset.mem_Icc, and_assoc]

/-- Exact finite assembly of the cube-free alternative. The density premise
counts the specified exceptional moduli, not an abstract set standing in for
the desired result. The second premise is the all-divisor Fourier supply API.
Both arithmetic premises remain explicit and must be proved separately. -/
theorem marked_rational_supply_of_cube_free_bad_divisors
    (m P B : ℕ) (Q : ℕ → Prop) (hP : 0 < P)
    (hbad : ((badCoprimeDivisorMultiples (m ^ 4) P Q).card : ℝ) <
      (m ^ 4 : ℕ) / 12)
    (hrep : ∀ d : ℕ, 0 < d → d ≤ m ^ 4 → Nat.Coprime d P →
      (∀ r : ℕ, 2 ≤ r → r ∣ d → Q r) →
      HasRationalDivisorSum (P ^ 2) (d : ℚ) B) :
    HasRationalDivisorSupply m (P ^ 4) (2 * B) := by
  classical
  let E := badCoprimeDivisorMultiples (m ^ 4) P Q
  let G := CubeFreeDensity.good (m ^ 4) \ E
  have hG : G ⊆ Finset.Icc 1 (m ^ 4) := by
    intro q hq
    have h := CubeFreeDensity.mem_good.mp (Finset.mem_sdiff.mp hq).1
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  apply marked_rational_supply_of_cube_free_set m P B G hP hG
  · have hh := CubeFreeDensity.card_good_sdiff_gt_two_thirds (m ^ 4) E hbad
    have hh' : (2 : ℝ) * (m ^ 4 : ℕ) < 3 * (G.card : ℝ) := by
      change (2 : ℝ) * (m ^ 4 : ℕ) / 3 < (G.card : ℝ) at hh
      linarith
    exact_mod_cast hh'
  · intro q hq p hp
    exact CubeFreeDensity.prime_cube_not_dvd_of_mem_good (Finset.mem_sdiff.mp hq).1 hp
  · intro q hq d hd hdq hdP
    have hqbounds := Finset.mem_Icc.mp (hG hq)
    apply hrep d hd ((Nat.le_of_dvd hqbounds.1 hdq).trans hqbounds.2) hdP
    intro r hr hrd
    by_contra hnot
    have hrcop : Nat.Coprime r P := hdP.of_dvd_left hrd
    exact (Finset.mem_sdiff.mp hq).2
      (mem_badCoprimeDivisorMultiples.mpr
        ⟨hqbounds.1, hqbounds.2, r, hr, hrd.trans hdq, hrcop, hnot⟩)

end Problem337

end

end OAI
