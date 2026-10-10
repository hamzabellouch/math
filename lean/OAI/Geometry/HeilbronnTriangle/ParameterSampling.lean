import OAI.Geometry.HeilbronnTriangle.ParameterConclusion
import OAI.Geometry.HeilbronnTriangle.SharedGeometricAlteration
import OAI.Geometry.HeilbronnTriangle.FinalSampling

namespace OAI


noncomputable section

namespace Problem355.ParameterSampling

open Parameters Parameters.PrimeParameterData

structure PointLaw where
  Environment : Type
  Column : Type
  environmentFintype : Fintype Environment
  columnFintype : Fintype Column
  rho : Environment → ℝ
  mu : Environment → Column → ℝ
  point : Environment → Column → Point
  rho_nonneg : ∀ θ, 0 ≤ rho θ
  rho_sum : @Finset.sum Environment ℝ _ Finset.univ rho = 1
  mu_nonneg : ∀ θ x, 0 ≤ mu θ x
  mu_sum : ∀ θ, @Finset.sum Column ℝ _ Finset.univ (mu θ) = 1
  in_square : ∀ θ x, pointInUnitSquare (point θ x)

attribute [instance] PointLaw.environmentFintype PointLaw.columnFintype

def PointLaw.pairProbability (L : PointLaw) : ℝ :=
  SharedGeometricAlteration.pairMass L.rho L.mu L.point

def PointLaw.tripleProbability (L : PointLaw) (a : ℝ) : ℝ :=
  SharedGeometricAlteration.tripleMass L.rho L.mu L.point a

lemma r_le_sampleCard {k r : ℕ} (D : PrimeParameterData k r) : r ≤ D.sampleCard := by
  have ht : (0 : ℝ) < D.tau := by exact_mod_cast D.tau_pos
  have hratio : (1 : ℝ) ≤ (D.N : ℝ) ^ 3 / D.tau :=
    (le_div_iff₀ ht).2 (by simpa using D.real_bounds.2.2.1)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((D.N : ℝ) ^ 3 / D.tau) := by
    simpa using Real.sqrt_le_sqrt hratio
  apply Nat.le_floor
  simpa using mul_le_mul_of_nonneg_left hsqrt (Nat.cast_nonneg r)

lemma relative_error_lt_one {k r : ℕ} (D : PrimeParameterData k r)
    {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r) :
    4 * (D.sampleCard : ℝ) * (Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3) +
      8 * (D.sampleCard : ℝ) ^ 2 *
        (Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
          ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) < 1 := by
  have hr : (1 : ℝ) ≤ r := by exact_mod_cast D.r_pos
  have hM : (r : ℝ) ≤ D.M := by exact_mod_cast D.r_le_M
  have ht : (1 : ℝ) ≤ D.tau := D.real_bounds.2.1
  have hN : (D.N : ℝ) = (D.M : ℝ) ^ 10 := by simp only [N, Nat.cast_pow]
  have hs : (D.sampleCard : ℝ) ^ 2 * D.tau ≤ (r : ℝ) ^ 2 * ((D.M : ℝ) ^ 10) ^ 3 := by
    rw [← hN]
    exact sample_floor_square_bound (Nat.cast_nonneg r) (Nat.cast_nonneg D.N)
      (by exact_mod_cast D.tau_pos)
  have hh : (D.h : ℝ) ≤ 3 * (D.B : ℝ) * D.tau := by
    exact_mod_cast power_le_three_base_threshold D.base_ge_three D.two_le_k
  have hb : (D.B : ℝ) ≤ (r : ℝ) ^ 31 := by exact_mod_cast D.base_polynomial
  have hp : (D.M : ℝ) ^ 10 ≤ (r : ℝ) ^ (31620 * k) := by
    rw [← hN]
    exact D.real_bounds.2.2.2.2
  have hl : 4 * Cp + 24 * Ct * ((31620 * k : ℕ) + 1 : ℝ) ^ 2 < r := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlarge
  have he := SamplingErrors.relative_error_lt_one hr hM ht (Nat.cast_nonneg D.h)
    hs hh hb hp hCp hCt hl
  rw [← hN] at he
  convert he using 1; ring

theorem configuration_of_law {k r : ℕ} (D : PrimeParameterData k r)
    (L : PointLaw) {Cp Ct : ℝ} (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hlarge : 4 * Cp + 24 * Ct * (31620 * k + 1 : ℝ) ^ 2 < r)
    (hpair : L.pairProbability ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3)
    (htriple : L.tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
      Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h / ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
    ∃ P : Finset Point, P.card = D.sampleCard ∧ pointsInUnitSquare P ∧
      triangleAreasAtLeast P (D.tau / (16 * (D.N : ℝ) ^ 3)) := by
  have hn : 0 < D.sampleCard := D.r_pos.trans_le (r_le_sampleCard D)
  have hbudget := FinalSampling.deletion_margin hn
    (show 0 ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 by positivity)
    (show 0 ≤ Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
      ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41) by positivity)
    (relative_error_lt_one D hCp hCt hlarge)
  exact SharedGeometricAlteration.exists_configuration (2 * D.sampleCard) D.sampleCard
    (by omega) _ _ _ L.rho L.mu L.point L.rho_nonneg L.rho_sum L.mu_nonneg L.mu_sum
    L.in_square hpair htriple hbudget

theorem heilbronn_power_lower_bound_of_point_laws
    (Cp Ct : ℝ) (hCp : 0 ≤ Cp) (hCt : 0 ≤ Ct)
    (hconstruction : ∃ r0 : ℕ, ∀ r : ℕ, r0 ≤ r → r.Prime → Odd r →
      ∀ D : PrimeParameterData heilbronnK r, ∃ L : PointLaw,
        L.pairProbability ≤ Cp * (D.M : ℝ) ^ 6 / (D.N : ℝ) ^ 3 ∧
        L.tripleProbability (D.tau / (16 * (D.N : ℝ) ^ 3)) ≤
          Ct * (Real.log (2 * (D.N : ℝ))) ^ 2 * D.h /
            ((D.N : ℝ) ^ 3 * (r : ℝ) ^ 41)) :
    0 < heilbronnExponent ∧
      ∃ n : ℕ → ℕ, ∃ P : ℕ → Finset Point,
        Filter.Tendsto n Filter.atTop Filter.atTop ∧
        ∀ j : ℕ, 3 ≤ n j ∧ (P j).card = n j ∧ pointsInUnitSquare (P j) ∧
          triangleAreasAtLeast (P j)
            (Real.rpow (n j : ℝ) (-2 + heilbronnExponent)) := by
  obtain ⟨r0, hc⟩ := hconstruction
  obtain ⟨r1, hr1⟩ := exists_nat_gt
    (4 * Cp + 24 * Ct * (31620 * (heilbronnK : ℝ) + 1) ^ 2)
  apply heilbronn_power_lower_bound_of_large_prime_configurations
  refine ⟨max r0 r1, ?_⟩
  intro r hr hp ho D
  obtain ⟨L, hpair, htriple⟩ := hc r ((le_max_left _ _).trans hr) hp ho D
  have hlarge : 4 * Cp + 24 * Ct * (31620 * (heilbronnK : ℝ) + 1) ^ 2 < r :=
    hr1.trans_le (by exact_mod_cast (le_max_right r0 r1).trans hr)
  exact configuration_of_law D L hCp hCt hlarge hpair htriple

end Problem355.ParameterSampling

end

end OAI
