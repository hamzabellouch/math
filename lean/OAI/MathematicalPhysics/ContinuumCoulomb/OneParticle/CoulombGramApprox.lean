import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombGram

namespace OAI

/-! Quantitative local duality for overlapping densities. The compact local
tests are disjoint; the electron density packets need not be disjoint. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

theorem dualMatrix_quadratic_lower {m : ℕ} (A : Fin m → Fin m → ℝ)
    {a delta : ℝ} (hdelta : 0 ≤ delta) (hdiag : ∀ i, a ≤ A i i)
    (hoff : ∀ i j, i ≠ j → |A i j| ≤ delta) (d : Fin m → ℝ) :
    (a - m * delta) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, A i j * d i * d j := by
  classical
  have hpoint (i j : Fin m) :
      (if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2) ≤
        A i j * d i * d j := by
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      have h := mul_le_mul_of_nonneg_right (hdiag i) (sq_nonneg (d i))
      have hzero := mul_nonneg hdelta (sq_nonneg (d i))
      nlinarith
    · rw [ite_eq_right hij, zero_sub]
      have hprod : |A i j * d i * d j| ≤ delta * (|d i| * |d j|) := by
        calc
          _ = |A i j| * (|d i| * |d j|) := by simp only [abs_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hoff i j hij)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      have htwo : 2 * (|d i| * |d j|) ≤ d i ^ 2 + d j ^ 2 := by
        nlinarith [sq_nonneg (|d i| - |d j|), sq_abs (d i), sq_abs (d j)]
      have hscaled := mul_le_mul_of_nonneg_left htwo hdelta
      nlinarith [neg_abs_le (A i j * d i * d j)]
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) fun j _ => hpoint i j
  have hrow (i : Fin m) :
      (∑ j, ((if i = j then a * d i ^ 2 else 0) - delta / 2 * (d i ^ 2 + d j ^ 2))) =
      a * d i ^ 2 - delta / 2 * ((m : ℝ) * d i ^ 2 + ∑ j, d j ^ 2) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [hrow] at hsum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  convert hsum using 1
  ring

variable {Ω : Set Position} [IsFiniteMeasure (volume.restrict Ω)]

theorem smoothTestPacket_sum_energy (hΩ : MeasurableSet Ω) {m : ℕ}
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i)) (hs : ∀ i, tsupport (χ i) ⊆ Ω)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K : ℝ} (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    Coulomb.tfCoulomb Ω (∑ i, d i • smoothTestPacket (χ i) (hχ i) (hc i))
      (∑ i, d i • smoothTestPacket (χ i) (hχ i) (hc i)) ≤ K * ∑ i, d i ^ 2 := by
  classical
  rw [coulombGram_sum hΩ]
  have hentry (i j : Fin m) :
      Coulomb.tfCoulomb Ω (smoothTestPacket (χ i) (hχ i) (hc i))
        (smoothTestPacket (χ j) (hχ j) (hc j)) =
      if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true] using smoothTestPacket_pair_test hΩ (χ i) (χ i)
        (hχ i) (hχ i) (hc i) (hc i) (hs i) (hs i)
    · rw [ite_eq_right hij]
      exact smoothTestPacket_orthogonal hΩ (χ i) (χ j) (hχ i) (hχ j)
        (hc i) (hc j) (hs i) (hs j) (hdisjoint i j hij)
  simp_rw [hentry]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

/-- Coercivity from approximate local duality; overlap of the densities is
allowed and all Coulomb interactions remain in the matrix. -/
theorem coulombGram_coercive_of_dual_lower (hΩ : MeasurableSet Ω) {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i)) (hs : ∀ i, tsupport (χ i) ⊆ Ω)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdual : ∀ d : Fin m → ℝ, a * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, d i * d j * ∫ x, Coulomb.tfExtend Ω (density i) x * χ j x)
    (d : Fin m → ℝ) :
    (a ^ 2 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, coulombGram density i j * d i * d j := by
  let ρ := ∑ i, d i • density i
  let η : Coulomb.TFLp (volume.restrict Ω) := ∑ i, d i • smoothTestPacket (χ i) (hχ i) (hc i)
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : a * S ≤ Coulomb.tfCoulomb Ω ρ η := by
    rw [coulombGram_sum hΩ]
    simp_rw [smoothTestPacket_pair hΩ _ _ _ (hs _) ]
    exact hdual d
  have hpair0 : 0 ≤ Coulomb.tfCoulomb Ω ρ η := (mul_nonneg ha hS).trans hpair
  have hsquare : (a * S) ^ 2 ≤ (Coulomb.tfCoulomb Ω ρ η) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha hS) hpair0).mpr hpair
  have htest := smoothTestPacket_sum_energy hΩ χ hχ hc hs hdisjoint henergy d
  have hQ : 0 ≤ Coulomb.tfCoulomb Ω ρ ρ := Coulomb.tfCoulomb_self_nonneg hΩ ρ
  have hCS := Coulomb.tfCoulomb_cauchy hΩ ρ η
  have hbound : (a * S) ^ 2 ≤ Coulomb.tfCoulomb Ω ρ ρ * (K * S) :=
    hsquare.trans (hCS.trans (mul_le_mul_of_nonneg_left htest hQ))
  have hcoercive : (a ^ 2 / K) * S ≤ Coulomb.tfCoulomb Ω ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have hcancel := (mul_le_mul_iff_left₀ hSpos).mp
        (show (a ^ 2 * S) * S ≤ (Coulomb.tfCoulomb Ω ρ ρ * K) * S by
          nlinarith only [hbound])
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hK).mpr hcancel
  have hform := coulombGram_sum hΩ density density d d
  change Coulomb.tfCoulomb Ω ρ ρ = _ at hform
  rw [hform] at hcoercive
  convert hcoercive using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  dsimp [coulombGram]
  ring

/-- The diagonal test mass may vary from site to site. Only a common lower
bound and small off-site leakage are needed. -/
theorem coulombGram_coercive_local_estimates (hΩ : MeasurableSet Ω) {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i)) (hs : ∀ i, tsupport (χ i) ⊆ Ω)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a delta : ℝ} (hK : 0 < K) (hdelta : 0 ≤ delta)
    (hmargin : 0 ≤ a - m * delta)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdiag : ∀ i, a ≤ ∫ x, Coulomb.tfExtend Ω (density i) x * χ i x)
    (hoff : ∀ i j, i ≠ j → |∫ x, Coulomb.tfExtend Ω (density i) x * χ j x| ≤ delta)
    (d : Fin m → ℝ) :
    ((a - m * delta) ^ 2 / K) * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, coulombGram density i j * d i * d j := by
  apply coulombGram_coercive_of_dual_lower hΩ density χ hχ hc hs hdisjoint
    hK hmargin henergy ?_ d
  intro e
  have h := dualMatrix_quadratic_lower
    (fun i j => ∫ x, Coulomb.tfExtend Ω (density i) x * χ j x) hdelta hdiag hoff e
  convert h using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ContinuumCoulomb

end

end OAI
