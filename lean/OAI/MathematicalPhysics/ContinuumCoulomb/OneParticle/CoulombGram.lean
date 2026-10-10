import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model
import OAI.Analysis.CoulombRadii.FieldAnalysis.CoulombTest

namespace OAI

/-!
# Coercivity of the actual Coulomb Gram matrix from local dual tests

The unit-charge paper retains all long-range direct interactions. Absolute
row dominance need not hold. Smooth disjoint local tests instead give a
uniform lower bound for the full Gram form. The hypotheses below concern
normalization/localization of the actual densities and the tests; no charge
gap or target spectral comparison is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb

variable {Ω : Set Position}

def coulombGram {m : ℕ} (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (i j : Fin m) : ℝ := Coulomb.tfCoulomb Ω (density i) (density j)

def offDiagonalCoulombGram {m : ℕ} (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (i j : Fin m) : ℝ := if i = j then 0 else coulombGram density i j

theorem offDiagonalCoulombGram_symmetric {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω)) (i j : Fin m) :
    offDiagonalCoulombGram density i j = offDiagonalCoulombGram density j i := by
  classical
  simp only [offDiagonalCoulombGram, coulombGram, eq_comm]
  rw [Coulomb.tfCoulomb_symm]

theorem offDiagonalCoulombGram_diag {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω)) (i : Fin m) :
    offDiagonalCoulombGram density i i = 0 := by
  simp [offDiagonalCoulombGram]

theorem coulombGram_diagonal_split {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω)) (d : Fin m → ℝ) :
    (∑ i, ∑ j, coulombGram density i j * d i * d j) =
      (∑ i, coulombGram density i i * d i ^ 2) +
        ∑ i, ∑ j, offDiagonalCoulombGram density i j * d i * d j := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ j, ((if i = j then coulombGram density i i * d i ^ 2 else 0) +
        offDiagonalCoulombGram density i j * d i * d j) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · subst j
        simp only [ite_true, offDiagonalCoulombGram_diag, zero_mul, add_zero, pow_two]
        ring
      · simp only [ite_eq_right hij, offDiagonalCoulombGram, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      ite_true]

variable [IsFiniteMeasure (volume.restrict Ω)]

def smoothTestPacket (χ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) : Coulomb.TFLp (volume.restrict Ω) :=
  (((Coulomb.testCharge_continuous hχ).memLp_of_hasCompactSupport
    (Coulomb.testCharge_compact hc)).restrict (s := Ω)).toLp (Coulomb.testCharge χ)

theorem smoothTestPacket_pair (hΩ : MeasurableSet Ω)
    (χ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ Ω) (density : Coulomb.TFLp (volume.restrict Ω)) :
    Coulomb.tfCoulomb Ω density (smoothTestPacket χ hχ hc) =
      ∫ x, Coulomb.tfExtend Ω density x * χ x :=
  Coulomb.tfCoulomb_testCharge hΩ hχ hc hs density

theorem smoothTestPacket_pair_test (hΩ : MeasurableSet Ω)
    (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hsχ : tsupport χ ⊆ Ω) (hsψ : tsupport ψ ⊆ Ω) :
    Coulomb.tfCoulomb Ω (smoothTestPacket χ hχ hcχ) (smoothTestPacket ψ hψ hcψ) =
      ∫ x, Coulomb.testCharge χ x * ψ x := by
  rw [smoothTestPacket_pair hΩ ψ hψ hcψ hsψ]
  have he := Coulomb.tfExtend_toLp hΩ
    (((Coulomb.testCharge_continuous hχ).memLp_of_hasCompactSupport
      (Coulomb.testCharge_compact hcχ)).restrict (s := Ω))
    (fun x hx => Coulomb.testCharge_zero (fun h => hx (hsχ h)))
  exact integral_congr_ae (he.mono (fun x hx => congrArg (· * ψ x) hx))

theorem smoothTestPacket_orthogonal (hΩ : MeasurableSet Ω)
    (χ ψ : Position → ℝ) (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (hcχ : HasCompactSupport χ) (hcψ : HasCompactSupport ψ)
    (hsχ : tsupport χ ⊆ Ω) (hsψ : tsupport ψ ⊆ Ω)
    (hdisjoint : Disjoint (tsupport χ) (tsupport ψ)) :
    Coulomb.tfCoulomb Ω (smoothTestPacket χ hχ hcχ) (smoothTestPacket ψ hψ hcψ) = 0 := by
  rw [smoothTestPacket_pair_test hΩ χ ψ hχ hψ hcχ hcψ hsχ hsψ]
  have hz (x : Position) : Coulomb.testCharge χ x * ψ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · have hy : x ∉ tsupport ψ := fun hy => Set.disjoint_left.mp hdisjoint hx hy
      rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    · rw [Coulomb.testCharge_zero hx, zero_mul]
  simp_rw [hz, integral_zero]

theorem coulombGram_sum (hΩ : MeasurableSet Ω) {m : ℕ}
    (density test : Fin m → Coulomb.TFLp (volume.restrict Ω)) (d e : Fin m → ℝ) :
    Coulomb.tfCoulomb Ω (∑ i, d i • density i) (∑ j, e j • test j) =
      ∑ i, ∑ j, d i * e j * Coulomb.tfCoulomb Ω (density i) (test j) := by
  let B := Coulomb.tfCoulombContinuous hΩ
  change B (∑ i, d i • density i) (∑ j, e j • test j) = _
  simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change e j * (d i * Coulomb.tfCoulomb Ω (density i) (test j)) = _
  ring

omit [IsFiniteMeasure (volume.restrict Ω)] in
/-- A cutoff equal to one on its own packet and disjoint from the other
cutoffs is an exact local dual, including for Lp representatives. -/
theorem coulombGram_local_duality {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (χ : Fin m → Position → ℝ)
    (hmass : ∀ i, (∫ x, Coulomb.tfExtend Ω (density i) x) = 1)
    (hown : ∀ i, ∀ᵐ x, Coulomb.tfExtend Ω (density i) x = 0 ∨ χ i x = 1)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (i j : Fin m) :
    (∫ x, Coulomb.tfExtend Ω (density i) x * χ j x) = if i = j then 1 else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl, ← hmass i]
    apply integral_congr_ae
    filter_upwards [hown i] with x hx
    rcases hx with hx | hx
    · rw [hx, zero_mul]
    · rw [hx, mul_one]
  · rw [ite_eq_right hij]
    calc
      _ = ∫ _ : Position, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hown i] with x hx
        rcases hx with hx | hx
        · rw [hx, zero_mul]
        · have hxi : x ∈ tsupport (χ i) := subset_tsupport _
            (Function.mem_support.mpr (by rw [hx]; norm_num))
          have hxj : x ∉ tsupport (χ j) :=
            fun hxj => Set.disjoint_left.mp (hdisjoint i j hij) hxi hxj
          rw [image_eq_zero_of_notMem_tsupport hxj, mul_zero]
      _ = 0 := integral_zero _ _

/-- Local duality and disjoint compact tests control the entire long-range
Coulomb matrix, with no summability or row-dominance assumption. -/
theorem coulombGram_coercive (hΩ : MeasurableSet Ω) {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω))
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i)) (hs : ∀ i, tsupport (χ i) ⊆ Ω)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    (hdual : ∀ i j, (∫ x, Coulomb.tfExtend Ω (density i) x * χ j x) =
      if i = j then 1 else 0)
    {K : ℝ} (hK : 0 < K)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    (1 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, coulombGram density i j * d i * d j := by
  classical
  let test : Fin m → Coulomb.TFLp (volume.restrict Ω) :=
    fun i => smoothTestPacket (χ i) (hχ i) (hc i)
  let ρ := ∑ i, d i • density i
  let η := ∑ i, d i • test i
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : Coulomb.tfCoulomb Ω ρ η = S := by
    rw [coulombGram_sum hΩ]
    simp_rw [show ∀ i j, Coulomb.tfCoulomb Ω (density i) (test j) =
      if i = j then 1 else 0 from
      fun i j => (smoothTestPacket_pair hΩ (χ j) (hχ j) (hc j) (hs j) (density i)).trans
        (hdual i j)]
    simp [S, mul_ite, pow_two]
  have htest : Coulomb.tfCoulomb Ω η η ≤ K * S := by
    rw [coulombGram_sum hΩ]
    have hentry (i j : Fin m) : Coulomb.tfCoulomb Ω (test i) (test j) =
        if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
      by_cases hij : i = j
      · subst j
        simpa only [ite_true] using
          smoothTestPacket_pair_test hΩ (χ i) (χ i) (hχ i) (hχ i)
            (hc i) (hc i) (hs i) (hs i)
      · rw [ite_eq_right hij]
        exact smoothTestPacket_orthogonal hΩ (χ i) (χ j) (hχ i) (hχ j)
          (hc i) (hc j) (hs i) (hs j) (hdisjoint i j hij)
    simp_rw [hentry]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    calc
      _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
        simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
      _ = K * S := by rw [← Finset.sum_mul]; exact mul_comm _ _
  have hQ : 0 ≤ Coulomb.tfCoulomb Ω ρ ρ := Coulomb.tfCoulomb_self_nonneg hΩ ρ
  have hCS := Coulomb.tfCoulomb_cauchy hΩ ρ η
  rw [hpair] at hCS
  have hbound : S ^ 2 ≤ Coulomb.tfCoulomb Ω ρ ρ * (K * S) :=
    hCS.trans (mul_le_mul_of_nonneg_left htest hQ)
  have hcoercive : (1 / K) * S ≤ Coulomb.tfCoulomb Ω ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hspos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have h := (mul_le_mul_iff_right₀ hspos).mp (show S * S ≤
        S * (Coulomb.tfCoulomb Ω ρ ρ * K) by nlinarith [hbound])
      have hh : S / K ≤ Coulomb.tfCoulomb Ω ρ ρ := (div_le_iff₀ hK).mpr h
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hh
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

omit [IsFiniteMeasure (volume.restrict Ω)] in
/-- Separate the common onsite term from the actual full Coulomb matrix,
in exactly the form used by the half-filled Hubbard charge estimate. -/
theorem coulombGram_uniform_charge_condition {m : ℕ}
    (density : Fin m → Coulomb.TFLp (volume.restrict Ω)) (U c : ℝ)
    (hdiag : ∀ i, coulombGram density i i = U)
    (hcoercive : ∀ d : Fin m → ℝ,
      c * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, coulombGram density i j * d i * d j)
    (d : Fin m → ℝ) :
    c * ∑ i, d i ^ 2 ≤ U * ∑ i, d i ^ 2 +
      ∑ i, ∑ j, offDiagonalCoulombGram density i j * d i * d j := by
  have h := hcoercive d
  rw [coulombGram_diagonal_split] at h
  simp_rw [hdiag] at h
  rw [← Finset.mul_sum] at h
  exact h

end ContinuumCoulomb

end

end OAI
