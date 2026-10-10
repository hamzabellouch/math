import OAI.AlgebraicGeometry.PlaneCurves.Interpolation
import OAI.AlgebraicGeometry.PlaneCurves.PolynomialBases
import OAI.AlgebraicGeometry.PlaneCurves.SectionDimensions

namespace OAI

/-!
# Parameterized coefficient blocks, their bases, evaluation, and interpolation
-/

section

/-! Exact multiplier identities in the manuscript's fixed covering-space frames.
These are equalities of the displayed complex scalars, without replacing bundles
by other isomorphic multiplier presentations. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents

/-- Positive real powers embedded into the actual complex multiplier field. -/
abbrev tauPower (τ s : ℝ) : ℂ := ((τ ^ s : ℝ) : ℂ)

theorem tauPower_ne_zero {τ : ℝ} (hτ : 0 < τ) (s : ℝ) : tauPower τ s ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos hτ s))

theorem tauPower_add {τ : ℝ} (hτ : 0 < τ) (s t : ℝ) :
    tauPower τ (s + t) = tauPower τ s * tauPower τ t := by
  simp only [tauPower, Real.rpow_add hτ, Complex.ofReal_mul]

theorem tauPower_zpow {τ : ℝ} (hτ : 0 < τ) (s : ℝ) (k : ℤ) :
    tauPower τ s ^ k = tauPower τ ((k : ℝ) * s) := by
  simp only [tauPower, ← Complex.ofReal_zpow, ← Real.rpow_mul_intCast hτ.le]
  rw [mul_comm]

theorem tauPower_div {τ : ℝ} (hτ : 0 < τ) (s t : ℝ) :
    tauPower τ s / tauPower τ t = tauPower τ (s - t) := by
  simp only [tauPower, Real.rpow_sub hτ, Complex.ofReal_div]

/-- The displayed multiplier of A is exactly minus tau to rho. -/
theorem normalMinusMarkedMultiplier_source {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) :
    normalMinusMarkedMultiplier (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) =
      -tauPower τ ρ := by
  unfold normalMinusMarkedMultiplier
  have hp : tauPower τ ((s + ρ) / 3) ^ (3 : ℕ) = tauPower τ (s + ρ) := by
    have h := tauPower_zpow hτ ((s + ρ) / 3) (3 : ℤ)
    norm_num at h
    convert h using 1
    congr 1
    ring
  rw [hp, div_neg, tauPower_div hτ]
  congr 2
  ring

/-- Literal low-branch multiplier and exponent, including its sign character. -/
theorem firstSourceMultiplier {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) (d m j : ℤ) :
    tauPower τ ((s + ρ) / 3) ^ (d - 3 * m) *
      normalMinusMarkedMultiplier (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) ^ (m - j) =
    (-1 : ℂ) ^ (m - j) *
      tauPower τ (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) := by
  rw [normalMinusMarkedMultiplier_source hτ, tauPower_zpow hτ]
  rw [show -tauPower τ ρ = (-1 : ℂ) * tauPower τ ρ by ring, mul_zpow,
    tauPower_zpow hτ, tauPower_add hτ]
  ring

/-- The high-branch source multiplier has no sign character. -/
theorem secondSourceMultiplier {τ : ℝ} (hτ : 0 < τ) (s ρ : ℝ) (d j : ℤ) :
    tauPower τ ((s + ρ) / 3) ^ (d - 3 * j) =
      tauPower τ (((d - 3 * j : ℤ) : ℝ) * ((s + ρ) / 3)) :=
  tauPower_zpow hτ _ _

theorem firstSourceEndpoint (s ρ Δ x₀ : ℝ) (d m j : ℤ) (hs : s = 9 * x₀ - Δ) :
    (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) -
      x₀ * (commonDegree d m : ℝ) = firstLower d m j ρ Δ := by
  simpa only [commonDegree, firstLower, Int.cast_mul, Int.cast_sub, Int.cast_ofNat] using
    Nagata.BundleArithmetic.first_interval_parameter (d : ℝ) (m : ℝ) (j : ℝ) s ρ Δ x₀ hs

theorem secondSourceEndpoint (s ρ Δ x₀ : ℝ) (d j : ℤ) (hs : s = 9 * x₀ - Δ) :
    (((d - 3 * j : ℤ) : ℝ) * ((s + ρ) / 3)) -
      x₀ * (sourceDegree d j : ℝ) = secondLower d j ρ Δ := by
  simpa only [sourceDegree, secondLower, Int.cast_mul, Int.cast_sub, Int.cast_ofNat] using
    Nagata.BundleArithmetic.second_interval_parameter (d : ℝ) (j : ℝ) s ρ Δ x₀ hs

end Nagata.Workers.W10

end
end

section

/-! The distribution-hypothesis form of Section 4's horizontal-row interpolation lemma. -/
namespace Nagata.Workers.W10

/-- Interpolation after sorting the represented rows by decreasing size.
Each represented row is required to be nonempty, as in the manuscript. -/
theorem interpolate_distributed_rows (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hpos : ∀ i, 1 ≤ (xs i).card) (hsize : ∀ i, (xs i).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1))
    (v : Nagata.W01.Plane → ℂ) :
    ∃ f ∈ Nagata.W01.monomialSpace q m,
      ∀ i, ∀ x ∈ xs i, f (x, K i) = v (x, K i) := by
  obtain ⟨σ, _, hσ⟩ := exists_ordered_rows (fun i => (xs i).card) q m
    hpos hsize hdistribution
  obtain ⟨f, hf, hv⟩ := Nagata.W01.interpolate_fin_rows q m s (K ∘ σ) (xs ∘ σ)
    (hK.comp σ.injective) (fun i => hsize (σ i)) hσ v
  refine ⟨f, hf, ?_⟩
  intro i x hx
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
    hv (σ.symm i) x (by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx)

/-- The interpolating function has a genuine bivariate polynomial representative. -/
theorem interpolate_distributed_rows_polynomial (q m s : ℕ) (K : Fin s → ℂ)
    (xs : Fin s → Finset ℂ) (hK : Function.Injective K)
    (hpos : ∀ i, 1 ≤ (xs i).card) (hsize : ∀ i, (xs i).card ≤ m)
    (hdistribution : ∀ t, 1 ≤ t → t ≤ m →
      (Finset.univ.filter fun i => t ≤ (xs i).card).card ≤ q * (m - t + 1))
    (v : Nagata.W01.Plane → ℂ) :
    ∃ p ∈ Nagata.W01.polynomialSpace q m,
      ∀ i, ∀ x ∈ xs i, Nagata.W01.planeEval p (x, K i) = v (x, K i) := by
  obtain ⟨f, hf, hv⟩ := interpolate_distributed_rows q m s K xs hK hpos hsize hdistribution v
  obtain ⟨p, hp, hpf⟩ := Nagata.W01.exists_polynomialSpace_of_mem hf
  exact ⟨p, hp, by simpa [hpf] using hv⟩

end Nagata.Workers.W10

end

section

/-! The assembled source-to-coefficient equivalence preserves literal local
expressions, including the marked-product power on the high branch. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces

theorem sourceCoefficientEquiv_apply (τ γL γP : ℂ) (d m j : ℤ) (P : ℂ → ℂ)
    (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
    (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
    (f : sourceBlock τ γL γP d m j) (z : ℂ) :
    (sourceCoefficientEquiv τ γL γP d m j P hP hPfin f).val z =
      if j ≤ m then f.val z else P z ^ (j - m).toNat * f.val z := by
  unfold sourceCoefficientEquiv
  split_ifs <;> rfl

end Nagata.Workers.W10

end
end

section

/-! Exact genuine source block identifications for the fixed manuscript
multipliers and centered theta parameters. -/
noncomputable section
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents Nagata.W08

/-- Low blocks use the exact centered theta multiplier, including the sign. -/
def firstSourceThetaEquiv {τ : ℝ} (hτ : 0 < τ) (s ρ Δ x₀ : ℝ)
    (d m j : ℤ) (hs : s = 9 * x₀ - Δ) (hj : j ≤ m) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
    automorphicSections (τ : ℂ) (commonDegree d m)
      ((-1 : ℂ) ^ (m - j) * tauPower τ (firstLower d m j ρ Δ + x₀ * (commonDegree d m : ℝ))) :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, ite_eq_left hj]
    rw [firstSourceMultiplier hτ]
    have he : (((d - 3 * m : ℤ) : ℝ) * ((s + ρ) / 3) + ((m - j : ℤ) : ℝ) * ρ) =
        firstLower d m j ρ Δ + x₀ * (commonDegree d m : ℝ) := by
      have h := firstSourceEndpoint s ρ Δ x₀ d m j hs
      linarith
    rw [he]
    rfl)

/-- Positive high blocks have the exact centered theta multiplier with epsilon1. -/
def secondSourceThetaEquiv {τ : ℝ} (hτ : 0 < τ) (s ρ Δ x₀ : ℝ)
    (d m j : ℤ) (hs : s = 9 * x₀ - Δ) (hj : m < j) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
    automorphicSections (τ : ℂ) (sourceDegree d j)
      ((1 : ℂ) * tauPower τ (secondLower d j ρ Δ + x₀ * (sourceDegree d j : ℝ))) :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, ite_eq_right (not_le.mpr hj), one_mul]
    rw [secondSourceMultiplier hτ]
    congr 1
    congr 1
    have he := secondSourceEndpoint s ρ Δ x₀ d j hs
    linarith)

/-- The literal degree-zero tip is exactly the genuine constant section space. -/
def zeroSourceThetaEquiv (τ s ρ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0) :
    sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j ≃ₗ[ℂ]
      automorphicSections (τ : ℂ) 0 1 :=
  LinearEquiv.ofEq _ _ (by
    simp only [sourceBlock, ite_eq_right (not_le.mpr hj), hz, mul_zero, zpow_zero])

end Nagata.Workers.W10

end
end

section

/-! The final algebraic assembly layer for actual independently constructed
source bases. Applications must supply the actual proved theta bases. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.CoefficientSpaces Nagata.FiniteExponents

variable (τ γL γP : ℂ) (d : ℤ) (m : ℕ) (a Δ : ℝ) (P : ℂ → ℂ)
  (hd : 3 * (m : ℤ) < d)
  (hP : AnalyticOnNhd ℂ P {z | z ≠ 0})
  (hPfin : ∀ z ≠ 0, analyticOrderAt P z ≠ ⊤)
  (b : ∀ j : Fin ((d / 3).toNat + 1),
    Basis (ColumnFiber d (m : ℤ) a Δ (j.val : ℤ)) ℂ
      (sourceBlock τ γL γP d (m : ℤ) (j.val : ℤ)))

def polynomialBasisFromSourceBases :
    Basis (Column d (m : ℤ) a Δ) ℂ (polynomialSections τ γL γP d (m : ℤ) P) :=
  literalPolynomialBasis τ γL γP d (m : ℤ) a Δ P (Int.natCast_nonneg m) hd hP hPfin
    (fun j => (b j).equivFun.toLinearMap) (fun j => (b j).equivFun.injective) (fun j K => b j K)
    (fun j K => by ext L; simp [Basis.equivFun_self, Pi.single_apply, eq_comm])

/-- Explicit local expression after both the section-image equivalence and
literal-column reindexing. The only piecewise factor is the actual Pi power. -/
theorem polynomialBasisFromSourceBases_local
    (j : Fin ((d / 3).toNat + 1)) (K : ColumnFiber d (m : ℤ) a Δ (j.val : ℤ))
    (z₀ x y : ℂ) :
    Nagata.W20.localScalar
      (polynomialBasisFromSourceBases τ γL γP d m a Δ P hd hP hPfin b
        (columnFiberEquiv d (m : ℤ) a Δ (Int.natCast_nonneg m) hd ⟨j, K⟩)) z₀ x y =
      (if (j.val : ℤ) ≤ (m : ℤ) then (b j K).val (z₀ * Complex.exp x)
        else P (z₀ * Complex.exp x) ^ ((j.val : ℤ) - (m : ℤ)).toNat *
          (b j K).val (z₀ * Complex.exp x)) * Complex.exp ((j.val : ℂ) * y) := by
  unfold polynomialBasisFromSourceBases
  rw [literalPolynomialBasis_localScalar, sourceCoefficientEquiv_apply]

end Nagata.Workers.W10

end
end

section

/-! The actual literal degree-zero source block has its constant-one basis,
without any Laurent injectivity assumption. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents

def zeroSourceBlockBasis {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (s ρ Δ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((Nagata.W19.degreeZeroConstantBasis.{0} hτ hτone).map
    (zeroSourceThetaEquiv τ s ρ d m j hj hz).symm).reindex
    (zeroColumnFiberEquiv.{1} d m j ρ Δ hj hz).symm

@[simp] theorem zeroSourceBlockBasis_apply {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (s ρ Δ : ℝ) (d m j : ℤ) (hj : m < j) (hz : d - 3 * j = 0)
    (K : ColumnFiber d m ρ Δ j) (z : ℂ) (hz0 : z ≠ 0) :
    (zeroSourceBlockBasis hτ hτone s ρ Δ d m j hj hz K).val z = 1 := by
  simp only [zeroSourceBlockBasis, Basis.reindex_apply, Basis.map_apply, Equiv.symm_symm]
  change (Nagata.W19.degreeZeroConstantBasis.{0} hτ hτone
    (zeroColumnFiberEquiv.{1} d m j ρ Δ hj hz K)).val z = 1
  rw [Nagata.W19.degreeZeroConstantBasis_apply]
  exact normalizedConstantSection_apply _ _ _ hz0

end Nagata.Workers.W10

end
end

section

/-! Actual positive source block bases in the manuscript's exact multiplier
frames. All scalar and interval identifications are proved. The sole analytic
completeness input is injectivity of the genuine circle coefficient map. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents Nagata.W08 Nagata.W09

variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d m j : ℤ) (hs : s = 9 * x₀ - Δ)

def firstSourceBlockBasis (hd : 3 * m < d) (hj0 : 0 ≤ j) (hj : j ≤ m)
    (hU : firstLower d m j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((thetaSectionBasisAtLower (commonDegree d m) (by unfold commonDegree; omega)
    (firstLower d m j ρ Δ) x₀ (zpow_ne_zero _ (by norm_num)) (by simp) hτ hτone
    (hC _ _) hU).map (firstSourceThetaEquiv hτ s ρ Δ x₀ d m j hs hj).symm).reindex
    (firstColumnFiberEquiv d m j ρ Δ hj0 hj hU).symm

def positiveSourceBlockBasis (hj : m < j) (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ)) :
    Basis (ColumnFiber d m ρ Δ j) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d m j) :=
  ((thetaSectionBasisAtLower (sourceDegree d j) (by unfold sourceDegree; omega)
    (secondLower d j ρ Δ) x₀ one_ne_zero (by simp) hτ hτone
    (hC _ _) hU).map (secondSourceThetaEquiv hτ s ρ Δ x₀ d m j hs hj).symm).reindex
    (positiveColumnFiberEquiv d m j ρ Δ hj hjd hn hU).symm

/-- The low source basis is exactly the source normalized theta family. -/
theorem firstSourceBlockBasis_local (hd : 3 * m < d) (hj0 : 0 ≤ j) (hj : j ≤ m)
    (hU : firstLower d m j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
    (K : ColumnFiber d m ρ Δ j) (x : ℂ) :
    (firstSourceBlockBasis hτ hτone hC s ρ Δ x₀ d m j hs hd hj0 hj hU K).val
      (tauPower τ x₀ * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (commonDegree d m : ℝ)
        ((K.val : ℝ) - firstLower d m j ρ Δ) (K.val : ℝ) ((-1 : ℂ) ^ (m - j)) τ x := by
  rw [firstSourceBlockBasis, Basis.reindex_apply, Basis.map_apply]
  simp only [Equiv.symm_symm, firstSourceThetaEquiv, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]
  exact thetaSectionBasisAtLower_local _ _ _ _ _ _ _ _ _ _ _ x

/-- The positive high source basis is its exact untwisted theta family. -/
theorem positiveSourceBlockBasis_local (hj : m < j) (hjd : j ≤ d / 3) (hn : 0 < d - 3 * j)
    (hU : secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
    (K : ColumnFiber d m ρ Δ j) (x : ℂ) :
    (positiveSourceBlockBasis hτ hτone hC s ρ Δ x₀ d m j hs hj hjd hn hU K).val
      (tauPower τ x₀ * Complex.exp x) =
      Nagata.W22.normalizedThetaSeries (sourceDegree d j : ℝ)
        ((K.val : ℝ) - secondLower d j ρ Δ) (K.val : ℝ) 1 τ x := by
  rw [positiveSourceBlockBasis, Basis.reindex_apply, Basis.map_apply]
  simp only [Equiv.symm_symm, secondSourceThetaEquiv, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply]
  exact thetaSectionBasisAtLower_local _ _ _ _ _ _ _ _ _ _ _ x

end Nagata.Workers.W10

end
end

section

/-! Assembly of every actual source block, including the constant tip. The sole
external analytic input is the genuine Laurent coefficient injectivity theorem. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents Nagata.W09

variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (hC : ∀ (n : ℤ) (γ : ℂ), Function.Injective (laurentCoefficientMap (τ : ℂ) n γ))
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))

def allSourceBlockBases (j : Fin ((d / 3).toNat + 1)) :
    Basis (ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d (m : ℤ) (j.val : ℤ)) := by
  have hj0 : 0 ≤ (j.val : ℤ) := Int.natCast_nonneg _
  have hjd : (j.val : ℤ) ≤ d / 3 := by omega
  by_cases hj : (j.val : ℤ) ≤ (m : ℤ)
  · exact firstSourceBlockBasis hτ hτone hC s ρ Δ x₀ d (m : ℤ) (j.val : ℤ) hs hd hj0 hj
      (hUfirst _ hj0 hj)
  · have hmj : (m : ℤ) < (j.val : ℤ) := lt_of_not_ge hj
    by_cases hn : 0 < d - 3 * (j.val : ℤ)
    · exact positiveSourceBlockBasis hτ hτone hC s ρ Δ x₀ d (m : ℤ) (j.val : ℤ) hs hmj hjd hn
        (hUsecond _ hmj hjd hn)
    · exact zeroSourceBlockBasis hτ hτone s ρ Δ d (m : ℤ) (j.val : ℤ) hmj (by omega)

theorem allSourceBlockBases_local (j : Fin ((d / 3).toNat + 1))
    (K : ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) (x : ℂ) :
    (allSourceBlockBases hτ hτone hC s ρ Δ x₀ d m hs hd hUfirst hUsecond j K).val
      (tauPower τ x₀ * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        Nagata.W22.normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) ρ Δ) (K.val : ℝ)
          ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        Nagata.W22.normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) ρ Δ) (K.val : ℝ) 1 τ x
      else 1 := by
  unfold allSourceBlockBases
  split_ifs with hj hn
  · exact firstSourceBlockBasis_local _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K x
  · exact positiveSourceBlockBasis_local _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K x
  · exact zeroSourceBlockBasis_apply _ _ _ _ _ _ _ _ _ _ K _
      (mul_ne_zero (tauPower_ne_zero hτ x₀) (Complex.exp_ne_zero x))

end Nagata.Workers.W10

end
end

section

/-! Unconditional genuine source-block bases, with the manuscript's exact finite
index set and local scalar expressions. No Laurent completeness input remains. -/
noncomputable section
open Module
namespace Nagata.Workers.W10
open Nagata.FiniteExponents

variable {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
  (s ρ Δ x₀ : ℝ) (d : ℤ) (m : ℕ) (hs : s = 9 * x₀ - Δ)
  (hd : 3 * (m : ℤ) < d)
  (hUfirst : ∀ j : ℤ, 0 ≤ j → j ≤ (m : ℤ) →
    firstLower d (m : ℤ) j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))
  (hUsecond : ∀ j : ℤ, (m : ℤ) < j → j ≤ d / 3 → 0 < d - 3 * j →
    secondLower d j ρ Δ ∉ Set.range (Int.cast : ℤ → ℝ))

def actualSourceBlockBases (j : Fin ((d / 3).toNat + 1)) :
    Basis (ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) ℂ
      (sourceBlock (τ : ℂ) (tauPower τ ((s + ρ) / 3)) (-tauPower τ s) d (m : ℤ) (j.val : ℤ)) :=
  allSourceBlockBases hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ))
    s ρ Δ x₀ d m hs hd hUfirst hUsecond j

theorem actualSourceBlockBases_local (j : Fin ((d / 3).toNat + 1))
    (K : ColumnFiber d (m : ℤ) ρ Δ (j.val : ℤ)) (x : ℂ) :
    (actualSourceBlockBases hτ hτone s ρ Δ x₀ d m hs hd hUfirst hUsecond j K).val
      (tauPower τ x₀ * Complex.exp x) =
      if (j.val : ℤ) ≤ (m : ℤ) then
        Nagata.W22.normalizedThetaSeries (commonDegree d (m : ℤ) : ℝ)
          ((K.val : ℝ) - firstLower d (m : ℤ) (j.val : ℤ) ρ Δ) (K.val : ℝ)
          ((-1 : ℂ) ^ ((m : ℤ) - (j.val : ℤ))) τ x
      else if 0 < d - 3 * (j.val : ℤ) then
        Nagata.W22.normalizedThetaSeries (sourceDegree d (j.val : ℤ) : ℝ)
          ((K.val : ℝ) - secondLower d (j.val : ℤ) ρ Δ) (K.val : ℝ) 1 τ x
      else 1 :=
  allSourceBlockBases_local hτ hτone (Nagata.W01.laurentCoefficientMap_injective (τ : ℂ))
    s ρ Δ x₀ d m hs hd hUfirst hUsecond j K x

end Nagata.Workers.W10

end
end

end OAI
