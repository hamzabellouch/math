import OAI.NumberTheory.DirichletL.QuadraticSieve.DualMiddleExpansion
import OAI.NumberTheory.DirichletL.Eisenstein.SmoothCuspCutoffs

namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

namespace CubicEisenstein
open Filter
open scoped BigOperators Classical Topology ContDiff

lemma cuspSeed_row_defect (a b : ℝ) (s c : ℂ) (u : Fin 2 → ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (fun q => c*cuspSeedProfile a b s (rowHeight u q)) p-
      s*(s-2)*(c*cuspSeedProfile a b s (rowHeight u p))=
        c*cuspSeedDefectProfile a b s (rowHeight u p) := by
  rw [axisLaplacian_const_mul,rowProfile_laplacian _ (cuspSeedProfile_contDiffAt a b s) u hu p hp]
  have h := cuspSeedProfile_laplace_defect a b s (rowHeight u p) (rowHeight_pos u hu p hp).ne'
  linear_combination c*h

theorem heightPoincare_cuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (heightPoincareField (cuspSeedProfile a b s)) p-
      s*(s-2)*heightPoincareField (cuspSeedProfile a b s) p=
        heightPoincareField (cuspSeedDefectProfile a b s) p := by
  obtain ⟨U,hU,hpU,S,hrows⟩ := locally_finite_high_rows p hp
  let f : CuspCosets → SpatialCoordinates → ℂ :=
    fun r q => (cosetCharacter r)⁻¹*cuspSeedProfile a b s (rowHeight (embeddedRow r) q)
  have heq : heightPoincareField (cuspSeedProfile a b s) =ᶠ[𝓝 p] (fun q => ∑r∈S,f r q) := by
    filter_upwards [hU.mem_nhds hpU] with q hq
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedProfile_zero a b s _ hab (le_trans ((hrows q hq).2 r hr).le ha.le),mul_zero]
  have hD : heightPoincareField (cuspSeedDefectProfile a b s) p=
      ∑r∈S,(cosetCharacter r)⁻¹*cuspSeedDefectProfile a b s (rowHeight (embeddedRow r) p) := by
    apply tsum_eq_sum
    intro r hr
    rw [cuspSeedDefectProfile_zero a b s _ hab (Or.inl (((hrows p hpU).2 r hr).trans ha)),mul_zero]
  have hreg : ∀r∈S,∀q,0<q 2→∀j : Fin 3,
      DifferentiableAt ℝ (axisSlice (f r) q j) (q j) ∧
      DifferentiableAt ℝ (deriv (axisSlice (f r) q j)) (q j) := by
    intro r hr q hq j
    have hc : ∀v,0<v→ContDiffAt ℝ ∞ (fun v => (cosetCharacter r)⁻¹*cuspSeedProfile a b s v) v :=
      fun v hv => contDiffAt_const.mul (cuspSeedProfile_contDiffAt a b s v hv)
    have h := rowProfile_axis_derivatives _ hc (embeddedRow r) (embeddedRow_ne_zero r) q hq j
    exact ⟨h.1.differentiableAt,h.2.differentiableAt⟩
  rw [axisLaplacian_congr_eventuallyEq _ _ p heq,axisLaplacian_finset_sum S f hreg p hp,
    heq.eq_of_nhds,hD,Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  exact cuspSeed_row_defect a b s (cosetCharacter r)⁻¹ (embeddedRow r) (embeddedRow_ne_zero r) p hp

def smoothCuspSeedField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeed a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

def smoothCuspSeedDefectField (a b : ℝ) (s : ℂ) (p : SpatialCoordinates) : ℂ :=
  if hp : 0<p 2 then smoothCuspSeedDefect a b s
    (upperPoint ((p 0:ℂ)+(p 1:ℂ)*Complex.I) (p 2) hp) else 0

lemma smoothCuspSeedField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedField a b s p=heightPoincareField (cuspSeedProfile a b s) p := by
  rw [smoothCuspSeedField,dite_eq_left hp,smoothCuspSeed_coordinate a b s ha hab p hp]
lemma smoothCuspSeedDefectField_eq (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    smoothCuspSeedDefectField a b s p=heightPoincareField (cuspSeedDefectProfile a b s) p := by
  rw [smoothCuspSeedDefectField,dite_eq_left hp,smoothCuspSeedDefect_coordinate a b s ha hab p hp]

lemma actual_smoothCuspSeed_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) : ContDiffAt ℝ ∞ (smoothCuspSeedField a b s) p := by
  have heq : smoothCuspSeedField a b s =ᶠ[𝓝 p] heightPoincareField (cuspSeedProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedField_eq a b s ha hab q hq
  exact (smoothCuspSeed_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

theorem actual_smoothCuspSeed_laplace_defect (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    axisLaplacian (smoothCuspSeedField a b s) p-s*(s-2)*smoothCuspSeedField a b s p=
      smoothCuspSeedDefectField a b s p := by
  rw [axisLaplacian_congr_positive _ _ (fun q hq => smoothCuspSeedField_eq a b s ha hab q hq) p hp,
    smoothCuspSeedField_eq a b s ha hab p hp,smoothCuspSeedDefectField_eq a b s ha hab p hp]
  exact heightPoincare_cuspSeed_laplace_defect a b s ha hab p hp

lemma cuspSeedProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedProfile a b s v) := by
  unfold cuspSeedProfile positiveHeightPower logRatioPower
  fun_prop
lemma cuspSeedDefectProfile_entire (a b v : ℝ) : Differentiable ℂ (fun s => cuspSeedDefectProfile a b s v) := by
  unfold cuspSeedDefectProfile positiveHeightPower logRatioPower
  fun_prop

lemma cuspCutoffCorrection_parameter_entire (F : ℂ → ℝ → ℂ)
    (hF : ∀v,Differentiable ℂ (fun s => F s v)) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => cuspCutoffCorrection 1 (F s) w) := by
  let S := (high_cosets_finite 1 le_rfl w).toFinset
  have heq : (fun s => cuspCutoffCorrection 1 (F s) w)=
      (fun s => ∑r∈S,cuspCutoffTerm 1 (F s) r w) := by
    funext s
    apply tsum_eq_sum
    intro r hr
    have hh : ¬1<cosetHeight r w := by simpa only [S,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hr
    simp [cuspCutoffTerm,hh]
  rw [heq]
  apply Differentiable.fun_sum
  intro r hr
  unfold cuspCutoffTerm
  split_ifs
  · exact (differentiable_const _).mul (hF _)
  · exact differentiable_const _

theorem smoothCuspSeed_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeed a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedProfile_entire a b) w

theorem smoothCuspSeedDefect_entire (a b : ℝ) (w : HyperbolicSpace) :
    Differentiable ℂ (fun s => smoothCuspSeedDefect a b s w) :=
  cuspCutoffCorrection_parameter_entire _ (cuspSeedDefectProfile_entire a b) w

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sectorBadIdeal (E : fixedBadPrimes.powerset) : Ideal O := ∏ P ∈ E.val, P

theorem sector_bad_good_product (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) :
    sectorBadIdeal E * goodSquarefreePart I = I := by
  have hs : badPrimeSupport I = E.val := congrArg Subtype.val hE
  simpa only [hs, sectorBadIdeal] using squarefree_bad_good_product I hI

theorem sectorBadIdeal_ne_zero_of_row (I : Ideal O) (hI : Squarefree I)
    (E : fixedBadPrimes.powerset) (hE : badPrimeSector I = E) : sectorBadIdeal E ≠ 0 := by
  intro hz
  have hp := sector_bad_good_product I hI E hE
  rw [hz, zero_mul] at hp
  exact hI.ne_zero hp.symm

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPairTerm (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) : ℂ :=
  if IsCoprime (left j) (right k) then
    star (a j) * b k * unrestrictedPairCharacter (left j) (right k) (rows i) else 0

omit [Fintype m] [Fintype n] [Fintype p] [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedPairTerm_sector (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (i : m) (j : n) (k : p) :
    unrestrictedPairTerm rows left right a b i j k =
      originalTerm (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) 1 1 i j k := by
  classical
  by_cases hc : IsCoprime (left j) (right k)
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_true, one_dvd]
    have hp := unrestrictedPairCharacter_squarefree_bad_split (left j) (right k) (rows i)
      (hleft j) (hright k) (hray j k) (hrows i)
    have hs : badPrimeSupport (rows i) = E.val := congrArg Subtype.val (hE i)
    rw [hp, hs]
    simp only [sectorBadIdeal, unrestrictedPairCharacter, star_mul,
      canonical_quadraticRow_star _ (hleft j)]
    ring
  · simp only [unrestrictedPairTerm, originalTerm, hc, ite_false]

def unrestrictedDualTruncatedMiddle (W : 𝓢(ℝ, ℂ))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) : ℂ) *
      middleTruncation (fun P : primePool {left j * right k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ)))) (Y i) (Z i) lengthScale)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualTruncatedMiddle_sector
    (W : 𝓢(ℝ, ℂ)) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E)
    (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ) : ℝ) : ℂ) *
        dualTruncatedMiddle W (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          (M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) F Y Z lengthScale := by
  classical
  have hQn : (Ideal.absNorm (sectorBadIdeal E) : ℝ) ≠ 0 := by
    exact_mod_cast (show Ideal.absNorm (sectorBadIdeal E) ≠ 0 from fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedDualTruncatedMiddle dualTruncatedMiddle
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i) : ℝ) =
      (Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ) := by
    calc
      (Ideal.absNorm (rows i) : ℝ) =
          (Ideal.absNorm (sectorBadIdeal E * goodSquarefreePart (rows i)) : ℝ) :=
        congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
          (sector_bad_good_product (rows i) (hrows i) E (hE i)).symm
      _ = _ := by rw [map_mul, Nat.cast_mul]
  rw [hn]
  have harg : F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      (M * ((Ideal.absNorm (sectorBadIdeal E) : ℝ) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ))) =
    F * (Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ) /
      ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) * (Ideal.absNorm (goodSquarefreePart (rows i)) : ℝ)) := by ring
  rw [harg]
  have hs : (M / (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F) : ℝ) =
      (1 / (Ideal.absNorm (sectorBadIdeal E) : ℝ)) *
        ((M * (Ideal.absNorm (sectorBadIdeal E) : ℝ)) /
          (Real.sqrt ((Ideal.absNorm (left j) : ℝ) * (Ideal.absNorm (right k) : ℝ)) * F)) := by
    field_simp [hQn]
  rw [hs, Complex.ofReal_mul]
  ring

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

lemma divisorEnergyFactor_mono_coefficients {n p : Type*} [Fintype n] [Fintype p]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    divisorEnergyFactor ε hε N a' b' ≤ divisorEnergyFactor ε hε N a b := by
  have hA : (∑ j, ‖a' j‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (ha j) _)
  have hB : (∑ k, ‖b' k‖ ^ 2) ≤ ∑ k, ‖b k‖ ^ 2 :=
    Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ (norm_nonneg _) (hb k) _)
  have hs := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
  have hd := (DivisorBlockCauchy.divisorConstant_pos ε hε).le
  unfold divisorEnergyFactor
  gcongr

lemma dual_bad_sector_scale (M F B Q U α : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 ≤ B) (hQ : 1 ≤ Q)
    (hU : 0 ≤ U) (hα : 1 / 2 ≤ α) :
    (1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)) ≤
      M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2) := by
  have hQp : 0 < Q := by linarith
  have hpow : (B / Q) ^ (α - 1 / 2) ≤ B ^ (α - 1 / 2) :=
    Real.rpow_le_rpow (by positivity) (div_le_self hB hQ) (by linarith)
  have hsQ : Real.sqrt Q ≤ Q := Real.sqrt_le_self_iff.mpr (Or.inr hQ)
  have hs : (1 / Q) * Real.sqrt (M * Q / F) ≤ Real.sqrt (M / F) := by
    have he : M * Q / F = (M / F) * Q := by ring
    rw [he, Real.sqrt_mul (by positivity)]
    have ht : Real.sqrt Q / Q ≤ 1 := (div_le_one hQp).mpr hsQ
    calc
      _ = Real.sqrt (M / F) * (Real.sqrt Q / Q) := by ring
      _ ≤ Real.sqrt (M / F) * 1 := mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  calc
    _ = M / F + (2 * U) * ((1 / Q) * Real.sqrt (M * Q / F)) * (B / Q) ^ (α - 1 / 2) := by
      field_simp

    _ ≤ _ := by gcongr

def dualMiddleMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) : ℝ :=
  ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
    ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
      divisorEnergyFactor ε hε N a b * (divisorExponentConstant hexp deltaLoss hδ * (B * N) ^ deltaLoss) *
        (M / F + (2 * U) * Real.sqrt (M / F) * B ^ (α - 1 / 2)))

lemma dualMiddleMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ))
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  have hc := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold dualMiddleMajorant
  positivity

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.dual_truncated_middle_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedDualTruncatedMiddle, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b W (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j * quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k * quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i) : ℝ) = Q * (Ideal.absNorm (good i) : ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I : ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul, Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B / Q) / 2 ≤ (Ideal.absNorm (good i) : ℝ) ∧
        (Ideal.absNorm (good i) : ℝ) ≤ B / Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B / Q / 2 = (B / 2) / Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B / Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀) : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZa (i : m) : Z i ≤ U * (N * Real.sqrt (F / ((M * Q) * (Ideal.absNorm (good i) : ℝ)))) := by
      simpa only [hn i, mul_assoc] using hZ i
    have hbnd := hexp.dual_truncated_middle deltaLoss hδ ε hε (B / Q) N (M * Q) F U hBQ hN
      (by positivity) hF hU good left right hgr hl hri hg a' b' W Y Z lengthScale hleft hright hZa
    change ‖dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale‖ ≤
      dualMiddleMajorant hexp deltaLoss hδ ε hε (B / Q) N (M * Q) F U a' b' W at hbnd
    have htr := unrestrictedDualTruncatedMiddle_sector W rows left right a b M F Y Z lengthScale
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ((1 / Q : ℝ) : ℂ) * dualTruncatedMiddle W good left right a' b' (M * Q) F Y Z lengthScale at htr
    rw [htr, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / Q)]
    apply (mul_le_mul_of_nonneg_left hbnd (by positivity)).trans
    have hae (j : n) : ‖a' j‖ ≤ ‖a j‖ := by
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have hbe (k : p) : ‖b' k‖ ≤ ‖b k‖ := by
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' hae hbe
    have hp : ((B / Q) * N) ^ deltaLoss ≤ (B * N) ^ deltaLoss := by
      apply Real.rpow_le_rpow (by positivity) _ hδ.le
      exact mul_le_mul_of_nonneg_right (div_le_self (by linarith) hQ) (by linarith)
    have hs := dual_bad_sector_scale M F B Q U α hM hF (by linarith) hQ hU hα
    have hc := nonzeroLatticeEnvelopeConstant_nonneg
    have hW := dualMiddleDecayConstant_nonneg W
    have hea := divisorEnergyFactor_nonneg ε hε N a' b'
    have heb := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    unfold dualMiddleMajorant
    calc
      _ = ((columnDyadicLength N + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * nonzeroLatticeEnvelopeConstant * dualMiddleDecayConstant W) *
          divisorEnergyFactor ε hε N a' b' * (divisorExponentConstant hexp deltaLoss hδ * ((B / Q) * N) ^ deltaLoss) *
            ((1 / Q) * (M * Q / F + (2 * U) * Real.sqrt (M * Q / F) * (B / Q) ^ (α - 1 / 2)))) := by ring
      _ ≤ _ := by gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.unrestricted_dual_truncated_middle {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1 / 2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B / 2 ≤ (Ideal.absNorm (rows i) : ℝ) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (a : n → ℂ) (b : p → ℂ) (W : 𝓢(ℝ, ℂ)) (Y Z : m → ℝ) (lengthScale : ℝ)
    (hleft : ∀ j, Admissible (left j) ∧ N / 2 ≤ (Ideal.absNorm (left j) : ℝ) ∧ (Ideal.absNorm (left j) : ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N / 2 ≤ (Ideal.absNorm (right k) : ℝ) ∧ (Ideal.absNorm (right k) : ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (hZ : ∀ i, Z i ≤ U * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) :
    ‖unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale‖ ≤
      4 * dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedDualTruncatedMiddle W rows left right a b M F Y Z lengthScale =
      ∑ E : fixedBadPrimes.powerset,
        unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale := by
    unfold unrestrictedDualTruncatedMiddle
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ ≤
        dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W := by
    apply hexp.dual_truncated_middle_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right
      (fun i k h => Subtype.ext (hr h)) hl hri (fun i => hrows i.val) a b W
      (fun i => Y i.val) (fun i => Z i.val) lengthScale hleft hright hray (fun i => hZ i.val) E
    exact fun i => i.property
  rw [hs]
  calc
    _ ≤ ∑ E : fixedBadPrimes.powerset,
        ‖unrestrictedDualTruncatedMiddle W (fun i : {i // σ i = E} => rows i.val)
          left right a b M F (fun i => Y i.val) (fun i => Z i.val) lengthScale‖ := norm_sum_le _ _
    _ ≤ ∑ _E : fixedBadPrimes.powerset, dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F U a b W :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe,
        fixedBadPrimes_powerset_card]
      norm_num

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_fixed_mask (Ψ : O →* ℂ) (m g f y : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*g) f y H U =
      rowCoprimeMask (fun i => Ideal.span {p i}) U g * secondChildColumn p hp hcop hg Ψ m f y H U := by
  simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg U m g]
  ring

theorem fixedChildRow_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F A : Finset ι) (Ψ : O →* ℂ) (m : O) (H : Finset ι → ℂ) (f y : O) :
    fixedChildRow p hp hcop hg (F\A) Ψ m H f y =
      fixedChildRow p hp hcop hg F Ψ (m*∏ i ∈ A,p i) H f y := by
  unfold fixedChildRow
  rw [sum_remove_common_pool p hg hinj F A]
  apply Finset.sum_congr rfl
  intro U hU
  exact (secondChildColumn_fixed_mask p hp hcop hg Ψ m _ f y H U).symm

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic
section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem childEnergy_fixed_pool (F A : Finset ι) (Ψ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V : ℝ → ℂ) (X : ℝ) (negative rowNegative : Bool) (a b : ℝ) :
    childEnergy p hp hcop hg (F\A) Ψ m T V X negative rowNegative a b =
      childEnergy p hp hcop hg F Ψ (m*∏ i ∈ A,p i) T V X negative rowNegative a b := by
  simp only [childEnergy,idealChildRow,fixedChildRow_fixed_pool p hp hcop hg hinj]

theorem childGeometricMean_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (q : JointLogSeparation.Frequency) :
    childGeometricMean p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q =
      childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ q := by
  simp only [childGeometricMean,childEnergy_fixed_pool p hp hcop hg hinj]

theorem densityChildEnergy_fixed_pool (F A : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m : O)
    (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (J : ℕ) :
    densityChildEnergy p hp hcop hg (F\A) Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ J =
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ (m*∏ i ∈ A,p i) T V₁ V₂ X₁ X₂ J := by
  simp only [densityChildEnergy,childGeometricMean_fixed_pool p hp hcop hg hinj]

end

open ConcreteTraceCRT (eisEmbedding)
open FirstPassCubeLabels (primeProductNorm)

theorem restored_child_mask_norm {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (m b0 : O) (R A : Finset ι) :
    ‖eisEmbedding ((m*b0*primeSubsetGenerator (fun i => Ideal.span {p i}) R)*∏ i ∈ A,p i)‖^2 =
      ‖eisEmbedding m‖^2*‖eisEmbedding b0‖^2*primeProductNorm p R*primeProductNorm p A := by
  simp only [map_mul,norm_mul,mul_pow,SecondPassArithmetic.primeSubsetGenerator_norm_eq_productNorm,
    primeProductNorm]

end SecondPassIntegration

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct primeProductNorm squarefreeLabel jLabel j2Label b0Label
  bit parity conductorExponent cubeActiveSupport)
open ConcreteTraceCRT (eisEmbedding)

lemma element_norm_le_of_dvd {a b : O} (hb : b ≠ 0) (h : a ∣ b) :
    ‖eisEmbedding a‖^2 ≤ ‖eisEmbedding b‖^2 := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [map_mul, norm_mul, mul_pow]
  exact le_mul_of_one_le_right (sq_nonneg _) (element_norm_ge_one c hc)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma squarefreeLabel_active_bound (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖eisEmbedding (squarefreeLabel p B v)‖^2 ≤ primeProductNorm p (cubeActiveSupport B v ε₁ ε₂) := by
  let S := B.filter (fun i => parity (v i))
  have he : squarefreeLabel p B v = ∏ i ∈ S, p i := by
    unfold squarefreeLabel primeProduct S
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : parity (v i) <;> simp [bit,hb]
  have hsub : S ⊆ cubeActiveSupport B v ε₁ ε₂ := by
    intro i hi
    obtain ⟨hi,hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi,?_⟩
    change parity (v i) = true at hpi
    rw [hpi]
    cases h1 : ε₁ i <;> cases h2 : ε₂ i <;> decide
  rw [he]
  exact primeProductNorm_mono p hp hsub

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma jLabel_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [← primeProduct_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  dsimp only
  unfold bit
  split <;> have h := hv i hi <;> omega

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_square_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ^ 2 ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma b0_jLabel_square (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)^2 =
      primeProduct p B v₁ * primeProduct p B v₂ * squarefreeLabel p B (fun i => v₁ i+v₂ i) := by
  rw [FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2,
    FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  ring

include hp in

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem cube_label_norm_bounds (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hb₁ : ‖eisEmbedding (primeProduct p B v₁)‖^2 ≤ B₀)
    (hb₂ : ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀) :
    let v := fun i => v₁ i+v₂ i
    ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 ≤ B₀^2 ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤ B₀ ∧
    ‖eisEmbedding (b0Label p B v ε₁ ε₂)‖^2 ≤
      B₀*‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂,p i)‖ /
        ‖eisEmbedding (jLabel p B v ε₁ ε₂)‖^2 := by
  dsimp only
  have hbb : ‖eisEmbedding (primeProduct p B v₁ * primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    rw [map_mul,norm_mul,mul_pow]
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hbb0 := mul_ne_zero (primeProduct_ne_zero p hp B v₁) (primeProduct_ne_zero p hp B v₂)
  have hJ := (element_norm_le_of_dvd hbb0 (jLabel_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  have hb0sq := (element_norm_le_of_dvd hbb0 (b0_square_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  simp only [map_pow,norm_pow] at hb0sq
  have hb0 : ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤ B₀ := by
    nlinarith [sq_nonneg ‖eisEmbedding (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖]
  refine ⟨hJ,hb0,?_⟩
  have heq := congrArg (fun a : O => ‖eisEmbedding a‖^2) (b0_jLabel_square p B v₁ v₂ ε₁ ε₂ hv)
  simp only [map_pow,map_mul,norm_pow,norm_mul,mul_pow] at heq
  have hs := squarefreeLabel_active_bound p hp B (fun i => v₁ i+v₂ i) ε₁ ε₂
  have hNprod : ‖eisEmbedding (primeProduct p B v₁)‖^2 * ‖eisEmbedding (primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    simpa only [map_mul,norm_mul,mul_pow] using hbb
  have hmul := mul_le_mul hNprod hs (sq_nonneg _) (sq_nonneg B₀)
  change _ ≤ B₀^2*‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2 at hmul
  have hjpos : 0 < ‖eisEmbedding (jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 := by
    exact zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp B _))
  apply (le_div_iff₀ hjpos).mpr
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg _))).mp
  simp only [mul_pow]
  exact heq.trans_le hmul

end SecondPassArithmetic

end

end OAI
