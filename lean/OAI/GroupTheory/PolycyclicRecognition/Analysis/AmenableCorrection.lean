import OAI.GroupTheory.Thompson.InvariantMean
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Correcting bounded height defects with an invariant mean

This is the averaging step in Proposition `recognition-from-height` of the
manuscript *Quasi-isometric recognition of virtually polycyclic groups*.
The mean is on the actual space of all bounded real functions. Neither the
height function itself nor its corrected homomorphism has to be bounded.
-/

noncomputable section

namespace PolycyclicRecognition

open ThompsonNonamenability
open scoped ENNReal

universe u v

variable {G : Type u} [Group G]

/-- The increment of a function of uniformly bounded additive defect is bounded. -/
def boundedIncrement (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) : BoundedReal G :=
  ⟨fun x => s (h * x) - s x, memℓp_infty ⟨D + |s h|, by
    rintro y ⟨x, rfl⟩
    change |s (h * x) - s x| ≤ D + |s h|
    calc
      |s (h * x) - s x| = |(s (h * x) - s h - s x) + s h| := by ring_nf
      _ ≤ |s (h * x) - s h - s x| + |s h| := abs_add_le _ _
      _ ≤ D + |s h| := add_le_add (hD h x) le_rfl⟩⟩

@[simp]
theorem boundedIncrement_apply (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h x : G) :
    boundedIncrement s D hD h x = s (h * x) - s x := rfl

/-- The cocycle identity holds for increments before applying the mean. -/
theorem boundedIncrement_mul (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h k : G) :
    boundedIncrement s D hD (h * k) =
      leftPull k (boundedIncrement s D hD h) + boundedIncrement s D hD k := by
  apply lp.ext
  funext x
  change s ((h * k) * x) - s x = (s (h * (k * x)) - s (k * x)) +
    (s (k * x) - s x)
  rw [mul_assoc]
  ring

/-- Averaging the bounded increments gives an additive homomorphism. -/
def meanCorrection (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) : ℝ :=
  M (boundedIncrement s D hD h)

theorem meanCorrection_mul (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h k : G) :
    meanCorrection M s D hD (h * k) =
      meanCorrection M s D hD h + meanCorrection M s D hD k := by
  unfold meanCorrection
  rw [boundedIncrement_mul, M.map_add]
  exact congrArg (fun t => t + M (boundedIncrement s D hD k))
    (M.left_invariant k (boundedIncrement s D hD h))

@[simp]
theorem meanCorrection_one (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) :
    meanCorrection M s D hD 1 = 0 := by
  have h := meanCorrection_mul M s D hD (1 : G) 1
  simp only [one_mul] at h
  linarith

/-- Positivity of the mean preserves the uniform defect bound exactly. -/
theorem meanCorrection_dist_le (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) (h : G) :
    |meanCorrection M s D hD h - s h| ≤ D := by
  have hlo := M.mono
    (f := (s h - D) • (1 : BoundedReal G))
    (g := boundedIncrement s D hD h) (fun x => by
      simp only [BoundedReal.smul_one_apply, boundedIncrement_apply]
      have hx := (abs_le.mp (hD h x)).1
      linarith)
  have hhi := M.mono
    (f := boundedIncrement s D hD h)
    (g := (s h + D) • (1 : BoundedReal G)) (fun x => by
      simp only [BoundedReal.smul_one_apply, boundedIncrement_apply]
      have hx := (abs_le.mp (hD h x)).2
      linarith)
  rw [M.map_const] at hlo hhi
  exact abs_le.mpr ⟨by unfold meanCorrection; linarith,
    by unfold meanCorrection; linarith⟩

/-- Scalar bounded-defect correction; the original function need not be bounded. -/
theorem exists_meanCorrection (M : InvariantMean G) (s : G → ℝ) (D : ℝ)
    (hD : ∀ h k, |s (h * k) - s h - s k| ≤ D) :
    ∃ τ : G → ℝ, τ 1 = 0 ∧ (∀ h k, τ (h * k) = τ h + τ k) ∧
      ∀ h, |τ h - s h| ≤ D :=
  ⟨meanCorrection M s D hD, meanCorrection_one M s D hD,
    meanCorrection_mul M s D hD, meanCorrection_dist_le M s D hD⟩

/-- Coordinate defects are bounded by the defect in the supremum norm. -/
theorem coordinate_defect_le {ι : Type v} [Fintype ι] (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (i : ι) (h k : G) :
    |s (h * k) i - s h i - s k i| ≤ D := by
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using
    (norm_le_pi_norm (s (h * k) - s h - s k) i).trans (hD h k)

/-- The finite-dimensional correction obtained by applying the mean to each coordinate. -/
def vectorMeanCorrection {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h : G) (i : ι) : ℝ :=
  meanCorrection M (fun k => s k i) D (coordinate_defect_le s D hD i) h

@[simp]
theorem vectorMeanCorrection_one {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    vectorMeanCorrection M s D hD 1 = 0 := by
  funext i
  exact meanCorrection_one M (fun k => s k i) D (coordinate_defect_le s D hD i)

theorem vectorMeanCorrection_mul {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h k : G) :
    vectorMeanCorrection M s D hD (h * k) =
      vectorMeanCorrection M s D hD h + vectorMeanCorrection M s D hD k := by
  funext i
  exact meanCorrection_mul M (fun k => s k i) D (coordinate_defect_le s D hD i) h k

/-- The correction remains within the original defect bound in the supremum norm. -/
theorem vectorMeanCorrection_dist_le {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) (h : G) :
    ‖vectorMeanCorrection M s D hD h - s h‖ ≤ D := by
  have hnonneg : 0 ≤ D := (norm_nonneg _).trans (hD 1 1)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  simpa only [Pi.sub_apply, Real.norm_eq_abs, vectorMeanCorrection] using
    meanCorrection_dist_le M (fun k => s k i) D (coordinate_defect_le s D hD i) h

/-- Finite-dimensional bounded-defect correction, packaged as a genuine homomorphism. -/
def correctedHom {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    G →* Multiplicative (ι → ℝ) where
  toFun h := Multiplicative.ofAdd (vectorMeanCorrection M s D hD h)
  map_one' := vectorMeanCorrection_one M s D hD
  map_mul' := vectorMeanCorrection_mul M s D hD

/-- A height map of uniformly bounded additive defect on an amenable group is uniformly
close to a homomorphism to a finite-dimensional real vector space. -/
theorem exists_correctedHom {ι : Type v} [Fintype ι]
    (M : InvariantMean G) (s : G → ι → ℝ) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ τ : G →* Multiplicative (ι → ℝ), ∀ h, ‖(τ h).toAdd - s h‖ ≤ D :=
  ⟨correctedHom M s D hD, vectorMeanCorrection_dist_le M s D hD⟩

/-- Transfer the finite-coordinate correction through a continuous linear equivalence.
The resulting bound records the change of norm explicitly. -/
theorem exists_correctedHom_of_equiv {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {ι : Type v} [Fintype ι]
    (e : W ≃L[ℝ] (ι → ℝ)) (M : InvariantMean G) (s : G → W) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ τ : G →* Multiplicative W,
      ∀ h, ‖(τ h).toAdd - s h‖ ≤
        ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D) := by
  have heD : ∀ h k, ‖e (s (h * k)) - e (s h) - e (s k)‖ ≤
      ‖e.toContinuousLinearMap‖ * D := by
    intro h k
    calc
      ‖e (s (h * k)) - e (s h) - e (s k)‖ =
          ‖e (s (h * k) - s h - s k)‖ := by rw [map_sub, map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖ * ‖s (h * k) - s h - s k‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ * D :=
        mul_le_mul_of_nonneg_left (hD h k) (norm_nonneg _)
  obtain ⟨τ', hτ'⟩ := exists_correctedHom M (fun h => e (s h))
    (‖e.toContinuousLinearMap‖ * D) heD
  let τ : G →* Multiplicative W :=
    { toFun := fun h => Multiplicative.ofAdd (e.symm (τ' h).toAdd)
      map_one' := by simp
      map_mul' := fun h k => by
        change e.symm (τ' (h * k)).toAdd = e.symm (τ' h).toAdd + e.symm (τ' k).toAdd
        rw [map_mul]
        exact map_add e.symm _ _ }
  refine ⟨τ, fun h => ?_⟩
  change ‖e.symm (τ' h).toAdd - s h‖ ≤ _
  calc
    ‖e.symm (τ' h).toAdd - s h‖ = ‖e.symm ((τ' h).toAdd - e (s h))‖ := by
      rw [map_sub, e.symm_apply_apply]
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖(τ' h).toAdd - e (s h)‖ :=
      e.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D) :=
      mul_le_mul_of_nonneg_left (hτ' h) (norm_nonneg _)

/-- On any finite-dimensional real normed space, a height map of uniformly
bounded additive defect is uniformly close to a homomorphism. -/
theorem exists_finiteDimensional_correctedHom {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (M : InvariantMean G) (s : G → W) (D : ℝ)
    (hD : ∀ h k, ‖s (h * k) - s h - s k‖ ≤ D) :
    ∃ (τ : G →* Multiplicative W) (B : ℝ), 0 ≤ B ∧
      ∀ h, ‖(τ h).toAdd - s h‖ ≤ B := by
  let e := (Module.finBasis ℝ W).equivFunL
  obtain ⟨τ, hτ⟩ := exists_correctedHom_of_equiv e M s D hD
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 1 1)
  exact ⟨τ, ‖e.symm.toContinuousLinearMap‖ * (‖e.toContinuousLinearMap‖ * D),
    mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) hD0), hτ⟩

end PolycyclicRecognition

end

end OAI
