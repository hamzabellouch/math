import OAI.Analysis.KadisonKastler.InvariantOperatorMean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! # Finite Cesaro averages in an abelian group

Iterating the one-generator averages over a finite list gives positive
contractions. A translation by any generator in the list changes the
average by at most twice the reciprocal averaging length.
-/

namespace KadisonKastler

open scoped BigOperators BoundedContinuousFunction

noncomputable section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]

def scalarTranslation (g : G) : (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ) :=
  LinearMap.mkContinuous
    { toFun := scalarMeanTranslate g
      map_add' f h := by ext t; rfl
      map_smul' c f := by ext t; rfl }
    1 (fun f => by
      rw [one_mul]
      exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
        (fun t => f.norm_coe_le_norm _))

@[simp] theorem scalarTranslation_apply (g : G) (f : G →ᵇ ℂ) (t : G) :
    scalarTranslation g f t = f (g⁻¹ * t) := rfl

theorem scalarTranslation_norm_le (g : G) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g f‖ ≤ ‖f‖ :=
  (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    (fun t => f.norm_coe_le_norm (g⁻¹ * t))

@[simp] theorem scalarTranslation_one (f : G →ᵇ ℂ) : scalarTranslation (1 : G) f = f := by
  ext t
  simp only [scalarTranslation_apply, inv_one, one_mul]

theorem scalarTranslation_mul (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (scalarTranslation h f) = scalarTranslation (g * h) f := by
  ext t
  simp only [scalarTranslation_apply, mul_inv_rev, mul_assoc]

theorem scalarTranslation_comm (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (scalarTranslation h f) = scalarTranslation h (scalarTranslation g f) := by
  rw [scalarTranslation_mul, scalarTranslation_mul, mul_comm g h]

@[simp] theorem scalarTranslation_const (g : G) (c : ℂ) :
    scalarTranslation g (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by ext t; rfl

def cesaroTranslation (n : ℕ) (g : G) : (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ) :=
  (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
    ∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i)

theorem cesaroTranslation_apply (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    cesaroTranslation n g f = (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) •
      ∑ i ∈ Finset.range (n + 1), scalarTranslation (g ^ i) f := by
  simp only [cesaroTranslation, smul_apply, sum_apply]

theorem cesaroTranslation_norm_le (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    ‖cesaroTranslation n g f‖ ≤ ‖f‖ := by
  have hp : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [cesaroTranslation_apply, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hp.le]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i ∈ Finset.range (n + 1), ‖scalarTranslation (g ^ i) f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hp.le)
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ _i ∈ Finset.range (n + 1), ‖f‖ := by
      gcongr with i hi
      exact scalarTranslation_norm_le _ _
    _ = ‖f‖ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

@[simp] theorem cesaroTranslation_const (n : ℕ) (g : G) (c : ℂ) :
    cesaroTranslation n g (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by
  rw [cesaroTranslation_apply]
  simp only [scalarTranslation_const, Finset.sum_const, Finset.card_range]
  have hp : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  change (((n + 1 : ℕ) : ℂ)⁻¹ * ((n + 1 : ℕ) : ℂ)) • _ = _
  rw [inv_mul_cancel₀ hp, one_smul]

theorem scalarTranslation_cesaro (n : ℕ) (g h : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (cesaroTranslation n h f) =
      cesaroTranslation n h (scalarTranslation g f) := by
  simp only [cesaroTranslation_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact scalarTranslation_comm _ _ _

theorem cesaroTranslation_difference (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (cesaroTranslation n g f) - cesaroTranslation n g f =
      (((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • (scalarTranslation (g ^ (n + 1)) f - f) := by
  simp only [cesaroTranslation_apply, map_smul, map_sum, ← smul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  have hsum : (∑ i ∈ Finset.range (n + 1),
      (scalarTranslation g (scalarTranslation (g ^ i) f) - scalarTranslation (g ^ i) f)) =
      ∑ i ∈ Finset.range (n + 1),
        (scalarTranslation (g ^ (i + 1)) f - scalarTranslation (g ^ i) f) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [scalarTranslation_mul, ← pow_succ']
  rw [hsum]
  simpa only [pow_zero, scalarTranslation_one] using
    (Finset.sum_range_sub (fun i : ℕ => scalarTranslation (g ^ i) f) (n + 1))

omit [CommGroup G] [TopologicalSpace G] [DiscreteTopology G] in
theorem norm_inv_nat_smul_sub_le {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℂ E] (n : ℕ) (x y : E) (hxy : ‖x‖ ≤ ‖y‖) :
    ‖(((n + 1 : ℕ) : ℝ)⁻¹ : ℂ) • (x - y)‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖y‖ := by
  have hp : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
  rw [norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (n + 1))]
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (‖x‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (‖y‖ + ‖y‖) :=
      mul_le_mul_of_nonneg_left (add_le_add hxy le_rfl) hp
    _ = _ := by ring

theorem cesaroTranslation_difference_norm_le (n : ℕ) (g : G) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g (cesaroTranslation n g f) - cesaroTranslation n g f‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  rw [cesaroTranslation_difference]
  exact norm_inv_nat_smul_sub_le n (scalarTranslation (g ^ (n + 1)) f) f
    (scalarTranslation_norm_le (g ^ (n + 1)) f)

def abelianBoxAverage (n : ℕ) : List G → (G →ᵇ ℂ) →L[ℂ] (G →ᵇ ℂ)
  | [] => 1
  | g :: s => (cesaroTranslation n g).comp (abelianBoxAverage n s)

@[simp] theorem abelianBoxAverage_nil (n : ℕ) (f : G →ᵇ ℂ) :
    abelianBoxAverage n [] f = f := rfl

@[simp] theorem abelianBoxAverage_cons (n : ℕ) (g : G) (s : List G) (f : G →ᵇ ℂ) :
    abelianBoxAverage n (g :: s) f = cesaroTranslation n g (abelianBoxAverage n s f) := rfl

theorem abelianBoxAverage_norm_le (n : ℕ) (s : List G) (f : G →ᵇ ℂ) :
    ‖abelianBoxAverage n s f‖ ≤ ‖f‖ := by
  induction s with
  | nil => exact le_rfl
  | cons g s ih => exact (cesaroTranslation_norm_le n g _).trans ih

@[simp] theorem abelianBoxAverage_const (n : ℕ) (s : List G) (c : ℂ) :
    abelianBoxAverage n s (BoundedContinuousFunction.const G c) =
      BoundedContinuousFunction.const G c := by
  induction s with
  | nil => rfl
  | cons g s ih => rw [abelianBoxAverage_cons, ih, cesaroTranslation_const]

theorem scalarTranslation_box (n : ℕ) (s : List G) (g : G) (f : G →ᵇ ℂ) :
    scalarTranslation g (abelianBoxAverage n s f) =
      abelianBoxAverage n s (scalarTranslation g f) := by
  induction s with
  | nil => rfl
  | cons h s ih => rw [abelianBoxAverage_cons, scalarTranslation_cesaro, ih,
      abelianBoxAverage_cons]

theorem abelianBoxAverage_difference_norm_le (n : ℕ) (s : List G) (g : G)
    (hg : g ∈ s) (f : G →ᵇ ℂ) :
    ‖scalarTranslation g (abelianBoxAverage n s f) - abelianBoxAverage n s f‖ ≤
      2 * (((n + 1 : ℕ) : ℝ)⁻¹) * ‖f‖ := by
  induction s with
  | nil => simp only [List.not_mem_nil] at hg
  | cons h s ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (cesaroTranslation_difference_norm_le n g _).trans
        (mul_le_mul_of_nonneg_left (abelianBoxAverage_norm_le n s f) (by positivity))
    · rw [abelianBoxAverage_cons, scalarTranslation_cesaro, ← map_sub]
      exact (cesaroTranslation_norm_le n h _).trans (ih hg)

end

end KadisonKastler

end OAI
