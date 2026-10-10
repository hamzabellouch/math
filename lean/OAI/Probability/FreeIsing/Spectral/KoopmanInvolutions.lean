import Mathlib

namespace OAI

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Problem367

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

def koopmanL2 (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).toContinuousLinearMap

@[simp] theorem koopmanL2_norm (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (f : Lp ℝ 2 μ) : ‖koopmanL2 τ hτ f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving f hτ

theorem koopmanL2_involutive (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : Function.Involutive (koopmanL2 τ hτ) := by
  intro f
  change Lp.compMeasurePreserving τ hτ (Lp.compMeasurePreserving τ hτ f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f hτ hτ]
  have hid : τ ∘ τ = id := funext hinv
  simp [hid]

theorem koopmanL2_selfAdjoint (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) : IsSelfAdjoint (koopmanL2 τ hτ) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  have hi := (Lp.compMeasurePreservingₗᵢ ℝ τ hτ).inner_map_map f (koopmanL2 τ hτ g)
  change inner ℝ (koopmanL2 τ hτ f)
    (koopmanL2 τ hτ (koopmanL2 τ hτ g)) = inner ℝ f (koopmanL2 τ hτ g) at hi
  simpa only [ContinuousLinearMap.coe_coe, koopmanL2_involutive τ hτ hinv g] using hi

def koopmanAverage {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Fintype.card ι : ℝ)⁻¹ • ∑ i, koopmanL2 (τ i) (hτ i)

theorem koopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (koopmanAverage τ hτ) := by
  unfold koopmanAverage
  refine (IsSelfAdjoint.all _).smul ?_
  exact isSelfAdjoint_sum (R := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) Finset.univ fun index _ =>
    koopmanL2_selfAdjoint (τ index) (hτ index) (hinv index)

theorem koopmanAverage_norm_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ) :
    ‖koopmanAverage τ hτ‖ ≤ 1 := by
  refine (koopmanAverage τ hτ).opNorm_le_bound (by norm_num) ?_
  intro f
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  calc
    ‖koopmanAverage τ hτ f‖
        = (Fintype.card ι : ℝ)⁻¹ * ‖∑ i, koopmanL2 (τ i) (hτ i) f‖ := by
          simp [koopmanAverage, norm_smul]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, ‖koopmanL2 (τ i) (hτ i) f‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hn.le)
    _ = 1 * ‖f‖ := by simp [ne_of_gt hn]

section Centered

variable [IsFiniteMeasure μ]

@[simp] theorem koopmanL2_const (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (c : ℝ) : koopmanL2 τ hτ (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Subtype.ext
  change (AEEqFun.const Ω c).compMeasurePreserving τ hτ = AEEqFun.const Ω c
  simp [AEEqFun.const, AEEqFun.compMeasurePreserving_mk, Function.comp_def]

theorem inner_const_one_eq_integral (f : Lp ℝ 2 μ) :
    inner ℝ (Lp.const 2 μ (1 : ℝ)) f = ∫ ω, f ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with ω hω
  change (AEEqFun.const Ω (1 : ℝ) : Ω →ₘ[μ] ℝ) ω = 1 at hω
  simp [hω]

def centeredL2 (μ : Measure Ω) [IsFiniteMeasure μ] : Submodule ℝ (Lp ℝ 2 μ) :=
  (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).ker

@[simp] theorem mem_centeredL2_iff (f : Lp ℝ 2 μ) :
    f ∈ centeredL2 μ ↔ (∫ ω, f ω ∂μ) = 0 := by
  change inner ℝ (Lp.const 2 μ (1 : ℝ)) f = 0 ↔ _
  rw [inner_const_one_eq_integral]

instance centeredL2Complete : CompleteSpace (centeredL2 μ) :=
  (innerSL ℝ (Lp.const 2 μ (1 : ℝ))).isComplete_ker.completeSpace_coe

theorem koopmanL2_integral (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) (f : Lp ℝ 2 μ) :
    (∫ ω, koopmanL2 τ hτ f ω ∂μ) = ∫ ω, f ω ∂μ := by
  rw [← inner_const_one_eq_integral, ← inner_const_one_eq_integral]
  have hsym := (koopmanL2_selfAdjoint τ hτ hinv).isSymmetric
  have hs := hsym (Lp.const 2 μ (1 : ℝ)) f
  simp only [ContinuousLinearMap.coe_coe, koopmanL2_const] at hs
  exact hs.symm

theorem koopmanL2_preserves_centered (τ : Ω → Ω) (hτ : MeasurePreserving τ μ μ)
    (hinv : Function.Involutive τ) :
    ∀ f ∈ centeredL2 μ, koopmanL2 τ hτ f ∈ centeredL2 μ := by
  intro f hf
  rw [mem_centeredL2_iff] at hf ⊢
  rw [koopmanL2_integral τ hτ hinv, hf]

theorem koopmanAverage_preserves_centered {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    ∀ f ∈ centeredL2 μ, koopmanAverage τ hτ f ∈ centeredL2 μ := by
  intro f hf
  change (Fintype.card ι : ℝ)⁻¹ • (∑ i, koopmanL2 (τ i) (hτ i)) f ∈ centeredL2 μ
  apply Submodule.smul_mem
  simp only [sum_apply]
  exact Submodule.sum_mem _ fun i _ => koopmanL2_preserves_centered (τ i) (hτ i) (hinv i) f hf

def centeredKoopmanAverage {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    centeredL2 μ →L[ℝ] centeredL2 μ :=
  (koopmanAverage τ hτ).restrict (koopmanAverage_preserves_centered τ hτ hinv)

@[simp] theorem centeredKoopmanAverage_apply_coe {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) (f : centeredL2 μ) :
    (centeredKoopmanAverage τ hτ hinv f : Lp ℝ 2 μ) = koopmanAverage τ hτ f := rfl

theorem centeredKoopmanAverage_selfAdjoint {ι : Type*} [Fintype ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    IsSelfAdjoint (centeredKoopmanAverage τ hτ hinv) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact (koopmanAverage_selfAdjoint τ hτ hinv).isSymmetric.restrict_invariant
    (koopmanAverage_preserves_centered τ hτ hinv)

theorem centeredKoopmanAverage_norm_le_one {ι : Type*} [Fintype ι] [Nonempty ι]
    (τ : ι → Ω → Ω) (hτ : ∀ i, MeasurePreserving (τ i) μ μ)
    (hinv : ∀ i, Function.Involutive (τ i)) :
    ‖centeredKoopmanAverage τ hτ hinv‖ ≤ 1 := by
  refine (centeredKoopmanAverage τ hτ hinv).opNorm_le_bound (by norm_num) ?_
  intro f
  change ‖koopmanAverage τ hτ f‖ ≤ 1 * ‖(f : Lp ℝ 2 μ)‖
  exact (koopmanAverage τ hτ).le_opNorm f |>.trans
    (mul_le_mul_of_nonneg_right (koopmanAverage_norm_le_one τ hτ) (norm_nonneg _))

end Centered

end Problem367

end

end OAI
