import OAI.NumberTheory.DirichletL.Reciprocity.RamifiedSymbol
import OAI.NumberTheory.DirichletL.CubicSieve.KernelEnergy

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

open scoped BigOperators Classical SchwartzMap FourierTransform
namespace EisensteinSchwartzPoisson

open ActualEisensteinCubic ConcreteTraceCRT

def quadraticSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => x ^ 2).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul, norm_pow]
      nlinarith [sq_nonneg (‖x‖ - 1)]⟩

@[simp] theorem quadraticSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticSquareProfileCLM W = quadraticSquareProfile W := by
  ext x
  rw [quadraticSquareProfile_apply]
  rfl

def realAxisProfileCLM : 𝓢(ℂ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℝ
    (show (fun x : ℝ => (x : ℂ)).HasTemperateGrowth by fun_prop)
    ⟨1, 1, fun x => by simp only [pow_one, one_mul, Complex.norm_real]; linarith⟩

@[simp] theorem realAxisProfileCLM_apply (f : 𝓢(ℂ, ℂ)) :
    realAxisProfileCLM f = horizontalSlice f 0 := by
  ext x
  simp only [realAxisProfileCLM, SchwartzMap.compCLM_apply, Function.comp_apply,
    horizontalSlice_apply, complexPoint_eq, Complex.ofReal_zero, mul_zero, add_zero]

def squareFrequencyScaleCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (2 / Real.sqrt 3) (by positivity)))).restrictScalars ℝ

def quadraticTransformedSquareProfileCLM : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
  (2 / Real.sqrt 3 : ℝ) •
    squareFrequencyScaleCLM.comp (realAxisProfileCLM.comp radialFourierCLM)

@[simp] theorem quadraticTransformedSquareProfileCLM_apply (W : 𝓢(ℝ, ℂ)) :
    quadraticTransformedSquareProfileCLM W = quadraticTransformedSquareProfile W := by
  simp only [quadraticTransformedSquareProfileCLM, _root_.smul_apply,
    ContinuousLinearMap.comp_apply, radialFourierCLM_apply, realAxisProfileCLM_apply,
    squareFrequencyScaleCLM, quadraticTransformedSquareProfile]
  rfl

theorem two_profile_seminorm_control
    (T₁ T₂ : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ)) (s : Finset (ℕ × ℕ)) :
    ∃ (t : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ W : 𝓢(ℝ, ℂ),
      s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₁ W) +
        s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (T₂ W) ≤
          C * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := by
  obtain ⟨t₁, C₁, hC₁, h₁⟩ := schwartzCLM_finite_seminorm_control T₁ s
  obtain ⟨t₂, C₂, hC₂, h₂⟩ := schwartzCLM_finite_seminorm_control T₂ s
  refine ⟨t₁ ∪ t₂, C₁ + C₂, add_pos hC₁ hC₂, ?_⟩
  intro W
  have ht₁ : t₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_left
  have ht₂ : t₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) ≤
      (t₁ ∪ t₂).sup (schwartzSeminormFamily ℝ ℝ ℂ) := Finset.sup_mono Finset.subset_union_right
  have hb₁ := (h₁ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₁ W) hC₁.le)
  have hb₂ := (h₂ W).trans (mul_le_mul_of_nonneg_left (Seminorm.le_def.mp ht₂ W) hC₂.le)
  nlinarith

theorem quadratic_principal_difference_large_scale (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) ≤ M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
            ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
  obtain ⟨t, C₀, hC₀, hrem⟩ := maskedPrincipalRemainder_large_scale A
  obtain ⟨s, C₁, hC₁, hctrl⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM t
  refine ⟨s, C₀ * C₁, mul_pos hC₀ hC₁, ?_⟩
  intro α _ P _ hinj S W M hM hsize
  have hbound := hctrl W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  have h₁ := hrem P S (quadraticTransformedSquareProfile W) M hM hsize
  have h₂ := hrem P S (quadraticSquareProfile W) M hM hsize
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A +
        (2 : ℝ) ^ S.card * (C₀ * t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := add_le_add h₁ h₂
    _ = (2 : ℝ) ^ S.card * C₀ *
        (t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          t.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by ring
    _ ≤ (2 : ℝ) ^ S.card * C₀ *
        (C₁ * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
          ((Ideal.absNorm (∏ i ∈ S, P i) : ℝ) / M) ^ A := by
      gcongr
    _ = _ := by ring

open ActualEisensteinCubic ConcreteTraceCRT QuadraticInitialBound

theorem paperRadialFourier_nonzero_sum_uniform (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    K * ‖∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖ ≤
      pvControl W := by
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have he : (∑' h : O, if h = 0 then 0 else paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)) =
      ∑' h : {h : O // h ≠ 0}, paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2) := by
    rw [← tsum_subtype_eq_of_support_subset (s := {h : O | h ≠ 0}) (by
      intro h hh hz
      subst h
      exact hh (by simp))]
    apply tsum_congr
    intro h
    simp only [ite_eq_right h.property]
  rw [he]
  exact (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (hs.subtype _)) hK.le).trans
    (pv_lattice_bound W K hK)

theorem maskedPrincipalRemainder_uniform {α : Type*} [DecidableEq α]
    (P : α → Ideal O) [∀ i, (P i).IsMaximal] (S : Finset α)
    (W : 𝓢(ℝ, ℂ)) (M : ℝ) (hM : 0 < M) :
    ‖maskedPrincipalRemainder P S W M‖ ≤ (2 : ℝ) ^ S.card * pvControl W := by
  let n := fun E : Finset α => (Ideal.absNorm (∏ i ∈ E, P i) : ℝ)
  have hn (E : Finset α) : 0 < n E := by
    dsimp [n]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P E)))
  let f := fun E : Finset α =>
    ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) /
      (Ideal.absNorm (∏ i ∈ E, P i) : ℂ)) *
    ∑' h : O, if h = 0 then 0 else paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)
  have hf (E : Finset α) : M * ‖f E‖ ≤ pvControl W := by
    have ht := paperRadialFourier_nonzero_sum_uniform W (M / n E) (div_pos hM (hn E))
    have he (h : O) : M / n E * ‖eisEmbedding h‖ ^ 2 = M * ‖eisEmbedding h‖ ^ 2 / n E := by ring
    simp only [he] at ht
    have hm := norm_ideal_moebius_le_one (∏ i ∈ E, P i)
    dsimp only [f]
    rw [norm_mul, norm_div, Complex.norm_natCast]
    calc
      _ = ‖(UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ)‖ *
          ((M / n E) * ‖∑' h : O, if h = 0 then 0 else
            paperRadialFourier W (M * ‖eisEmbedding h‖ ^ 2 / n E)‖) := by dsimp [n]; ring
      _ ≤ 1 * pvControl W := mul_le_mul hm ht (by positivity) zero_le_one
      _ = _ := one_mul _
  change ‖(M : ℂ) * ∑ E ∈ S.powerset, f E‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM]
  calc
    _ ≤ M * ∑ E ∈ S.powerset, ‖f E‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hM.le
    _ = ∑ E ∈ S.powerset, M * ‖f E‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ E ∈ S.powerset, pvControl W := Finset.sum_le_sum (fun E _ => hf E)
    _ = _ := by simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem quadratic_principal_difference_uniform :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s, C, hC, hb⟩ := two_profile_seminorm_control
    quadraticTransformedSquareProfileCLM quadraticSquareProfileCLM pvSeminorms
  refine ⟨s, pvConstant * C, mul_pos pvConstant_pos hC, ?_⟩
  intro α _ P _ hinj S W M hM
  have hbound := hb W
  simp only [quadraticTransformedSquareProfileCLM_apply, quadraticSquareProfileCLM_apply] at hbound
  rw [quadratic_square_poisson_main_cancel P hinj S W M hM]
  calc
    _ ≤ ‖maskedPrincipalRemainder P S (quadraticTransformedSquareProfile W) M‖ +
        ‖maskedPrincipalRemainder P S (quadraticSquareProfile W) M‖ := norm_sub_le _ _
    _ ≤ (2 : ℝ) ^ S.card * pvControl (quadraticTransformedSquareProfile W) +
        (2 : ℝ) ^ S.card * pvControl (quadraticSquareProfile W) :=
      add_le_add (maskedPrincipalRemainder_uniform P S _ M hM) (maskedPrincipalRemainder_uniform P S _ M hM)
    _ = (2 : ℝ) ^ S.card * pvConstant *
        (pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W) +
          pvSeminorms.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) := by unfold pvControl; ring
    _ ≤ (2 : ℝ) ^ S.card * pvConstant * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
      exact mul_le_mul_of_nonneg_left hbound (mul_nonneg (by positivity) pvConstant_pos.le)
    _ = _ := by ring

theorem two_regime_decay (A : ℕ) (f B₀ B₁ M N : ℝ)
    (_hf : 0 ≤ f) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hM : 0 < M) (hN : 0 < N)
    (hsmall : f ≤ B₀) (hlarge : N ≤ M → f ≤ B₁ * (N / M) ^ A) :
    f ≤ (2 : ℝ) ^ A * (B₀ + B₁) / (1 + M / N) ^ A := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < 1 + M / N) A)).mpr
  by_cases hMN : M ≤ N
  · have hratio : M / N ≤ 1 := (div_le_one hN).mpr hMN
    have hp : (1 + M / N) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    calc
      _ ≤ B₀ * (2 : ℝ) ^ A := mul_le_mul hsmall hp (by positivity) hB₀
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]
  · have hNM : N ≤ M := le_of_not_ge hMN
    have hratio : N / M ≤ 1 := (div_le_one hM).mpr hNM
    have hp : (1 + N / M) ^ A ≤ (2 : ℝ) ^ A :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have he : N / M * (1 + M / N) = 1 + N / M := by field_simp; ring
    calc
      _ ≤ (B₁ * (N / M) ^ A) * (1 + M / N) ^ A :=
        mul_le_mul_of_nonneg_right (hlarge hNM) (by positivity)
      _ = B₁ * (1 + N / M) ^ A := by rw [mul_assoc, ← mul_pow, he]
      _ ≤ B₁ * (2 : ℝ) ^ A := mul_le_mul_of_nonneg_left hp hB₁
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) A]

theorem quadratic_principal_difference_decay (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {α : Type*} [DecidableEq α] (P : α → Ideal O) [∀ i, (P i).IsMaximal]
        (_hinj : Function.Injective P) (S : Finset α) (W : 𝓢(ℝ, ℂ)) (M : ℝ), 0 < M →
        ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
          (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖ ≤
          (2 : ℝ) ^ S.card * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            (1 + M / (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)) ^ A := by
  obtain ⟨s₀, C₀, hC₀, h₀⟩ := quadratic_principal_difference_uniform
  obtain ⟨s₁, C₁, hC₁, h₁⟩ := quadratic_principal_difference_large_scale A
  refine ⟨s₀ ∪ s₁, (2 : ℝ) ^ A * (C₀ + C₁), by positivity, ?_⟩
  intro α _ P _ hinj S W M hM
  let N := (Ideal.absNorm (∏ i ∈ S, P i) : ℝ)
  let Q := (s₀ ∪ s₁).sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let d := (2 : ℝ) ^ S.card
  let deltaLoss := ‖(∑' z : O, rowCoprimeMask P S z * paperRadialFourier W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2)) -
    (∑' z : O, rowCoprimeMask P S z * W ((‖eisEmbedding z‖ ^ 2 / M) ^ 2))‖
  have hN : 0 < N := by
    dsimp [N]
    rw [← primeSubsetGenerator_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (primeSubsetGenerator_ne_zero P S)))
  have hQ : 0 ≤ Q := apply_nonneg _ _
  have hd : 0 ≤ d := by positivity
  have hq₀ : s₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_left) W
  have hq₁ : s₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) W ≤ Q :=
    Seminorm.le_def.mp (Finset.sup_mono Finset.subset_union_right) W
  have hb₀ : deltaLoss ≤ d * (C₀ * Q) := by
    apply (h₀ P hinj S W M hM).trans
    dsimp only [d]
    gcongr
  have hb₁ : N ≤ M → deltaLoss ≤ d * (C₁ * Q) * (N / M) ^ A := by
    intro hsize
    apply (h₁ P hinj S W M hM hsize).trans
    dsimp only [d, N]
    gcongr
  have h := two_regime_decay A deltaLoss (d * (C₀ * Q)) (d * (C₁ * Q)) M N
    (norm_nonneg _) (by positivity) (by positivity) hM hN hb₀ hb₁
  calc
    _ = deltaLoss := rfl
    _ ≤ (2 : ℝ) ^ A * (d * (C₀ * Q) + d * (C₁ * Q)) / (1 + M / N) ^ A := h
    _ = _ := by dsimp [d, N, Q]; ring

end EisensteinSchwartzPoisson

open scoped BigOperators Classical
namespace FirstPassCubeLabels
open ActualEisensteinCubic MixedCrossSeparation FirstCauchyArithmetic RayFourExpansion

theorem supportRay_star {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by
  simp only [supportRay, rayCharacter, MulChar.star_apply]

theorem supportRay_mul {ι : Type*} (p : ι → ActualEisensteinCubic.O) (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by
  simp only [supportRay, rayCharacter, MulChar.mul_apply]

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    columnG p hp hcop hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  have h := canonicalProductG_character_expansion (fun i : S => p i.val)
    (fun i => hp i.val) (columnPrimeCoprime p hcop S) (fun i => hg i.val)
    (fun i => hc i.val) (fun i => hpr i.val)
  simpa only [columnG, supportRay, Finset.prod_coe_sort] using h

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ

theorem core_phase_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F S : Finset ι) (negative : Bool) :
    (if negative then star (fixedRayExpansion p F S) else fixedRayExpansion p F S) *
        columnG p hp hcop hg S =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        coreRayCoefficient p F negative χ η ξ * supportRay p (coreRayCharacter negative χ ξ) S := by
  rw [columnG_ray_expansion p hp hcop hg hc hpr S]
  cases negative <;> simp only [Bool.false_eq_true,  ite_false, ite_true,
    fixedRayExpansion, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    coreRayCoefficient, coreRayCharacter, supportRay_mul, supportRay_star]
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring

theorem coreRayCoefficient_norm_le {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

theorem coreRayCoefficient_mass {ι : Type*} (p : ι → ActualEisensteinCubic.O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ 32 * 512 := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
        (∑ ξ : RayCharacter, ‖gCoeff ξ‖) := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ 512 * 32 := mul_le_mul crossCoeff_sum_norm_le gCoeff_sum_norm_le (by positivity) (by norm_num)
    _ = 32 * 512 := by ring

def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : ActualEisensteinCubic.O →* ℂ where
  toFun a := rayCharacter (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayCharacter]
  map_mul' a b := rayCharacter_mul _ a b

@[simp] theorem coreRayTwist_prod {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (negative : Bool) (χ ξ : RayCharacter) :
    coreRayTwist negative χ ξ (∏ i ∈ S, p i) =
      supportRay p (coreRayCharacter negative χ ξ) S := rfl

@[simp] theorem twisted_core_product {ι : Type*} (p : ι → ActualEisensteinCubic.O)
    (S : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (negative : Bool) (χ ξ : RayCharacter) :
    (Ψ * coreRayTwist negative χ ξ) (∏ i ∈ S, p i) =
      Ψ (∏ i ∈ S, p i) * supportRay p (coreRayCharacter negative χ ξ) S := rfl

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

theorem actual_first_kernel_uniform_energy_envelope {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open FirstCauchyArithmetic (supportConjugateSum)
open RayFourExpansion (RayCharacter crossCoeff)

section FixedColumn
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
  (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
  (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)

def dilatedCoreRow (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z

private theorem cubeCoreCoefficient_continuous (S : Finset ι) :
    Continuous (fun t : ℝ => cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S) := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true]
  all_goals
    have h := FourierBridge.logPhase_continuous_left (-(y S))
    fun_prop

private theorem norm_cubeCoreCoefficient (S : Finset ι) (t : ℝ) :
    ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t S‖ =
      ‖cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y 0 S‖ := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, FourierBridge.logPhase_norm]

theorem dilatedCoreRow_continuous (z : O) :
    Continuous (fun t : ℝ => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  apply continuous_finsetSum
  intro U hU
  have h := cubeCoreCoefficient_continuous p hp hcop hg B v ε₁ ε₂ negative C V y (D ∪ U)
  fun_prop

theorem dilatedCoreRow_uniform_bound (z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t,
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) =>
    FirstCauchyArithmetic.supportMobius (fun i => Ideal.span {p i}) U *
      ((if negative then star (FirstCauchyArithmetic.supportRay p χ U)
        else FirstCauchyArithmetic.supportRay p χ U) *
        cubeCoreCoefficient p hp hcop hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
        afterDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ c d U) *
      star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg U z)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U hU
  simp only [q, norm_mul, norm_cubeCoreCoefficient]

theorem dilatedCoreRow_integrable (z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t : ℝ => k t *
      ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := dilatedCoreRow_uniform_bound p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((dilatedCoreRow_continuous p hp hcop hg F D B v ε₁ ε₂ negative χ C V y c d z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)
end FixedColumn

def firstRayIntegrand {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) (t : ℝ) : ℝ :=
  ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖rayIdealRow p hg F
      (cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d)
      negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem firstRayIntegrand_integrable {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d f h b) volume := by
  have hi := dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)
    b.integrable.norm
  convert hi.mul_const (‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ * ‖rayPairWeight p r D h‖ *
    ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D‖ ^ 2) using 1
  funext t
  simp only [firstRayIntegrand, rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv,
    norm_mul, mul_pow, dilatedCoreRow]
  ring

theorem first_ray_energy_integral (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (negative : Bool) (r : RayCharacter × RayCharacter) (C : Finset ι → ℂ)
      (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ)
      (b : Ideal O × O → 𝓢(ℝ, ℂ)) (J : ℕ) (M H Y : ℝ),
      0 ≤ M → 0 ≤ H → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t) →
      (∑ x ∈ s, ‖w x‖ * ∫ t : ℝ,
        firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
          (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t) ≤
      (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) *
        ∫ t : ℝ, firstLogDensity J t * ∑ z ∈ T,
          ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpoint⟩ := first_cube_energy_small_power deltaLoss hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc F D B v ε₁ ε₂ hv negative r C V y c d s T w b J M H Y hM hH hY hs hmap hT hnorm hw hdom
  let Ψ := fun t z => dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
    (if negative then r.1 else r.2) C V y c d t z
  let source := fun t : ℝ => ∑ x ∈ s, ‖w x‖ *
    firstRayIntegrand p hp hcop hg F D B v ε₁ ε₂ negative r C V y c d
      (ConcretePrimeRowBridge.idealGenerator x.1) x.2 (b x) t
  let target := fun t : ℝ => firstLogDensity J t * ∑ z ∈ T, ‖Ψ t z‖ ^ 2
  have isource : Integrable source volume := by
    apply integrable_finsetSum
    intro x hx
    exact (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖
  have itarget : Integrable target volume := by
    simp only [target, Finset.mul_sum]
    exact integrable_finsetSum _ (fun z hz =>
      dilatedCoreRow_integrable p hp hcop hg F D B v ε₁ ε₂ negative
        (if negative then r.1 else r.2) C V y c d z (firstLogDensity_integrable J))
  have hst (t : ℝ) : source t ≤ (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t := by
    let wt := fun x : Ideal O × O => w x * (b x t) *
      cubeBaseFactor p hp hg B v ε₁ ε₂ d x.2 * rayPairWeight p r D x.2
    have hwt (x) (hx : x ∈ s) : ‖wt x‖ ≤ M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖ := by
      simp only [wt, norm_mul]
      calc
        _ ≤ M * (H * firstLogDensity J t) * 1 * ‖crossCoeff r.1 r.2‖ := by
          have hden := firstLogDensity_nonneg J t
          gcongr <;> first
            | positivity
            | exact hw x hx
            | exact hdom x hx t
            | exact cubeBaseFactor_norm_le_one p hp hcop hg hc B v ε₁ ε₂ d x.2
            | exact rayPairWeight_norm_le p hinj hc r D x.2
        _ = _ := by ring
    have hh := hpoint p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
      (if negative then r.1 else r.2) C V y t c d s T wt
      (M * H * firstLogDensity J t * ‖crossCoeff r.1 r.2‖) Y
      (by exact mul_nonneg (mul_nonneg (mul_nonneg hM hH) (firstLogDensity_nonneg J t)) (norm_nonneg _))
      hY hs hmap hT hnorm hwt
    convert hh using 1
    · apply Finset.sum_congr rfl
      intro x hx
      simp only [firstRayIntegrand, wt, norm_mul]
      ring
    · dsimp only [target, Ψ, dilatedCoreRow]
      ring
  calc
    _ = ∫ t : ℝ, source t := by
      rw [integral_finsetSum _ (fun x hx =>
        (firstRayIntegrand_integrable p hp hinj hcop hg F D B v ε₁ ε₂ hv negative r C V y c d _ _ (b x)).const_mul ‖w x‖)]
      exact Finset.sum_congr rfl (fun x hx => (integral_const_mul _ _).symm)
    _ ≤ ∫ t : ℝ, (M * H * K * Y ^ deltaLoss * ‖crossCoeff r.1 r.2‖) * target t :=
      integral_mono isource (itarget.const_mul _) hst
    _ = _ := integral_const_mul _ _

end FirstPassCubeLabels

end

end OAI
