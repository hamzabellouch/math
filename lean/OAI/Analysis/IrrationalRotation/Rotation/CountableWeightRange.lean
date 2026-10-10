import Mathlib
import OAI.Analysis.IrrationalRotation.Spectral.PolarStructure

namespace OAI

namespace InvariantProjection.CountableWeightRange

open scoped BigOperators
open Set MeasureTheory

variable {X ι J : Type*}

theorem exp_tsum_mem_finite_cost_values
    (c b : ι → ℝ) (hfinite : (Function.support b).Finite)
    (hzero_one : ∀ i, b i = 0 ∨ b i = 1) :
    Real.exp (-(∑' i, c i * b i)) ∈
      Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i))) := by
  classical
  let s := hfinite.toFinset
  have hsum : (∑' i, c i * b i) = ∑ i ∈ s, c i := by
    rw [tsum_eq_sum (s := s) (fun i hi => ?_)]
    · apply Finset.sum_congr rfl
      intro i hi
      have hb : b i ≠ 0 := by simpa [s, Function.support] using hi
      rcases hzero_one i with h | h
      · contradiction
      · simp [h]
    · have hb : b i = 0 := by simpa [s, Function.support] using hi
      simp [hb]
  exact ⟨s, by rw [hsum]⟩

theorem countable_exp_tsum_image [Countable ι]
    (c : ι → ℝ) (b : X → ι → ℝ) (S : Set X)
    (hfinite : ∀ x ∈ S, (Function.support (b x)).Finite)
    (hzero_one : ∀ x ∈ S, ∀ i, b x i = 0 ∨ b x i = 1) :
    ((fun x => Real.exp (-(∑' i, c i * b x i))) '' S).Countable := by
  apply (PolarStructure.countable_finite_drop_values c).mono
  rintro y ⟨x, hx, rfl⟩
  exact exp_tsum_mem_finite_cost_values c (b x) (hfinite x hx) (hzero_one x hx)

theorem ae_exp_tsum_mem_countable [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (c : ι → ℝ) (b : X → ι → ℝ)
    (hfinite : ∀ᵐ x ∂μ, (Function.support (b x)).Finite)
    (hzero_one : ∀ᵐ x ∂μ, ∀ i, b x i = 0 ∨ b x i = 1) :
    ∃ V : Set ℝ, V.Countable ∧
      ∀ᵐ x ∂μ, Real.exp (-(∑' i, c i * b x i)) ∈ V := by
  refine ⟨_, PolarStructure.countable_finite_drop_values c, ?_⟩
  filter_upwards [hfinite, hzero_one] with x hx hx'
  exact exp_tsum_mem_finite_cost_values c (b x) hx hx'

theorem finite_cost_values_subset_Ioc (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    Set.range (fun s : Finset ι => Real.exp (-(∑ i ∈ s, c i))) ⊆ Set.Ioc 0 1 := by
  rintro y ⟨s, rfl⟩
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Finset.sum_nonneg (fun i _ => hc i))

theorem floor_add_zero_or_one {x θ : ℝ}
    (hx : x ∈ Set.Ico 0 1) (hθ : θ ∈ Set.Ico 0 1) :
    Int.floor (x + θ) = 0 ∨ Int.floor (x + θ) = 1 := by
  have hlo : 0 ≤ Int.floor (x + θ) := Int.floor_nonneg.mpr (add_nonneg hx.1 hθ.1)
  have hhi : Int.floor (x + θ) < 2 := Int.floor_lt.mpr (by norm_num; linarith [hx.2, hθ.2])
  omega

theorem ae_floor_weight_mem_countable [Countable ι] [MeasurableSpace X]
    (μ : Measure X) (c θ : ι → ℝ) (x : X → ι → ℝ)
    (hθ : ∀ i, θ i ∈ Set.Ico 0 1)
    (hx : ∀ᵐ z ∂μ, ∀ i, x z i ∈ Set.Ico 0 1)
    (hfinite : ∀ᵐ z ∂μ, {i | Int.floor (x z i + θ i) ≠ 0}.Finite) :
    ∃ V : Set ℝ, V.Countable ∧
      ∀ᵐ z ∂μ, Real.exp (-(∑' i, c i * (Int.floor (x z i + θ i) : ℝ))) ∈ V := by
  apply ae_exp_tsum_mem_countable μ c (fun z i => (Int.floor (x z i + θ i) : ℝ))
  · filter_upwards [hfinite] with z hz
    simpa [Function.support] using hz
  · filter_upwards [hx] with z hz
    intro i
    rcases floor_add_zero_or_one (hz i) (hθ i) with h | h
    · left; simp [h]
    · right; simp [h]

end InvariantProjection.CountableWeightRange

end OAI
