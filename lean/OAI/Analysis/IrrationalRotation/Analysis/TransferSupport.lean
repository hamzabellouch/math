import Mathlib

namespace OAI

open scoped BigOperators ENNReal
open MeasureTheory Set Filter

namespace Invariant233.TransferSupport

variable {X : Type*}

theorem support_relocation_subset (τ : X → X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) :
    Function.support (fun x => ∑ n ∈ Finset.range (H + 1),
      ∑ r ∈ Finset.Icc 1 n, h (τ^[r] x) * φ n (τ^[r] x)) ⊆
      ⋃ r ∈ Finset.Icc 1 H, (τ^[r]) ⁻¹' Function.support h := by
  classical
  intro x hx
  obtain ⟨n, hn, hnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  obtain ⟨r, hr, hrz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hnz
  have hrH : r ∈ Finset.Icc 1 H := by
    simp only [Finset.mem_Icc] at hr ⊢
    have hnH := Finset.mem_range.mp hn
    omega
  refine Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨hrH, ?_⟩⟩
  exact (mul_ne_zero_iff.mp hrz).1

variable [MeasurableSpace X] {μ : Measure X}

theorem measure_support_relocation_le (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) :
    μ (Function.support (fun x => ∑ n ∈ Finset.range (H + 1),
      ∑ r ∈ Finset.Icc 1 n, h (τ^[r] x) * φ n (τ^[r] x))) ≤
      (H : ℝ≥0∞) * μ (Function.support h) := by
  classical
  calc
    _ ≤ μ (⋃ r ∈ Finset.Icc 1 H, (τ^[r]) ⁻¹' Function.support h) :=
      measure_mono (support_relocation_subset τ h φ H)
    _ ≤ ∑ r ∈ Finset.Icc 1 H, μ ((τ^[r]) ⁻¹' Function.support h) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.Icc 1 H, μ (Function.support h) := by
      exact Finset.sum_le_sum fun r _ => (hτ.iterate r).measure_preimage_le _
    _ = (H : ℝ≥0∞) * μ (Function.support h) := by simp [nsmul_eq_mul]

theorem ae_finite_transfer_support {ι : Type*} [Countable ι] (d : ι → X → ℝ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => d i x)).Finite := by
  simpa only [Function.support, Set.mem_ofPred_eq] using
    (ae_finite_setOfPred_mem hd)

theorem ae_finite_transfer_support_comp {ι κ : Type*} [Countable ι] [Countable κ]
    (d : ι → X → ℝ) (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (ρ : κ → X → X) (hρ : ∀ k, Measure.QuasiMeasurePreserving (ρ k) μ μ) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => d i (ρ k x))).Finite := by
  exact ae_all_iff.mpr fun k => (hρ k).ae (ae_finite_transfer_support d hd)

theorem ae_finite_transfer_support_pair {ι : Type*} [Countable ι]
    (d : ι → X → ℝ) (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (σ : X → X) (hσ : Measure.QuasiMeasurePreserving σ μ μ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => d i x)).Finite ∧
      (Function.support (fun i => d i (σ x))).Finite := by
  exact (ae_finite_transfer_support d hd).and
    (hσ.ae (ae_finite_transfer_support d hd))

theorem ae_finite_relocation_support {ι : Type*} [Countable ι]
    (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (h : ι → X → ℝ) (φ : ι → ℕ → X → ℝ) (H : ι → ℕ)
    (hcost : ∑' i, (H i : ℝ≥0∞) * μ (Function.support (h i)) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => ∑ n ∈ Finset.range (H i + 1),
      ∑ r ∈ Finset.Icc 1 n, h i (τ^[r] x) * φ i n (τ^[r] x))).Finite := by
  apply ae_finite_transfer_support
  exact ne_top_of_le_ne_top hcost (ENNReal.tsum_le_tsum fun i =>
    measure_support_relocation_le τ hτ (h i) (φ i) (H i))

theorem measure_support_background_le (τ : X → X) (hτ : MeasurePreserving τ μ μ)
    (v : X → ℝ) (W : ℕ) (c : ℝ) :
    μ (Function.support (fun x => c * (∑ n ∈ Finset.range (W + 1),
      ∑ r ∈ Finset.Icc 1 n, v (τ^[r] x)))) ≤
      (W : ℝ≥0∞) * μ (Function.support v) := by
  calc
    _ ≤ μ (Function.support (fun x => ∑ n ∈ Finset.range (W + 1),
        ∑ r ∈ Finset.Icc 1 n, v (τ^[r] x))) := by
      apply measure_mono
      intro x hx
      exact (mul_ne_zero_iff.mp hx).2
    _ ≤ (W : ℝ≥0∞) * μ (Function.support v) := by
      simpa only [mul_one] using measure_support_relocation_le τ hτ v (fun _ _ => 1) W

theorem ae_tsum_coboundary {ι : Type*} [Countable ι]
    (h g d : ι → X → ℝ) (σ : X → X)
    (hσ : Measure.QuasiMeasurePreserving σ μ μ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (hh : ∀ᵐ x ∂μ, Summable (fun i => h i x))
    (heq : ∀ i, g i =ᵐ[μ] fun x => h i x + d i x - d i (σ x)) :
    ∀ᵐ x ∂μ, Summable (fun i => g i x) ∧
      (∑' i, g i x) = (∑' i, h i x) + (∑' i, d i x) - (∑' i, d i (σ x)) := by
  filter_upwards [hh, ae_finite_transfer_support_pair d hd σ hσ,
    ae_all_iff.mpr heq] with x hhx hdx heqx
  have hd0 : Summable (fun i => d i x) := summable_of_hasFiniteSupport hdx.1
  have hd1 : Summable (fun i => d i (σ x)) := summable_of_hasFiniteSupport hdx.2
  have hg : Summable (fun i => g i x) :=
    ((hhx.add hd0).sub hd1).congr (fun i => (heqx i).symm)
  refine ⟨hg, ?_⟩
  calc
    (∑' i, g i x) = ∑' i, (h i x + d i x - d i (σ x)) := tsum_congr heqx
    _ = (∑' i, h i x) + (∑' i, d i x) - (∑' i, d i (σ x)) := by
      rw [(hhx.add hd0).tsum_sub hd1, hhx.tsum_add hd0]

theorem exists_measurable_tsum_transfer {ι : Type*} [Countable ι]
    (h g d : ι → X → ℝ) (σ : X → X)
    (hσ : Measure.QuasiMeasurePreserving σ μ μ)
    (hmd : ∀ i, Measurable (d i))
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (hh : ∀ᵐ x ∂μ, Summable (fun i => h i x))
    (heq : ∀ i, g i =ᵐ[μ] fun x => h i x + d i x - d i (σ x)) :
    ∃ b : X → ℝ, Measurable b ∧
      (∀ᵐ x ∂μ, (Function.support (fun i => d i x)).Finite ∧
        b x = ∑' i, d i x) ∧
      ∀ᵐ x ∂μ, (∑' i, g i x) = (∑' i, h i x) + b x - b (σ x) := by
  refine ⟨fun x => ∑' i, d i x, Measurable.tsum hmd, ?_, ?_⟩
  · filter_upwards [ae_finite_transfer_support d hd] with x hx
    exact ⟨hx, rfl⟩
  · filter_upwards [ae_tsum_coboundary h g d σ hσ hd hh heq] with x hx
    exact hx.2

theorem tsum_measure_support_add_ne_top {ι : Type*} [Countable ι]
    (d e : ι → X → ℝ)
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (he : ∑' i, μ (Function.support (e i)) ≠ ∞) :
    ∑' i, μ (Function.support (fun x => d i x + e i x)) ≠ ∞ := by
  apply ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hd, he⟩)
  calc
    _ ≤ ∑' i, (μ (Function.support (d i)) + μ (Function.support (e i))) := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact (measure_mono (Function.support_add _ _)).trans (measure_union_le _ _)
    _ = (∑' i, μ (Function.support (d i))) + ∑' i, μ (Function.support (e i)) :=
      ENNReal.tsum_add

theorem assemble_continuous_coboundary {ι : Type*} [Countable ι]
    (cost moved d e : ι → X → ℝ) (g₀ b₀ : X → ℝ) (σ : X → X)
    (hσ : Measure.QuasiMeasurePreserving σ μ μ)
    (hmb₀ : Measurable b₀) (hmd : ∀ i, Measurable (d i))
    (hme : ∀ i, Measurable (e i))
    (hd : ∑' i, μ (Function.support (d i)) ≠ ∞)
    (he : ∑' i, μ (Function.support (e i)) ≠ ∞)
    (hcost : ∀ᵐ x ∂μ, Summable (fun i => cost i x))
    (hmoved : ∀ i, moved i =ᵐ[μ] fun x => cost i x +
      (d i x + e i x) - (d i (σ x) + e i (σ x)))
    (hbackground : g₀ =ᵐ[μ] fun x => 1 + b₀ (σ x) - b₀ x) :
    ∃ b : X → ℝ, Measurable b ∧
      (∀ x, b x = b₀ x - ∑' i, (d i x + e i x)) ∧
      ∀ᵐ x ∂μ, g₀ x + (∑' i, moved i x) =
        (∑' i, cost i x) + 1 + b (σ x) - b x := by
  let D : ι → X → ℝ := fun i x => d i x + e i x
  have hD : ∑' i, μ (Function.support (D i)) ≠ ∞ :=
    tsum_measure_support_add_ne_top d e hd he
  refine ⟨fun x => b₀ x - ∑' i, D i x,
    hmb₀.sub (Measurable.tsum fun i => (hmd i).add (hme i)), fun _ => rfl, ?_⟩
  filter_upwards [ae_tsum_coboundary cost moved D σ hσ hD hcost hmoved,
    hbackground] with x hsum hbg
  rw [hsum.2, hbg]
  ring

end Invariant233.TransferSupport

end OAI
