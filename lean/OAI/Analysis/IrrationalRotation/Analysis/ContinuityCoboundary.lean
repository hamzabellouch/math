import OAI.Analysis.IrrationalRotation.Model.ContinuityCoboundary
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection.Continuity

variable {X : Type*}

@[simp] theorem backwardSum_zero (σ : X ≃ X) (v : X → ℝ) (x : X) :
    backwardSum σ v 0 x = 0 := by
  simp [backwardSum]

theorem backwardSum_succ (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) :
    backwardSum σ v (n + 1) x =
      backwardSum σ v n x + v ((σ.symm : X → X)^[n + 1] x) := by
  simp [backwardSum, Finset.sum_range_succ]

theorem backwardSum_sub_comp (σ : X ≃ X) (v : X → ℝ) (n : ℕ) (x : X) :
    backwardSum σ v n x - backwardSum σ v n (σ x) =
      v ((σ.symm : X → X)^[n] x) - v x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [backwardSum_succ, backwardSum_succ]
    have hcancel : (σ.symm : X → X)^[n + 1] (σ x) =
        (σ.symm : X → X)^[n] x := by
      rw [Function.iterate_succ_apply]
      simp
    rw [hcancel]
    linarith

theorem relocated_eq_add_coboundary (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (x : X)
    (hpartition : ∑ n ∈ Finset.range (H + 1), φ n x = 1) :
    relocated σ h φ H x = h x + relocationTransfer σ h φ H x -
      relocationTransfer σ h φ H (σ x) := by
  have ht : relocationTransfer σ h φ H x -
      relocationTransfer σ h φ H (σ x) = relocated σ h φ H x - h x := by
    unfold relocationTransfer
    rw [← Finset.sum_sub_distrib]
    simp_rw [backwardSum_sub_comp]
    rw [Finset.sum_sub_distrib]
    change relocated σ h φ H x -
      (∑ n ∈ Finset.range (H + 1), h x * φ n x) = _
    rw [← Finset.mul_sum, hpartition, mul_one]
  linarith

theorem relocationTransfer_eq_zero (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (x : X)
    (hzero : ∀ r, 1 ≤ r → r ≤ H → h ((σ.symm : X → X)^[r] x) = 0) :
    relocationTransfer σ h φ H x = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  apply Finset.sum_eq_zero
  intro r hr
  have hn' : n ≤ H := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have hr' : r + 1 ≤ n := Finset.mem_range.mp hr
  change h ((σ.symm : X → X)^[r + 1] x) *
    φ n ((σ.symm : X → X)^[r + 1] x) = 0
  rw [hzero (r + 1) (by omega) (by omega), zero_mul]

theorem background_coboundary (σ : X ≃ X) (v : X → ℝ)
    (W : ℕ) (hW : W ≠ 0) (x : X) :
    v x - backwardAverage σ v W x =
      backgroundTransfer σ v W (σ x) - backgroundTransfer σ v W x := by
  have ht : (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) x) -
      (∑ n ∈ Finset.range W, backwardSum σ v (n + 1) (σ x)) =
      backwardSum σ v W x - (W : ℝ) * v x := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [backwardSum_sub_comp]
    rw [Finset.sum_sub_distrib]
    simp [backwardSum]
  have hW' : (W : ℝ) ≠ 0 := by exact_mod_cast hW
  unfold backwardAverage backgroundTransfer
  field_simp
  nlinarith

end InvariantProjection.Continuity

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*}

theorem relocated_nonneg (σ : X ≃ X) (h : X → ℝ) (φ : ℕ → X → ℝ)
    (H : ℕ) (hh : ∀ x, 0 ≤ h x) (hφ : ∀ n ≤ H, ∀ x, 0 ≤ φ n x) (x : X) :
    0 ≤ relocated σ h φ H x := by
  apply Finset.sum_nonneg
  intro n hn
  exact mul_nonneg (hh _) (hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)) _)

theorem support_relocated_subset (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) (O : Set X)
    (hφ : ∀ n ≤ H, (σ : X → X)^[n] '' support (φ n) ⊆ O) :
    support (relocated σ h φ H) ⊆ O := by
  intro x hx
  by_contra hxO
  apply hx
  apply Finset.sum_eq_zero
  intro n hn
  have hz : φ n ((σ.symm : X → X)^[n] x) = 0 := by
    by_contra hne
    apply hxO
    apply hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
    refine ⟨(σ.symm : X → X)^[n] x, hne, ?_⟩
    exact (Function.LeftInverse.iterate σ.apply_symm_apply n) x
  rw [hz, mul_zero]

theorem continuous_relocated [TopologicalSpace X] (σ : X ≃ₜ X)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (hh : Continuous h)
    (hφ : ∀ n ≤ H, Continuous (φ n)) :
    Continuous (relocated σ.toEquiv h φ H) := by
  apply continuous_finsetSum
  intro n hn
  exact (hh.comp (σ.symm.continuous.iterate n)).mul
    ((hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).comp
      (σ.symm.continuous.iterate n))

theorem continuous_relocationTransfer [TopologicalSpace X] (σ : X ≃ₜ X)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (hh : Continuous h)
    (hφ : ∀ n ≤ H, Continuous (φ n)) :
    Continuous (relocationTransfer σ.toEquiv h φ H) := by
  apply continuous_finsetSum
  intro n hn
  apply continuous_finsetSum
  intro r _hr
  exact (hh.comp (σ.symm.continuous.iterate (r + 1))).mul
    ((hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))).comp
      (σ.symm.continuous.iterate (r + 1)))

theorem tsupport_relocated_subset [TopologicalSpace X] (σ : X ≃ₜ X)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ) (O : Set X)
    (hφ : ∀ n ≤ H, (σ : X → X)^[n] '' tsupport (φ n) ⊆ O) :
    tsupport (relocated σ.toEquiv h φ H) ⊆ O := by
  have hsub : support (relocated σ.toEquiv h φ H) ⊆
      ⋃ n ∈ Finset.range (H + 1), ((σ.symm : X → X)^[n]) ⁻¹' tsupport (φ n) := by
    intro x hx
    by_contra hout
    apply hx
    apply Finset.sum_eq_zero
    intro n hn
    have hz : φ n ((σ.symm : X → X)^[n] x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hm
      exact hout (Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hn, hm⟩⟩)
    exact mul_eq_zero_of_right _ hz
  have hclosed : IsClosed
      (⋃ n ∈ Finset.range (H + 1), ((σ.symm : X → X)^[n]) ⁻¹' tsupport (φ n)) :=
    isClosed_biUnion_finset (fun n _ =>
      (isClosed_tsupport (φ n)).preimage (σ.symm.continuous.iterate n))
  intro x hx
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (closure_minimal hsub hclosed hx)
  obtain ⟨hn, hx⟩ := Set.mem_iUnion.mp hn
  apply hφ n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
  refine ⟨(σ.symm : X → X)^[n] x, hx, ?_⟩
  exact (Function.LeftInverse.iterate σ.apply_symm_apply n) x

theorem support_relocationTransfer_subset (σ : X ≃ X) (h : X → ℝ)
    (φ : ℕ → X → ℝ) (H : ℕ) :
    support (relocationTransfer σ h φ H) ⊆
      ⋃ r ∈ Finset.range H, ((σ.symm : X → X)^[r + 1]) ⁻¹' support h := by
  intro x hx
  by_contra hxU
  apply hx
  apply relocationTransfer_eq_zero
  intro r hr hrH
  by_contra hne
  apply hxU
  refine Set.mem_iUnion.mpr ⟨r - 1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_range.mpr (by omega)
  · change h ((σ.symm : X → X)^[r - 1 + 1] x) ≠ 0
    simpa [Nat.sub_add_cancel hr] using hne

end InvariantProjection.Continuity

namespace InvariantProjection.Continuity

open Function MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem measurableEmbedding_iterate (σ : X ≃ᵐ X) (n : ℕ) :
    MeasurableEmbedding (σ : X → X)^[n] := by
  induction n with
  | zero => exact MeasurableEmbedding.id
  | succ n ih =>
    rw [Function.iterate_succ]
    exact ih.comp σ.measurableEmbedding

theorem integral_relocated (σ : X ≃ᵐ X) (hσ : MeasurePreserving σ μ μ)
    (h : X → ℝ) (φ : ℕ → X → ℝ) (H : ℕ)
    (hint : ∀ n ≤ H, Integrable (fun x => h x * φ n x) μ)
    (hpartition : ∀ x, ∑ n ∈ Finset.range (H + 1), φ n x = 1) :
    ∫ x, relocated σ.toEquiv h φ H x ∂μ = ∫ x, h x ∂μ := by
  have hb := hσ.symm σ
  have hp (n : ℕ) : MeasurePreserving (σ.symm : X → X)^[n] μ μ := hb.iterate n
  unfold relocated
  rw [integral_finsetSum]
  · calc
      (∑ n ∈ Finset.range (H + 1),
          ∫ x, h ((σ.symm : X → X)^[n] x) *
            φ n ((σ.symm : X → X)^[n] x) ∂μ) =
          ∑ n ∈ Finset.range (H + 1), ∫ x, h x * φ n x ∂μ := by
        apply Finset.sum_congr rfl
        intro n hn
        exact (hp n).integral_comp (measurableEmbedding_iterate σ.symm n)
          (fun x : X => h x * φ n x)
      _ = ∫ x, ∑ n ∈ Finset.range (H + 1), h x * φ n x ∂μ := by
        symm
        apply integral_finsetSum
        intro n hn
        exact hint n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))
      _ = ∫ x, h x ∂μ := by
        congr 1
        funext x
        rw [← Finset.mul_sum, hpartition x, mul_one]
  · intro n hn
    exact (hp n).integrable_comp_of_integrable
      (hint n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))

theorem measure_support_relocationTransfer_le (σ : X ≃ᵐ X)
    (hσ : MeasurePreserving σ μ μ) (h : X → ℝ) (hh : Measurable h)
    (φ : ℕ → X → ℝ) (H : ℕ) :
    μ (support (relocationTransfer σ.toEquiv h φ H)) ≤
      (H : ℝ≥0∞) * μ (support h) := by
  have hb := hσ.symm σ
  calc
    μ (support (relocationTransfer σ.toEquiv h φ H)) ≤
        μ (⋃ r ∈ Finset.range H,
          ((σ.symm : X → X)^[r + 1]) ⁻¹' support h) :=
      measure_mono (support_relocationTransfer_subset σ.toEquiv h φ H)
    _ ≤ ∑ r ∈ Finset.range H,
        μ (((σ.symm : X → X)^[r + 1]) ⁻¹' support h) :=
      measure_biUnion_finset_le _ _
    _ = ∑ _r ∈ Finset.range H, μ (support h) := by
      apply Finset.sum_congr rfl
      intro r hr
      exact (hb.iterate (r + 1)).measure_preimage (measurableSet_support hh).nullMeasurableSet
    _ = (H : ℝ≥0∞) * μ (support h) := by simp

end InvariantProjection.Continuity

end OAI
