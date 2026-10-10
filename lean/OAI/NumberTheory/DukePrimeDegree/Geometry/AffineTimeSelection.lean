import OAI.NumberTheory.DukePrimeDegree.Dynamics.DiagonalFlowMaximal

namespace OAI

/-!
# Synchronizing the shearing time windows

Affine changes of time with slope at least one half at most double
Lebesgue measure. This yields the loss of eight in EKL (2006), Lemma 4.5.
A finite family of bad windows can then be avoided simultaneously.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal BigOperators

namespace DukePrimeDegree

lemma volume_real_affine_preimage (a b : ℝ) (ha : 0 < a) (E : Set ℝ) :
    volume.real ((fun t => b + a * t) ⁻¹' E) = a⁻¹ * volume.real E := by
  have he : (fun t => b + a * t) ⁻¹' E =
      (fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' E) := rfl
  rw [measureReal_def, he, Real.volume_preimage_mul_left ha.ne', measure_preimage_add,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (inv_pos.mpr ha)]
  rfl

lemma affine_bad_time_bound (a b T : ℝ) (ha : 1 / 2 ≤ a)
    (E : Set ℝ) (hfinite : volume E ≠ ∞) :
    volume.real (Ioc 0 T ∩ ((fun t => b + a * t) ⁻¹' E)) ≤ 2 * volume.real E := by
  have hapos : 0 < a := by linarith
  have hpre : volume ((fun t => b + a * t) ⁻¹' E) ≠ ∞ := by
    change volume ((fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' E)) ≠ ∞
    rw [Real.volume_preimage_mul_left hapos.ne', measure_preimage_add]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite
  calc
    volume.real (Ioc 0 T ∩ ((fun t => b + a * t) ⁻¹' E))
        ≤ volume.real ((fun t => b + a * t) ⁻¹' E) := measureReal_mono inter_subset_right hpre
    _ = a⁻¹ * volume.real E := volume_real_affine_preimage a b hapos E
    _ ≤ 2 * volume.real E := by
      apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
      apply (inv_le_comm₀ hapos (by norm_num : (0 : ℝ) < 2)).mpr
      norm_num
      exact ha

lemma ekl_affine_time_mem (T θ η τ : ℝ) (hT : 0 < T)
    (hθlo : 4 * T ≤ θ) (hθhi : θ ≤ 6 * T) (hη : η = 0 ∨ η = 1)
    (hτ : τ ∈ Ioc 0 T) : (θ + (2 - η) * τ) / 2 ∈ Ioc 0 (4 * T) := by
  rcases hη with rfl | rfl <;> constructor <;> nlinarith [hτ.1, hτ.2]

/-- The precise affine-time loss used to transfer the small-ball set
from the interval of length `4*T` to the shearing interval of length `T`. -/
theorem ekl_pullback_bad_time_bound (T θ η ε : ℝ)
    (hη : η = 0 ∨ η = 1) (E : Set ℝ) (hE : E ⊆ Ioc 0 (4 * T))
    (hbad : volume.real E ≤ ε * (4 * T)) :
    volume.real (Ioc 0 T ∩
      ((fun τ => (θ + (2 - η) * τ) / 2) ⁻¹' E)) ≤ 8 * ε * T := by
  have ha : (1 : ℝ) / 2 ≤ (2 - η) / 2 := by
    rcases hη with rfl | rfl <;> norm_num
  have hfinite : volume E ≠ ∞ :=
    measure_ne_top_of_subset hE (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have heq : (fun τ => (θ + (2 - η) * τ) / 2) =
      (fun τ => θ / 2 + ((2 - η) / 2) * τ) := by
    funext τ
    ring
  rw [heq]
  have h := affine_bad_time_bound ((2 - η) / 2) (θ / 2) T ha E hfinite
  nlinarith

/-- Finite exceptional time sets whose relative losses sum to less
than one leave a common admissible time. -/
theorem exists_time_avoiding_finite_bad_sets (m : ℕ) (T : ℝ) (hT : 0 < T)
    (B : Fin m → Set ℝ) (c : Fin m → ℝ)
    (hB : ∀ k, B k ⊆ Ioc 0 T)
    (hbad : ∀ k, volume.real (B k) ≤ c k * T)
    (hsum : ∑ k, c k < 1) :
    ∃ t ∈ Ioc 0 T, ∀ k, t ∉ B k := by
  by_contra h
  have hcover : Ioc 0 T ⊆ ⋃ k, B k := by
    intro t ht
    by_contra hn
    apply h
    refine ⟨t, ht, ?_⟩
    intro k hk
    exact hn (mem_iUnion.mpr ⟨k, hk⟩)
  have hsub : (⋃ k, B k) ⊆ Ioc 0 T := iUnion_subset hB
  have hfinite : volume (⋃ k, B k) ≠ ∞ := measure_ne_top_of_subset hsub (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hle := measureReal_mono hcover hfinite
  have hunion := measureReal_iUnion_fintype_le (μ := volume) B
  have hbound : ∑ k, volume.real (B k) ≤ (∑ k, c k) * T := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hbad k
  have hstrict : (∑ k, c k) * T < T := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hsum hT
  rw [Real.volume_real_Ioc_of_le hT.le, sub_zero] at hle
  linarith

end DukePrimeDegree

end

end OAI
