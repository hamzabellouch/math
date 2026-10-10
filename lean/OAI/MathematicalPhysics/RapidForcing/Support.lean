import OAI.MathematicalPhysics.RapidForcing.Model

namespace OAI

open scoped BigOperators ENNReal Topology
open Set MeasureTheory
namespace RapidForcing

lemma K_closed : IsClosed K := by
  unfold K
  have h (i : Fin 3) : Continuous (fun x : Space => x i) :=
    (EuclideanSpace.proj i).continuous
  exact (isClosed_le continuous_const (h 0)).inter
    ((isClosed_le (h 0) continuous_const).inter
      ((isClosed_le continuous_const (h 1)).inter
        ((isClosed_le (h 1) continuous_const).inter
          ((isClosed_le continuous_const (h 2)).inter
            (isClosed_le (h 2) continuous_const)))))

lemma norm_le_three_of_mem_K {x : Space} (hx : x ∈ K) : ‖x‖ ≤ 3 := by
  obtain ⟨hx₀, hx₀', hx₁, hx₁', hx₂, hx₂'⟩ := hx
  have h₀ : (x 0) ^ 2 ≤ 4 := by nlinarith
  have h₁ : (x 1) ^ 2 ≤ 4 := by nlinarith
  have h₂ : (x 2) ^ 2 ≤ 1 := by nlinarith
  have hn : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x
  nlinarith [norm_nonneg x]

lemma K_compact : IsCompact K := by
  apply (isCompact_closedBall (0 : Space) 3).of_isClosed_subset K_closed
  intro x hx
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_le_three_of_mem_K hx

section Support
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Field E}

omit [NormedSpace ℝ E] in
lemma supported_iff_zero_off : Supported f ↔
    ∀ (t : ℝ), 0 ≤ t → ∀ x : Space, x ∉ K → f t x = 0 := by
  constructor
  · intro hf t ht x hx
    by_contra hn
    exact hx (hf t ht (subset_closure hn))
  · intro hf t ht
    apply closure_minimal _ K_closed
    intro x hx
    by_contra hn
    exact hx (hf t ht x hn)

omit [NormedSpace ℝ E] in
lemma Supported.zero_off (hf : Supported f) {t : ℝ} (ht : 0 ≤ t)
    {x : Space} (hx : x ∉ K) : f t x = 0 :=
  supported_iff_zero_off.mp hf t ht x hx

lemma Supported.spatialD (hf : Supported f) (i : Fin 3) : Supported (spatialD i f) := by
  intro t ht
  exact (tsupport_fderiv_apply_subset ℝ (basis i)).trans (hf t ht)

lemma Supported.timeD (hf : Supported f) : Supported (timeD f) := by
  apply supported_iff_zero_off.mpr
  intro t ht x hx
  change derivWithin (fun s => f s x) (Ici 0) t = 0
  have h : EqOn (fun s => f s x) (fun _ => (0 : E)) (Ici 0) :=
    fun s hs => hf.zero_off hs hx
  rw [derivWithin_congr h (hf.zero_off ht hx)]
  simp

lemma Supported.spatialIter (hf : Supported f) (i : Fin 3) (n : ℕ) :
    Supported ((RapidForcing.spatialD i)^[n] f) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    simpa only [Function.iterate_succ_apply'] using ih.spatialD i

lemma Supported.spatialMulti (hf : Supported f) (α : MultiIndex) :
    Supported (RapidForcing.spatialMulti α f) :=
  (((hf.spatialIter 2 (α 2)).spatialIter 1 (α 1)).spatialIter 0 (α 0))

lemma Supported.mixedD (hf : Supported f) (l : ℕ) (α : MultiIndex) :
    Supported (RapidForcing.mixedD l α f) := by
  unfold RapidForcing.mixedD
  induction l with
  | zero => simpa using hf.spatialMulti α
  | succ l ih => simpa only [Function.iterate_succ_apply'] using ih.timeD

theorem rapidSpaceTime_of_supported_rapid (hs : Supported f) (hr : Rapid f) :
    RapidSpaceTime f := by
  intro J l α
  obtain ⟨C, hC, hbound⟩ := hr J l α
  refine ⟨4 ^ J * C, mul_nonneg (by positivity) hC, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · have hw : 1 + t + ‖x‖ ≤ 4 * (1 + t) := by
      have := norm_le_three_of_mem_K hx
      linarith
    calc
      (1 + t + ‖x‖) ^ J * ‖mixedD l α f t x‖ ≤
          (4 * (1 + t)) ^ J * ‖mixedD l α f t x‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (by positivity) hw J) (norm_nonneg _)
      _ = 4 ^ J * ((1 + t) ^ J * ‖mixedD l α f t x‖) := by rw [mul_pow]; ring
      _ ≤ 4 ^ J * C := mul_le_mul_of_nonneg_left (hbound t ht x) (by positivity)
  · rw [(hs.mixedD l α).zero_off ht hx, norm_zero, mul_zero]
    exact mul_nonneg (by positivity) hC

end Support
end RapidForcing

end OAI
