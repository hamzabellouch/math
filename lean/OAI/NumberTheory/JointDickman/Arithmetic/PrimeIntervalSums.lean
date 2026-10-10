import OAI.NumberTheory.JointDickman.Amplification.ArithmeticInputs
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeTupleBounds

namespace OAI

/-!
# Reciprocal primes on fixed logarithmic intervals

Mertens' second theorem supplies the fixed-power interval limit. Together
with Chebyshev's estimate, it bounds the error in the marginal tuple count.
-/

namespace JointDickman

open Filter Finset
open scoped Topology

noncomputable def primeReciprocalSum (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, 1 / (p : ℝ)

theorem primesLE_eq_filter (N : ℕ) :
    Nat.primesLE N = (Icc 2 N).filter Nat.Prime := by
  apply Finset.ext
  intro p
  simp only [Nat.mem_primesLE, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hle, hp⟩
    exact ⟨⟨hp.two_le, hle⟩, hp⟩
  · rintro ⟨⟨_, hle⟩, hp⟩
    exact ⟨hle, hp⟩

/-- The Mertens remainder tends to its additive constant. -/
theorem primeReciprocalSum_remainder_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∃ M : ℝ, Tendsto (fun x : ℝ => primeReciprocalSum x - Real.log (Real.log x))
      atTop (𝓝 M) := by
  obtain ⟨M, C, _, hC⟩ := hM
  refine ⟨M, tendsto_iff_norm_sub_tendsto_zero.mpr ?_⟩
  have hlim : Tendsto (fun x : ℝ => C / Real.log x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ hlim
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  simpa [Real.norm_eq_abs, primeReciprocalSum, primesLE_eq_filter] using hC x hx

theorem largePrimeSet_eq_sdiff {N y : ℝ} (hy : 0 ≤ y) :
    largePrimeSet N y = Nat.primesLE ⌊N⌋₊ \ Nat.primesLE ⌊y⌋₊ := by
  apply Finset.ext
  intro p
  rw [Finset.mem_sdiff]
  simp only [largePrimeSet, Finset.mem_filter, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpN, hp⟩, hpy⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    rintro ⟨hpy', _⟩
    exact (not_le_of_gt hpy) ((Nat.le_floor_iff hy).mp hpy')
  · rintro ⟨⟨hpN, hp⟩, hnot⟩
    refine ⟨⟨hpN, hp⟩, ?_⟩
    by_contra h
    exact hnot ⟨Nat.le_floor (le_of_not_gt h), hp⟩

theorem largePrimeSet_reciprocal_eq {N y : ℝ} (hy : 0 ≤ y) (hyN : y ≤ N) :
    (∑ p ∈ largePrimeSet N y, 1 / (p : ℝ)) = primeReciprocalSum N - primeReciprocalSum y := by
  have hsub : Nat.primesLE ⌊y⌋₊ ⊆ Nat.primesLE ⌊N⌋₊ := by
    intro p hp
    obtain ⟨hpy, hp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpy.trans (Nat.floor_mono hyN), hp⟩
  rw [largePrimeSet_eq_sdiff hy]
  exact eq_sub_of_add_eq (sum_sdiff hsub)

/-- Mertens' logarithmic interval mass, at the exact powers used in the
smooth-number inclusion-exclusion. -/
theorem largePrimeSet_reciprocal_tendsto
    (hM : PublishedInputs.PrimeReciprocalMertensInput) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ))
      atTop (𝓝 (-Real.log c)) := by
  obtain ⟨M, hrem⟩ := primeReciprocalSum_remainder_tendsto hM
  have hpower : Tendsto (fun N : ℝ => N ^ c) atTop atTop := tendsto_rpow_atTop hc
  have hlim := (hrem.sub (hrem.comp hpower)).sub_const (Real.log c)
  have heq : (fun N : ℝ =>
      (primeReciprocalSum N - Real.log (Real.log N)) -
      (primeReciprocalSum (N ^ c) - Real.log (Real.log (N ^ c))) - Real.log c) =ᶠ[atTop]
      (fun N : ℝ => ∑ p ∈ largePrimeSet N (N ^ c), 1 / (p : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 < N := lt_trans zero_lt_one hN
    have hlog : 0 < Real.log N := Real.log_pos hN
    have hpN : N ^ c ≤ N := by
      simpa using Real.rpow_le_rpow_of_exponent_le hN.le hc1
    rw [largePrimeSet_reciprocal_eq (Real.rpow_nonneg hN0.le c) hpN,
      Real.log_rpow hN0, Real.log_mul hc.ne' hlog.ne']
    ring
  simpa using hlim.congr' heq

namespace PublishedInputs

/-- The large-argument Chebyshev upper bound; Montgomery–Vaughan,
Multiplicative Number Theory I, Corollary 2.6. -/
def ChebyshevPrimeCountingInput : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 2 ≤ t →
    (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ C * t / Real.log t

end PublishedInputs

/-- Mertens and Chebyshev estimates bound the marginal tuple error. -/
theorem largePrimeTupleCount_tendsto_of_published
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hCheb : PublishedInputs.ChebyshevPrimeCountingInput)
    (h : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    Tendsto (fun N : ℝ =>
      (primeTupleCount (largePrimeSet N (N ^ c)) (h + 1) N : ℝ) / N)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hcount⟩ := hCheb
  have hrecip := largePrimeSet_reciprocal_tendsto hM hc hc1
  apply largePrimeTupleCount_density_tendsto_zero h hc hC
  · filter_upwards [(tendsto_rpow_atTop hc).eventually (eventually_ge_atTop (2 : ℝ))] with N hN
    intro t ht
    exact hcount t (hN.trans ht)
  · have hb := hrecip.eventually (Iio_mem_nhds (lt_add_one (-Real.log c)))
    exact hb.mono (fun _ hh => hh.le)

end JointDickman

end OAI
