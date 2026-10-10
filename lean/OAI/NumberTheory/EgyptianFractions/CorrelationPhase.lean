import OAI.NumberTheory.EgyptianFractions.ForwardDifference
import OAI.NumberTheory.EgyptianFractions.IteratedDifferencing

namespace OAI
noncomputable section
open scoped BigOperators
open ComplexConjugate
namespace Problem337

/-- The unit complex phase with frequency one. -/
def differencingPhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

@[simp] theorem differencingPhase_norm (x : ℝ) : ‖differencingPhase x‖ = 1 := by
  simp [differencingPhase, Complex.norm_exp]

theorem differencingPhase_sub (x y : ℝ) :
    differencingPhase (x - y) = differencingPhase x * conj (differencingPhase y) := by
  simp only [differencingPhase, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/-- A phase sequence with zero extension outside a closed integer interval. -/
def intervalPhase (f : ℝ → ℝ) (L U : ℤ) : ℤ → ℂ :=
  fun n => if L ≤ n ∧ n ≤ U then differencingPhase (f n) else 0

theorem correlationShift_intervalPhase (f : ℝ → ℝ) (L U h : ℤ) (hh : 0 ≤ h) :
    correlationShift (intervalPhase f L U) h =
      intervalPhase (fun x => f (x + h) - f x) L (U - h) := by
  funext n
  by_cases hn : L ≤ n ∧ n ≤ U - h
  · have hn0 : L ≤ n ∧ n ≤ U := by omega
    have hn1 : L ≤ n + h ∧ n + h ≤ U := by omega
    simp [correlationShift, intervalPhase, hn, hn0, hn1, differencingPhase_sub]
  · have hbad : ¬ (L ≤ n + h ∧ n + h ≤ U) ∨ ¬ (L ≤ n ∧ n ≤ U) := by omega
    rcases hbad with hbad | hbad
    · simp [correlationShift, intervalPhase, hn, hbad]
    · simp [correlationShift, intervalPhase, hn, hbad]

theorem forwardDifference_sub_input (hs : List ℝ) (f g : ℝ → ℝ) :
    forwardDifference hs (fun x => f x - g x) =
      fun x => forwardDifference hs f x - forwardDifference hs g x := by
  induction hs with
  | nil => rfl
  | cons h hs ih =>
    funext x
    simp only [forwardDifference, ih]
    ring

theorem forwardDifference_translate_input (hs : List ℝ) (f : ℝ → ℝ) (h : ℝ) :
    forwardDifference hs (fun x => f (x + h)) =
      fun x => forwardDifference hs f (x + h) := by
  induction hs with
  | nil => rfl
  | cons t hs ih =>
    funext x
    simp only [forwardDifference, ih]
    congr 1
    congr 1
    ring

theorem forwardDifference_cons_input (hs : List ℝ) (f : ℝ → ℝ) (h : ℝ) :
    forwardDifference hs (fun x => f (x + h) - f x) =
      forwardDifference (h :: hs) f := by
  rw [forwardDifference_sub_input, forwardDifference_translate_input]
  rfl

/-- Positive iterated correlations of a truncated phase are exactly the
    differentiated phase on the interval shortened by the total shift. -/
theorem iteratedCorrelation_intervalPhase (hs : List ℤ) (f : ℝ → ℝ) (L U : ℤ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) :
    iteratedCorrelation (intervalPhase f L U) hs =
      intervalPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f) L (U - hs.sum) := by
  induction hs generalizing f L U with
  | nil => simp [iteratedCorrelation, forwardDifference]
  | cons h hs ih =>
    have hh : 0 ≤ h := hhs h (by simp)
    have htail : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    rw [iteratedCorrelation, correlationShift_intervalPhase f L U h hh,
      ih _ _ _ htail, forwardDifference_cons_input]
    simp only [List.map_cons, List.sum_cons]
    congr 1
    omega

/-- A zero-extended interval phase sums to its untruncated phase sum on
    any larger integer interval. Empty subintervals are included. -/
theorem intervalPhase_sum (f : ℝ → ℝ) (L U A B : ℤ)
    (hAL : A ≤ L) (hUB : U ≤ B) :
    (∑ n ∈ Finset.Icc A B, intervalPhase f L U n) =
      ∑ n ∈ Finset.Icc L U, differencingPhase (f n) := by
  classical
  have hsub : Finset.Icc L U ⊆ Finset.Icc A B := Finset.Icc_subset_Icc hAL hUB
  calc
    (∑ n ∈ Finset.Icc A B, intervalPhase f L U n) =
        ∑ n ∈ Finset.Icc L U, intervalPhase f L U n := by
      apply (Finset.sum_subset hsub _).symm
      intro n hn hnot
      simp only [Finset.mem_Icc] at hnot
      simp [intervalPhase, hnot]
    _ = ∑ n ∈ Finset.Icc L U, differencingPhase (f n) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [intervalPhase, Finset.mem_Icc.mp hn]

/-- The exact terminal sum after differencing a phase supported on `[1,N]`. -/
theorem iteratedCorrelation_intervalPhase_sum (hs : List ℤ) (f : ℝ → ℝ) (N : ℕ)
    (hhs : ∀ h ∈ hs, 0 ≤ h) :
    (∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation (intervalPhase f 1 N) hs n) =
      ∑ n ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n) := by
  rw [iteratedCorrelation_intervalPhase hs f 1 N hhs]
  apply intervalPhase_sum _ _ _ _ _ le_rfl
  have hsum : 0 ≤ hs.sum := List.sum_nonneg hhs
  omega

/-- Reduction of a phase sum to the untruncated forward-difference sums
    needed by a derivative test. All interval endpoints are explicit. -/
theorem interval_phase_iterated_power_bound (r N H : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hHε : 2 / (H : ℝ) ≤ ε) (f : ℝ → ℝ)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) ((N : ℤ) - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ /
          (N : ℝ) ≤ ε) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, differencingPhase (f n)‖ / (N : ℝ) ≤
      3 * ε ^ (1 / (2 : ℝ)^r) := by
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → intervalPhase f 1 N n = 0 := by
    intro n hn
    simpa only [intervalPhase, Finset.mem_Icc, ite_eq_right_iff] using
      (fun h : (1 : ℤ) ≤ n ∧ n ≤ N => False.elim (hn (Finset.mem_Icc.mpr h)))
  have hnrm : ∀ n : ℤ, ‖intervalPhase f 1 N n‖ ≤ 1 := by
    intro n
    unfold intervalPhase
    split_ifs <;> simp
  have hbound := iterated_differencing_power_bound r N H hH hHN ε hε hε1 hHε
    (intervalPhase f 1 N) hsupp hnrm (by
      intro hs hlen hgood
      rw [iteratedCorrelation_intervalPhase_sum hs f N (fun h hh => (hgood h hh).1.le)]
      exact hterminal hs hlen hgood)
  rwa [intervalPhase_sum f 1 N 1 N le_rfl le_rfl] at hbound

/-- Integer translation of a finite interval sum. -/
theorem sum_integer_interval_translate {M : Type*} [AddCommMonoid M]
    (f : ℤ → M) (A B t : ℤ) :
    (∑ n ∈ Finset.Icc A B, f (n + t)) =
      ∑ n ∈ Finset.Icc (A + t) (B + t), f n := by
  classical
  apply Finset.sum_bij (fun n _ => n + t)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn m hm heq
    omega
  · intro n hn
    refine ⟨n - t, ?_, by omega⟩
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intros
    rfl

theorem phase_sum_integer_translate (f : ℝ → ℝ) (A B t : ℤ) :
    (∑ n ∈ Finset.Icc A B, differencingPhase (f ((n : ℝ) + t))) =
      ∑ n ∈ Finset.Icc (A + t) (B + t), differencingPhase (f n) := by
  simpa only [Int.cast_add] using
    sum_integer_interval_translate (fun n => differencingPhase (f n)) A B t

/-- The phase differencing bound on an arbitrary translated integer interval. -/
theorem translated_interval_phase_power_bound (r N H : ℕ) (L : ℤ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hHε : 2 / (H : ℝ) ≤ ε) (f : ℝ → ℝ)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc L (L + (N : ℤ) - 1 - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ /
          (N : ℝ) ≤ ε) :
    ‖∑ n ∈ Finset.Icc L (L + (N : ℤ) - 1), differencingPhase (f n)‖ /
        (N : ℝ) ≤ 3 * ε ^ (1 / (2 : ℝ)^r) := by
  let g : ℝ → ℝ := fun x => f (x + ((L - 1 : ℤ) : ℝ))
  have hbound := interval_phase_iterated_power_bound r N H hH hHN ε hε hε1 hHε g (by
    intro hs hlen hgood
    simp only [g, forwardDifference_translate_input]
    rw [phase_sum_integer_translate]
    have hleft : (1 : ℤ) + (L - 1) = L := by omega
    have hright : ((N : ℤ) - hs.sum) + (L - 1) = L + (N : ℤ) - 1 - hs.sum := by omega
    rw [hleft, hright]
    exact hterminal hs hlen hgood)
  dsimp [g] at hbound
  rw [phase_sum_integer_translate] at hbound
  have hleft : (1 : ℤ) + (L - 1) = L := by omega
  have hright : (N : ℤ) + (L - 1) = L + (N : ℤ) - 1 := by omega
  rwa [hleft, hright] at hbound

/-- Differencing a subinterval inside a larger normalization interval.
This permits `N = ceil(2U)` in a dyadic reciprocal-phase estimate. -/
theorem interval_phase_ambient_power_bound (r N H : ℕ) (L U : ℤ)
    (hL : 1 ≤ L) (hU : U ≤ N)
    (hH : 1 ≤ H) (hHN : H ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hHε : 2 / (H : ℝ) ≤ ε) (f : ℝ → ℝ)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc L (U - hs.sum),
        differencingPhase (forwardDifference (hs.map (fun h : ℤ => (h : ℝ))) f n)‖ /
          (N : ℝ) ≤ ε) :
    ‖∑ n ∈ Finset.Icc L U, differencingPhase (f n)‖ / (N : ℝ) ≤
      3 * ε ^ (1 / (2 : ℝ)^r) := by
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → intervalPhase f L U n = 0 := by
    intro n hn
    have hout : ¬ (L ≤ n ∧ n ≤ U) := by
      simp only [Finset.mem_Icc] at hn
      omega
    simp [intervalPhase, hout]
  have hnrm : ∀ n : ℤ, ‖intervalPhase f L U n‖ ≤ 1 := by
    intro n
    unfold intervalPhase
    split_ifs <;> simp
  have hbound := iterated_differencing_power_bound r N H hH hHN ε hε hε1 hHε
    (intervalPhase f L U) hsupp hnrm (by
      intro hs hlen hgood
      have hnonneg : ∀ h ∈ hs, 0 ≤ h := fun h hh => (hgood h hh).1.le
      rw [iteratedCorrelation_intervalPhase hs f L U hnonneg]
      have hsum : 0 ≤ hs.sum := List.sum_nonneg hnonneg
      rw [intervalPhase_sum _ L (U - hs.sum) 1 N hL (by omega)]
      exact hterminal hs hlen hgood)
  rwa [intervalPhase_sum f L U 1 N hL hU] at hbound

end Problem337

end

end OAI
