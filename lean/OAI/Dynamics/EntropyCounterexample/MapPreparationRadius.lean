import OAI.Dynamics.EntropyCounterexample.MapBoundedOrbit
import OAI.Dynamics.EntropyCounterexample.MapFiniteOrbit

namespace OAI

noncomputable section
open Set
open scoped OnePoint

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem periodicReadout_eq_zero_before_readout (i : Fin 3) (t : ℝ) (k : ℤ)
    (hlo : 0 ≤ t - (k : ℝ) * 100) (hhi : t - (k : ℝ) * 100 ≤ 74) :
    periodicReadout i (t : AddCircle (100 : ℝ)) = 0 := by
  have hperiod := (periodicReadout_coe_periodic i).sub_int_mul_eq (x := t) k
  change periodicReadout i ((t - (k : ℝ) * 100 : ℝ) : AddCircle (100 : ℝ)) =
    periodicReadout i (t : AddCircle (100 : ℝ)) at hperiod
  rw [← hperiod, periodicReadout,
    AddCircle.liftIco_coe_apply (show t - (k : ℝ) * 100 ∈ Set.Ico (0 : ℝ) (0 + 100) by
      exact ⟨hlo, by linarith⟩)]
  by_contra hn
  have hs : t - (k : ℝ) * 100 ∈ Function.support (readoutCoeff i) := hn
  rw [readoutCoeff_support] at hs
  have hread := readoutInterval_subset i hs
  linarith [hread.1]

theorem concrete_norm_gt_half_before_barrier (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (N : ℕ) (k : ℤ)
    (hstart : 8 ≤ rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ∧
      rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ≤ 50) :
    1 / 2 < ‖z N‖ := by
  let t := rawClockLift (concreteData L hL) x t₀
  let s : ℕ → ℝ := fun n => t n - (k : ℝ) * 100
  have hmono : Monotone s := by
    intro i j hij
    exact sub_le_sub_right (monotone_rawClockLift _ (concrete_gate_mem_Icc L hL)
      x t₀ hij) _
  have hunbounded' : ¬ BddAbove (Set.range s) := by
    rintro ⟨M, hM⟩
    apply hunbounded
    refine ⟨M + (k : ℝ) * 100, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hn := hM (Set.mem_range_self n)
    dsimp [s, t] at hn
    linarith
  apply ClockDynamics.preparation_norm_gt_half hmono hunbounded' hstart
  intro n _ hlo hhi hsmall
  have hgate : (concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1) = 0 := by
    rw [← hz n]
    exact SphereCutoffs.affineClockGate_eq_zero hsmall
  have hstep := rawClockLift_succ (concreteData L hL) x t₀ h₀ n
  change t (n + 1) = t n + Clock.increment (t n)
    ((concreteData L hL).gate (((concreteMap L hL)^[n] x).2.1)) at hstep
  rw [hgate, Clock.increment_zero] at hstep
  have hbar : Clock.barrier (s n) = Clock.barrier (t n) :=
    Clock.barrier_periodic.sub_int_mul_eq k
  have hstop := Clock.barrier_stops (s n) hhi
  constructor
  · dsimp [s] at hbar hstop ⊢
    linarith
  · have hread : readout (concreteData L hL) (((concreteMap L hL)^[n] x).1)
        (((concreteMap L hL)^[n] x).2.2) = 0 := by
      have hβ : ∀ i, periodicReadout i (((concreteMap L hL)^[n] x).1) = 0 := by
        intro i
        change periodicReadout i (((rawMap (concreteData L hL))^[n] x).1) = 0
        rw [← coe_rawClockLift (concreteData L hL) x t₀ h₀ n]
        apply periodicReadout_eq_zero_before_readout i _ k
        · change 0 ≤ s n
          linarith
        · change s n ≤ 74
          linarith
      simp [readout, hβ]
    rw [finiteMainOrbit_recurrence (concreteData L hL) x z hz n]
    change z n ^ 2 + readout (concreteData L hL) (((concreteMap L hL)^[n] x).1)
      (((concreteMap L hL)^[n] x).2.2) = z n ^ 2
    rw [hread, add_zero]

theorem concrete_preparation_radius (L : ℝ) (hL : 2 < L)
    (x : RawManifold) (t₀ : ℝ) (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift (concreteData L hL) x t₀)))
    (z : ℕ → ℂ) (hz : ∀ n, (z n : Sphere) = ((concreteMap L hL)^[n] x).2.1)
    (N : ℕ) (k : ℤ)
    (hprep : rawClockLift (concreteData L hL) x t₀ N - (k : ℝ) * 100 ∈ Set.Ioo 8 12) :
    1 / 2 < ‖z N‖ := by
  apply concrete_norm_gt_half_before_barrier L hL x t₀ h₀ hunbounded z hz N k
  exact ⟨hprep.1.le, by linarith [hprep.2]⟩

end Problem340.Construction

end

end OAI
