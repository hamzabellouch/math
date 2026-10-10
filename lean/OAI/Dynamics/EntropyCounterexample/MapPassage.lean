import OAI.Dynamics.EntropyCounterexample.MapOrbitLift
import OAI.Dynamics.EntropyCounterexample.ClockPassage

namespace OAI

noncomputable section

namespace Problem340.Construction

def HasScheduledPassageAt (t : ℕ → ℝ) (k : ℤ) : Prop :=
    ∃ lo hi : ℕ,
      let s := fun n => t n - 100 * (k : ℝ)
      let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (s i))
      lo < hi ∧ (0 ≤ s lo ∧ s lo < 1) ∧ (100 ≤ s hi ∧ s hi < 101) ∧
      (∀ n, lo ≤ n → n < hi → 0 ≤ s n ∧ s n < 100) ∧
      I.Nonempty ∧ I.card ≤ 5 ∧
      (∃ i ∈ I, preparationCoeff (s i) = 1) ∧
      (∃ r ∈ Finset.Ico lo hi, 2 ≤ s r ∧ s r < 3 ∧ ∀ i ∈ I, r + 1 ≤ i) ∧
      (∃ j ∈ Finset.Ico lo hi, 76 ≤ s j ∧ s j < 77 ∧
        ∃ l : Fin 3, readoutCoeff l (s j) = 1)

def HasScheduledPassage (t : ℕ → ℝ) : Prop := ∃ k : ℤ, HasScheduledPassageAt t k

theorem preparation_indices_mem_iff {t : ℕ → ℝ} (hmono : Monotone t)
    {lo hi : ℕ} (hstart : t lo < 1) (hend : 100 ≤ t hi) (n : ℕ) :
    n ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)) ↔
      preparationCoeff (t n) ≠ 0 := by
  classical
  constructor
  · intro hn
    exact ne_of_gt (Finset.mem_filter.mp hn).2
  · intro hn
    have hs : t n ∈ Set.Ioo 8 12 := by
      rw [← preparationCoeff_support]
      exact hn
    have hlo : lo ≤ n := by
      by_contra h
      have := hmono (show n ≤ lo by omega)
      linarith [hs.1]
    have hhi : n < hi := by
      by_contra h
      have := hmono (show hi ≤ n by omega)
      linarith [hs.2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlo, hhi⟩,
      lt_of_le_of_ne (preparationCoeff_nonneg _) (Ne.symm hn)⟩

theorem preparationCoeff_zero_of_not_mem {t : ℕ → ℝ} (hmono : Monotone t)
    {lo hi : ℕ} (hstart : t lo < 1) (hend : 100 ≤ t hi) {n : ℕ}
    (hn : n ∉ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))) :
    preparationCoeff (t n) = 0 := by
  by_contra h
  exact hn ((preparation_indices_mem_iff hmono hstart hend n).mpr h)

theorem preparation_before_readout {t : ℕ → ℝ} (hmono : Monotone t)
    {i j : ℕ} {l : Fin 3}
    (hi : preparationCoeff (t i) ≠ 0) (hj : readoutCoeff l (t j) ≠ 0) : i < j := by
  have hi' : t i ∈ Set.Ioo 8 12 := by
    rw [← preparationCoeff_support]
    exact hi
  have hj' : t j ∈ readoutInterval l := by
    rw [← readoutCoeff_support]
    exact hj
  have hj'' := readoutInterval_subset l hj'
  by_contra h
  have := hmono (show j ≤ i by omega)
  linarith [hi'.2, hj''.1]

theorem clock_passage_scheduling_at (D : SphereData)
    {t : ℕ → ℝ} {z : ℕ → Sphere}
    (hgate0 : ∀ z, 0 ≤ D.gate z) (hgate1 : ∀ z, D.gate z ≤ 1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (z n)))
    (hunbounded : ¬ BddAbove (Set.range t))
    (k : ℤ) (hstart : t 0 < 100 * (k : ℝ)) :
    HasScheduledPassageAt t k := by
  classical
  have hmono : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate0 _))
  have hstep : ∀ n, t (n + 1) ≤ t n + 1 := by
    intro n
    rw [hclock n]
    exact add_le_add_right (Clock.increment_le_one _ (hgate1 _)) _
  have hreach : ∀ A : ℝ, ∃ n, A ≤ t n := by
    intro A
    obtain ⟨x, ⟨n, rfl⟩, hn⟩ := not_bddAbove_iff.mp hunbounded A
    exact ⟨n, hn.le⟩
  obtain ⟨lo, hi, hlohi, hlo, hlo', hhi, hhi', hinside⟩ :=
    exists_complete_clock_passage hmono hstep hstart hreach
  let s := fun n => t n - 100 * (k : ℝ)
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (s i))
  have hmonoS : Monotone s := by
    intro i j hij
    exact sub_le_sub_right (hmono hij) _
  have hstepS : ∀ n, s (n + 1) ≤ s n + 1 := by
    intro n
    dsimp [s]
    linarith [hstep n]
  have hstartS : s lo < 1 := by dsimp [s]; linarith
  have hendS : 100 ≤ s hi := by dsimp [s]; linarith
  have hsupport : ∀ x, 0 < preparationCoeff x → 8 < x ∧ x < 12 := by
    intro x hx
    have hx' : x ∈ Function.support preparationCoeff := ne_of_gt hx
    rwa [preparationCoeff_support] at hx'
  have hunitS : ∀ n, 8 ≤ s n → s n ≤ 12 → s (n + 1) = s n + 1 := by
    intro n hn0 hn1
    have hbarrier : Clock.barrier (s n) = 1 := by
      apply Clock.barrier_plateau (by linarith) (by linarith)
      rw [abs_of_nonpos (by linarith : s n - 50 ≤ 0)]
      linarith
    have hperiod := (Clock.increment_periodic (D.gate (z n))).sub_int_mul_eq
      (x := t n) k
    have hinc : Clock.increment (t n) (D.gate (z n)) = 1 := by
      rw [← hperiod]
      have heq : t n - (k : ℝ) * 100 = s n := by dsimp [s]; ring
      rw [heq]
      exact Clock.increment_eq_one_of_barrier_eq_one hbarrier
    dsimp [s]
    rw [hclock n, hinc]
    ring
  have hprep := preparation_indices_properties hmonoS hstepS hlohi.le hstartS hendS
    hsupport (fun x hx0 hx1 => preparationCoeff_eq_one ⟨hx0, hx1⟩) hunitS
  change I.Nonempty ∧ I.card ≤ 5 ∧ (∃ i ∈ I, preparationCoeff (s i) = 1) at hprep
  obtain ⟨r, hr, hr0, hr1, hrbefore⟩ :=
    exists_reset_before_preparation hmonoS hstepS hlohi.le hstartS hendS
  have hread := exists_readout_plateau hmonoS hstepS hlohi.le hstartS hendS
    (fun x hx0 hx1 => readoutCoeff_cover ⟨hx0, hx1⟩)
  have hlobounds : 0 ≤ s lo ∧ s lo < 1 := by
    dsimp [s]
    constructor <;> linarith
  have hhibounds : 100 ≤ s hi ∧ s hi < 101 := by
    dsimp [s]
    constructor <;> linarith
  refine ⟨lo, hi, hlohi, hlobounds, hhibounds, ?_,
    hprep.1, hprep.2.1, hprep.2.2, ?_, hread⟩
  · intro n hnlo hnhi
    have hn := hinside n hnlo hnhi
    change 0 ≤ s n ∧ s n < 100
    dsimp [s]
    constructor <;> linarith [hn.1, hn.2]
  · refine ⟨r, hr, hr0, hr1, ?_⟩
    intro i hiI
    exact hrbefore i (hsupport _ (Finset.mem_filter.mp hiI).2).1

theorem unbounded_clock_passage_scheduling (D : SphereData)
    {t : ℕ → ℝ} {z : ℕ → Sphere}
    (hgate0 : ∀ z, 0 ≤ D.gate z) (hgate1 : ∀ z, D.gate z ≤ 1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (z n)))
    (hunbounded : ¬ BddAbove (Set.range t)) : HasScheduledPassage t := by
  obtain ⟨k, hk⟩ := exists_int_gt (t 0 / 100)
  exact ⟨k, clock_passage_scheduling_at D hgate0 hgate1 hclock hunbounded k (by linarith)⟩

theorem rawOrbit_hasScheduledPassageAt (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift D x t₀)))
    (k : ℤ) (hstart : t₀ < 100 * (k : ℝ)) :
    HasScheduledPassageAt (rawClockLift D x t₀) k :=
  clock_passage_scheduling_at D
    (fun z => (hgate z).1) (fun z => (hgate z).2)
    (rawClockLift_succ D x t₀ h₀) hunbounded k (by simpa using hstart)

theorem rawOrbit_hasScheduledPassage (D : SphereData)
    (hgate : ∀ z, D.gate z ∈ Set.Icc (0 : ℝ) 1)
    (x : RawManifold) (t₀ : ℝ)
    (h₀ : (t₀ : AddCircle (100 : ℝ)) = x.1)
    (hunbounded : ¬ BddAbove (Set.range (rawClockLift D x t₀))) :
    HasScheduledPassage (rawClockLift D x t₀) :=
  unbounded_clock_passage_scheduling D
    (fun z => (hgate z).1) (fun z => (hgate z).2)
    (rawClockLift_succ D x t₀ h₀) hunbounded

end Problem340.Construction

end

end OAI
