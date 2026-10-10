import OAI.Dynamics.EntropyCounterexample.MapPassage
import OAI.Dynamics.EntropyCounterexample.MapPassagePhase
import OAI.Dynamics.EntropyCounterexample.MapPreparationReset

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem preparation_phase_window
    {t : ℕ → ℝ} (hmono : Monotone t) (I : Finset ℕ) (hne : I.Nonempty)
    {lo hi : ℕ} (hI : ∀ i ∈ I, lo ≤ i ∧ i < hi)
    (hprep : ∀ i ∈ I, preparationCoeff (t i) ≠ 0) :
    ∃ s K : ℕ, s ∈ I ∧ lo ≤ s ∧ s < K ∧ K ≤ hi ∧
      (∀ i ∈ I, s ≤ i ∧ i < K) ∧
      (∀ n, s ≤ n → n < K → ∀ l : Fin 3, readoutCoeff l (t n) = 0) ∧
      t s ∈ Set.Ioo 8 12 := by
  classical
  let s := I.min' hne
  let K := I.max' hne + 1
  have hs : s ∈ I := Finset.min'_mem I hne
  have hmax : I.max' hne ∈ I := Finset.max'_mem I hne
  have hsmax : s ≤ I.max' hne := Finset.min'_le_max' I hne
  have hK : K ≤ hi := by
    have := (hI _ hmax).2
    dsimp [K]
    omega
  refine ⟨s, K, hs, (hI _ hs).1, by dsimp [K]; omega, hK, ?_, ?_, ?_⟩
  · intro i hiI
    have hmin : s ≤ i := Finset.min'_le I i hiI
    have hmax' : i ≤ I.max' hne := Finset.le_max' I i hiI
    exact ⟨hmin, by dsimp [K]; omega⟩
  · intro n _ hn l
    by_contra hb
    have hbefore := preparation_before_readout hmono (hprep _ hmax) hb
    dsimp [K] at hn
    omega
  · rw [← preparationCoeff_support]
    exact hprep _ hs

theorem orbitReadoutCoeff_eq_of_clock_lift
    (x : ℕ → RawManifold) (t : ℕ → ℝ)
    (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (n : ℕ) (hn : t n ∈ Set.Ico (0 : ℝ) 100) (l : Fin 3) :
    orbitReadoutCoeff x n l = readoutCoeff l (t n) := by
  unfold orbitReadoutCoeff
  rw [← hclock n]
  exact AddCircle.liftIco_coe_apply (p := (100 : ℝ)) (a := 0)
    (by simpa only [zero_add] using hn)

theorem complete_passage_phase_window
    (x : ℕ → RawManifold) (t : ℕ → ℝ) (hmono : Monotone t)
    (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (lo hi : ℕ)
    (hinside : ∀ n, lo ≤ n → n < hi → t n ∈ Set.Ico (0 : ℝ) 100)
    (hne : ((Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))).Nonempty) :
    let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))
    ∃ s K : ℕ, s ∈ I ∧ lo ≤ s ∧ s < K ∧ K ≤ hi ∧
      (∀ i ∈ I, s ≤ i ∧ i < K) ∧
      (∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0) ∧
      t s ∈ Set.Ioo 8 12 := by
  classical
  let I := (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i))
  have hI : ∀ i ∈ I, lo ≤ i ∧ i < hi := by
    intro i hiI
    exact Finset.mem_Ico.mp (Finset.mem_filter.mp hiI).1
  have hp : ∀ i ∈ I, preparationCoeff (t i) ≠ 0 := by
    intro i hiI
    exact ne_of_gt (Finset.mem_filter.mp hiI).2
  obtain ⟨s, K, hs, hlos, hsK, hKhi, hIK, hearly, hts⟩ :=
    preparation_phase_window hmono I hne hI hp
  refine ⟨s, K, hs, hlos, hsK, hKhi, hIK, ?_, hts⟩
  intro n hsn hnK l
  rw [orbitReadoutCoeff_eq_of_clock_lift x t hclock n
    (hinside n (by omega) (by omega)) l]
  exact hearly n hsn hnK l

theorem preparation_indices_eq_after_first
    (t : ℕ → ℝ) (lo s hi : ℕ) (hlos : lo ≤ s)
    (hfirst : ∀ i ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)),
      s ≤ i) :
    (Finset.Ico s hi).filter (fun i => 0 < preparationCoeff (t i)) =
      (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)) := by
  classical
  ext i
  constructor
  · intro hiI
    obtain ⟨hiI, hp⟩ := Finset.mem_filter.mp hiI
    obtain ⟨hsi, hihi⟩ := Finset.mem_Ico.mp hiI
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hlos.trans hsi, hihi⟩, hp⟩
  · intro hiI
    have hsi := hfirst i hiI
    obtain ⟨hiI, hp⟩ := Finset.mem_filter.mp hiI
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hsi, (Finset.mem_Ico.mp hiI).2⟩, hp⟩

theorem complete_passage_register_reset_at_first_preparation
    (L : ℝ) (hL : 2 < L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = concreteMap L hL (x n))
    (t : ℕ → ℝ) (hclock : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (lo hi r s : ℕ) (hlor : lo ≤ r) (hrs : r + 1 ≤ s) (hshi : s < hi)
    (hreset : t r ∈ Set.Icc 2 5)
    (hinside : ∀ n, lo ≤ n → n < hi → t n ∈ Set.Ico (0 : ℝ) 100)
    (hfirst : ∀ i ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)),
      s ≤ i) :
    ∀ l : Fin 3, (x s).2.2 l = ((0 : ℂ) : Sphere) := by
  apply concreteMap_register_zero_after_reset_before_preparation
    L hL x horbit t hclock r s hrs hreset
  · intro n hrn hns
    exact hinside n (by omega) (by omega)
  · intro n hrn hns
    by_contra hp
    have hp' : 0 < preparationCoeff (t n) :=
      lt_of_le_of_ne (preparationCoeff_nonneg _) (Ne.symm hp)
    have hnI : n ∈ (Finset.Ico lo hi).filter (fun i => 0 < preparationCoeff (t i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp'⟩
    have := hfirst n hnI
    omega

end Problem340.Construction

end

end OAI
