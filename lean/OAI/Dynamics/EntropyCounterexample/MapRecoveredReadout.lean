import OAI.Dynamics.EntropyCounterexample.MapReadout
import OAI.Dynamics.EntropyCounterexample.MapPassagePhase

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem scheduledSignal_eq_passageWeight
    (D : SphereData) (l : Fin 3) (t : ℕ → ℝ) (z : ℕ → ℂ) (i j : ℕ) :
    scheduledSignal D l (t i) (t j) (z i : Sphere) (j - i) =
      ((readoutCoeff l (t j) / 10 : ℝ) : ℂ) *
        ((passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (j - i + 1))) := by
  simp only [scheduledSignal, passageWeight, phase_coe, PassagePhase.phase,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  ring

theorem sum_scheduledSignal_eq_passageWeight
    (D : SphereData) (l : Fin 3) (x : ℕ → RawManifold)
    (t : ℕ → ℝ) (z : ℕ → ℂ) (I : Finset ℕ) (j : ℕ)
    (hz : ∀ i ∈ I, (z i : Sphere) = (x i).2.1) :
    (∑ i ∈ I, scheduledSignal D l (t i) (t j) (x i).2.1 (j - i)) =
      ((readoutCoeff l (t j) / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (j - i + 1)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hz i hi]
  exact scheduledSignal_eq_passageWeight D l t z i j

theorem orbitReadoutCoeff_eq_of_mem_Ico
    (x : ℕ → RawManifold) (t : ℕ → ℝ) (j : ℕ) (l : Fin 3)
    (hlift : (t j : AddCircle (100 : ℝ)) = (x j).1)
    (hj : t j ∈ Set.Ico 0 100) :
    orbitReadoutCoeff x j l = readoutCoeff l (t j) := by
  change AddCircle.liftIco 100 0 (readoutCoeff l) (x j).1 = _
  rw [← hlift, AddCircle.liftIco_zero_coe_apply hj]

theorem rawMap_recovered_readout_of_gain_profile
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ u, 0 ≤ D.gate u) (hχ : ∀ u, D.cutoff u ∈ Set.Icc 0 1)
    (hS : ∀ u : ℂ, ‖u‖ ≤ 1 → D.saturation (u : Sphere) = u)
    (hgain : ∀ r ∈ Set.Icc 7 90, D.gain r = D.L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (z : ℕ → ℂ) (I : Finset ℕ) (l : Fin 3) (s j : ℕ)
    (hsj : s ≤ j) (hs : 7 ≤ t s)
    (hreset : (x s).2.2 l = ((0 : ℂ) : Sphere))
    (hI : passagePreparationIndices t s j = I)
    (hz : ∀ i ∈ I, (z i : Sphere) = (x i).2.1)
    (hj : t j ∈ Set.Ico 0 100)
    (hread : orbitReadoutCoeff x j l ≠ 0) :
    orbitSaturatedRegister D x j l = ((orbitReadoutCoeff x j l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (passageWeight D t z i : ℂ) *
        PassagePhase.phase (z i) ^ (2 ^ (j - i + 1)) := by
  have hcoeff := orbitReadoutCoeff_eq_of_mem_Ico x t j l (hlift j) hj
  have hread' : readoutCoeff l (t j) ≠ 0 := by rwa [hcoeff] at hread
  have h := (rawMap_register_readout_of_gain_profile D hL hgate hχ hS hgain
    x horbit t hlift hclock l s j hsj hs hreset hread').1
  rw [hI] at h
  change D.saturation ((x j).2.2 l) = _
  rw [h, hcoeff]
  exact sum_scheduledSignal_eq_passageWeight D l x t z I j hz

theorem passagePreparationIndices_eq_of_complete_support
    (t : ℕ → ℝ) (ht : Monotone t) (I : Finset ℕ)
    (hI : ∀ i, i ∈ I ↔ preparationCoeff (t i) ≠ 0)
    (s j : ℕ) (hs : t s ≤ 8) (l : Fin 3)
    (hread : readoutCoeff l (t j) ≠ 0) :
    passagePreparationIndices t s j = I := by
  classical
  have hjmem : t j ∈ readoutInterval l := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset l hjmem
  apply Finset.ext
  intro i
  constructor
  · intro hi
    exact (hI i).mpr (Finset.mem_filter.mp hi).2
  · intro hi
    have hprep := (hI i).mp hi
    have hiprep : t i ∈ Set.Ioo 8 12 := by
      rwa [← preparationCoeff_support, Function.mem_support]
    have hsi : s ≤ i := by
      by_contra h
      have htime := ht (show i ≤ s by omega)
      linarith [hiprep.1]
    have hij : i < j := by
      by_contra h
      have htime := ht (show j ≤ i by omega)
      linarith [hiprep.2, hjbounds.1]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hsi, hij⟩, hprep⟩

theorem rawMap_recovered_readout_of_complete_support
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ u, 0 ≤ D.gate u) (hχ : ∀ u, D.cutoff u ∈ Set.Icc 0 1)
    (hS : ∀ u : ℂ, ‖u‖ ≤ 1 → D.saturation (u : Sphere) = u)
    (hgain : ∀ r ∈ Set.Icc 7 90, D.gain r = D.L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (z : ℕ → ℂ) (I : Finset ℕ)
    (hI : ∀ i, i ∈ I ↔ preparationCoeff (t i) ≠ 0)
    (hz : ∀ i ∈ I, (z i : Sphere) = (x i).2.1)
    (s : ℕ) (hs : t s ∈ Set.Icc 7 8)
    (hreset : ∀ l : Fin 3, (x s).2.2 l = ((0 : ℂ) : Sphere))
    (j : ℕ) (hj : t j ∈ Set.Ico 0 100) (l : Fin 3)
    (hread : orbitReadoutCoeff x j l ≠ 0) :
    orbitSaturatedRegister D x j l = ((orbitReadoutCoeff x j l / 10 : ℝ) : ℂ) *
      ∑ i ∈ I, (passageWeight D t z i : ℂ) *
        PassagePhase.phase (z i) ^ (2 ^ (j - i + 1)) := by
  have ht : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate _))
  have hcoeff := orbitReadoutCoeff_eq_of_mem_Ico x t j l (hlift j) hj
  have hread' : readoutCoeff l (t j) ≠ 0 := by rwa [hcoeff] at hread
  have hjmem : t j ∈ readoutInterval l := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset l hjmem
  have hsj : s ≤ j := by
    by_contra h
    have htime := ht (show j ≤ s by omega)
    linarith [hs.2, hjbounds.1]
  exact rawMap_recovered_readout_of_gain_profile D hL hgate hχ hS hgain
    x horbit t hlift hclock z I l s j hsj hs.1 (hreset l)
    (passagePreparationIndices_eq_of_complete_support t ht I hI s j hs.2 l hread')
    hz hj hread

end Problem340.Construction

end

end OAI
