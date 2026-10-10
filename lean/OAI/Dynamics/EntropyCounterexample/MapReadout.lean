import OAI.Dynamics.EntropyCounterexample.MapPrediction
import OAI.Dynamics.EntropyCounterexample.RegisterEmbedded

namespace OAI

noncomputable section

namespace Problem340.Construction

local instance : Fact ((0 : ℝ) < 100) := ⟨by norm_num⟩

theorem rawMap_register_readout
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ z, 0 ≤ D.gate z) (hχ : ∀ z, D.cutoff z ∈ Set.Icc 0 1)
    (hS : ∀ z : ℂ, ‖z‖ ≤ 1 → D.saturation (z : Sphere) = z)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (ℓ : Fin 3) (s j : ℕ) (hsj : s ≤ j)
    (hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100)
    (hgain : ∀ n, s ≤ n → n < j → D.gain (t n) = D.L)
    (hreset : (x s).2.2 ℓ = ((0 : ℂ) : Sphere))
    (I : Finset ℕ) (hI : I ⊆ Finset.Ico s j) (hcard : I.card ≤ 5)
    (hprep : ∀ n ∈ Finset.Ico s j, n ∉ I → preparationCoeff (t n) = 0)
    (hread : readoutCoeff ℓ (t j) ≠ 0)
    (hpredict : ∀ n ∈ I,
      predictedClock D (j - n) (t n) (x n).2.1 = t j) :
    D.saturation ((x j).2.2 ℓ) =
        ∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) ∧
      ‖D.saturation ((x j).2.2 ℓ)‖ ≤ (1 / 2 : ℝ) ∧
      (x j).2.2 ℓ =
        ((∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) : ℂ) : Sphere) := by
  classical
  let c : ℕ → ℂ := fun n =>
    if n ∈ I then scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) else 0
  let a : ℕ → ℝ := fun n => periodicGain D (x n).1
  let u : ℕ → ℂ := fun n => input D ℓ (x n).1 (x n).2.1
  let v : ℕ → Sphere := fun n => (x n).2.2 ℓ
  have hrec : ∀ n, v (n + 1) =
      ((a n • D.saturation (v n) + u n : ℂ) : Sphere) := by
    intro n
    simp only [v, a, u, horbit n, rawMap, Complex.real_smul]
  have hagain : ∀ n, s ≤ n → n < j → a n = D.L := by
    intro n hsn hnj
    change AddCircle.liftIco 100 0 D.gain (x n).1 = D.L
    rw [← hlift n, AddCircle.liftIco_zero_coe_apply (hstrip n hsn hnj)]
    exact hgain n hsn hnj
  have hu : ∀ n, s ≤ n → n < j →
      u n = D.L ^ ((n : ℤ) + 1 - (j : ℤ)) • c n := by
    intro n hsn hnj
    by_cases hnI : n ∈ I
    · have hsignal := input_eq_delayed_signal_of_predicted_hit D hgate ℓ
        (t n) (t j) (x n).2.1 (hstrip n hsn hnj) n j hnj (hpredict n hnI) hread
      simpa only [u, hlift n, c, ite_eq_left hnI, add_comm (1 : ℤ) (n : ℤ)] using hsignal
    · have hα := hprep n (Finset.mem_Ico.mpr ⟨hsn, hnj⟩) hnI
      change input D ℓ (x n).1 (x n).2.1 = _
      rw [← hlift n, input_eq_baseInput_of_mem_Ico D ℓ (hstrip n hsn hnj)]
      simp [baseInput, hα, c, hnI]
  have hc : ∀ n ∈ I, ‖c n‖ ≤ (1 / 10 : ℝ) := by
    intro n hn
    simp only [c, ite_eq_left hn]
    exact norm_scheduledSignal_le D ℓ (t n) (t j) (x n).2.1 (j - n) (hχ _)
  have hsupp : ∀ n ∈ Finset.Ico s j, n ∉ I → c n = 0 := by
    intro n _ hn
    simp [c, hn]
  obtain ⟨_, hv, hsat, hnorm⟩ := Register.embedded_register_readout_of_identified_inputs
    D.L hL s j hsj a u c v (fun z : ℂ => (z : Sphere)) D.saturation
    hrec hagain hu I hI hcard hc hsupp hS hreset
  have hsum : (∑ n ∈ I, c n) =
      ∑ n ∈ I, scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [c, hn]
  exact ⟨hsat.trans hsum, hnorm, hv.trans (congrArg (fun z : ℂ => (z : Sphere)) hsum)⟩

def passagePreparationIndices (t : ℕ → ℝ) (s j : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico s j).filter (fun n => preparationCoeff (t n) ≠ 0)

theorem rawMap_register_readout_of_gain_profile
    (D : SphereData) (hL : 1 ≤ D.L)
    (hgate : ∀ z, 0 ≤ D.gate z) (hχ : ∀ z, D.cutoff z ∈ Set.Icc 0 1)
    (hS : ∀ z : ℂ, ‖z‖ ≤ 1 → D.saturation (z : Sphere) = z)
    (hgain : ∀ r ∈ Set.Icc 7 90, D.gain r = D.L)
    (x : ℕ → RawManifold) (horbit : ∀ n, x (n + 1) = rawMap D (x n))
    (t : ℕ → ℝ) (hlift : ∀ n, (t n : AddCircle (100 : ℝ)) = (x n).1)
    (hclock : ∀ n, t (n + 1) = t n + Clock.increment (t n) (D.gate (x n).2.1))
    (ℓ : Fin 3) (s j : ℕ) (hsj : s ≤ j) (hs : 7 ≤ t s)
    (hreset : (x s).2.2 ℓ = ((0 : ℂ) : Sphere))
    (hread : readoutCoeff ℓ (t j) ≠ 0) :
    D.saturation ((x j).2.2 ℓ) =
        ∑ n ∈ passagePreparationIndices t s j,
          scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) ∧
      ‖D.saturation ((x j).2.2 ℓ)‖ ≤ (1 / 2 : ℝ) ∧
      (x j).2.2 ℓ =
        ((∑ n ∈ passagePreparationIndices t s j,
          scheduledSignal D ℓ (t n) (t j) (x n).2.1 (j - n) : ℂ) : Sphere) := by
  classical
  let I := passagePreparationIndices t s j
  have ht : Monotone t := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hclock n]
    exact le_add_of_nonneg_right (Clock.increment_nonneg _ (hgate _))
  have hjmem : t j ∈ readoutInterval ℓ := by
    rwa [← readoutCoeff_support, Function.mem_support]
  have hjbounds := readoutInterval_subset ℓ hjmem
  have hstrip : ∀ n, s ≤ n → n < j → t n ∈ Set.Ico 0 100 := by
    intro n hsn hnj
    have hlow := hs.trans (ht hsn)
    have hupp := ht hnj.le
    exact ⟨by linarith, by linarith [hjbounds.2]⟩
  have hgain' : ∀ n, s ≤ n → n < j → D.gain (t n) = D.L := by
    intro n hsn hnj
    apply hgain
    exact ⟨hs.trans (ht hsn), by have hupp := ht hnj.le; linarith [hjbounds.2]⟩
  have hI : I ⊆ Finset.Ico s j := by
    intro n hn
    exact (Finset.mem_filter.mp hn).1
  have hcard : I.card ≤ 5 := by
    apply clock_preparation_card_le_five ht
    · intro n hn8 hn12
      rw [hclock n]
      have hb : Clock.barrier (t n) = 1 := by
        apply Clock.barrier_plateau (by linarith) (by linarith)
        rw [abs_of_nonpos (by linarith)]
        linarith
      rw [Clock.increment_eq_one_of_barrier_eq_one hb]
    · intro n hn
      have hn' := (Finset.mem_filter.mp hn).2
      change t n ∈ Set.Ioo 8 12
      rwa [← preparationCoeff_support, Function.mem_support]
  have hprep : ∀ n ∈ Finset.Ico s j, n ∉ I → preparationCoeff (t n) = 0 := by
    intro n hn hnot
    by_contra hα
    exact hnot (Finset.mem_filter.mpr ⟨hn, hα⟩)
  have hpredict : ∀ n ∈ I, predictedClock D (j - n) (t n) (x n).2.1 = t j := by
    intro n hn
    obtain ⟨hsn, hnj⟩ := Finset.mem_Ico.mp (hI hn)
    exact rawMap_predictedClock_at_readout D x horbit t ht hlift hclock ℓ n j hnj.le
      (hstrip n hsn hnj).1 hread
  exact rawMap_register_readout D hL hgate hχ hS x horbit t hlift ℓ s j hsj hstrip
    hgain' hreset I hI hcard hprep hread hpredict

end Problem340.Construction

end

end OAI
