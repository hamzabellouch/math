import OAI.Dynamics.EntropyCounterexample.Map
import OAI.Dynamics.EntropyCounterexample.PassagePhaseInterval

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem finite_main_step_of_rawMap (D : SphereData)
    {x y : RawManifold} {z w : ℂ}
    (hstep : y = rawMap D x)
    (hz : (z : Sphere) = x.2.1) (hw : (w : Sphere) = y.2.1) :
    w = z ^ 2 + readout D x.1 x.2.2 := by
  apply OnePoint.coe_injective
  calc
    (w : Sphere) = y.2.1 := hw
    _ = (rawMap D x).2.1 := congrArg (fun p : RawManifold => p.2.1) hstep
    _ = perturbedSquare (readout D x.1 x.2.2) x.2.1 := rfl
    _ = ((z ^ 2 + readout D x.1 x.2.2 : ℂ) : Sphere) := by rw [← hz]; rfl

def passageWeight (D : SphereData) (t : ℕ → ℝ) (z : ℕ → ℂ) (i : ℕ) : ℝ :=
  preparationCoeff (t i) * D.cutoff ((z i : ℂ) : Sphere)

def orbitReadoutCoeff (x : ℕ → RawManifold) (n : ℕ) (l : Fin 3) : ℝ :=
  periodicReadout l (x n).1

def orbitSaturatedRegister (D : SphereData) (x : ℕ → RawManifold)
    (n : ℕ) (l : Fin 3) : ℂ := D.saturation ((x n).2.2 l)

lemma passageWeight_nonneg (D : SphereData) (hχ : ∀ z, 0 ≤ D.cutoff z)
    (t : ℕ → ℝ) (z : ℕ → ℂ) (i : ℕ) : 0 ≤ passageWeight D t z i :=
  mul_nonneg (preparationCoeff_nonneg _) (hχ _)

theorem rawMap_passage_phase
    (D : SphereData) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hχ : ∀ z, 0 ≤ D.cutoff z) (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister D x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = rawMap D (x n)) :
    ∀ n, s ≤ n → n ≤ N → z n ≠ 0 ∧
      PassagePhase.phase (z n) = PassagePhase.phase (z s) ^ (2 ^ (n - s)) := by
  apply PassagePhase.passage_phase_interval I Finset.univ z (passageWeight D t z)
    (orbitReadoutCoeff x) (orbitSaturatedRegister D x) s K N hzs hI
  · intro i _
    exact passageWeight_nonneg D hχ t z i
  · intro n hsn hn l _
    exact hearly n hsn hn l
  · intro n hsn hn l _ hb
    exact hregister n hsn hn l hb
  · intro n hsn hn
    exact finite_main_step_of_rawMap D (hstep n hsn hn)
      (hz n hsn hn.le) (hz (n + 1) (by omega) (by omega))

theorem rawMap_passage_square_le
    (D : SphereData) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hχ : ∀ z, 0 ≤ D.cutoff z) (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister D x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = rawMap D (x n)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  apply PassagePhase.passage_square_le_interval I Finset.univ z (passageWeight D t z)
    (orbitReadoutCoeff x) (orbitSaturatedRegister D x) s K N hzs hI
  · intro i _
    exact passageWeight_nonneg D hχ t z i
  · intro n hsn hn l _
    exact hearly n hsn hn l
  · intro n hsn hn l _ hb
    exact hregister n hsn hn l hb
  · intro n hsn hn
    exact finite_main_step_of_rawMap D (hstep n hsn hn)
      (hz n hsn hn.le) (hz (n + 1) (by omega) (by omega))

theorem rawMap_passage_escape
    (D : SphereData) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hχ : ∀ z, 0 ≤ D.cutoff z) (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister D x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight D t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = rawMap D (x n))
    (hKN : K ≤ N)
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hcutoff : ∀ u : ℂ, (1 / 2 : ℝ) ≤ ‖u‖ → ‖u‖ ≤ 1 → D.cutoff (u : Sphere) = 1)
    (hprep : ∃ i ∈ I, preparationCoeff (t i) = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l : Fin 3, orbitReadoutCoeff x j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  refine PassagePhase.passage_escape_of_preparation_plateau I Finset.univ z
    (passageWeight D t z) (orbitReadoutCoeff x) (orbitSaturatedRegister D x)
    s K N hzs hI ?_ ?_ ?_ ?_ (fun i => preparationCoeff (t i))
    (fun u => D.cutoff (u : Sphere)) hKN ?_ hhalf hcutoff hprep ?_
  · intro i _
    exact passageWeight_nonneg D hχ t z i
  · intro n hsn hn l _
    exact hearly n hsn hn l
  · intro n hsn hn l _ hb
    exact hregister n hsn hn l hb
  · intro n hsn hn
    exact finite_main_step_of_rawMap D (hstep n hsn hn)
      (hz n hsn hn.le) (hz (n + 1) (by omega) (by omega))
  · intro i _
    rfl
  · obtain ⟨j, hsj, hj, l, hl⟩ := hread
    exact ⟨j, hsj, hj, l, Finset.mem_univ _, hl⟩

end Problem340.Construction

end

end OAI
