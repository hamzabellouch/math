import OAI.Dynamics.EntropyCounterexample.MapData
import OAI.Dynamics.EntropyCounterexample.MapPassagePhase

namespace OAI

noncomputable section

namespace Problem340.Construction

theorem concreteMap_passage_square_le
    (L : ℝ) (hL : 2 < L) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister (concreteData L hL) x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight (concreteData L hL) t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = concreteMap L hL (x n)) :
    ∀ n, s ≤ n → n < N → ‖z n‖ ^ 2 ≤ ‖z (n + 1)‖ := by
  exact rawMap_passage_square_le (concreteData L hL) x t z I s K N
    (fun u => (concrete_cutoff_mem_Icc L hL u).1) hzs hz hI hearly hregister hstep

theorem concreteMap_passage_escape
    (L : ℝ) (hL : 2 < L) (x : ℕ → RawManifold) (t : ℕ → ℝ) (z : ℕ → ℂ)
    (I : Finset ℕ) (s K N : ℕ)
    (hzs : z s ≠ 0)
    (hz : ∀ n, s ≤ n → n ≤ N → (z n : Sphere) = (x n).2.1)
    (hI : ∀ i ∈ I, s ≤ i ∧ i < K)
    (hearly : ∀ n, s ≤ n → n < K → ∀ l : Fin 3, orbitReadoutCoeff x n l = 0)
    (hregister : ∀ n, s ≤ n → n < N → ∀ l : Fin 3,
      orbitReadoutCoeff x n l ≠ 0 →
      orbitSaturatedRegister (concreteData L hL) x n l = ((orbitReadoutCoeff x n l / 10 : ℝ) : ℂ) *
        ∑ i ∈ I, (passageWeight (concreteData L hL) t z i : ℂ) *
          PassagePhase.phase (z i) ^ (2 ^ (n - i + 1)))
    (hstep : ∀ n, s ≤ n → n < N → x (n + 1) = concreteMap L hL (x n))
    (hKN : K ≤ N)
    (hhalf : ∀ i ∈ I, (1 / 2 : ℝ) < ‖z i‖)
    (hprep : ∃ i ∈ I, preparationCoeff (t i) = 1)
    (hread : ∃ j, s ≤ j ∧ j < N ∧ ∃ l : Fin 3, orbitReadoutCoeff x j l = 1) :
    ∃ n, s ≤ n ∧ n ≤ N ∧ 1 < ‖z n‖ := by
  apply rawMap_passage_escape (concreteData L hL) x t z I s K N
    (fun u => (concrete_cutoff_mem_Icc L hL u).1) hzs hz hI hearly hregister hstep
    hKN hhalf _ hprep hread
  intro u hlo hhi
  exact SphereCutoffs.affinePreparationCutoff_eq_one hlo hhi

end Problem340.Construction

end

end OAI
