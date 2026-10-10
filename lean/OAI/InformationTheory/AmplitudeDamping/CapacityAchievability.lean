import OAI.InformationTheory.AmplitudeDamping.CodingAsymptotics

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix Filter
namespace GAD

/-- Direct operational coding for the phase pair; conditional and global typical subspaces
and a sequential collective POVM, rather than an assumed coding theorem. -/
theorem phase_rate_achievable (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    {r : ℝ} (hr : 0 ≤ r) (hrχ : r < objective γ ν p) :
    Achievable γ ν (r/Real.log 2) := by
  classical
  obtain ⟨q,U,hq,hs,hphase,hent⟩ := phase_spectral γ ν hγ hν hp
  let δ := (objective γ ν p-r)/4
  let K := 9*logVariance (meanPhaseWeights γ ν p)+8*logVariance q
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hb : 0 < objective γ ν p-2*δ-r := by dsimp [δ]; linarith
  have hex (n : ℕ) : ∃ C : Code n, 0 < n →
      C.messages=codingMessages r n ∧ averageError γ ν C ≤
        K/((n:ℝ)*δ^2)+4*(codingMessages r n:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    by_cases hn : 0 < n
    · obtain ⟨C,hC,he⟩ := exists_phase_code γ ν hγ hν hp q U hq hs hphase hent hδ hn
        (codingMessages r n) (codingMessages_pos r n)
      exact ⟨C,fun _ ↦ ⟨hC,he⟩⟩
    · exact ⟨trivialCode n,fun hn' ↦ (hn hn').elim⟩
  choose C hC using hex
  refine ⟨C,?_,?_⟩
  · apply squeeze_zero' (Filter.Eventually.of_forall (fun n ↦ averageError_nonneg γ ν hγ hν (C n)))
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : 0 < n := by omega
      exact ((hC n hn0).2).trans (add_le_add le_rfl
        (coding_cross_bound hr (objective γ ν p-2*δ) n))
    · exact coding_error_tendsto K δ hb
  · intro ε hε
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    rw [(hC n hn0).1]
    exact (sub_le_self _ hε.le).trans (codingMessages_rate r hn0)

end GAD

end

end OAI
