import OAI.InformationTheory.AmplitudeDamping.PhaseProducts

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem holevo_formula (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) (n : ℕ) :
    holevo γ ν n = (n:ℝ)/Real.log 2*objective γ ν p := by
  have hv := phaseEnsemble_value n γ ν p hp.1
  rw [phaseValue_formula n γ ν hγ hν hp.1] at hv
  apply le_antisymm
  · apply csSup_le
    · exact ⟨ensembleValue γ ν (phaseEnsemble n p hp.1), Set.mem_range_self _⟩
    · rintro _ ⟨E,rfl⟩
      exact ensembleValue_upper γ ν hγ hν E hp
  · rw [← hv]
    apply le_csSup
    · exact ⟨_, fun _ hx ↦ by obtain ⟨E,rfl⟩ := hx; exact ensembleValue_upper γ ν hγ hν E hp⟩
    · exact Set.mem_range_self _

theorem holevo_additive (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    holevo γ ν n = (n:ℝ)*holevo γ ν 1 := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  rw [holevo_formula γ ν hγ hν ⟨hp,hmax⟩ n,holevo_formula γ ν hγ hν ⟨hp,hmax⟩ 1]
  norm_num
  ring

theorem holevo_maximizer (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) :
    ∃ p : ℝ, Maximizes γ ν p ∧
      ∀ n : ℕ, 1 ≤ n → holevo γ ν n = (n:ℝ)/Real.log 2*objective γ ν p := by
  obtain ⟨p,hp,hmax⟩ := exists_maximizer γ ν
  exact ⟨p,⟨hp,hmax⟩,fun n _ ↦ holevo_formula γ ν hγ hν ⟨hp,hmax⟩ n⟩

theorem phase_attainment (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : Maximizes γ ν p) (n : ℕ) :
    (∀ s : Basis n, IsState (phaseState p s)) ∧ holevo γ ν n = phaseValue γ ν p n := by
  exact ⟨fun s ↦ phaseState_state hp.1 s, by
    rw [holevo_formula γ ν hγ hν hp n,phaseValue_formula n γ ν hγ hν hp.1]⟩

end GAD

end

end OAI
