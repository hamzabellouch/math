import OAI.Analysis.IrrationalRotation.Analysis.VonNeumannStrongClosure
import Mathlib.Analysis.VonNeumannAlgebra.Basic

namespace OAI

noncomputable section
open Filter Topology

namespace Invariant233.BicommutantDensity

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def strongView (T : H →L[ℂ] H) : H →Lₚₜ[ℂ] H :=
  UniformConvergenceCLM.ofFun (RingHom.id ℂ) H {s : Set H | s.Finite} T

@[simp] theorem strongView_apply (T : H →L[ℂ] H) (x : H) : strongView T x = T x := rfl
@[simp] theorem underlying_apply (T : H →Lₚₜ[ℂ] H) (x : H) :
    strongOperatorUnderlying T x = T x := rfl

@[simp] theorem underlying_strongView (T : H →L[ℂ] H) :
    strongOperatorUnderlying (strongView T) = T := rfl
@[simp] theorem strongView_underlying (T : H →Lₚₜ[ℂ] H) :
    strongView (strongOperatorUnderlying T) = T := rfl

theorem mem_strongClosure_iff (S : Set (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    strongView T ∈ closure {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ S} ↔
      ∀ (s : Set H), s.Finite → ∀ ε : ℝ, 0 < ε →
        ∃ A ∈ S, ∀ x ∈ s, ‖A x - T x‖ < ε := by
  have hb := (PointwiseConvergenceCLM.hasBasis_nhds_zero_of_basis
    (σ := RingHom.id ℂ) (E := H) (Metric.nhds_basis_ball (x := (0 : H)))).nhds_of_zero
      (strongView T)
  rw [mem_closure_iff_nhds_basis hb]
  constructor
  · intro h s hs ε hε
    obtain ⟨A, hA, hclose⟩ := h (s, ε) ⟨hs, hε⟩
    refine ⟨strongOperatorUnderlying A, hA, ?_⟩
    intro x hx
    have hx' := hclose x hx
    simpa only [Set.mem_ofPred_eq, Metric.mem_ball, dist_zero_right,
      sub_apply, strongView_apply, underlying_apply] using hx'
  · intro h ⟨s, ε⟩ ⟨hs, hε⟩
    obtain ⟨A, hA, hclose⟩ := h s hs ε hε
    refine ⟨strongView A, hA, ?_⟩
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right, sub_apply,
      strongView_apply] using hclose x hx

theorem isClosed_strongCentralizer (S : Set (H →L[ℂ] H)) :
    IsClosed {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ Set.centralizer S} :=
  centralizer_stronglyClosed S

theorem strongClosure_subset_bicommutant (S : Set (H →L[ℂ] H)) :
    closure {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈ S} ⊆
      {B : H →Lₚₜ[ℂ] H | strongOperatorUnderlying B ∈
        Set.centralizer (Set.centralizer S)} := by
  apply closure_minimal
  · intro B hB A hA
    exact (hA _ hB).symm
  · exact isClosed_strongCentralizer _

end Invariant233.BicommutantDensity

end

end OAI
