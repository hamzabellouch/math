import OAI.Probability.SwitchChain.SwitchPairFiber
import OAI.Probability.SwitchChain.OrthogonalPairResampling

namespace OAI

noncomputable section

namespace Problem315

attribute [local instance] Classical.propDecidable

theorem sameFiber_of_same_side {n : ℕ} {d : Fin n → ℕ}
    (A : Finset (Fin n)) (G H : GraphState n d)
    (hsame : ∀ u v, (u ∈ A ↔ v ∈ A) → (G.val.Adj u v ↔ H.val.Adj u v)) :
    PairResampling.SameFiber A G.val H.val := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro u hu v hv
    exact hsame u v (by simp [hu, hv])
  · intro w hw
    apply SwitchPairFiber.degree_into_eq G.val H.val A w
    · exact (G.property w).trans (H.property w).symm
    · intro v hv
      exact hsame w v (by simp [hw, hv])

theorem switchStep_sameFiber {n : ℕ} {d : Fin n → ℕ}
    {G H : GraphState n d} (hstep : SwitchStep n d G H) :
    ∃ A ∈ PairResampling.pairs n, PairResampling.SameFiber A G.val H.val := by
  obtain ⟨p, hp, hresult⟩ := hstep
  obtain ⟨A, hA, hAS, hfrozen⟩ := SwitchPairFiber.exists_frozen_cut p hp
  refine ⟨A, ?_, sameFiber_of_same_side A G H ?_⟩
  · simp [PairResampling.pairs, hA]
  · intro u v hside
    have h := hfrozen u v hside
    rw [hresult] at h
    exact h.symm

theorem generator_kernel_constant_on_paths {n : ℕ} {d : Fin n → ℕ}
    (f : PairResampling.StateSpace n d) (hf : PairResampling.generator n d f = 0)
    {G H : GraphState n d} (hpath : Relation.ReflTransGen (SwitchStep n d) G H) :
    f G = f H := by
  have hfib := (PairResampling.generator_eq_zero_iff f).mp hf
  induction hpath with
  | refl => rfl
  | @tail H K hpath hstep ih =>
    obtain ⟨A, hA, hGH⟩ := switchStep_sameFiber hstep
    exact ih.trans (hfib A hA H K hGH)

theorem generator_eq_zero_iff_constant_of_connected {n : ℕ} {d : Fin n → ℕ}
    (hconn : ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H)
    (f : PairResampling.StateSpace n d) :
    PairResampling.generator n d f = 0 ↔ ∀ G H, f G = f H := by
  constructor
  · intro hf G H
    exact generator_kernel_constant_on_paths f hf (hconn G H)
  · intro hf
    apply (PairResampling.generator_eq_zero_iff f).mpr
    intro A hA G H hGH
    exact hf G H

end Problem315

end

end OAI
