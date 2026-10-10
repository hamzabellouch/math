import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdges
import OAI.Probability.CriticalPercolation.ProductMeasure.ForceClosed

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

theorem search_contact_moments (G : BondGraph V E) (order : List (Dart V E))
    (ho : Exhaustive G order) (O B : Set V) (hB : B ⊆ O) (a : V) (ha : a ∉ O)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let C := G.cutEdges O
    let A := (search G order a B).contactScore p C F w
    expect (forceClosed w C) A = prob w F ∧
      expect (forceClosed w C) (fun ω => (A ω)^2) ≤ 3 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let C := G.cutEdges O
  let v := forceClosed w C
  let T := search G order a B
  let H := fun st : State V E => ∃ b ∈ st.reached, b ∈ B
  have hw := homogeneous_normalized w p h0 h1
  have hn : ∀ e b, 0 ≤ w e b := fun e b => (homogeneous_positive w hp h0 h1 e b).le
  have hv := forceClosed_normalized w C hw
  have hnv := forceClosed_nonneg w C hn
  have hvalid : T.Valid ∅ := compile_valid G order B _ _ _
  have hf : Fresh w p ∅ := fun e _ => ⟨h0 e,h1 e⟩
  have hc : ClosedFresh v p C ∅ := by
    intro e _
    by_cases heC : e ∈ C <;> simp [v,forceClosed,heC,h0,h1]
  have hT : ∀ ω, density w ω ≠ 0 → (F ω ↔ H (T.run (fun e => decide (ω e)))) := by
    intro ω _
    have hs := search_decides G order ho a B (fun e => decide (ω e))
    have heq : {e | decide (ω e) = true} = ω := by
      ext e
      change decide (ω e) = true ↔ ω e
      simp
    simpa only [heq] using hs.symm
  have hac : ∀ ω, density v ω ≠ 0 → density w ω ≠ 0 :=
    fun ω _ => homogeneous_support w hp h0 h1 ω
  have hfail : ∀ ω, density v ω ≠ 0 → ¬F ω := by
    intro ω hω ⟨b,hb,hab⟩
    exact G.not_reachable_of_cut_closed O ω (forceClosed_support w C ω hω) ha (hB hb) hab
  have hnorm := contact_normalization T ∅ hvalid p C F H w v hw hv hf hc hT hac hfail
  have hmono : ∀ s t : Set E, s ⊆ t → F s → F t := by
    rintro s t hst ⟨b,hb,hab⟩
    exact ⟨b,hb,hab.mono (G.openGraph_mono hst)⟩
  have hsecond := contact_second_le_three_mean T ∅ hvalid hp C F hmono w v hw hv hn hnv hf hc
  rw [hnorm] at hsecond
  exact ⟨hnorm,hsecond.trans (by linarith [prob_le_one w hw hn F])⟩

end CriticalPercolation.LazyDFS

end
end

end OAI
