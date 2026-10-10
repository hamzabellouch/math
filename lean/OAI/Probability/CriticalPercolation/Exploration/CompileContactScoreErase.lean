import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClosedFresh
import OAI.Probability.CriticalPercolation.GraphGeometry.CutEdgesSubsetIncident
import OAI.Probability.CriticalPercolation.ProductMeasure.ExposureLaw

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

variable {V E : Type*} [Fintype E] [DecidableEq V] [DecidableEq E]

theorem compile_contactScore_erase (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (fuel : ℕ) (st : State V E) (stack : List (Dart V E))
    (p : ℝ) (F : Set E → Prop) (w : E → Prop → ℝ) (ω : Set E)
    (hc : ∀ e ∈ G.cutEdges O, ¬ω e) (hs : ∀ v ∈ st.reached, v ∉ O) :
    (compile G order B fuel st stack).contactScore p (G.cutEdges O) F w ω =
      (compile G order B fuel st stack).contactScore p (G.cutEdges O) F w (G.eraseVertices ω O) := by
  induction fuel generalizing st stack w with
  | zero => rfl
  | succ n ih =>
    rw [compile.eq_def]
    dsimp only
    split_ifs with hh
    · rfl
    · cases stack with
      | nil => rfl
      | cons d rest =>
        dsimp only
        split_ifs with hd
        · exact ih st rest w hs
        · have htail : d.1 ∈ st.reached := by
            by_contra h; exact hd (Or.inr (Or.inr (Or.inl h)))
          have he : G.ends d.2.1 = s(d.1,d.2.2) := by
            by_contra h; exact hd (Or.inr (Or.inr (Or.inr h)))
          have hbit := G.eraseVertices_agree_of_cutClosed O ω hc (hs d.1 htail) he
          simp only [contactScore,hbit]
          congr 1
          by_cases hb : ω d.2.1
          · have hb' : G.eraseVertices ω O d.2.1 := by rwa [← hbit]
            simp only [hb',↓reduceIte]
            apply ih
            intro v hv
            rcases Finset.mem_insert.mp hv with rfl | hv
            · exact fun hz => hc d.2.1 ⟨d.1,d.2.2,he,hs d.1 htail,hz⟩ hb
            · exact hs v hv
          · have hb' : ¬G.eraseVertices ω O d.2.1 := by rwa [← hbit]
            simp only [hb',↓reduceIte]
            exact ih _ _ _ hs

variable [Fintype V]
lemma search_contactScore_erase (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (a : V) (ha : a ∉ O) (p : ℝ) (F : Set E → Prop)
    (w : E → Prop → ℝ) (ω : Set E) (hc : ∀ e ∈ G.cutEdges O, ¬ω e) :
    (search G order a B).contactScore p (G.cutEdges O) F w ω =
      (search G order a B).contactScore p (G.cutEdges O) F w (G.eraseVertices ω O) := by
  apply compile_contactScore_erase G order B O _ _ _ p F w ω hc
  intro v hv
  have : v = a := Finset.mem_singleton.mp hv
  rwa [this]

theorem contact_expect_exterior (G : BondGraph V E) (order : List (Dart V E))
    (B O : Set V) (a : V) (ha : a ∉ O) (p : ℝ) (F : Set E → Prop)
    (w v v' : E → Prop → ℝ) (hv : ∀ e, ∑ b, v e b = 1)
    (hv' : ∀ e, ∑ b, v' e b = 1)
    (hcut : ∀ ω, density v ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e)
    (hcut' : ∀ ω, density v' ω ≠ 0 → ∀ e ∈ G.cutEdges O, ¬ω e)
    (heq : ∀ e ∉ G.incidentEdges O, v e = v' e) (ψ : ℝ → ℝ) :
    expect v (fun ω => ψ ((search G order a B).contactScore p (G.cutEdges O) F w ω)) =
      expect v' (fun ω => ψ ((search G order a B).contactScore p (G.cutEdges O) F w ω)) := by
  let A := (search G order a B).contactScore p (G.cutEdges O) F w
  let f := fun ω : E → Prop => ψ (A (G.eraseVertices ω O))
  have hdep : DependsOn f (G.incidentEdges O)ᶜ := by
    intro ω η hω
    have hh := G.eraseVertices_dependsOn O hω
    exact congrArg (fun x => ψ (A x)) hh
  have hvf : expect v (fun ω => ψ (A ω)) = expect v f := by
    apply expect_congr_support
    intro ω hω
    exact congrArg ψ (search_contactScore_erase G order B O a ha p F w ω (hcut ω hω))
  have hvf' : expect v' (fun ω => ψ (A ω)) = expect v' f := by
    apply expect_congr_support
    intro ω hω
    exact congrArg ψ (search_contactScore_erase G order B O a ha p F w ω (hcut' ω hω))
  exact hvf.trans ((expect_eq_on v v' hv hv' _ f hdep heq).trans hvf'.symm)

end CriticalPercolation.LazyDFS

end
end

end OAI
