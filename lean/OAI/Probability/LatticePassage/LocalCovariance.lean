import OAI.Probability.LatticePassage.LocalSelection
import OAI.Probability.LatticePassage.LocalizationMean

namespace OAI

namespace CompanionFPP
open MeasureTheory

lemma environmentTranslation_add (a b : Vertex) (ω : Environment) :
    environmentTranslation a (environmentTranslation b ω) =
      environmentTranslation (b+a) ω := by
  funext e
  unfold environmentTranslation
  congr 1
  apply Subtype.ext
  change Sym2.map (fun x : Vertex => b+x) (Sym2.map (fun x : Vertex => a+x) e.val) =
    Sym2.map (fun x : Vertex => (b+a)+x) e.val
  rw [Sym2.map_map]
  congr 1
  funext x
  simp only [Function.comp_apply, add_assoc]

lemma pathCost_copy {x y x' y' : Vertex} (ω : Environment)
    (p : lattice.Walk x y) (hx : x = x') (hy : y = y') :
    pathCost ω (p.copy hx hy) = pathCost ω p := by
  cases hx
  cases hy
  rfl

noncomputable def localPatch (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) (ω : Environment) : lattice.Walk x (x+d) :=
  ((selectedLocalPath 0 d R hR (environmentTranslation x ω)).map
    (latticeTranslation x).toHom).copy
      (show (latticeTranslation x).toHom 0 = x from add_zero x)
      (show (latticeTranslation x).toHom d = x+d from rfl)

lemma localPatch_support (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) (ω : Environment) :
    (localPatch d R hR x ω).support =
      (selectedLocalPath 0 d R hR (environmentTranslation x ω)).support.map (fun v => x+v) := by
  unfold localPatch
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map]
  rfl

theorem localPatch_spec (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) (ω : Environment) :
    (localPatch d R hR x ω).IsPath ∧ (localPatch d R hR x ω).length < R ∧
      pathCost ω (localPatch d R hR x ω) =
        localPassageTime (environmentTranslation x ω) 0 d R := by
  obtain ⟨hp,hl,hm⟩ := selectedLocalPath_spec 0 d R hR (environmentTranslation x ω)
  constructor
  · unfold localPatch
    rw [SimpleGraph.Walk.isPath_copy]
    exact hp.map (f := (latticeTranslation x).toHom) (latticeTranslation x).injective
  constructor
  · unfold localPatch
    rw [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
    exact hl
  · unfold localPatch
    rw [pathCost_copy, pathCost_map_translation]
    exact hm

theorem localPatch_covariance (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (a x : Vertex) (ω : Environment) :
    (localPatch d R hR (a+x) ω).support =
      (localPatch d R hR x (environmentTranslation a ω)).support.map (fun v => a+v) := by
  simp only [localPatch_support, environmentTranslation_add, List.map_map]
  congr 1
  funext v
  simp only [Function.comp_apply, add_assoc]

theorem measurable_localPatch_observation (d : Vertex) (R : ℕ)
    (hR : latticeDistance 0 d < R) (x : Vertex) (f : lattice.Walk x (x+d) → ℝ) :
    Measurable (fun ω => f (localPatch d R hR x ω)) := by
  exact (measurable_selectedLocalPath_observation 0 d R hR
    (fun p => f ((p.map (latticeTranslation x).toHom).copy (add_zero x) rfl))).comp
      (measurable_environmentTranslation x)

theorem localPatch_eq_of_agree (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) (ω ω' : Environment)
    (h : ∀ e ∈ localEdges 0 R,
      ω ((latticeTranslation x).mapEdgeSet e) = ω' ((latticeTranslation x).mapEdgeSet e)) :
    localPatch d R hR x ω = localPatch d R hR x ω' := by
  unfold localPatch
  rw [selectedLocalPath_eq_of_agree 0 d R hR (environmentTranslation x ω)
    (environmentTranslation x ω') h]

theorem localPatch_cost_integrable (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) : Integrable (fun ω : Environment => pathCost ω (localPatch d R hR x ω))
      environmentLaw := by
  simp_rw [(localPatch_spec d R hR x _).2.2]
  exact (environmentTranslation_preserving x).integrable_comp_of_integrable
    (integrable_localPassageTime 0 d R hR)

theorem localPatch_mean (d : Vertex) (R : ℕ) (hR : latticeDistance 0 d < R)
    (x : Vertex) :
    (∫ ω : Environment, pathCost ω (localPatch d R hR x ω) ∂environmentLaw) =
      ∫ ω : Environment, localPassageTime ω 0 d R ∂environmentLaw := by
  simp_rw [(localPatch_spec d R hR x _).2.2]
  have hm := integral_map (μ := environmentLaw) (measurable_environmentTranslation x).aemeasurable
    (measurable_localPassageTime 0 d R).aestronglyMeasurable
  rw [(environmentTranslation_preserving x).map_eq] at hm
  exact hm.symm

end CompanionFPP

end OAI
