import OAI.Probability.LatticePassage.PassageRegularity

namespace OAI

namespace CompanionFPP
open MeasureTheory ProbabilityTheory

def latticeTranslation (a : Vertex) : lattice ≃g lattice where
  toEquiv := Equiv.addLeft a
  map_rel_iff' := by
    intro x y
    change |(a.1+x.1)-(a.1+y.1)| + |(a.2+x.2)-(a.2+y.2)| = 1 ↔
      |x.1-y.1| + |x.2-y.2| = 1
    simp only [add_sub_add_left_eq_sub]

@[simp] lemma latticeTranslation_apply (a x : Vertex) : latticeTranslation a x = a+x := rfl

def environmentTranslation (a : Vertex) (ω : Environment) : Environment :=
  fun e => ω ((latticeTranslation a).mapEdgeSet e)

@[fun_prop] theorem measurable_environmentTranslation (a : Vertex) :
    Measurable (environmentTranslation a) := by
  unfold environmentTranslation
  fun_prop

theorem environmentTranslation_preserving (a : Vertex) :
    MeasurePreserving (environmentTranslation a) environmentLaw environmentLaw := by
  refine ⟨measurable_environmentTranslation a, ?_⟩
  have h := Measure.infinitePi_map_piCongrLeft (fun _ : Edge => expMeasure 1)
    (latticeTranslation a).mapEdgeSet.symm
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Edge => ℝ)
      (latticeTranslation a).mapEdgeSet.symm : Environment → Environment) =
      environmentTranslation a := by
    funext ω e
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, environmentTranslation]
  rw [he] at h
  exact h

lemma pathCost_map_translation (a : Vertex) (ω : Environment) {x y : Vertex}
    (p : lattice.Walk x y) :
    pathCost ω (p.map (latticeTranslation a).toHom) =
      pathCost (environmentTranslation a ω) p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.map_cons, pathCost_cons, ih]
    rfl

lemma walk_map_iso_surjective {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (x y : V) :
    Function.Surjective (fun p : G.Walk x y => p.map f.toHom) := by
  intro q
  let p := (q.map f.symm.toHom).copy (f.symm_apply_apply x) (f.symm_apply_apply y)
  refine ⟨p, ?_⟩
  apply SimpleGraph.Walk.ext_support
  simp only [p, SimpleGraph.Walk.support_map, SimpleGraph.Walk.support_copy, List.map_map]
  have he : (⇑f.toHom ∘ ⇑f.symm.toHom) = id := by
    funext v
    exact f.apply_symm_apply v
  simp only [he, List.map_id_fun, id_eq]

theorem passageTime_translation (a : Vertex) (ω : Environment) (x y : Vertex) :
    passageTime ω (a+x) (a+y) = passageTime (environmentTranslation a ω) x y := by
  unfold passageTime
  congr 1
  ext c
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨p,rfl⟩ := walk_map_iso_surjective (latticeTranslation a) x y q
    exact ⟨p,(pathCost_map_translation a ω p).symm⟩
  · rintro ⟨p,rfl⟩
    exact ⟨p.map (latticeTranslation a).toHom, pathCost_map_translation a ω p⟩

theorem mean_passageTime_translation (a x y : Vertex) :
    (∫ ω : Environment, passageTime ω (a+x) (a+y) ∂environmentLaw) =
      ∫ ω : Environment, passageTime ω x y ∂environmentLaw := by
  simp_rw [passageTime_translation]
  have hm := integral_map (μ := environmentLaw) (measurable_environmentTranslation a).aemeasurable
    (measurable_passageTime x y).aestronglyMeasurable
  rw [(environmentTranslation_preserving a).map_eq] at hm
  exact hm.symm

theorem mean_passageTime_subadditive (x y : Vertex) :
    (∫ ω : Environment, passageTime ω 0 (x+y) ∂environmentLaw) ≤
      (∫ ω : Environment, passageTime ω 0 x ∂environmentLaw) +
      (∫ ω : Environment, passageTime ω 0 y ∂environmentLaw) := by
  have hb := integral_mono_ae (integrable_passageTime 0 (x+y))
    ((integrable_passageTime 0 x).add (integrable_passageTime x (x+y)))
    (by
      filter_upwards [passageTime_properties] with ω hω
      exact hω.2.2.2 0 x (x+y))
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_passageTime 0 x) (integrable_passageTime x (x+y))] at hb
  have ht := mean_passageTime_translation x 0 y
  simp only [add_zero] at ht
  rw [ht] at hb
  exact hb

end CompanionFPP

end OAI
