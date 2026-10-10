import OAI.Probability.FreeIsing.Model

namespace OAI

namespace Problem367

noncomputable section

open Relation

variable {d : ℕ}

theorem ConnectedFinset.image {D : Finset (TreeVertex d)}
    (hD : ConnectedFinset D) (g : TreeAut d) :
    ConnectedFinset (D.image g.toEquiv) := by
  classical
  refine ⟨hD.1.image _, ?_⟩
  intro u hu v hv
  obtain ⟨u, huD, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v, hvD, rfl⟩ := Finset.mem_image.mp hv
  exact ReflTransGen.lift g.toEquiv
    (fun x y hxy => ⟨Finset.mem_image.mpr ⟨x, hxy.1, rfl⟩,
      Finset.mem_image.mpr ⟨y, hxy.2.1, rfl⟩,
      (g.map_adj x y).mpr hxy.2.2⟩) _ _ (hD.2 u huD v hvD)

namespace CylinderAut

private theorem adj_symm {u v : TreeVertex d} (h : treeAdj u v) : treeAdj v u :=
  h.symm

private theorem length_ne_of_adj {u v : TreeVertex d} (h : treeAdj u v) :
    u.1.length ≠ v.1.length := by
  rcases h with ⟨c, hc⟩ | ⟨c, hc⟩
  all_goals
    have hlen := congrArg List.length hc
    simp only [List.length_append, List.length_singleton] at hlen
    omega

def orient (e : TreeVertex d × TreeVertex d) : TreeVertex d × TreeVertex d :=
  if e.1.1.length < e.2.1.length then e else e.swap

private theorem orient_swap (e : TreeVertex d × TreeVertex d)
    (hne : e.1.1.length ≠ e.2.1.length) :
    orient e.swap = orient e := by
  unfold orient
  simp only [Prod.fst_swap, Prod.snd_swap, Prod.swap_swap]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem mem_inducedEdges {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} :
    e ∈ inducedEdges D ↔ e.1 ∈ D ∧ e.2 ∈ D ∧ treeAdj e.1 e.2 ∧
      e.1.1.length < e.2.1.length := by
  classical
  simp [inducedEdges, and_assoc]

private theorem orient_mem {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (h₁ : e.1 ∈ D) (h₂ : e.2 ∈ D)
    (ha : treeAdj e.1 e.2) : orient e ∈ inducedEdges D := by
  classical
  unfold orient
  split_ifs with h
  · exact mem_inducedEdges.mpr ⟨h₁, h₂, ha, h⟩
  · exact mem_inducedEdges.mpr ⟨h₂, h₁, adj_symm ha,
      lt_of_le_of_ne (le_of_not_gt h) (length_ne_of_adj ha).symm⟩

private theorem orient_eq_of_mem {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    orient e = e := by
  simp [orient, (mem_inducedEdges.mp he).2.2.2]

def push (g : TreeAut d) (e : TreeVertex d × TreeVertex d) :
    TreeVertex d × TreeVertex d :=
  orient (g.toEquiv e.1, g.toEquiv e.2)

def pull (g : TreeAut d) (e : TreeVertex d × TreeVertex d) :
    TreeVertex d × TreeVertex d :=
  orient (g.toEquiv.symm e.1, g.toEquiv.symm e.2)

private theorem push_mem (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    push g e ∈ inducedEdges (D.image g.toEquiv) := by
  classical
  obtain ⟨h₁, h₂, ha, _⟩ := mem_inducedEdges.mp he
  exact orient_mem (Finset.mem_image.mpr ⟨e.1, h₁, rfl⟩)
    (Finset.mem_image.mpr ⟨e.2, h₂, rfl⟩) ((g.map_adj _ _).mpr ha)

private theorem pull_push (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges D) :
    pull g (push g e) = e := by
  have hedir := (mem_inducedEdges.mp he).2.2.2
  unfold push pull orient
  by_cases h : (g.toEquiv e.1).1.length < (g.toEquiv e.2).1.length
  all_goals simp [h, hedir, not_lt_of_ge (le_of_lt hedir)]

private theorem pull_mem (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges (D.image g.toEquiv)) :
    pull g e ∈ inducedEdges D := by
  classical
  obtain ⟨h₁, h₂, ha, _⟩ := mem_inducedEdges.mp he
  have hp₁ : g.toEquiv.symm e.1 ∈ D := by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h₁
    simpa [← hxe] using hx
  have hp₂ : g.toEquiv.symm e.2 ∈ D := by
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp h₂
    simpa [← hxe] using hx
  have hpa : treeAdj (g.toEquiv.symm e.1) (g.toEquiv.symm e.2) := by
    apply (g.map_adj _ _).mp
    simpa using ha
  exact orient_mem hp₁ hp₂ hpa

private theorem push_pull (g : TreeAut d) {D : Finset (TreeVertex d)}
    {e : TreeVertex d × TreeVertex d} (he : e ∈ inducedEdges (D.image g.toEquiv)) :
    push g (pull g e) = e := by
  have hedir := (mem_inducedEdges.mp he).2.2.2
  unfold push pull orient
  by_cases h : (g.toEquiv.symm e.1).1.length < (g.toEquiv.symm e.2).1.length
  all_goals simp [h, hedir, not_lt_of_ge (le_of_lt hedir)]

theorem prod_inducedEdges_image {M : Type*} [CommMonoid M]
    (g : TreeAut d) (D : Finset (TreeVertex d))
    (f : TreeVertex d → TreeVertex d → M)
    (hf : ∀ u v, f u v = f v u) :
    (∏ e ∈ inducedEdges (D.image g.toEquiv),
      f (g.toEquiv.symm e.1) (g.toEquiv.symm e.2)) =
      ∏ e ∈ inducedEdges D, f e.1 e.2 := by
  classical
  symm
  apply Finset.prod_bij (fun e _ => push g e)
  · intro e he
    exact push_mem g he
  · intro e₁ he₁ e₂ he₂ heq
    have h := congrArg (pull g) heq
    simpa only [pull_push g he₁, pull_push g he₂] using h
  · intro e he
    exact ⟨pull g e, pull_mem g he, push_pull g he⟩
  · intro e he
    unfold push orient
    split_ifs
    · simp
    · simpa using hf e.1 e.2

end CylinderAut

theorem freeCylinderWeight_image_relabel (g : TreeAut d) (theta : ℝ)
    (D : Finset (TreeVertex d)) (eta : TreeVertex d → IsingSpin) :
    freeCylinderWeight theta (D.image g.toEquiv) (relabel g eta) =
      freeCylinderWeight theta D eta := by
  classical
  unfold freeCylinderWeight
  apply congrArg ENNReal.ofReal
  apply congrArg ((1 / 2 : ℝ) * ·)
  exact CylinderAut.prod_inducedEdges_image g D
    (fun u v => (1 + (if eta u = eta v then theta else -theta)) / 2)
    (by intro u v; simp only [eq_comm])

private def cylinderInverseAut (g : TreeAut d) : TreeAut d where
  toEquiv := g.toEquiv.symm
  map_adj := by
    intro u v
    simpa using (g.map_adj (g.toEquiv.symm u) (g.toEquiv.symm v)).symm

private theorem measurable_spin_cylinder (D : Finset (TreeVertex d))
    (eta : TreeVertex d → IsingSpin) :
    MeasurableSet {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} := by
  have hsingle (s : IsingSpin) : MeasurableSet ({s} : Set IsingSpin) := by
    trivial
  convert D.measurableSet_biInter
    (fun v _ => (measurable_pi_apply v) (hsingle (eta v))) using 1
  ext x
  simp

theorem HasFreeIsingLaw.map_relabel {theta : ℝ}
    {mu : MeasureTheory.Measure (TreeVertex d → IsingSpin)}
    (hmu : HasFreeIsingLaw theta mu) (g : TreeAut d) :
    HasFreeIsingLaw theta (MeasureTheory.Measure.map (relabel g) mu) := by
  classical
  intro D hD eta
  have hm : Measurable (relabel g : (TreeVertex d → IsingSpin) → _) :=
    measurable_pi_iff.mpr (fun v => measurable_pi_apply (g.toEquiv.symm v))
  rw [MeasureTheory.Measure.map_apply hm (measurable_spin_cylinder D eta)]
  let gi := cylinderInverseAut g
  have hpre : relabel g ⁻¹' {x : TreeVertex d → IsingSpin | ∀ v ∈ D, x v = eta v} =
      {x : TreeVertex d → IsingSpin | ∀ v ∈ D.image gi.toEquiv,
        x v = relabel gi eta v} := by
    ext x
    constructor
    · intro hx v hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
      simpa [relabel, gi, cylinderInverseAut] using hx u hu
    · intro hx v hv
      have hh := hx (gi.toEquiv v) (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
      simpa [relabel, gi, cylinderInverseAut] using hh
  rw [hpre, hmu _ (hD.image gi), freeCylinderWeight_image_relabel]

end
end Problem367

end OAI
