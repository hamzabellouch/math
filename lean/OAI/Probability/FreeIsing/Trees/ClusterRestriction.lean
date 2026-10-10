import OAI.Probability.FreeIsing.Estimates.CylinderAutomorphism
import OAI.Probability.FreeIsing.Trees.ConnectedHull
import OAI.Probability.FreeIsing.Trees.Parents
import OAI.Probability.FreeIsing.Trees.Transitivity

namespace OAI

namespace Problem367

namespace ClusterRestriction

theorem entering_prefix_edge {d : ℕ} {r u v : TreeVertex d}
    (hu : ¬ r.1 <+: u.1) (hv : r.1 <+: v.1) (hadj : treeAdj u v) :
    u = parentVertex r ∧ v = r := by
  have hvr : v = r := by
    by_contra hne
    exact hu (treeAdj_preserves_prefix hv hadj.symm hne)
  subst v
  refine ⟨?_, rfl⟩
  rcases hadj with ⟨c, hc⟩ | ⟨c, hc⟩
  · apply Subtype.ext
    simp [parentVertex, hc]
  · exact False.elim (hu (hc ▸ List.prefix_append r.1 [c]))

theorem relation_parent_of_reachable {d : ℕ}
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    {r x y : TreeVertex d} (hx : ¬ r.1 <+: x.1) (hy : r.1 <+: y.1)
    (hxy : Relation.ReflTransGen R x y) : R (parentVertex r) r := by
  by_contra hedge
  have hstay : ¬ r.1 <+: y.1 := by
    clear hy
    induction hxy with
    | refl => exact hx
    | @tail z w hpath hzw ih =>
        intro hw
        obtain ⟨hz, hw⟩ := entering_prefix_edge ih hw (hR hzw)
        exact hedge (by simpa only [hz, hw] using hzw)
  exact hstay hy

theorem prefix_step_of_reachable {d : ℕ}
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    {y : TreeVertex d}
    (hxy : Relation.ReflTransGen R (ConnectedHull.root d) y)
    {n : ℕ} (hn : n < y.1.length) :
    R (ConnectedHull.takeVertex y n) (ConnectedHull.takeVertex y (n + 1)) := by
  have hlength : n + 1 ≤ y.1.length := by omega
  have hout : ¬ (ConnectedHull.takeVertex y (n + 1)).1 <+:
      (ConnectedHull.root d).1 := by
    intro hpre
    have hle := hpre.length_le
    simp only [ConnectedHull.takeVertex, ConnectedHull.root, List.length_take,
      List.length_nil, Nat.min_eq_left hlength] at hle
    omega
  have hparent : parentVertex (ConnectedHull.takeVertex y (n + 1)) =
      ConnectedHull.takeVertex y n := by
    apply treeAdj_parent_of_length_lt (ConnectedHull.prefix_adj y hn)
    simp only [ConnectedHull.takeVertex, List.length_take,
      Nat.min_eq_left hn.le, Nat.min_eq_left hlength]
    omega
  have h := relation_parent_of_reachable hR hout (List.take_prefix (n + 1) y.1) hxy
  simpa only [hparent] using h

theorem reachable_restrict_of_root_mem {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    (hroot : ConnectedHull.root d ∈ D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    {y : TreeVertex d} (hy : y ∈ D)
    (hxy : Relation.ReflTransGen R (ConnectedHull.root d) y) :
    Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ R u v)
      (ConnectedHull.root d) y := by
  have hpref (n : ℕ) : ConnectedHull.takeVertex y n ∈ D := by
    apply hD.prefix_mem_of_min_length_le hroot
      (fun w _ => by simp [ConnectedHull.root]) hy
    · exact List.take_prefix n y.1
    · simp [ConnectedHull.root]
  have hpath : ∀ n ≤ y.1.length,
      Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ R u v)
        (ConnectedHull.root d) (ConnectedHull.takeVertex y n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simpa only [ConnectedHull.prefix_zero] using
          (Relation.ReflTransGen.refl : Relation.ReflTransGen
            (fun u v => u ∈ D ∧ v ∈ D ∧ R u v)
            (ConnectedHull.root d) (ConnectedHull.root d))
    | succ n ih =>
        intro hn
        exact (ih (by omega)).tail
          ⟨hpref n, hpref (n + 1), prefix_step_of_reachable hR hxy (by omega)⟩
  simpa only [ConnectedHull.prefix_length] using hpath y.1.length le_rfl

end ClusterRestriction

theorem ConnectedFinset.reachable_restrict_iff {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    {x y : TreeVertex d} (hx : x ∈ D) (hy : y ∈ D) :
    Relation.ReflTransGen R x y ↔
      Relation.ReflTransGen (fun u v => u ∈ D ∧ v ∈ D ∧ R u v) x y := by
  classical
  constructor
  · intro hxy
    obtain ⟨g, hg⟩ := exists_treeAut_to_root x
    let E := D.image g.toEquiv
    let R' : TreeVertex d → TreeVertex d → Prop :=
      fun u v => R (g.toEquiv.symm u) (g.toEquiv.symm v)
    have hE : ConnectedFinset E := hD.image g
    have hxE : ConnectedHull.root d ∈ E := by
      change (⟨[], List.IsChain.nil⟩ : TreeVertex d) ∈ D.image g.toEquiv
      rw [← hg]
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    have hyE : g.toEquiv y ∈ E := Finset.mem_image.mpr ⟨y, hy, rfl⟩
    have hR' : ∀ {u v}, R' u v → treeAdj u v := by
      intro u v huv
      have h := (g.map_adj (g.toEquiv.symm u) (g.toEquiv.symm v)).mpr (hR huv)
      simpa only [Equiv.apply_symm_apply] using h
    have hxy' : Relation.ReflTransGen R' (ConnectedHull.root d) (g.toEquiv y) := by
      have h := Relation.ReflTransGen.lift g.toEquiv
        (p := R') (fun u v huv => by simpa only [Function.onFun, R', Equiv.symm_apply_apply] using huv)
        x y hxy
      simpa only [Function.onFun, hg, ConnectedHull.root] using h
    have hinner := ClusterRestriction.reachable_restrict_of_root_mem hE hxE hR' hyE hxy'
    have hmem : ∀ z ∈ E, g.toEquiv.symm z ∈ D := by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
      simpa only [Equiv.symm_apply_apply] using hw
    have hback := Relation.ReflTransGen.lift g.toEquiv.symm
      (p := fun u v => u ∈ D ∧ v ∈ D ∧ R u v)
      (fun u v huv => ⟨hmem u huv.1, hmem v huv.2.1, huv.2.2⟩)
      (ConnectedHull.root d) (g.toEquiv y) hinner
    have hgroot : g.toEquiv.symm (ConnectedHull.root d) = x := by
      change g.toEquiv.symm (⟨[], List.IsChain.nil⟩ : TreeVertex d) = x
      rw [← hg, Equiv.symm_apply_apply]
    simpa only [Function.onFun, hgroot, Equiv.symm_apply_apply] using hback
  · exact Relation.ReflTransGen.mono (fun _ _ h => h.2.2) x y

theorem ConnectedFinset.reachable_congr_on {d : ℕ}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R S : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v)
    (hS : ∀ {u v}, S u v → treeAdj u v)
    (hRS : ∀ u ∈ D, ∀ v ∈ D, R u v ↔ S u v)
    {x y : TreeVertex d} (hx : x ∈ D) (hy : y ∈ D) :
    Relation.ReflTransGen R x y ↔ Relation.ReflTransGen S x y := by
  rw [hD.reachable_restrict_iff hR hx hy, hD.reachable_restrict_iff hS hx hy]
  have heq : (fun u v => u ∈ D ∧ v ∈ D ∧ R u v) =
      (fun u v => u ∈ D ∧ v ∈ D ∧ S u v) := by
    funext u v
    apply propext
    constructor
    · exact fun h => ⟨h.1, h.2.1, (hRS u h.1 v h.2.1).mp h.2.2⟩
    · exact fun h => ⟨h.1, h.2.1, (hRS u h.1 v h.2.1).mpr h.2.2⟩
  rw [heq]

theorem ConnectedFinset.cluster_constant_iff_edges {d : ℕ} {α : Type*}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v) (eta : TreeVertex d → α) :
    (∀ u ∈ D, ∀ v ∈ D, Relation.ReflTransGen R u v → eta u = eta v) ↔
      (∀ u ∈ D, ∀ v ∈ D, R u v → eta u = eta v) := by
  constructor
  · exact fun h u hu v hv huv => h u hu v hv (.single huv)
  · intro he u hu v hv huv
    have hp := (hD.reachable_restrict_iff hR hu hv).mp huv
    clear huv hv
    induction hp with
    | refl => rfl
    | @tail z w hp hzw ih =>
        exact ih.trans (he z hzw.1 w hzw.2.1 hzw.2.2)

theorem ConnectedFinset.cluster_constant_iff_inducedEdges {d : ℕ} {α : Type*}
    {D : Finset (TreeVertex d)} (hD : ConnectedFinset D)
    {R : TreeVertex d → TreeVertex d → Prop}
    (hR : ∀ {u v}, R u v → treeAdj u v) (hRsymm : ∀ {u v}, R u v → R v u)
    (eta : TreeVertex d → α) :
    (∀ u ∈ D, ∀ v ∈ D, Relation.ReflTransGen R u v → eta u = eta v) ↔
      (∀ e ∈ inducedEdges D, R e.1 e.2 → eta e.1 = eta e.2) := by
  classical
  rw [hD.cluster_constant_iff_edges hR eta]
  constructor
  · intro h e he hRe
    have hmem := Finset.mem_product.mp (Finset.mem_filter.mp he).1
    exact h e.1 hmem.1 e.2 hmem.2 hRe
  · intro h u hu v hv huv
    have hadj := hR huv
    rcases treeAdj_length hadj with hlen | hlen
    · apply h (u, v) _ huv
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hu, hv⟩,
        hadj, by change u.1.length < v.1.length; omega⟩
    · have he : (v, u) ∈ inducedEdges D :=
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hu⟩,
          hadj.symm, by change v.1.length < u.1.length; omega⟩
      exact (h (v, u) he (hRsymm huv)).symm

end Problem367

end OAI
