import OAI.Combinatorics.Ramsey.CycleClique.Construction.SingleAttachment
import OAI.Combinatorics.Ramsey.CycleClique.Construction.RestrictedLongest

namespace OAI

/-! Connectivity and nontriviality of the path after removing the endpoint clique. -/

namespace CycleClique.Construction
theorem connected_induce_difference_single_attachment {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U E : Finset V} {u : V}
    (hconn : (H.induce (U : Set V)).Connected) (huU : u ∈ U) (huE : u ∉ E)
    (hattach : ∀ e ∈ E, ∀ v ∈ U, H.Adj e v → v ∉ E → v = u) :
    (H.induce {v | v ∈ U ∧ v ∉ E}).Connected := by
  classical
  let K := H.induce (U : Set V)
  let E' : Finset (U : Set V) := Finset.univ.filter fun v => v.val ∈ E
  let u' : (U : Set V) := ⟨u, huU⟩
  have hu' : u' ∉ E' := by simp [E', u', huE]
  have hattach' : ∀ e ∈ E', ∀ v, K.Adj e v → v ∉ E' → v = u' := by
    intro e he v hev hv
    have heE : e.val ∈ E := (Finset.mem_filter.mp he).2
    have hvE : v.val ∉ E := by simpa [E'] using hv
    exact Subtype.ext (hattach e.val heE v.val v.property hev hvE)
  have hc := connected_outside_single_attachment hconn hu' hattach'
  let f : {v : (U : Set V) | v ∉ E'} → {v : V | v ∈ U ∧ v ∉ E} := fun v =>
    ⟨v.val.val, v.val.property, by simpa [E'] using v.property⟩
  let φ : (K.induce {v | v ∉ E'}) →g H.induce {v | v ∈ U ∧ v ∉ E} :=
    { toFun := f, map_rel' := fun h => h }
  have hsurj : Function.Surjective φ := by
    intro v
    let w : {v : (U : Set V) | v ∉ E'} :=
      ⟨⟨v.val, v.property.1⟩, by simpa [E'] using v.property.2⟩
    exact ⟨w, rfl⟩
  exact hc.map φ hsurj

theorem restricted_longest_nontrivial {V : Type*} [Fintype V]
    {H : SimpleGraph V} {U : Finset V} {x : V} {r : ℕ}
    (hconn : (H.induce (U : Set V)).Connected) (hcard : 2 ≤ U.card) (hx : x ∈ U)
    (hmax : ∀ q (g : Fin (q + 1) → V), IsIndexedPath H g → g 0 = x →
      (∀ i, g i ∈ U) → q ≤ r) : 1 ≤ r := by
  classical
  let K := H.induce (U : Set V)
  let : Nontrivial (U : Set V) := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa using (show 1 < U.card by omega))
  let x' : (U : Set V) := ⟨x, hx⟩
  have hpos := hconn.preconnected.degree_pos_of_nontrivial x'
  have hcardpos : 0 < (K.neighborFinset x').card := by
    rw [K.card_neighborFinset_eq_degree]
    exact hpos
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcardpos
  have hadj := (K.mem_neighborFinset x' v).mp hv
  let g : Fin 2 → V := Fin.cons x (fun _ : Fin 1 => v.val)
  have hg : IsIndexedPath H g := by
    refine ⟨?_, ?_⟩
    · apply Fin.cons_injective_iff.mpr
      constructor
      · rintro ⟨i, hi⟩
        exact hadj.ne (Subtype.ext hi.symm)
      · intro i j _
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
    · intro i
      have hi : i = 0 := by apply Fin.ext; have := i.isLt; omega
      subst i
      exact hadj
  have hgU : ∀ i, g i ∈ U := by
    intro i
    refine Fin.cases hx (fun _ => v.property) i
  exact hmax 1 g hg rfl hgU

end CycleClique.Construction

end OAI
