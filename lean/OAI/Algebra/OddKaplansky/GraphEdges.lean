import OAI.Algebra.OddKaplansky.IncidenceCycles

namespace OAI

section

namespace OddKaplansky.GraphEdges
noncomputable section
open scoped Classical
variable {V : Type} [LinearOrder V] (Γ : SimpleGraph V)

abbrev Edge := {e : V × V // e.1 < e.2 ∧ Γ.Adj e.1 e.2}
def Inc (v : V) (e : Edge Γ) : Prop := v = e.val.1 ∨ v = e.val.2

def neighbor (v : V) (e : Edge Γ) : V := if v = e.val.1 then e.val.2 else e.val.1

lemma incident_exists (e : Edge Γ) : ∃ v, Inc Γ v e := ⟨e.val.1, Or.inl rfl⟩
lemma endpoints_ne (e : Edge Γ) : e.val.1 ≠ e.val.2 := (ne_of_lt e.property.1)

lemma neighbor_incident (v : V) (e : Edge Γ) (_hv : Inc Γ v e) : Inc Γ (neighbor Γ v e) e := by
  simp only [neighbor, Inc]
  split_ifs <;> simp

lemma neighbor_ne (v : V) (e : Edge Γ) (hv : Inc Γ v e) : neighbor Γ v e ≠ v := by
  rcases hv with rfl | rfl <;> simp [neighbor, endpoints_ne Γ e, (endpoints_ne Γ e).symm]

lemma neighbor_of_other {v w : V} {e : Edge Γ} (hv : Inc Γ v e) (hw : Inc Γ w e)
    (hne : w ≠ v) : neighbor Γ v e = w := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl <;>
    simp_all [neighbor, endpoints_ne Γ e, (endpoints_ne Γ e).symm]

lemma endpoints_of_inc {v w : V} {e : Edge Γ} (hv : Inc Γ v e) (hw : Inc Γ w e)
    (hne : v ≠ w) : e.val = (v, w) ∨ e.val = (w, v) := by
  rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
  · exact (hne rfl).elim
  · exact Or.inl (Prod.eta _).symm
  · exact Or.inr (Prod.eta _).symm
  · exact (hne rfl).elim

lemma edge_eq_of_inc {v w : V} {e f : Edge Γ}
    (hev : Inc Γ v e) (hew : Inc Γ w e) (hfv : Inc Γ v f) (hfw : Inc Γ w f)
    (hne : v ≠ w) : e = f := by
  have he := endpoints_of_inc Γ hev hew hne
  have hf := endpoints_of_inc Γ hfv hfw hne
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Subtype.ext (he.trans hf.symm)
  · have h₁ := e.property.1
    have h₂ := f.property.1
    rw [he] at h₁
    rw [hf] at h₂
    exact (lt_asymm h₁ h₂).elim
  · have h₁ := e.property.1
    have h₂ := f.property.1
    rw [he] at h₁
    rw [hf] at h₂
    exact (lt_asymm h₁ h₂).elim
  · exact Subtype.ext (he.trans hf.symm)

lemma neighbor_injective (v : V) : Function.Injective (fun e : {e : Edge Γ // Inc Γ v e} =>
    neighbor Γ v e.val) := by
  intro e f h
  change neighbor Γ v e.val = neighbor Γ v f.val at h
  apply Subtype.ext
  apply edge_eq_of_inc Γ e.property (neighbor_incident Γ v e.val e.property) f.property
  · rw [h]
    exact neighbor_incident Γ v f.val f.property
  · exact (neighbor_ne Γ v e.val e.property).symm

lemma adj_of_inc {v w : V} {e : Edge Γ} (hv : Inc Γ v e) (hw : Inc Γ w e) (hne : v ≠ w) :
    Γ.Adj v w := by
  have he := endpoints_of_inc Γ hv hw hne
  rcases he with he | he
  · simpa only [he] using e.property.2
  · exact (show Γ.Adj w v by simpa only [he] using e.property.2).symm

theorem incidence_girth (htri : ∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj c a → False) :
    8 ≤ (Planar.incidenceGraph (Inc Γ)).egirth := by
  apply SimpleGraph.le_egirth.mpr
  intro z w hw
  obtain ⟨k, hk, hk2, point, line, hp, hl, hi, hn⟩ := Planar.cycle_polygon (Inc Γ) w hw
  have hk4 : 4 ≤ k := by
    by_contra hh
    have hk' : k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl
    · have hv0 : Inc Γ (point 1) (line 0) := by simpa using hn (0 : Fin 2)
      have hv1 : Inc Γ (point 0) (line 1) := by simpa using hn (1 : Fin 2)
      have he := edge_eq_of_inc Γ (hi 0) hv0 hv1 (hi 1) (fun h => by have := hp h; simp at this)
      have hh := hl he
      exact (by decide : (0 : Fin 2) ≠ 1) hh
    · have h01 : Γ.Adj (point 0) (point 1) :=
        adj_of_inc Γ (hi 0) (by simpa using hn (0 : Fin 3)) (fun h => by have := hp h; simp at this)
      have h12 : Γ.Adj (point 1) (point 2) :=
        adj_of_inc Γ (hi 1) (by simpa using hn (1 : Fin 3)) (fun h => by have := hp h; simp at this)
      have h20 : Γ.Adj (point 2) (point 0) :=
        adj_of_inc Γ (hi 2) (by simpa using hn (2 : Fin 3)) (fun h => by have := hp h; simp at this)
      exact htri _ _ _ h01 h12 h20
  exact_mod_cast (show 8 ≤ w.length by omega)

end
end OddKaplansky.GraphEdges

namespace OddKaplansky.SourceGraph
noncomputable section
open scoped Classical

@[ext] structure Vertex where
  val : Finset (Fin 1200)
  property : val.card = 600

def vertexEquiv : Vertex ≃ {s : Finset (Fin 1200) // s.card = 600} where
  toFun v := ⟨v.val, v.property⟩
  invFun s := ⟨s.val, s.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Vertex := Fintype.ofEquiv _ vertexEquiv.symm
instance : LinearOrder Vertex := LinearOrder.lift' (fun s => s.val.sort) (by
  intro s t h
  apply Vertex.ext
  simpa using congrArg List.toFinset h)

lemma card_vertices : Fintype.card Vertex = sourceM := by
  unfold sourceM
  have h := Fintype.card_finset_len (α := Fin 1200) 600
  rw [Fintype.card_fin] at h
  exact (Fintype.card_congr vertexEquiv).trans h

def index (v : Vertex) : ℕ :=
  ((Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm v).val + 1

lemma index_pos (v : Vertex) : 0 < index v := Nat.succ_pos _
lemma index_le (v : Vertex) : index v ≤ sourceM :=
  Nat.succ_le_of_lt ((Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm v).isLt
lemma index_injective : Function.Injective index := by
  intro x y h
  apply (Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm.injective
  apply Fin.ext
  exact Nat.add_right_cancel h

lemma index_strictMono : StrictMono index := by
  intro x y h
  exact Nat.add_lt_add_right ((Fintype.orderIsoFinOfCardEq Vertex card_vertices).symm.strictMono h) 1

def graph : SimpleGraph Vertex where
  Adj i j := i ≠ j ∧ (i.val ∩ j.val).card < 200
  symm := ⟨by intro i j h; exact ⟨h.1.symm, by simpa only [Finset.inter_comm] using h.2⟩⟩
  loopless := ⟨by intro i h; exact h.1 rfl⟩

theorem no_triangle (a b c : Vertex) (hab : graph.Adj a b) (hbc : graph.Adj b c)
    (hca : graph.Adj c a) : False := by
  have hAB := Finset.card_union_add_card_inter a.val b.val
  have hABC := Finset.card_union_add_card_inter (a.val ∪ b.val) c.val
  have hI : ((a.val ∪ b.val) ∩ c.val).card ≤
      (a.val ∩ c.val).card + (b.val ∩ c.val).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  have hU : (a.val ∪ b.val ∪ c.val).card ≤ 1200 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (a.val ∪ b.val ∪ c.val))
  have ha := a.property
  have hb := b.property
  have hc := c.property
  have h₁ := hab.2
  have h₂ := hbc.2
  have h₃ : (a.val ∩ c.val).card < 200 := by simpa only [Finset.inter_comm] using hca.2
  omega

abbrev Edge := GraphEdges.Edge graph
abbrev Inc := GraphEdges.Inc graph
abbrev neighbor := GraphEdges.neighbor graph

lemma incidence_girth : 8 ≤ (Planar.incidenceGraph Inc).egirth :=
  GraphEdges.incidence_girth graph no_triangle

end
end OddKaplansky.SourceGraph

end

end OAI
