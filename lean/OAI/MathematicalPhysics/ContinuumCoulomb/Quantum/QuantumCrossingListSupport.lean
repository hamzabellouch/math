import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingListMatrix

namespace OAI

/-! The literal nine-bond crossing block has precisely the unordered
endpoint support of the physical crossing graph. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListLayer
open QuantumCrossingListBlock
open scoped Classical

variable {r : ℕ} (C : QMARationalCrossingLayer r) (N : ℚ)

theorem edge_base_or_tag (e : (C.output N).Edge) :
    (∃ a : C.base.Edge, e = Sum.inl (Sum.inl a)) ∨
      ∃ i k, e = edgeTag C N i k := by
  rcases e with (a | ⟨i,k⟩) | (i | ⟨i,k⟩)
  · exact Or.inl ⟨a,rfl⟩
  · right
    fin_cases k
    · exact ⟨i,0,rfl⟩
    · exact ⟨i,1,rfl⟩
    · exact ⟨i,2,rfl⟩
    · exact ⟨i,3,rfl⟩
  · exact Or.inr ⟨i,4,rfl⟩
  · right
    fin_cases k
    · exact ⟨i,5,rfl⟩
    · exact ⟨i,6,rfl⟩
    · exact ⟨i,7,rfl⟩
    · exact ⟨i,8,rfl⟩

theorem bond_support_actual {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (p : Sym2 ℕ) :
    (∃ b ∈ bonds (actualInput C N labels), s(b.1,b.2.1) = p) ↔
      ∃ e : (C.output N).Edge,
        s(((C.output N).left e).val,((C.output N).right e).val) = p := by
  have hb (a : C.base.Edge) :
      s(((C.output N).left (Sum.inl (Sum.inl a))).val,
        ((C.output N).right (Sum.inl (Sum.inl a))).val) =
        s((C.base.left a).val,(C.base.right a).val) := rfl
  have hmem (i : Fin r) (k : Fin 9) :
      bond ((C.base.n,C.scale N),i.val,actualCrossing C i) k ∈
        family ((C.base.n,C.scale N),List.ofFn (actualCrossing C)) := by
    rw [family_ofFn]
    exact List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,
      List.mem_ofFn.mpr ⟨k,rfl⟩⟩
  change (∃ b ∈ QuantumListGraph.packed C.base labels ++
    family (parameters (actualInput C N labels),List.ofFn (actualCrossing C)),
      s(b.1,b.2.1)=p) ↔ _
  rw [parameters_actual]
  constructor
  · rintro ⟨b,hbonds,hp⟩
    rcases List.mem_append.mp hbonds with ho | hf
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ho
      exact ⟨Sum.inl (Sum.inl (labels.symm i)),(hb _).trans hp⟩
    · rw [family_ofFn] at hf
      obtain ⟨bs,hbs,hb⟩ := List.mem_flatten.mp hf
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hbs
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hb
      exact ⟨edgeTag C N i k,by simpa only [bond_actual] using hp⟩
  · rintro ⟨e,he⟩
    rcases edge_base_or_tag C N e with ⟨a,rfl⟩ | ⟨i,k,rfl⟩
    · refine ⟨((C.base.left a).val,(C.base.right a).val,C.base.weight a),
        List.mem_append_left _ (List.mem_ofFn.mpr ⟨labels a,?_⟩),?_⟩
      · simp only [Equiv.symm_apply_apply]
      · exact (hb a).symm.trans he
    · exact ⟨_,List.mem_append_right _ (hmem i k),by simpa only [bond_actual] using he⟩

private theorem fin_pair {n : ℕ} {a b c d : Fin n}
    (h : s(a.val,b.val)=s(c.val,d.val)) : s(a,b)=s(c,d) := by
  rcases Sym2.eq_iff.mp h with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Sym2.eq_iff.mpr (Or.inl ⟨Fin.ext h1,Fin.ext h2⟩)
  · exact Sym2.eq_iff.mpr (Or.inr ⟨Fin.ext h1,Fin.ext h2⟩)

def actualVertex {m : ℕ} (labels : C.base.Edge ≃ Fin m) :
    Fin (actualGraph C N labels).n ≃ Fin (C.output N).n :=
  finCongr (count_actual C N labels)

theorem actual_support_source {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (e : (actualGraph C N labels).Edge) :
    ∃ f : (C.output N).Edge,
      s(actualVertex C N labels ((actualGraph C N labels).left e),
        actualVertex C N labels ((actualGraph C N labels).right e)) =
          s((C.output N).left f,(C.output N).right f) := by
  let xs := bonds (actualInput C N labels)
  obtain ⟨f,hf⟩ := (bond_support_actual C N labels
    s(((xs.get e).1),((xs.get e).2.1))).mp ⟨xs.get e,List.get_mem xs e,rfl⟩
  refine ⟨f,fin_pair ?_⟩
  exact hf.symm

theorem actual_support_target {m : ℕ} (labels : C.base.Edge ≃ Fin m)
    (f : (C.output N).Edge) :
    ∃ e : (actualGraph C N labels).Edge,
      s(actualVertex C N labels ((actualGraph C N labels).left e),
        actualVertex C N labels ((actualGraph C N labels).right e)) =
          s((C.output N).left f,(C.output N).right f) := by
  obtain ⟨b,hb,hp⟩ := (bond_support_actual C N labels
    s(((C.output N).left f).val,((C.output N).right f).val)).mpr ⟨f,rfl⟩
  obtain ⟨e,he⟩ := List.mem_iff_get.mp hb
  refine ⟨e,fin_pair ?_⟩
  change s(((bonds (actualInput C N labels)).get e).1,
    ((bonds (actualInput C N labels)).get e).2.1) = _
  rw [he]
  exact hp

end ContinuumCoulomb.QuantumCrossingListLayer

end

end OAI
