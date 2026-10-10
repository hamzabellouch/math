import OAI.Probability.BenjaminiSchramm.MixedRootSurgery

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

omit [Countable V] [Countable E] in
lemma walk_internal_restriction {x y : V} (q : (openSimpleGraph G Set.univ).Walk x y)
    (P : Set V) (hP : ∀ v ∈ q.support, v ∈ P) :
    ∃ q' : (openSimpleGraph G (internalEdges G P)).Walk x y,
      q'.length=q.length ∧ q'.support=q.support := by
  induction q with
  | nil => exact ⟨.nil,rfl,rfl⟩
  | @cons x z y hxy q ih =>
    have htail : ∀ v ∈ q.support, v ∈ P :=
      fun v hv => hP v (List.mem_cons_of_mem x hv)
    obtain ⟨q',hlen,hsupp⟩ := ih htail
    obtain ⟨e,he,heq⟩ := hxy.2
    have heP : e ∈ internalEdges G P := by
      intro v hv
      rw [heq] at hv
      rcases Sym2.mem_iff.mp hv with hv | hv
      · subst v
        exact hP x (SimpleGraph.Walk.start_mem_support (.cons hxy q))
      · subst v
        exact hP z (List.mem_cons_of_mem x q.start_mem_support)
    refine ⟨.cons ⟨hxy.1,e,heP,heq⟩ q',?_,?_⟩
    · change q'.length+1=q.length+1
      rw [hlen]
    · change x::q'.support=x::q.support
      rw [hsupp]

theorem mixed_root_walk_probability (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (D J : Set E) (hJD : J ⊆ D)
    (T : Set V) (u v w : V) (q : (openSimpleGraph G J).Walk u v)
    (hT : ∀ z ∈ q.support, z ∉ T) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q.length+1)))*
      law p (connectionAvoidingHit G D J v w T) ≤ law p (connectionAvoidingHit G D J u w T) := by
  let P := q.support.toFinset
  obtain ⟨l,hlift,hends,hopen⟩ := walk_lift_bonds G J q
  let γ : Set E := (l.toFinset : Set E)
  have hγJ : γ ⊆ J := fun e he => hopen e (List.mem_toFinset.mp he)
  have hγP : γ ⊆ internalEdges G (P : Set V) := by
    intro e he z hze
    exact List.mem_toFinset.mpr (SimpleGraph.Walk.mem_support_of_mem_edges
      (hends ▸ List.mem_map_of_mem (List.mem_toFinset.mp he)) hze)
  have hPT : Disjoint (P : Set V) T := Set.disjoint_left.mpr
    fun z hz hzT => hT z (List.mem_toFinset.mp hz) hzT
  have hcard : (incidentSupport G hl P).card ≤ d*(q.length+1) := by
    calc
      _ ≤ P.card*d := incidentSupport_card_le G hl d hd P
      _ ≤ (q.length+1)*d := Nat.mul_le_mul_right d
        ((List.toFinset_card_le q.support).trans_eq q.length_support)
      _ = _ := by ring
  have hδ : 0 ≤ min (p : ℝ) (1-p) := le_min p.2.1 (sub_nonneg.mpr p.2.2)
  have hδ1 : min (p : ℝ) (1-p) ≤ 1 := (min_le_left _ _).trans p.2.2
  exact (mul_le_mul' (ENNReal.ofReal_le_ofReal
    (pow_le_pow_of_le_one hδ hδ1 hcard)) le_rfl).trans
      (mixed_root_connection_probability G hl p D J γ P T hJD hγJ hγP hPT u v w
        (List.mem_toFinset.mpr q.start_mem_support) (hlift.conn (fun e he => List.mem_toFinset.mpr he)))

theorem mixed_root_walk_layer_moment (hl : LocallyFinite G) (d : ℕ)
    (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (D J : Set E) (hJD : J ⊆ D)
    (T W : Set V) (u v : V) (q : (openSimpleGraph G J).Walk u v)
    (hT : ∀ z ∈ q.support, z ∉ T) :
    ENNReal.ofReal ((min (p : ℝ) (1-p))^(d*(q.length+1)))*
      (∑' w, if w ∈ W then law p (connectionAvoidingHit G D J v w T) else 0) ≤
      ∑' w, if w ∈ W then law p (connectionAvoidingHit G D J u w T) else 0 := by
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hw : w ∈ W
  · simp only [hw,ite_true]
    exact mixed_root_walk_probability G hl d hd p D J hJD T u v w q hT
  · simp only [hw,ite_false,mul_zero]
    exact le_rfl

end Percolation.BenjaminiSchramm

end

end OAI
