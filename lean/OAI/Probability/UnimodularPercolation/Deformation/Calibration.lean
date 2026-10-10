import Mathlib
import OAI.Probability.UnimodularPercolation.Deformation.Derivatives

namespace OAI

/-! Calibration for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformDeformedEndpoint
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_uniform_deformed_endpoint_comparison [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ (t : ℝ), 0 ≤ t → ∀ (D : Set V) (b z : V) (l : List E),
      b ∈ D → Along G b l z → (∀ e ∈ l, e ∈ internalEdges G D) →
      Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) * (p:ℝ)^l.length *
        deformedSusceptibility G (walkKernel G hloc a) p k t D z ≤
        deformedSusceptibility G (walkKernel G hloc a) p k t D b := by
  obtain ⟨C,hC,hcost⟩ := exists_uniform_corridor_edge_cost G hloc d hd a hP hpcrit hpcrit₁
  refine ⟨C,hC,?_⟩
  intro p hpnear hp k hk t ht D b z l hb hl hD
  have hc : ∀ e, (∑' w : RawCorridor G k,
      if e ∈ w.retained then w.weight (walkKernel G hloc a) p else 0) ≤ Real.exp (C*(k:ℝ)) := by
    intro e
    exact (hcost p hpnear hp k hk e).trans (div_le_self (Real.exp_pos _).le (by exact_mod_cast (show 1 ≤ k by omega)))
  have hh := deformedSusceptibility_move_lower G hloc hqt (walkKernel G hloc a) hP p hp k t ht D
    l.toFinset (fun e he => hD e (List.mem_toFinset.mp he)) b z hb
    (hl.conn (fun e he => List.mem_toFinset.mpr he)) (Real.exp (C*(k:ℝ))) hc
  have hcard : (l.toFinset.card:ℝ) ≤ (l.length:ℝ) := Nat.cast_le.mpr l.toFinset_card_le
  have he : Real.exp (-t*((l.length:ℝ)*Real.exp (C*(k:ℝ)))) ≤
      Real.exp (-t*((l.toFinset.card:ℝ)*Real.exp (C*(k:ℝ)))) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le) (neg_nonpos.mpr ht)
  have hpw : (p:ℝ)^l.length ≤ (p:ℝ)^l.toFinset.card :=
    pow_le_pow_of_le_one p.2.1 p.2.2 l.toFinset_card_le
  exact (mul_le_mul_of_nonneg_right (mul_le_mul he hpw (pow_nonneg p.2.1 _) (Real.exp_pos _).le)
    (tsum_nonneg (deformedKernel_nonneg G (walkKernel G hloc a) p k t D z))).trans hh

end UniformDeformedEndpoint
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section PivotalLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

theorem pivotal_endpoint_connected (G : BondGraph V E) (S : Set E) (x y : V)
    (hc : Conn G S x y) (e : E) (hp : ¬Conn G (S \ {e}) x y) (z : V) (hz : z ∈ G e) :
    Conn G S x z := by
  obtain ⟨q⟩ := (conn_iff_reachable G S x y).mp hc
  have hzs : z ∈ q.support := SimpleGraph.Walk.mem_support_of_mem_edges
    (pivotal_image_mem_edges G S q e hp) hz
  exact (conn_iff_reachable G S x z).mpr ⟨q.takeUntil z hzs⟩

theorem conn_delete_of_unconnected_endpoint (G : BondGraph V E) (S : Set E) (x y z : V)
    (hc : Conn G S x y) (e : E) (hz : z ∈ G e) (hn : ¬Conn G S x z) :
    Conn G (S \ {e}) x y := by
  by_contra hh
  exact hn (pivotal_endpoint_connected G S x y hc e hh z hz)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem retained_conn_base (w : RawCorridor G k) (z : V) (hz : z ∈ w.path.support) :
    Conn G w.retained w.base z := by
  obtain ⟨l,hl,hm,_⟩ := walk_lift_bonds G Set.univ (w.path.takeUntil z hz)
  apply hl.conn
  intro e he
  exact w.path.edges_takeUntil_subset_edges hz (hm ▸ List.mem_map_of_mem he)

theorem retained_conn (w : RawCorridor G k) : Conn G w.retained w.base w.endpoint :=
  w.retained_conn_base w.endpoint w.path.end_mem_support

theorem retained_connects_support (w : RawCorridor G k) (x y : V)
    (hx : x ∈ w.path.support) (hy : y ∈ w.path.support) : Conn G w.retained x y :=
  conn_trans G _ (conn_symm G _ (w.retained_conn_base x hx)) (w.retained_conn_base y hy)

theorem retained_nonempty (w : RawCorridor G k) (hl : 0 < w.path.length) : w.retained.Nonempty := by
  have hp : w.path.edges ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp only [SimpleGraph.Walk.length_edges,List.length_nil] at hh
    omega
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ hp
  obtain ⟨e,he,_⟩ := w.edge_has_label s hs
  exact ⟨e,he⟩

end RawCorridor
end PivotalLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section OneLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem counted_one_leg (r : RawCorridor G k) (D : Set V) (ω B : Set E)
    (x y u v : V) (hc : r.counted Set.univ ω x y)
    (hr : r.retained ⊆ ω ∩ internalEdges G D) (hB : B ⊆ ω)
    (hd : Disjoint B r.retained) (huv : Conn G B u v)
    (hxu : Conn G (ω ∩ internalEdges G D) x u)
    (hvy : Conn G (ω ∩ internalEdges G D) v y)
    (hne : ¬Conn G (ω ∩ internalEdges G D) u v)
    (e : E) (he : e ∈ r.retained)
    (hep : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x u) : r.counted D ω x u := by
  let S := ω ∩ internalEdges G D
  have huniv : ω ∩ internalEdges G Set.univ = ω := by
    apply Set.Subset.antisymm Set.inter_subset_left
    exact fun _ he => ⟨he,fun _ _ => trivial⟩
  obtain ⟨z,z',hzz⟩ : ∃ z z', G e = s(z,z') := by
    obtain ⟨⟨z,z'⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨z,z',hh.symm⟩
  have hz : z ∈ G e := hzz.symm ▸ Sym2.mem_mk_left z z'
  have hxz : Conn G S x z := pivotal_endpoint_connected G S x u hxu e hep z hz
  have hzsupport : z ∈ r.path.support := SimpleGraph.Walk.mem_support_of_mem_edges he hz
  apply (r.counted_iff D ω x u).mpr
  refine ⟨hc.1,hxu,?_,hc.2.2.2.2.mono_right ?_⟩
  · intro f hf
    refine ⟨hr hf,?_⟩
    intro hxf
    obtain ⟨a,b,hab⟩ : ∃ a b, G f = s(a,b) := by
      obtain ⟨⟨a,b⟩,hh⟩ := Quot.exists_rep (G f)
      exact ⟨a,b,hh.symm⟩
    have ha : a ∈ G f := hab.symm ▸ Sym2.mem_mk_left a b
    have haz : Conn G S z a := conn_mono G hr (r.retained_connects_support z a hzsupport
      (SimpleGraph.Walk.mem_support_of_mem_edges hf ha))
    have hua : Conn G S u a := conn_trans G S (conn_symm G S hxu) (conn_trans G S hxz haz)
    have hvf : Conn G (S \ {f}) v y := conn_delete_of_unconnected_endpoint G S v y a hvy f ha
      (fun hva => hne (conn_trans G S hua (conn_symm G S hva)))
    have hBf : Conn G (ω \ {f}) u v := conn_mono G (show B ⊆ ω \ {f} from fun g hg => ⟨hB hg,fun hgf =>
      Set.disjoint_left.mp hd hg ((Set.mem_singleton_iff.mp hgf).symm ▸ hf)⟩) huv
    apply (hc.2.2.2.1 f hf).2
    rw [huniv]
    exact conn_trans G _ (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hxf)
      (conn_trans G _ hBf (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hvf))
  · rw [huniv]
    exact Set.inter_subset_left

end RawCorridor
end OneLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLegGeometry
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem counted_split_legs (r : RawCorridor G k) (D : Set V) (ω B : Set E)
    (x y u v : V) (hc : r.counted Set.univ ω x y)
    (hr : r.retained ⊆ ω ∩ internalEdges G D) (hB : B ⊆ ω)
    (hd : Disjoint B r.retained) (huv : Conn G B u v)
    (hxu : Conn G (ω ∩ internalEdges G D) x u)
    (hvy : Conn G (ω ∩ internalEdges G D) v y)
    (hne : ¬Conn G (ω ∩ internalEdges G D) u v) :
    r.counted D ω x u ∨ r.counted D ω v y := by
  obtain ⟨e,he⟩ := r.retained_nonempty (by have := hc.1; omega)
  by_cases hp : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) x u
  · exact Or.inl (r.counted_one_leg D ω B x y u v hc hr hB hd huv hxu hvy hne e he hp)
  · have hxu' : Conn G ((ω ∩ internalEdges G D) \ {e}) x u := not_not.mp hp
    have hp' : ¬Conn G ((ω ∩ internalEdges G D) \ {e}) y v := by
      intro hyv
      apply (hc.2.2.2.1 e he).2
      have huniv : ω ∩ internalEdges G Set.univ = ω := by
        apply Set.Subset.antisymm Set.inter_subset_left
        exact fun _ he => ⟨he,fun _ _ => trivial⟩
      rw [huniv]
      have hB' : Conn G (ω \ {e}) u v := conn_mono G (show B ⊆ ω \ {e} from fun f hf => ⟨hB hf,fun hfe =>
        Set.disjoint_left.mp hd hf ((Set.mem_singleton_iff.mp hfe).symm ▸ he)⟩) huv
      exact conn_trans G _ (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) hxu')
        (conn_trans G _ hB' (conn_mono G (Set.sdiff_subset_sdiff_left Set.inter_subset_left) (conn_symm G _ hyv)))
    exact Or.inr ((r.counted_symm D ω y v).mp (r.counted_one_leg D ω B y x v u
      ((r.counted_symm Set.univ ω x y).mp hc) hr hB hd (conn_symm G B huv)
      (conn_symm G _ hvy) (conn_symm G _ hxu) (fun h => hne (conn_symm G _ h)) e he hp'))

 
theorem counted_legs_of_disjoint (w r : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base)
    (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint)
    (hc : r.counted Set.univ ω x y) (hd : Disjoint w.retained r.retained) :
    r.counted (w.interior : Set V)ᶜ ω x w.base ∨ r.counted (w.interior : Set V)ᶜ ω w.endpoint y := by
  apply r.counted_split_legs (w.interior : Set V)ᶜ ω w.retained x y w.base w.endpoint
    hc ?_ hq.1 hd w.retained_conn hxu hvy hne
  intro e he
  have heω := (hc.2.2.2.1 e he).1.1
  exact (w.open_subset_exterior_retained ω hq heω).resolve_right
    (fun hw => Set.disjoint_left.mp hd hw he)

end RawCorridor
end TwoLegGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TwoLegPenaltyTerms
attribute [local instance] Classical.propDecidable Classical.decEq

theorem corridorPenaltyTerm_legs (G : BondGraph V E) (hG : Function.Injective G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (w r : RawCorridor G k) (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) :
    corridorPenaltyTerm G P p Set.univ ω x y r ≤
      (∑ e ∈ (w.retained_finite hG).toFinset, if e ∈ r.retained then r.weight P p else 0) +
        corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω x w.base r +
        corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω w.endpoint y r := by
  have hr := r.weight_nonneg P hP p
  have hs : 0 ≤ ∑ e ∈ (w.retained_finite hG).toFinset, if e ∈ r.retained then r.weight P p else 0 :=
    Finset.sum_nonneg (fun _ _ => ite_nonneg hr (le_refl _))
  have hl := corridorPenaltyTerm_nonneg G P hP p (w.interior : Set V)ᶜ ω x w.base r
  have ht := corridorPenaltyTerm_nonneg G P hP p (w.interior : Set V)ᶜ ω w.endpoint y r
  by_cases hc : r.counted Set.univ ω x y
  · rw [corridorPenaltyTerm,ite_eq_left hc]
    by_cases hd : Disjoint w.retained r.retained
    · rcases w.counted_legs_of_disjoint r ω hq x y hxu hvy hne hc hd with hh | hh
      · have he : corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω x w.base r = r.weight P p := ite_eq_left hh
        linarith
      · have he : corridorPenaltyTerm G P p (w.interior : Set V)ᶜ ω w.endpoint y r = r.weight P p := ite_eq_left hh
        linarith
    · obtain ⟨e,hew,her⟩ := Set.not_disjoint_iff.mp hd
      have he := Finset.single_le_sum (f := fun e => if e ∈ r.retained then r.weight P p else 0)
        (s := (w.retained_finite hG).toFinset) (fun _ _ => ite_nonneg hr (le_refl _))
        ((w.retained_finite hG).mem_toFinset.mpr hew)
      rw [ite_eq_left her] at he
      linarith
  · rw [corridorPenaltyTerm,ite_eq_right hc]
    linarith

 

theorem corridorPenalty_legs (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) :
    corridorPenalty G P p k Set.univ ω x y ≤
      (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) +
      corridorPenalty G P p k (w.interior : Set V)ᶜ ω x w.base +
      corridorPenalty G P p k (w.interior : Set V)ᶜ ω w.endpoint y := by
  have hs : Summable (fun r : RawCorridor G k => ∑ e ∈ (w.retained_finite hG).toFinset,
      if e ∈ r.retained then r.weight P p else 0) :=
    (hasSum_sum (fun e (_ : e ∈ (w.retained_finite hG).toFinset) =>
      (summable_raw_edge_weights G hloc P p k e).hasSum)).summable
  have hl := corridorPenalty_summable G hloc P p k (w.interior : Set V)ᶜ ω x w.base
  have hr := corridorPenalty_summable G hloc P p k (w.interior : Set V)ᶜ ω w.endpoint y
  have hh := (corridorPenalty_summable G hloc P p k Set.univ ω x y).tsum_le_tsum
    (fun r => corridorPenaltyTerm_legs G hG P hP p k w r ω hq x y hxu hvy hne) ((hs.add hl).add hr)
  rw [(hs.add hl).tsum_add hr,hs.tsum_add hl,
    Summable.tsum_finsetSum (fun e _ => summable_raw_edge_weights G hloc P p k e)] at hh
  exact hh

end TwoLegPenaltyTerms
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section WeightedLegComparison
attribute [local instance] Classical.propDecidable Classical.decEq

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
theorem base_not_interior (w : RawCorridor G k) : w.base ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,true_or,not_true_eq_false,and_false,not_false_eq_true]
theorem endpoint_not_interior (w : RawCorridor G k) : w.endpoint ∉ w.interior := by
  simp only [interior,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton,or_true,not_true_eq_false,and_false,not_false_eq_true]
end RawCorridor

 
theorem deformedConnection_legs_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (ω : Set E)
    (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) (c : ℝ)
    (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-t*c) * deformedConnection G P p k t (w.interior : Set V)ᶜ ω x w.base *
      deformedConnection G P p k t (w.interior : Set V)ᶜ ω w.endpoint y ≤
        deformedConnection G P p k t Set.univ ω x y := by
  have hx : x ∈ (w.interior : Set V)ᶜ := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hxu with h | h
    · rw [h]; exact w.base_not_interior
    · exact h.1
  have hy : y ∈ (w.interior : Set V)ᶜ := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hvy with h | h
    · rw [←h]; exact w.endpoint_not_interior
    · exact h.2
  have hxy : Conn G (ω ∩ internalEdges G Set.univ) x y := by
    apply conn_mono G (show ω ⊆ ω ∩ internalEdges G Set.univ from fun _ h => ⟨h,fun _ _ => trivial⟩)
    exact conn_trans G ω (conn_mono G Set.inter_subset_left hxu)
      (conn_trans G ω (conn_mono G hq.1 w.retained_conn) (conn_mono G Set.inter_subset_left hvy))
  have hleft : x ∈ (w.interior : Set V)ᶜ ∧ w.base ∈ (w.interior : Set V)ᶜ ∧
      Conn G (ω ∩ internalEdges G (w.interior : Set V)ᶜ) x w.base := ⟨hx,w.base_not_interior,hxu⟩
  have hright : w.endpoint ∈ (w.interior : Set V)ᶜ ∧ y ∈ (w.interior : Set V)ᶜ ∧
      Conn G (ω ∩ internalEdges G (w.interior : Set V)ᶜ) w.endpoint y := ⟨w.endpoint_not_interior,hy,hvy⟩
  simp only [deformedConnection,ite_eq_left hleft,ite_eq_left hright,Set.mem_univ,hxy,and_self,ite_true]
  rw [←Real.exp_add,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := (corridorPenalty_legs G hG hloc P hP p k w ω hq x y hxu hvy hne).trans
    (add_le_add (add_le_add hc le_rfl) le_rfl)
  simpa only [mul_add] using mul_le_mul_of_nonpos_left hh (neg_nonpos.mpr ht)

end WeightedLegComparison
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section UniformLegCost
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem exists_uniform_corridor_leg_cost (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (d : ℕ) (hd : ∀ x, degree G x ≤ d) (a : ℝ)
    (hP : ∀ x y, 0 ≤ walkKernel G hloc a x y)
    (hpcrit : 0 < (pc G:ℝ)) (hpcrit₁ : (pc G:ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : unitInterval), (pc G:ℝ)/2 ≤ (p:ℝ) → p < pc G →
      ∀ (k : ℕ), 3 ≤ k → ∀ w : RawCorridor G k,
      (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight (walkKernel G hloc a) p else 0) ≤ Real.exp (C*(k:ℝ)) := by
  obtain ⟨C,hC,hcost⟩ := exists_uniform_corridor_edge_cost G hloc d hd a hP hpcrit hpcrit₁
  refine ⟨C,hC,?_⟩
  intro p hpnear hp k hk w
  have hh := Finset.sum_le_sum (s := (w.retained_finite hG).toFinset)
    (fun e _ => hcost p hpnear hp k hk e)
  have hcard : ((w.retained_finite hG).toFinset.card:ℝ) ≤ (k:ℝ) := by
    rw [←Set.ncard_eq_toFinset_card w.retained (w.retained_finite hG),w.retained_ncard hG]
    exact Nat.cast_le.mpr w.path_length
  have hk0 : (0:ℝ) < k := Nat.cast_pos.mpr (by omega)
  calc
    _ ≤ ((w.retained_finite hG).toFinset.card:ℝ)*(Real.exp (C*(k:ℝ))/(k:ℝ)) := by
      simpa only [Finset.sum_const,nsmul_eq_mul] using hh
    _ ≤ (k:ℝ)*(Real.exp (C*(k:ℝ))/(k:ℝ)) := mul_le_mul_of_nonneg_right hcard (div_nonneg (Real.exp_pos _).le hk0.le)
    _ = _ := by field_simp

end UniformLegCost
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SimplePathCuts
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem simplePath_edge_cut {H : SimpleGraph V} {u v : V} (q : H.Walk u v)
    (hq : q.IsPath) (e : Sym2 V) (he : e ∈ q.edges) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧ (∀ z ∈ A, z ∈ q.support) ∧
      ∀ f ∈ q.edges, f ≠ e → ∀ a ∈ f, ∀ b ∈ f, a ∈ A ↔ b ∈ A := by
  induction q with
  | nil => simp only [SimpleGraph.Walk.edges_nil,List.not_mem_nil] at he
  | @cons u a v h q ih =>
    have hu : u ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hq).2
    have huv : v ≠ u := fun hvu => hu (hvu ▸ q.end_mem_support)
    by_cases hh : e = s(u,a)
    · refine ⟨{u},rfl,huv,?_,?_⟩
      · intro z hz; rw [Set.mem_singleton_iff] at hz; subst z; simp
      · intro f hf hfe x hx y hy
        have hfq : f ∈ q.edges := (List.mem_cons.mp hf).resolve_left (fun h' => hfe (h'.trans hh.symm))
        have hxu : x ≠ u := fun hxu => hu (hxu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hfq hx)
        have hyu : y ≠ u := fun hyu => hu (hyu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hfq hy)
        simp only [Set.mem_singleton_iff,hxu,hyu]
    · have heq : e ∈ q.edges := (List.mem_cons.mp he).resolve_left hh
      obtain ⟨A,ha,hv,hA,hcut⟩ := ih hq.of_cons heq
      refine ⟨insert u A,Set.mem_insert u A,?_,?_,?_⟩
      · intro hvA
        rcases hvA with h' | h'
        · exact huv h'
        · exact hv h'
      · intro z hz
        rcases hz with rfl | hz
        · simp
        · exact List.mem_cons_of_mem u (hA z hz)
      · intro f hf hfe x hx y hy
        rcases List.mem_cons.mp hf with rfl | hf
        · have hx' : x = u ∨ x = a := by simpa only [SimpleGraph.Dart.edge,Sym2.mem_iff] using hx
          have hy' : y = u ∨ y = a := by simpa only [SimpleGraph.Dart.edge,Sym2.mem_iff] using hy
          have hxm : x ∈ insert u A := hx'.elim (fun h' => h' ▸ Set.mem_insert u A)
            (fun h' => h' ▸ Set.mem_insert_of_mem u ha)
          have hym : y ∈ insert u A := hy'.elim (fun h' => h' ▸ Set.mem_insert u A)
            (fun h' => h' ▸ Set.mem_insert_of_mem u ha)
          exact iff_of_true hxm hym
        · have hxu : x ≠ u := fun hxu => hu (hxu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hf hx)
          have hyu : y ≠ u := fun hyu => hu (hyu ▸ SimpleGraph.Walk.mem_support_of_mem_edges hf hy)
          simpa only [Set.mem_insert_iff,hxu,hyu,false_or] using hcut f hf hfe x hx y hy

theorem conn_closed_vertex_set (G : BondGraph V E) (S : Set E) (A : Set V)
    (hA : ∀ e ∈ S, ∀ a ∈ G e, ∀ b ∈ G e, a ∈ A → b ∈ A)
    {x y : V} (hc : Conn G S x y) (hx : x ∈ A) : y ∈ A := by
  induction hc with
  | refl => exact hx
  | @tail a b _ hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact hA e he a (heq.symm ▸ Sym2.mem_mk_left a b) b (heq.symm ▸ Sym2.mem_mk_right a b) ih

end SimplePathCuts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section CalibratedCut
attribute [local instance] Classical.propDecidable Classical.decEq

theorem conn_edge_members (G : BondGraph V E) (S : Set E) (e : E) (he : e ∈ S)
    (a b : V) (ha : a ∈ G e) (hb : b ∈ G e) : Conn G S a b := by
  obtain ⟨x,y,hxy⟩ : ∃ x y, G e = s(x,y) := by
    obtain ⟨⟨x,y⟩,hh⟩ := Quot.exists_rep (G e)
    exact ⟨x,y,hh.symm⟩
  rw [hxy,Sym2.mem_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact conn_refl G S _
  · exact Relation.ReflTransGen.single ⟨e,he,hxy⟩
  · exact conn_symm G S (Relation.ReflTransGen.single ⟨e,he,hxy⟩)
  · exact conn_refl G S _

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

 

theorem calibration_pivotal_ports (hG : Function.Injective G) (w : RawCorridor G k)
    (ω : Set E) (hq : ω ∈ w.calibrationEvent)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint)
    (e : E) (he : e ∈ w.retained) : ¬Conn G (ω \ {e}) w.base w.endpoint := by
  obtain ⟨A,hu,hv,hA,hcut⟩ := simplePath_edge_cut w.path w.path_isPath (G e) he
  let B := A ∪ {z | Conn G (w.exterior ω) w.base z}
  have hAport (z : V) (hz : z ∈ A) (ho : z ∉ w.interior) : z = w.base := by
    rcases w.support_exterior_ports (hA z hz) ho with h | h
    · exact h
    · exact (hv (h ▸ hz)).elim
  have hConnOut (z : V) (hz : Conn G (w.exterior ω) w.base z) : z ∉ w.interior := by
    rcases conn_internal_eq_or_mem G (w.interior : Set V)ᶜ hz with h | h
    · rw [←h]; exact w.base_not_interior
    · exact h.2
  have hBclosed : ∀ f ∈ ω \ {e}, ∀ a ∈ G f, ∀ b ∈ G f, a ∈ B → b ∈ B := by
    intro f hf a ha b hb hba
    rcases w.open_subset_exterior_retained ω hq hf.1 with hfs | hfr
    · have hab := conn_edge_members G (w.exterior ω) f hfs a b ha hb
      rcases hba with haa | hua
      · have hau : a = w.base := hAport a haa (hfs.2 a ha)
        exact Or.inr (hau ▸ hab)
      · exact Or.inr (conn_trans G _ hua hab)
    · have hfe : G f ≠ G e := fun h => hf.2 (hG h)
      have haa : a ∈ A := by
        rcases hba with h | h
        · exact h
        · rcases w.support_exterior_ports (SimpleGraph.Walk.mem_support_of_mem_edges hfr ha)
            (hConnOut a h) with hau | hav
          · exact hau ▸ hu
          · exact (hne (hav ▸ h)).elim
      exact Or.inl ((hcut (G f) hfr hfe a ha b hb).mp haa)
  intro hc
  have hh := conn_closed_vertex_set G (ω \ {e}) B hBclosed hc (Or.inl hu)
  exact hh.elim hv hne

end RawCorridor
end CalibratedCut
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ReverseCalibration
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem calibration_counted_of_orientation (hG : Function.Injective G) (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V)
    (hxu : Conn G (w.exterior ω) x w.base) (hvy : Conn G (w.exterior ω) w.endpoint y)
    (hne : ¬Conn G (w.exterior ω) w.base w.endpoint) : w.counted Set.univ ω x y := by
  have huniv : ω ∩ internalEdges G Set.univ = ω := by
    apply Set.Subset.antisymm Set.inter_subset_left
    exact fun _ he => ⟨he,fun _ _ => trivial⟩
  apply (w.counted_iff Set.univ ω x y).mpr
  refine ⟨hlen,?_⟩
  unfold corridorCounted
  rw [huniv]
  refine ⟨conn_trans G ω (conn_mono G Set.inter_subset_left hxu)
    (conn_trans G ω (conn_mono G hq.1 w.retained_conn) (conn_mono G Set.inter_subset_left hvy)),?_,hq.2⟩
  intro e he
  refine ⟨hq.1 he,?_⟩
  intro hxy
  have hS : w.exterior ω ⊆ ω \ {e} := by
    intro f hf
    refine ⟨hf.1,?_⟩
    intro hfe
    have hfe' : f = e := hfe
    subst f
    exact Set.disjoint_left.mp (w.specified_disjoint_exterior hlen) (Or.inl he) hf.2
  exact w.calibration_pivotal_ports hG ω hq hne e he
    (conn_trans G _ (conn_mono G hS (conn_symm G _ hxu))
      (conn_trans G _ hxy (conn_mono G hS (conn_symm G _ hvy))))

 

theorem calibration_counted_iff (hG : Function.Injective G) (w : RawCorridor G k)
    (hlen : 3 ≤ w.path.length) (ω : Set E) (hq : ω ∈ w.calibrationEvent) (x y : V) :
    w.counted Set.univ ω x y ↔ ¬Conn G (w.exterior ω) w.base w.endpoint ∧
      ((Conn G (w.exterior ω) w.base x ∧ Conn G (w.exterior ω) w.endpoint y) ∨
       (Conn G (w.exterior ω) w.endpoint x ∧ Conn G (w.exterior ω) w.base y)) := by
  constructor
  · intro hc
    exact w.counted_exterior_orientation hlen ω hq x y hc.2.2
  · rintro ⟨hne,ho⟩
    rcases ho with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · exact w.calibration_counted_of_orientation hG hlen ω hq x y (conn_symm G _ hx) hy hne
    · exact (w.counted_symm Set.univ ω y x).mp
        (w.calibration_counted_of_orientation hG hlen ω hq y x (conn_symm G _ hy) hx hne)

end RawCorridor
end ReverseCalibration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorLegObservable
attribute [local instance] Classical.propDecidable Classical.decEq

theorem deformedConnection_restrict_config (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) (k : ℕ) (t : ℝ) (D : Set V) (ω : Set E) (x y : V) :
    deformedConnection G P p k t D (ω ∩ internalEdges G D) x y =
      deformedConnection G P p k t D ω x y := by
  have he : (ω ∩ internalEdges G D) ∩ internalEdges G D = ω ∩ internalEdges G D :=
    Set.inter_assoc _ _ _ |>.trans (congrArg (ω ∩ ·) (Set.inter_self _))
  have hc (w : RawCorridor G k) : w.counted D (ω ∩ internalEdges G D) x y ↔ w.counted D ω x y := by
    simp only [RawCorridor.counted,corridorCounted,he]
  simp only [deformedConnection,corridorPenalty,corridorPenaltyTerm,hc,he]

noncomputable def exteriorLegProduct (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) : ℝ :=
  if ¬Conn G (w.exterior ω) w.base w.endpoint then
    deformedConnection G P p k t (w.interior : Set V)ᶜ ω x w.base *
      deformedConnection G P p k t (w.interior : Set V)ᶜ ω w.endpoint y else 0

theorem exteriorLegProduct_nonneg (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) :
    0 ≤ exteriorLegProduct G P p t w ω x y := by
  unfold exteriorLegProduct
  by_cases h : ¬Conn G (w.exterior ω) w.base w.endpoint
  · rw [ite_eq_left h]
    exact mul_nonneg (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
      (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
  · rw [ite_eq_right h]

theorem exteriorLegProduct_le_one (G : BondGraph V E) (P : V → V → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) {k : ℕ} (t : ℝ) (ht : 0 ≤ t)
    (w : RawCorridor G k) (ω : Set E) (x y : V) :
    exteriorLegProduct G P p t w ω x y ≤ 1 := by
  unfold exteriorLegProduct
  by_cases h : ¬Conn G (w.exterior ω) w.base w.endpoint
  · rw [ite_eq_left h]
    exact (mul_le_of_le_one_left (deformedConnection_nonneg _ _ _ _ _ _ _ _ _)
      (deformedConnection_le_one G P hP p k t ht _ _ _ _)).trans
      (deformedConnection_le_one G P hP p k t ht _ _ _ _)
  · rw [ite_eq_right h]
    exact zero_le_one

theorem measurable_exteriorLegProduct [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (p : ℝ) {k : ℕ} (t : ℝ)
    (w : RawCorridor G k) (x y : V) :
    Measurable (fun ω => exteriorLegProduct G P p t w ω x y) := by
  apply Measurable.ite
    ((measurableSet_restrictedConn G (internalEdges G (w.interior:Set V)ᶜ) w.base w.endpoint).compl)
  · exact (measurable_deformedConnection G P p k t _ x w.base).mul
      (measurable_deformedConnection G P p k t _ w.endpoint y)
  · exact measurable_const

theorem exteriorLegProduct_restrict (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E) (x y : V) :
    exteriorLegProduct G P p t w ω x y =
      exteriorLegProduct G P p t w (ω ∩ internalEdges G (w.interior:Set V)ᶜ) x y := by
  simp only [exteriorLegProduct,RawCorridor.exterior,Set.inter_assoc,Set.inter_self,
    deformedConnection_restrict_config]
  rfl

end ExteriorLegObservable
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibrationFactor
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem measurableSet_calibration (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) : MeasurableSet w.calibrationEvent := by
  rw [w.calibrationEvent_eq hG hloc]
  apply measurableSet_edgePattern
  apply Finset.disjoint_left.mpr
  intro e he hb
  exact Set.disjoint_left.mp w.retained_disjoint_blockers
    ((w.retained_finite hG).mem_toFinset.mp he) ((w.blockers_finite hloc).mem_toFinset.mp hb)

 

theorem calibration_integral (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (p : unitInterval)
    (f : Set E → ℝ) (hf : Measurable f)
    (hfr : ∀ ω, f ω = f (ω ∩ internalEdges G (w.interior:Set V)ᶜ)) :
    (∫ ω, if ω ∈ w.calibrationEvent then f ω else 0 ∂law p) =
      (law p).real w.calibrationEvent * ∫ ω, f ω ∂law p := by
  have hh := integral_mul_disjoint_coordinates p _ _ (w.specified_disjoint_exterior hlen)
    (fun ω => if ω ∈ w.calibrationEvent then (1:ℝ) else 0) f
    (Measurable.ite (w.measurableSet_calibration hG hloc) measurable_const measurable_const) hf
    (fun ω => by rw [w.calibration_restriction ω]) hfr
  simpa only [ite_mul,one_mul,zero_mul,integral_event_indicator p _ (w.measurableSet_calibration hG hloc)] using hh

theorem calibration_weighted_integral (hG : Function.Injective G) (hloc : LocallyFinite G)
    (w : RawCorridor G k) (hlen : 3 ≤ w.path.length) (P : V → V → ℝ)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1)
    (f : Set E → ℝ) (hf : Measurable f)
    (hfr : ∀ ω, f ω = f (ω ∩ internalEdges G (w.interior:Set V)ᶜ)) :
    (∫ ω, if ω ∈ w.calibrationEvent then w.weight P p * f ω else 0 ∂law p) =
      w.probability P * ∫ ω, f ω ∂law p := by
  have he : (fun ω => if ω ∈ w.calibrationEvent then w.weight P p * f ω else 0) =
      (fun ω => w.weight P p * (if ω ∈ w.calibrationEvent then f ω else 0)) := by
    funext ω
    by_cases h : ω ∈ w.calibrationEvent <;> simp only [h,ite_true,ite_false,mul_zero]
  rw [he,integral_const_mul,w.calibration_integral hG hloc hlen p f hf hfr,
    ←mul_assoc,w.calibration_identity hG hloc P p hp hp₁]

end RawCorridor
end CalibrationFactor
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibratedDerivativeTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem calibrated_leg_product_le_term (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (ω : Set E) (x y : V) :
    (if ω ∈ w.calibrationEvent then w.weight P p * (Real.exp (-t*c) *
      exteriorLegProduct G P p t w ω x y) else 0) ≤
        corridorPenaltyTerm G P p Set.univ ω x y w * deformedConnection G P p k t Set.univ ω x y := by
  have hr : 0 ≤ corridorPenaltyTerm G P p Set.univ ω x y w * deformedConnection G P p k t Set.univ ω x y :=
    mul_nonneg (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
      (deformedConnection_nonneg G P p k t Set.univ ω x y)
  by_cases hq : ω ∈ w.calibrationEvent
  · rw [ite_eq_left hq]
    by_cases hn : ¬Conn G (w.exterior ω) w.base w.endpoint
    · rw [exteriorLegProduct,ite_eq_left hn]
      by_cases hx : Conn G (w.exterior ω) x w.base
      · by_cases hy : Conn G (w.exterior ω) w.endpoint y
        · have hj := w.calibration_counted_of_orientation hG hlen ω hq x y hx hy hn
          rw [corridorPenaltyTerm,ite_eq_left hj]
          have hh := mul_le_mul_of_nonneg_left
            (deformedConnection_legs_lower G hG hloc P hP p k w ω hq x y hx hy hn c hc t ht)
            (w.weight_nonneg P hP p)
          simpa only [mul_assoc] using hh
        · have hz : deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.endpoint y = 0 := by
            simp only [deformedConnection,show ¬Conn G (ω ∩ internalEdges G (w.interior:Set V)ᶜ) w.endpoint y from hy,and_false,ite_false]
          simpa only [hz,mul_zero] using hr
      · have hz : deformedConnection G P p k t (w.interior:Set V)ᶜ ω x w.base = 0 := by
          simp only [deformedConnection,show ¬Conn G (ω ∩ internalEdges G (w.interior:Set V)ᶜ) x w.base from hx,and_false,ite_false]
        simpa only [hz,zero_mul,mul_zero] using hr
    · simpa only [exteriorLegProduct,ite_eq_right hn,mul_zero] using hr
  · simpa only [ite_eq_right hq] using hr

theorem integrable_corridorDerivativeTerm [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (D : Set V) (x y : V)
    (w : RawCorridor G k) :
    Integrable (fun ω => corridorPenaltyTerm G P p D ω x y w *
      deformedConnection G P p k t D ω x y) (law p) := by
  have hh := ((integrable_deformedConnection G P hP p k t ht D x y).const_mul
    (w.weight P p)).indicator (w.measurableSet_counted D x y)
  have he : (fun ω => corridorPenaltyTerm G P p D ω x y w *
      deformedConnection G P p k t D ω x y) =
      {ω | w.counted D ω x y}.indicator (fun ω => w.weight P p * deformedConnection G P p k t D ω x y) := by
    funext ω
    simp only [Set.indicator,Set.mem_ofPred_eq,corridorPenaltyTerm,ite_mul,zero_mul]
  rw [he]
  exact hh

end CalibratedDerivativeTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section CalibratedDecreaseKernel
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_exteriorLegProduct [Countable V] [Countable E]
    (G : BondGraph V E) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) (x y : V) :
    Integrable (fun ω => exteriorLegProduct G P p t w ω x y) (law p) := by
  apply Integrable.mono' (integrable_const (1:ℝ))
    (measurable_exteriorLegProduct G P p t w x y).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_of_nonneg (exteriorLegProduct_nonneg G P p t w ω x y)]
  exact exteriorLegProduct_le_one G P hP p t ht w ω x y

 

theorem calibrated_derivative_kernel_lower [Countable V] [Countable E]
    (G : BondGraph V E) (hG : Function.Injective G) (hloc : LocallyFinite G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp : 0 < (p:ℝ)) (hp₁ : (p:ℝ) < 1)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) (x y : V) :
    w.probability P * Real.exp (-t*c) * (∫ ω, exteriorLegProduct G P p t w ω x y ∂law p) ≤
      ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
        deformedConnection G P p k t Set.univ ω x y ∂law p := by
  have hf := integrable_exteriorLegProduct G P hP p t ht w x y
  have hi : Integrable (fun ω => if ω ∈ w.calibrationEvent then w.weight P p *
      (Real.exp (-t*c) * exteriorLegProduct G P p t w ω x y) else 0) (law p) :=
    ((hf.const_mul (Real.exp (-t*c))).const_mul (w.weight P p)).indicator
      (w.measurableSet_calibration hG hloc)
  have hh := integral_mono hi (integrable_corridorDerivativeTerm G P hP p k t ht Set.univ x y w)
    (fun ω => calibrated_leg_product_le_term G hG hloc P hP p k w hlen c hc t ht ω x y)
  rw [w.calibration_weighted_integral hG hloc hlen P p hp hp₁
    (fun ω => Real.exp (-t*c)*exteriorLegProduct G P p t w ω x y)
    ((measurable_exteriorLegProduct G P p t w x y).const_mul _)
    (fun ω => congrArg (Real.exp (-t*c)*·) (exteriorLegProduct_restrict G P p t w ω x y)),
    integral_const_mul] at hh
  simpa only [mul_assoc] using hh

end CalibratedDecreaseKernel
end Percolation

 
namespace Percolation
open MeasureTheory
section NonnegativeRealTonelli
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem real_tonelli_of_integrable_sum {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (μ : Measure Ω) (F : I → Ω → ℝ) (hF : ∀ i, Integrable (F i) μ)
    (hn : ∀ i ω, 0 ≤ F i ω) (hs : ∀ᵐ ω ∂μ, Summable (fun i => F i ω))
    (hi : Integrable (fun ω => ∑' i, F i ω) μ) :
    Summable (fun i => ∫ ω, F i ω ∂μ) ∧
      (∑' i, ∫ ω, F i ω ∂μ) = ∫ ω, ∑' i, F i ω ∂μ := by
  have he : (∑' i, ENNReal.ofReal (∫ ω, F i ω ∂μ)) =
      ∫⁻ ω, ENNReal.ofReal (∑' i, F i ω) ∂μ := by
    simp_rw [ofReal_integral_eq_lintegral_ofReal (hF _) (Filter.Eventually.of_forall (hn _))]
    rw [←lintegral_tsum (fun i => (hF i).aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
    apply lintegral_congr_ae
    filter_upwards [hs] with ω hω
    exact (ENNReal.ofReal_tsum_of_nonneg (fun i => hn i ω) hω).symm
  have ht : (∑' i, ENNReal.ofReal (∫ ω, F i ω ∂μ)) ≠ ⊤ := by
    rw [he,←ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall (fun ω => tsum_nonneg (fun i => hn i ω)))]
    exact ENNReal.ofReal_ne_top
  have hh : Summable (fun i => ∫ ω, F i ω ∂μ) := by
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn _))] using ENNReal.summable_toReal ht
  refine ⟨hh,?_⟩
  apply integral_tsum_of_summable_integral_norm hF
  simpa only [Real.norm_of_nonneg (hn _ _)] using hh

end NonnegativeRealTonelli
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section TotalExteriorLegs
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exteriorLegProduct_sum (G : BondGraph V E) (P : V → V → ℝ)
    (p : ℝ) {k : ℕ} (t : ℝ) (w : RawCorridor G k) (ω : Set E)
    (hu : (cluster G ω w.base).Finite) (hv : (cluster G ω w.endpoint).Finite) :
    Summable (fun xy : V × V => exteriorLegProduct G P p t w ω xy.1 xy.2) ∧
    (∑' xy : V × V, exteriorLegProduct G P p t w ω xy.1 xy.2) =
      if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0 := by
  by_cases hn : ¬Conn G (w.exterior ω) w.base w.endpoint
  · have hsu : Summable (deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.base) :=
      summable_of_hasFiniteSupport (deformedConnection_finite_support G P p k t (w.interior:Set V)ᶜ ω w.base hu)
    have hsv : Summable (deformedConnection G P p k t (w.interior:Set V)ᶜ ω w.endpoint) :=
      summable_of_hasFiniteSupport (deformedConnection_finite_support G P p k t (w.interior:Set V)ᶜ ω w.endpoint hv)
    have hsx : Summable (fun x => deformedConnection G P p k t (w.interior:Set V)ᶜ ω x w.base) := by
      simpa only [deformedConnection_symm G P p k t (w.interior:Set V)ᶜ ω _ w.base] using hsu
    have hs := hsx.mul_of_nonneg hsv
      (fun x => deformedConnection_nonneg G P p k t _ ω x w.base)
      (fun y => deformedConnection_nonneg G P p k t _ ω w.endpoint y)
    simp only [exteriorLegProduct,ite_eq_left hn]
    refine ⟨hs,?_⟩
    rw [←hsx.tsum_mul_tsum hsv hs]
    simp only [deformedClusterMass,deformedConnection_symm G P p k t (w.interior:Set V)ᶜ ω _ w.base]
  · simp only [exteriorLegProduct,ite_eq_right hn,summable_zero,tsum_zero,and_self]

 

theorem exteriorLegProduct_integral_sum [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (hp : p < pc G)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) :
    Summable (fun xy : V × V => ∫ ω, exteriorLegProduct G P p t w ω xy.1 xy.2 ∂law p) ∧
    (∑' xy : V × V, ∫ ω, exteriorLegProduct G P p t w ω xy.1 xy.2 ∂law p) =
      ∫ ω, (if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0) ∂law p := by
  have hae : ∀ᵐ ω ∂law p, Summable (fun xy : V × V => exteriorLegProduct G P p t w ω xy.1 xy.2) ∧
    (∑' xy : V × V, exteriorLegProduct G P p t w ω xy.1 xy.2) =
      if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0 := by
    filter_upwards [subcritical_cluster_finite_ae G p hp w.base,
      subcritical_cluster_finite_ae G p hp w.endpoint] with ω hu hv
    exact exteriorLegProduct_sum G P p t w ω hu hv
  have hi := (integrable_distinct_deformed_product G hloc hqt P hP p hp k t ht
    (w.interior:Set V)ᶜ w.base w.endpoint).congr (hae.mono (fun _ h => h.2.symm))
  obtain ⟨hs,he⟩ := real_tonelli_of_integrable_sum (law p)
    (fun xy : V × V => fun ω => exteriorLegProduct G P p t w ω xy.1 xy.2)
    (fun xy => integrable_exteriorLegProduct G P hP p t ht w xy.1 xy.2)
    (fun xy ω => exteriorLegProduct_nonneg G P p t w ω xy.1 xy.2)
    (hae.mono (fun _ h => h.1)) hi
  exact ⟨hs,he.trans (integral_congr_ae (hae.mono (fun _ h => h.2)))⟩

end TotalExteriorLegs
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SummableDerivativeTerm
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

omit [Nonempty V] in
theorem integral_corridorDerivativeTerm_le (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp1 : (p:ℝ) < 1)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) (x y : V) :
    (∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
      deformedConnection G P p k t Set.univ ω x y ∂law p) ≤
      w.probability P * (twoPoint G p x w.base * twoPoint G p w.endpoint y +
        twoPoint G p x w.endpoint * twoPoint G p w.base y) := by
  apply le_trans (integral_mono (integrable_corridorDerivativeTerm G P hP p k t ht Set.univ x y w)
    (integrable_corridorPenaltyTerm G P p Set.univ x y w) (fun ω =>
      mul_le_of_le_one_right (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
        (deformedConnection_le_one G P hP p k t ht Set.univ ω x y)))
  exact integral_corridorPenaltyTerm_le G hG hloc P hP p hp0 hp1 x y w

theorem summable_twoPoint_pairs (G : BondGraph V E)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G) (p : unitInterval)
    (hp : p < pc G) (u v : V) :
    Summable (fun xy : V × V => twoPoint G p xy.1 u * twoPoint G p v xy.2) := by
  have hs : Summable (fun x => twoPoint G p x u) := by
    simpa only [twoPoint_symm G p _ u] using summable_twoPoint_subcritical G hloc hqt p hp u
  exact hs.mul_of_nonneg (summable_twoPoint_subcritical G hloc hqt p hp v)
    (fun x => twoPoint_nonneg G p x u) (fun y => twoPoint_nonneg G p v y)

omit [Nonempty V] [Countable V] [Countable E] in
 theorem integral_corridorDerivativeTerm_nonneg (G : BondGraph V E)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : unitInterval) (k : ℕ)
    (t : ℝ) (w : RawCorridor G k) (x y : V) :
    0 ≤ ∫ ω, corridorPenaltyTerm G P p Set.univ ω x y w *
      deformedConnection G P p k t Set.univ ω x y ∂law p :=
  integral_nonneg (fun ω => mul_nonneg (corridorPenaltyTerm_nonneg G P hP p Set.univ ω x y w)
    (deformedConnection_nonneg G P p k t Set.univ ω x y))

theorem summable_corridorDerivativeTerm_pairs (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    {k : ℕ} (t : ℝ) (ht : 0 ≤ t) (w : RawCorridor G k) :
    Summable (fun xy : V × V => ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
      deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p) := by
  have hs : Summable (fun xy : V × V => w.probability P *
      (twoPoint G p xy.1 w.base * twoPoint G p w.endpoint xy.2 +
       twoPoint G p xy.1 w.endpoint * twoPoint G p w.base xy.2)) :=
    ((summable_twoPoint_pairs G hloc hqt p hp w.base w.endpoint).add
      (summable_twoPoint_pairs G hloc hqt p hp w.endpoint w.base)).mul_left (w.probability P)
  exact Summable.of_nonneg_of_le
    (fun (xy : V × V) => integral_corridorDerivativeTerm_nonneg G P hP p k t w xy.1 xy.2)
    (fun (xy : V × V) => integral_corridorDerivativeTerm_le G hG hloc P hP p hp0
      ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) t ht w xy.1 xy.2) hs

end SummableDerivativeTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SingleTemplateDecrease
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Countable V] [Countable E] [Nonempty V]

 

theorem calibrated_derivative_template_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    w.probability P * Real.exp (-t*c) *
      (∫ ω, (if ¬Conn G (w.exterior ω) w.base w.endpoint then
        deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.base *
          deformedClusterMass G P p k t (w.interior:Set V)ᶜ ω w.endpoint else 0) ∂law p) ≤
      ∑' xy : V × V, ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
        deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p := by
  obtain ⟨hs,he⟩ := exteriorLegProduct_integral_sum G hloc hqt P hP p hp t ht w
  have hh := (hs.mul_left (w.probability P * Real.exp (-t*c))).tsum_le_tsum
    (fun (xy : V × V) => calibrated_derivative_kernel_lower G hG hloc P hP p hp0
      ((show (p:ℝ)<(pc G:ℝ) from hp).trans_le (pc G).2.2) k w hlen c hc t ht xy.1 xy.2)
    (summable_corridorDerivativeTerm_pairs G hG hloc hqt P hP p hp0 hp t ht w)
  rwa [tsum_mul_left,he] at hh

 

theorem calibrated_derivative_template_row_lower (G : BondGraph V E) (hG : Function.Injective G)
    (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ a, (neighbors G hloc a).card ≤ d)
    (P : V → V → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hpcrit : 0 < (pc G:ℝ))
    (p : unitInterval) (hp : p < pc G) (hpnear : (pc G:ℝ)/2 ≤ (p:ℝ))
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (k : ℕ) (w : RawCorridor G k) (hlen : 3 ≤ w.path.length)
    (c : ℝ) (hc : (∑ e ∈ (w.retained_finite hG).toFinset, ∑' r : RawCorridor G k,
        if e ∈ r.retained then r.weight P p else 0) ≤ c)
    (t : ℝ) (ht : 0 ≤ t) :
    w.probability P * Real.exp (-t*c) *
      (deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.base *
        deformedSusceptibility G P p k t (w.interior:Set V)ᶜ w.endpoint -
        (1+2*(d:ℝ)/(pc G:ℝ))*(maxSusceptibility G p)^2*(matrixCoeff (T^3) w.base w.endpoint).re) ≤
      ∑' xy : V × V, ∫ ω, corridorPenaltyTerm G P p Set.univ ω xy.1 xy.2 w *
        deformedConnection G P p k t Set.univ ω xy.1 xy.2 ∂law p := by
  have hm := deformed_distinct_correlation_uniform G hloc hqt d hd P hP hpcrit p hp hpnear T hT
    k t ht (w.interior:Set V)ᶜ w.base w.endpoint
  exact (mul_le_mul_of_nonneg_left hm (mul_nonneg (w.2.2.mass_nonneg P hP) (Real.exp_pos _).le)).trans
    (calibrated_derivative_template_lower G hG hloc hqt P hP p ((half_pos hpcrit).trans_le hpnear)
      hp k w hlen c hc t ht)

end SingleTemplateDecrease
end Percolation

 
namespace Percolation
universe u u' v
section ErasureNaturality
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {H : SimpleGraph V} {H' : SimpleGraph V'}

theorem walk_map_dropUntil (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) (z : V) (hz : z ∈ w.support) :
    (w.dropUntil z hz).map f = (w.map f).dropUntil (f z)
      (by simpa only [SimpleGraph.Walk.support_map] using List.mem_map_of_mem hz) := by
  induction w with
  | @nil x =>
    have he : z = x := by simpa using hz
    subst z
    rfl
  | @cons x a y h w ih =>
    by_cases he : x = z
    · subst z
      simp only [SimpleGraph.Walk.dropUntil_first]
    · have hfe : f x ≠ f z := fun h => he (hf h)
      simp only [SimpleGraph.Walk.dropUntil,he,hfe,SimpleGraph.Walk.map_cons]
      exact ih _

 

theorem walk_map_bypass (f : H →g H') (hf : Function.Injective f)
    {x y : V} (w : H.Walk x y) : w.bypass.map f = (w.map f).bypass := by
  induction w with
  | nil => rfl
  | @cons x a y h w ih =>
    have hm : f x ∈ (w.map f).bypass.support ↔ x ∈ w.bypass.support := by
      rw [←ih,SimpleGraph.Walk.support_map]
      exact List.mem_map_of_injective hf
    by_cases hx : x ∈ w.bypass.support
    · have hfx := hm.mpr hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_left hx,dite_eq_left hfx]
      simp only [walk_map_dropUntil f hf,ih]
    · have hfx := mt hm.mp hx
      simp only [SimpleGraph.Walk.bypass,SimpleGraph.Walk.map_cons,dite_eq_right hx,dite_eq_right hfx,ih]

namespace HoldingWalk

def map (f : H →g H') : {k : ℕ} → {x y : V} → HoldingWalk H k x y → HoldingWalk H' k (f x) (f y)
  | _,_,_,.nil _ => .nil _
  | _,_,_,.hold w => .hold (w.map f)
  | _,_,_,.step h w => .step (f.map_rel h) (w.map f)

theorem map_vertices (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).vertices = w.vertices.map f := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,vertices,List.map_cons,ih]
  | step h w ih => simp only [map,vertices,List.map_cons,ih]

theorem map_withoutHolds (f : H →g H') {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).withoutHolds = w.withoutHolds.map f := by
  induction w with
  | nil => rfl
  | hold w ih => exact ih
  | step h w ih => simp only [map,withoutHolds,SimpleGraph.Walk.map_cons,ih]

theorem map_erase (f : H →g H') (hf : Function.Injective f)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) :
    (w.map f).erase = w.erase.map f := by
  simp only [erase,map_withoutHolds,SimpleGraph.Walk.reverse_map,
    ←walk_map_bypass f hf]

end HoldingWalk
end ErasureNaturality
end Percolation

 
namespace Percolation
universe u u' u'' v
section RawWalkMaps
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {V' : Type u'} {V'' : Type u''}
  {H : SimpleGraph V} {H' : SimpleGraph V'} {H'' : SimpleGraph V''}
namespace HoldingWalk

theorem map_map (f : H →g H') (g : H' →g H'')
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).map g = w.map (g.comp f) := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

theorem map_id {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : w.map ((SimpleGraph.Hom.id : H →g H)) = w := by
  induction w with
  | nil => rfl
  | hold w ih => exact congrArg hold ih
  | step h w ih => exact congrArg (step _) ih

theorem mass_map (f : H →g H') (P : V → V → ℝ) (Q : V' → V' → ℝ)
    (hPQ : ∀ x y, Q (f x) (f y) = P x y)
    {k : ℕ} {x y : V} (w : HoldingWalk H k x y) : (w.map f).mass Q = w.mass P := by
  induction w with
  | nil => rfl
  | hold w ih => simp only [map,mass,hPQ,ih]
  | step h w ih => simp only [map,mass,hPQ,ih]
end HoldingWalk

def rawWalkMap (f : H →g H') (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    Σ x y, HoldingWalk H' k x y := ⟨f w.1,f w.2.1,w.2.2.map f⟩

theorem rawWalkMap_comp (f : H →g H') (g : H' →g H'') (k : ℕ)
    (w : Σ x y, HoldingWalk H k x y) : rawWalkMap g k (rawWalkMap f k w) = rawWalkMap (g.comp f) k w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_map]
      rfl

theorem rawWalkMap_id (k : ℕ) (w : Σ x y, HoldingWalk H k x y) :
    rawWalkMap ((SimpleGraph.Hom.id : H →g H)) k w = w := by
  cases w with
  | mk x w =>
    cases w with
    | mk y w =>
      simp only [rawWalkMap,HoldingWalk.map_id]
      rfl

def rawWalkEquiv (f : H ≃g H') (k : ℕ) :
    (Σ x y, HoldingWalk H k x y) ≃ (Σ x y, HoldingWalk H' k x y) where
  toFun := rawWalkMap f.toHom k
  invFun := rawWalkMap f.symm.toHom k
  left_inv w := by
    rw [rawWalkMap_comp]
    have he : f.symm.toHom.comp f.toHom = (SimpleGraph.Hom.id : H →g H) := by
      ext x
      exact f.symm_apply_apply x
    rw [he,rawWalkMap_id]
  right_inv w := by
    rw [rawWalkMap_comp]
    have he : f.toHom.comp f.symm.toHom = (SimpleGraph.Hom.id : H' →g H') := by
      ext x
      exact f.apply_symm_apply x
    rw [he,rawWalkMap_id]

end RawWalkMaps
section GraphAutWalks
attribute [local instance] Classical.propDecidable Classical.decEq
variable {V : Type u} {E : Type v}

theorem openSimpleGraph_univ_adj (G : BondGraph V E) (x y : V) :
    (openSimpleGraph G Set.univ).Adj x y ↔ x ≠ y ∧ Adj G x y := by
  simp only [openSimpleGraph,Adj,Set.mem_univ,true_and]

def autSimpleGraph (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) :
    openSimpleGraph G Set.univ ≃g openSimpleGraph G Set.univ where
  toEquiv := a
  map_rel_iff' := by
    intro x y
    simp only [openSimpleGraph_univ_adj,a.injective.ne_iff]
    exact and_congr_right (fun _ => ⟨fun h => by simpa using adj_aut G (isAut_symm G hab) h,
      adj_aut G hab⟩)

namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}
def autEquiv {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) : RawCorridor G k ≃ RawCorridor G k :=
  rawWalkEquiv (autSimpleGraph G hab) k

theorem aut_path {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path = w.path.map (autSimpleGraph G hab).toHom :=
  w.2.2.map_erase _ a.injective

theorem aut_path_length {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.length = w.path.length := by
  have hh := congrArg (fun q => q.length) (aut_path hab w)
  exact hh.trans (SimpleGraph.Walk.length_map _ _)

end RawCorridor
end GraphAutWalks
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TemplateCovariance
attribute [local instance] Classical.propDecidable Classical.decEq
namespace RawCorridor
variable {G : BondGraph V E} {k : ℕ}

theorem aut_base {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).base = a w.base := rfl

theorem aut_endpoint {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).endpoint = a w.endpoint := rfl

theorem aut_support {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.support = w.path.support.map a := by
  exact (congrArg (fun q => q.support) (aut_path hab w)).trans
    (SimpleGraph.Walk.support_map _ _)

theorem aut_edges {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).path.edges = w.path.edges.map (Sym2.map a) := by
  exact (congrArg (fun q => q.edges) (aut_path hab w)).trans
    (SimpleGraph.Walk.edges_map _ _)

theorem aut_interior {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (z : V) :
    a z ∈ (autEquiv hab w).interior ↔ z ∈ w.interior := by
  simp only [interior,Finset.mem_sdiff,List.mem_toFinset]
  rw [aut_support hab w]
  simp only [aut_base,aut_endpoint,Finset.mem_insert,Finset.mem_singleton,
    List.mem_map_of_injective a.injective,a.injective.eq_iff]

theorem aut_retained {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).retained ↔ e ∈ w.retained := by
  simp only [retained,Set.mem_ofPred_eq,aut_edges hab w,hab e]
  exact List.mem_map_of_injective (Sym2.map.injective a.injective)

theorem aut_blockers {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) (e : E) :
    b e ∈ (autEquiv hab w).blockers ↔ e ∈ w.blockers := by
  simp only [blockers,Set.mem_sdiff,Set.mem_ofPred_eq,aut_retained]
  apply and_congr_left
  intro _
  constructor
  · rintro ⟨z,hz,he⟩
    rw [hab e] at he
    obtain ⟨y,hy,rfl⟩ := Sym2.mem_map.mp he
    exact ⟨y,(aut_interior hab w y).mp hz,hy⟩
  · rintro ⟨z,hz,he⟩
    refine ⟨a z,(aut_interior hab w z).mpr hz,?_⟩
    rw [hab e]
    exact Sym2.mem_map.mpr ⟨z,he,rfl⟩

theorem aut_blockers_ncard {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (w : RawCorridor G k) :
    (autEquiv hab w).blockers.ncard = w.blockers.ncard := by
  have he : w.blockers = b ⁻¹' (autEquiv hab w).blockers := by
    ext e
    exact (aut_blockers hab w e).symm
  rw [he,Set.ncard_preimage_of_injective_subset_range b.injective]
  exact fun e _ => b.surjective e

theorem aut_probability {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (w : RawCorridor G k) :
    (autEquiv hab w).probability P = w.probability P :=
  w.2.2.mass_map (autSimpleGraph G hab).toHom P P hP

theorem aut_weight {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (P : V → V → ℝ) (hP : ∀ x y, P (a x) (a y) = P x y) (p : ℝ) (w : RawCorridor G k) :
    (autEquiv hab w).weight P p = w.weight P p := by
  simp only [weight,aut_probability hab P hP,aut_path_length,aut_blockers_ncard]

end RawCorridor
end TemplateCovariance
end Percolation

end OAI
