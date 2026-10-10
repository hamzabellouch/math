import OAI.Geometry.PinnedDistances.UniformCore

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
noncomputable section
open NumberField
open scoped BigOperators
noncomputable section
open MeasureTheory
open scoped Topology
noncomputable section
open MeasureTheory
open scoped Topology ENNReal
noncomputable section
open MeasureTheory NumberField
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MeasureTheory
noncomputable section
open Filter
open scoped Topology
noncomputable section
open scoped BigOperators

namespace WeakPinned.Core.Fibers
open scoped BigOperators
open Variance
variable {V : Type u1} {I : Type u2} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

def edges : Finset (V × V) := G.edgeSet (-1) Finset.univ

def edgeCount : ℝ := G.edges.card

def edgeLaw (x y : V) : ℝ := if (x,y) ∈ G.edges then 1/G.edgeCount else 0

def fiberWeight (e : I) : ℝ := (G.targets e).card / G.edgeCount

def incoming (y : V) : Finset V := Finset.univ.filter (fun x => (x,y) ∈ G.edges)

def incomingWeight (y : V) : ℝ := (G.incoming y).card / G.edgeCount

omit [Fintype I] in
lemma active_univ_neg_one (e : I) : G.active (-1) Finset.univ e := by
  refine ⟨Finset.mem_univ _,?_⟩
  have h := Nat.cast_nonneg (α:=ℝ) (G.size Finset.univ e)
  linarith

lemma edgeCount_eq : G.edgeCount = ∑ e, ((G.targets e).card : ℝ) := by
  unfold edgeCount edges
  rw [edgeSet_card]
  simp [G.active_univ_neg_one,size]

omit [Fintype I] in
lemma edgeLaw_nonneg (x y : V) : 0 ≤ G.edgeLaw x y := by
  unfold edgeLaw edgeCount
  split_ifs <;> positivity

omit [Fintype I] in
lemma edgeLaw_diag (x : V) : G.edgeLaw x x=0 := by
  have hh : (x,x) ∉ G.edges := by
    intro h
    exact G.edge_no_loop (-1) Finset.univ x (Finset.mem_filter.mp h).2
  simp [edgeLaw,hh]

omit [Fintype I] in
lemma fiberWeight_nonneg (e : I) : 0 ≤ G.fiberWeight e := by
  unfold fiberWeight edgeCount
  positivity

lemma sum_fiberWeight (hG : 0 < G.edgeCount) : ∑ e, G.fiberWeight e=1 := by
  simp only [fiberWeight,← Finset.sum_div,← G.edgeCount_eq,div_self hG.ne']

omit [Fintype I] in
lemma fiberWeight_prob (e : I) (y : V) :
    G.fiberWeight e*prob (G.targets e) y = if y ∈ G.targets e then 1/G.edgeCount else 0 := by
  by_cases hy : y ∈ G.targets e
  · have hk : ((G.targets e).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr ⟨y,hy⟩)
    simp only [fiberWeight,prob,ite_eq_left hy]
    field_simp
  · simp [prob,hy]

lemma sampling_fiber (x y : V) :
    (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      G.edgeLaw x y := by
  have he := G.edge_indicator (-1) Finset.univ x y
  simp only [G.active_univ_neg_one,true_and,Finset.mem_inter,Finset.mem_univ,and_true] at he
  have hh : (∑ e, if G.source e=x then G.fiberWeight e * prob (G.targets e) y else 0) =
      (∑ e, if G.source e=x ∧ y ∈ G.targets e then (1:ℝ) else 0)/G.edgeCount := by
    simp only [Finset.sum_div,G.fiberWeight_prob]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hs : G.source e=x <;> by_cases hy : y ∈ G.targets e <;> simp [hs,hy]
  rw [hh,he]
  by_cases he : G.edge (-1) Finset.univ x y <;> simp [edgeLaw,edges,edgeSet,he]

lemma fiber_marginal (y : V) :
    (∑ e, G.fiberWeight e * prob (G.targets e) y) = ∑ x, G.edgeLaw x y := by
  simp_rw [← G.sampling_fiber]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  simp

omit [Fintype I] in
lemma incoming_marginal (y : V) : ∑ x, G.edgeLaw x y=G.incomingWeight y := by
  simp only [edgeLaw,incomingWeight,incoming,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  simp only [mul_one_div]

omit [Fintype I] in
lemma sampling_incoming (x y : V) :
    G.incomingWeight y*prob (G.incoming y) x=G.edgeLaw x y := by
  by_cases he : (x,y) ∈ G.edges
  · have hm : x ∈ G.incoming y := by simp [incoming,he]
    have hk : ((G.incoming y).card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_ne_zero.mpr ⟨x,hm⟩)
    simp only [incomingWeight,prob,ite_eq_left hm,edgeLaw,ite_eq_left he]
    field_simp
  · have hm : x ∉ G.incoming y := by simp [incoming,he]
    simp [prob,hm,edgeLaw,he]

omit [Fintype I] in
lemma sum_edgeLaw (hG : 0 < G.edgeCount) : (∑ x, ∑ y, G.edgeLaw x y)=1 := by
  rw [← Fintype.sum_prod_type (f:=fun xy : V × V => G.edgeLaw xy.1 xy.2)]
  simp only [edgeLaw,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  have he : Finset.univ.filter (fun xy : V × V => xy ∈ G.edges)=G.edges := by simp
  rw [he]
  change G.edgeCount*(1/G.edgeCount)=1
  field_simp

omit [Fintype I] in
lemma sum_incomingWeight (hG : 0 < G.edgeCount) : ∑ y, G.incomingWeight y=1 := by
  simp_rw [← G.incoming_marginal]
  rw [Finset.sum_comm,G.sum_edgeLaw hG]

lemma fiber_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (y : V) :
    (∑ e, G.fiberWeight e*prob (G.targets e) y) ≤ B*prob Finset.univ y := by
  rw [G.fiber_marginal]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun x _ => hdom x y)
  simpa only [← Finset.mul_sum,pairProb_symm _ _ y,sum_pairProb Finset.univ (by simpa using hn)] using hh

omit [Fintype I] in
lemma incoming_domination (B : ℝ) (hdom : ∀ x y, G.edgeLaw x y ≤ B*pairProb Finset.univ x y)
    (hn : 2 ≤ Fintype.card V) (x : V) :
    (∑ y, G.incomingWeight y*prob (G.incoming y) x) ≤ B*prob Finset.univ x := by
  simp_rw [G.sampling_incoming]
  have hh := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hdom x y)
  simpa only [← Finset.mul_sum,sum_pairProb Finset.univ (by simpa using hn)] using hh

omit [Fintype I] in
/-- The exact bound on omitted small incoming degrees, not just a formal
    little-o assertion. -/
lemma small_incoming_mass (T : ℝ) (hT : 0 ≤ T) :
    (∑ y, if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤
      (Fintype.card V : ℝ)*T/G.edgeCount := by
  have hn : 0 ≤ G.edgeCount := by unfold edgeCount; positivity
  have hh : ∀ y, (if ((G.incoming y).card : ℝ)<T then G.incomingWeight y else 0) ≤ T/G.edgeCount := by
    intro y
    split_ifs with hy
    · exact div_le_div_of_nonneg_right hy.le hn
    · exact div_nonneg hT hn
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun y _ => hh y)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_div_assoc] using hs

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u3} {I : Type u4} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

abbrev Active (K : ℝ) (C : Finset V) := {e : I // G.active K C e}

instance (K : ℝ) (C : Finset V) : Fintype (G.Active K C) := by
  classical
  exact Fintype.ofFinite _

def onCore (K : ℝ) (C : Finset V) : Fibers C (G.Active K C) where
  source e := ⟨G.source e.val,e.property.1⟩
  targets e := Finset.univ.filter (fun y : C => y.val ∈ G.targets e.val)
  no_loop e := by simpa using G.no_loop e.val
  disjoint e f hef hs := by
    apply Finset.disjoint_left.mpr
    intro y hye hyf
    have hne : e.val ≠ f.val := fun h => hef (Subtype.ext h)
    have hs' : G.source e.val=G.source f.val := congrArg Subtype.val hs
    exact Finset.disjoint_left.mp (G.disjoint _ _ hne hs')
      (Finset.mem_filter.mp hye).2 (Finset.mem_filter.mp hyf).2

omit [Fintype V] [Fintype I] in
lemma onCore_targets (K : ℝ) (C : Finset V) (e : G.Active K C) :
    ((G.onCore K C).targets e).image Subtype.val=G.targets e.val ∩ C := by
  ext y
  simp only [onCore,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter]
  constructor
  · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
  · rintro ⟨hy,hC⟩; exact ⟨⟨y,hC⟩,hy,rfl⟩

omit [Fintype V] [Fintype I] in
lemma onCore_size (K : ℝ) (C : Finset V) (e : G.Active K C) :
    ((G.onCore K C).targets e).card=G.size C e.val := by
  rw [← Finset.card_image_of_injective _ Subtype.val_injective,G.onCore_targets,size]

omit [Fintype I] in
omit [Fintype V] in
lemma onCore_edge (K : ℝ) (C : Finset V) (x y : C) :
    (G.onCore K C).edge (-1) Finset.univ x y ↔ G.edge K C x.val y.val := by
  simp only [edge,active_univ_neg_one,true_and,Finset.mem_inter,Finset.mem_univ,and_true]
  constructor
  · rintro ⟨e,hs,hy⟩
    refine ⟨e.val,e.property,congrArg Subtype.val hs,?_⟩
    exact ⟨(Finset.mem_filter.mp hy).2,y.property⟩
  · rintro ⟨e,ha,hs,hy⟩
    exact ⟨⟨e,ha⟩,Subtype.ext hs,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy.1⟩⟩

omit [Fintype I] in
lemma onCore_edges_image (K : ℝ) (C : Finset V) :
    ((G.onCore K C).edges).image (fun xy : C × C => (xy.1.val,xy.2.val))=G.edgeSet K C := by
  ext xy
  simp only [edges,edgeSet,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨x,y⟩,hxy,rfl⟩
    exact (G.onCore_edge K C x y).mp hxy
  · intro hxy
    obtain ⟨e,ha,hs,hy⟩ := hxy
    have hxC : xy.1 ∈ C := hs ▸ ha.1
    have hyC : xy.2 ∈ C := (Finset.mem_inter.mp hy).2
    refine ⟨(⟨xy.1,hxC⟩,⟨xy.2,hyC⟩),?_,rfl⟩
    exact (G.onCore_edge K C _ _).mpr ⟨e,ha,hs,hy⟩

omit [Fintype I] in
lemma onCore_card (K : ℝ) (C : Finset V) :
    ((G.onCore K C).edges).card=(G.edgeSet K C).card := by
  rw [← G.onCore_edges_image]
  apply (Finset.card_image_of_injective _ _).symm
  intro a b h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

omit [Fintype I] in
lemma onCore_degree (K : ℝ) (C : Finset V) (x : C) :
    (G.onCore K C).degree (-1) Finset.univ x=G.degree K C x.val := by
  simp only [degree,G.onCore_edge]
  have hsum (f : V → ℝ) (hf : ∀ y, y ∉ C → f y=0) : (∑ y : C, f y.val)=∑ y, f y := by
    rw [Finset.sum_coe_sort]
    apply Finset.sum_subset (Finset.subset_univ _) (fun y _ hy => hf y hy)
  simp only [← Finset.sum_boole,← Finset.sum_add_distrib]
  apply hsum (fun y => (if G.edge K C x.val y then 1 else 0)+(if G.edge K C y x.val then 1 else 0))
  intro y hy
  have h1 : ¬ G.edge K C x.val y := by
    rintro ⟨e,ha,hs,he⟩
    exact hy (Finset.mem_inter.mp he).2
  have h2 : ¬ G.edge K C y x.val := by
    rintro ⟨e,ha,hs,he⟩
    exact hy (hs ▸ ha.1)
  simp [h1,h2]

end WeakPinned.Core.Fibers

namespace WeakPinned.Core.Fibers
open scoped BigOperators
variable {V : Type u5} {I : Type u6} [Fintype V] [Fintype I] [DecidableEq V]
variable (G : Fibers V I)

omit [Fintype V] [Fintype I] in
lemma onCore_size_subset (K : ℝ) (C : Finset V) (D : Finset C) (e : G.Active K C) :
    (G.onCore K C).size D e=G.size (D.image Subtype.val) e.val := by
  unfold size
  rw [← Finset.card_image_of_injective _ Subtype.val_injective]
  congr 1
  ext y
  simp only [Finset.mem_image,Finset.mem_inter]
  constructor
  · rintro ⟨z,⟨hz,hd⟩,rfl⟩
    exact ⟨(Finset.mem_filter.mp hz).2,⟨z,hd,rfl⟩⟩
  · rintro ⟨hy,z,hz,rfl⟩
    exact ⟨z,⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hy⟩,hz⟩,rfl⟩

def heavyCount (lam : ℝ) (D : Finset V) : ℝ :=
  ∑ e, if lam*((G.targets e).card : ℝ) ≤ (G.size D e : ℝ) ∧ G.source e ∈ D
    then (G.size D e : ℝ) else 0

omit [Fintype V] in
lemma onCore_heavyCount (K lam : ℝ) (C : Finset V) (D : Finset C) :
    (G.onCore K C).heavyCount lam D =
      ∑ e, if G.active K C e ∧ lam*(G.size C e : ℝ) ≤ (G.size (D.image Subtype.val) e : ℝ) ∧
        G.source e ∈ D.image Subtype.val then (G.size (D.image Subtype.val) e : ℝ) else 0 := by
  classical
  unfold heavyCount
  simp_rw [G.onCore_size_subset,G.onCore_size]
  have hs (e : G.Active K C) : (G.onCore K C).source e ∈ D ↔ G.source e.val ∈ D.image Subtype.val := by
    constructor
    · intro h; exact Finset.mem_image.mpr ⟨_,h,rfl⟩
    · intro h
      obtain ⟨y,hy,he⟩ := Finset.mem_image.mp h
      have hh : y=(G.onCore K C).source e := Subtype.ext he
      simpa only [hh] using hy
  simp_rw [hs]
  rw [← Finset.sum_subtype (p:=G.active K C) (Finset.univ.filter (G.active K C)) (by simp)
    (fun e => if lam*(G.size C e : ℝ) ≤ (G.size (D.image Subtype.val) e : ℝ) ∧
      G.source e ∈ D.image Subtype.val then (G.size (D.image Subtype.val) e : ℝ) else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : G.active K C e <;> simp [he]

omit [Fintype I] in
lemma degree_marginal (x : V) : (∑ y, G.edgeLaw x y)+(∑ y, G.edgeLaw y x)=
    G.degree (-1) Finset.univ x/G.edgeCount := by
  simp only [edgeLaw,edges,edgeSet,Finset.mem_filter,Finset.mem_univ,true_and,
    ← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,degree,add_div,mul_one_div]

end WeakPinned.Core.Fibers

namespace WeakPinned
open scoped BigOperators
open WeakPinned.Core

abbrev coreGraph (P : Finset Plane) (s : ℝ) (C : Finset P) :=
  (planarFibers P s).onCore (cutoff s P.card) C

lemma coreGraph_heavy (P : Finset Plane) (s lam : ℝ) (C : Finset P) (D : Finset C) :
    (coreGraph P s C).heavyCount lam D = heavyCount P s (cutoff s P.card) lam C (D.image Subtype.val) := by
  rw [(planarFibers P s).onCore_heavyCount]
  unfold heavyCount heavyFiber
  apply Finset.sum_congr rfl
  intro e _
  simp only [and_assoc]

structure PreparedGraph (V : Type u7) (I : Type u8) [Fintype V] [Fintype I] [DecidableEq V]
    (G : Fibers V I) (θ γ c η : ℝ) : Prop where
  card_ge : 2 ≤ Fintype.card V
  lower : (θ-η)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1) ≤ G.edgeCount
  upper : G.edgeCount ≤ (θ+η/8)*(Fintype.card V : ℝ)*((Fintype.card V : ℝ)-1)
  degree : ∀ x, 2*(θ-η)*((Fintype.card V : ℝ)-1) ≤ G.degree (-1) Finset.univ x
  fiber : ∀ e, (Fintype.card V : ℝ)^γ < ((G.targets e).card : ℝ)
  subset : ∀ D, G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D ≤ (θ+η)*(D.card : ℝ)*((D.card : ℝ)-1)
  small : ∀ D, (D.card : ℝ) ≤ (Fintype.card V : ℝ)^(1-c) →
    G.heavyCount (1/Real.log (Fintype.card V : ℝ)) D ≤ η*(D.card : ℝ)*((D.card : ℝ)-1)

lemma PreparedCore.graph {s γ c η : ℝ} {P : Finset Plane} {C : Finset P}
    (h : PreparedCore s γ c η P C) :
    PreparedGraph C ((planarFibers P s).Active (cutoff s P.card) C) (coreGraph P s C) (Theta s) γ c η := by
  have hn : Fintype.card C=C.card := Fintype.card_coe C
  have he : (coreGraph P s C).edgeCount = ((planarFibers P s).edgeSet (cutoff s P.card) C).card := by
    unfold Core.Fibers.edgeCount
    rw [(planarFibers P s).onCore_card]
  refine ⟨by simpa only [hn] using h.card_two,?_,?_,?_,?_,?_,?_⟩
  · simpa only [he,hn] using h.lower
  · simpa only [he,hn] using h.upper
  · intro x
    simpa only [hn,(planarFibers P s).onCore_degree] using h.degree x.val x.property
  · intro e
    rw [(planarFibers P s).onCore_size,hn]
    exact h.large_fiber.trans_lt e.property.2
  · intro D
    rw [hn,coreGraph_heavy]
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using h.subset (D.image Subtype.val)
  · intro D hD
    rw [hn,coreGraph_heavy]
    have hc : (D.image Subtype.val).card=D.card := Finset.card_image_of_injective _ Subtype.val_injective
    simpa only [hc] using h.small (D.image Subtype.val) (by simpa only [hc,hn] using hD)

/-- Actual arbitrarily large real planar graphs, with all uniform subset
bounds simultaneously. No graph condition is added to the main hypothesis. -/
theorem arbitrarily_large_graph (hfail : ¬ MainStatement) {s γ c : ℝ}
    (hγ : 0<γ) (hγs : γ<s) (hc : 0<c) (hc1 : c<1)
    (hsc : (1-c)*criticalExponent<s) (hs : ContinuousAt Theta s)
    (η : ℝ) (hη : 0<η) (M : ℕ) :
    ∃ (P : Finset Plane) (C : Finset P), M<C.card ∧
      PreparedGraph C ((planarFibers P s).Active (cutoff s P.card) C) (coreGraph P s C) (Theta s) γ c η := by
  obtain ⟨P,C,hM,hC⟩ := arbitrarily_large_prepared hfail hγ hγs hc hc1 hsc hs η hη M
  exact ⟨P,C,hM,hC.graph⟩

end WeakPinned

end
end
end
end
end
end
end
end

end OAI
