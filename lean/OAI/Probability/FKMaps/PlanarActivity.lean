import OAI.Probability.FKMaps.MapEncoding

namespace OAI

noncomputable section
open Set
namespace FKCRT.GraphMerge
variable {V : Type*} (G : SimpleGraph V)

lemma reachable_eq_of_adj_eq {C : Type*} (f : V→C)
    (h : ∀ u v,G.Adj u v → f u=f v) {u v : V} (hr : G.Reachable u v) : f u=f v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => rfl
  | cons ha p ih => exact (h _ _ ha).trans ih

def componentEquiv {C : Type*} (f : V→C) (hf : Function.Surjective f)
    (he : ∀ u v,G.Reachable u v ↔ f u=f v) : G.ConnectedComponent ≃ C :=
  Equiv.ofBijective (Quot.lift f (fun u v h => (he u v).mp h)) ⟨by
    intro x y h
    refine SimpleGraph.ConnectedComponent.ind₂ (fun u v hh => ?_) x y h
    exact SimpleGraph.ConnectedComponent.sound ((he u v).mpr hh),by
    intro c
    obtain ⟨v,rfl⟩ := hf c
    exact ⟨G.connectedComponentMk v,rfl⟩⟩

lemma sup_edge_reachable_of_reachable {u v : V} (h : G.Reachable u v) (x y : V) :
    (G⊔SimpleGraph.edge u v).Reachable x y ↔ G.Reachable x y := by
  constructor
  · intro hh
    obtain ⟨p⟩ := hh
    induction p with
    | nil => exact .refl _
    | @cons x z y ha p ih =>
      rcases ha with ha | ha
      · exact ha.reachable.trans ih
      · rcases (SimpleGraph.edge_adj _ _ _ _).mp ha with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,hne⟩
        · exact h.trans ih
        · exact h.symm.trans ih
  · exact fun hh => hh.mono le_sup_left

lemma card_sup_edge_of_reachable [Finite V] {u v : V} (h : G.Reachable u v) :
    Nat.card (G⊔SimpleGraph.edge u v).ConnectedComponent=Nat.card G.ConnectedComponent := by
  apply Nat.card_congr
  exact componentEquiv _ G.connectedComponentMk Quot.mk_surjective
    (fun x y => (sup_edge_reachable_of_reachable G h x y).trans SimpleGraph.ConnectedComponent.eq.symm)

/-- Adding one edge between distinct components merges precisely those two
components, including graphs with other isolated vertices. -/
lemma card_sup_edge_of_not_reachable [Finite V] {u v : V} (h : ¬G.Reachable u v) :
    Nat.card (G⊔SimpleGraph.edge u v).ConnectedComponent+1=Nat.card G.ConnectedComponent := by
  classical
  let cu := G.connectedComponentMk u
  let cv := G.connectedComponentMk v
  have hne : cu≠cv := fun hh => h (SimpleGraph.ConnectedComponent.eq.mp hh)
  let f : V → {c : G.ConnectedComponent // c≠cv} := fun x =>
    if hx : G.connectedComponentMk x=cv then ⟨cu,hne⟩ else ⟨G.connectedComponentMk x,hx⟩
  have hf (x : V) : (f x).val=if G.connectedComponentMk x=cv then cu else G.connectedComponentMk x := by
    simp only [f]
    split_ifs <;> rfl
  have hfu : (f u).val=cu := by rw [hf]; simp [cu,hne]
  have hfv : (f v).val=cu := by rw [hf]; simp [cv]
  have he : ∀ x y,(G⊔SimpleGraph.edge u v).Reachable x y ↔ f x=f y := by
    intro x y
    constructor
    · apply reachable_eq_of_adj_eq
      intro a b hab
      apply Subtype.ext
      rcases hab with hab | hab
      · have hh := SimpleGraph.ConnectedComponent.sound hab.reachable
        simp only [hf,hh]
      · rcases (SimpleGraph.edge_adj _ _ _ _).mp hab with ⟨⟨rfl,rfl⟩ | ⟨rfl,rfl⟩,hne'⟩
        · exact hfu.trans hfv.symm
        · exact hfv.trans hfu.symm
    · intro hh
      have hh' := congrArg Subtype.val hh
      simp only [hf] at hh'
      have hedge : (G⊔SimpleGraph.edge u v).Reachable u v := by
        exact (show (G⊔SimpleGraph.edge u v).Adj u v from Or.inr (by
          exact (SimpleGraph.edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,fun huv => h (huv ▸ SimpleGraph.Reachable.refl u)⟩)).reachable
      by_cases hx : G.connectedComponentMk x=cv <;>
        by_cases hy : G.connectedComponentMk y=cv <;>
        simp only [hx,hy,ite_true,ite_false] at hh'
      · exact (SimpleGraph.ConnectedComponent.eq.mp (hx.trans hy.symm)).mono le_sup_left
      · have hxu : (G⊔SimpleGraph.edge u v).Reachable x v :=
          (SimpleGraph.ConnectedComponent.eq.mp hx).mono le_sup_left
        have huy : (G⊔SimpleGraph.edge u v).Reachable u y :=
          (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
        exact hxu.trans (hedge.symm.trans huy)
      · have hxu : (G⊔SimpleGraph.edge u v).Reachable x u :=
          (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
        have hvy : (G⊔SimpleGraph.edge u v).Reachable v y :=
          (SimpleGraph.ConnectedComponent.eq.mp hy.symm).mono le_sup_left
        exact hxu.trans (hedge.trans hvy)
      · exact (SimpleGraph.ConnectedComponent.eq.mp hh').mono le_sup_left
  have hsurj : Function.Surjective f := by
    intro c
    obtain ⟨x,hx⟩ := Quot.mk_surjective c.val
    change G.connectedComponentMk x=c.val at hx
    refine ⟨x,Subtype.ext ?_⟩
    rw [hf,hx,ite_eq_right c.property]
  have hc := Nat.card_congr (componentEquiv _ f hsurj he)
  rw [hc]
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hp : 0 < Fintype.card G.ConnectedComponent := by
    exact Fintype.card_pos_iff.mpr ⟨cu⟩
  omega

end FKCRT.GraphMerge
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_insert (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a) :
    spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a)) =
      spanningGraph a s (A : Set (Orbit a)) ⊔ SimpleGraph.edge (orbit s e.out) (orbit s (a e.out)) := by
  ext v w
  change (v≠w ∧ ((∃ d,orbit a d∈insert e A ∧ orbit s d=v ∧ orbit s (a d)=w) ∨
    (∃ d,orbit a d∈insert e A ∧ orbit s d=w ∧ orbit s (a d)=v))) ↔ _
  constructor
  · rintro ⟨hne,hh|hh⟩
    · obtain ⟨d,hd,hv,hw⟩ := hh
      rcases Finset.mem_insert.mp hd with hd | hd
      · right
        apply (SimpleGraph.edge_adj _ _ _ _).mpr
        refine ⟨?_,hne⟩
        rcases (MapFinite.mk_eq_iff_involution a ha d e).mp hd with rfl | rfl
        · exact Or.inl ⟨hv.symm,hw.symm⟩
        · rw [ha] at hw
          exact Or.inr ⟨hv.symm,hw.symm⟩
      · exact Or.inl ⟨hne,Or.inl ⟨d,hd,hv,hw⟩⟩
    · obtain ⟨d,hd,hw,hv⟩ := hh
      rcases Finset.mem_insert.mp hd with hd | hd
      · right
        apply (SimpleGraph.edge_adj _ _ _ _).mpr
        refine ⟨?_,hne⟩
        rcases (MapFinite.mk_eq_iff_involution a ha d e).mp hd with rfl | rfl
        · exact Or.inr ⟨hv.symm,hw.symm⟩
        · rw [ha] at hv
          exact Or.inl ⟨hv.symm,hw.symm⟩
      · exact Or.inl ⟨hne,Or.inr ⟨d,hd,hw,hv⟩⟩
  · rintro (⟨hne,hh|hh⟩|hh)
    · obtain ⟨d,hd,hv,hw⟩ := hh
      exact ⟨hne,Or.inl ⟨d,Finset.mem_insert_of_mem hd,hv,hw⟩⟩
    · obtain ⟨d,hd,hw,hv⟩ := hh
      exact ⟨hne,Or.inr ⟨d,Finset.mem_insert_of_mem hd,hw,hv⟩⟩
    · rcases (SimpleGraph.edge_adj _ _ _ _).mp hh with ⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,hne⟩
      · refine ⟨hne,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
        rw [show orbit a e.out=e from Quotient.out_eq e]
        exact Finset.mem_insert_self _ _
      · refine ⟨hne,Or.inr ⟨e.out,?_,rfl,rfl⟩⟩
        rw [show orbit a e.out=e from Quotient.out_eq e]
        exact Finset.mem_insert_self _ _

def submapComponents (a s : Perm (Dart n)) (A : Finset (Orbit a)) : ℕ :=
  Nat.card (spanningGraph a s (A : Set (Orbit a))).ConnectedComponent

lemma components_insert_of_reachable (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (h : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    submapComponents a s (insert e A)=submapComponents a s A := by
  simp only [submapComponents,spanningGraph_insert a s ha]
  exact GraphMerge.card_sup_edge_of_reachable _ h

lemma components_insert_of_not_reachable (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (h : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    submapComponents a s (insert e A)+1=submapComponents a s A := by
  simp only [submapComponents,spanningGraph_insert a s ha]
  exact GraphMerge.card_sup_edge_of_not_reachable _ h

/-- The orientable genus defect, on all spanning ribbon subgraphs. -/
def submapDefect (a s : Perm (Dart n)) (ha : Function.Involutive a) (A : Finset (Orbit a)) : ℤ :=
  (A.card:ℤ) - Nat.card (Orbit s) + 2*(submapComponents a s A:ℤ) -
    Nat.card (Orbit (s*partialReversal a ha A))

lemma submapDefect_monotone (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (hf : ∀ d,a d≠d) : Monotone (submapDefect a s ha) := by
  apply Finset.monotone_iff_forall_le_insert.mpr
  intro A e he
  let p := s*partialReversal a ha A
  have hnew : s*partialReversal a ha (insert e A)=p*swap e.out (a e.out) := by
    rw [partialReversal_insert a ha A e he,← mul_assoc]
  have hnc : p e.out ≠ p (a e.out) := fun hh => hf e.out (p.injective hh).symm
  by_cases hr : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))
  · have hk := components_insert_of_reachable a s ha A e hr
    have hb := card_orbit_mul_swap_le p e.out (a e.out)
    simp only [submapDefect,Finset.card_insert_of_notMem he,hnew,hk] at ⊢
    change (A.card:ℤ) - _ + 2*(_ : ℤ) - (Nat.card (Orbit p):ℤ) ≤ _
    omega
  · have hk := components_insert_of_not_reachable a s ha A e hr
    have hn : ¬p.SameCycle e.out (a e.out) := fun hh =>
      hr (spanningGraph_reachable_of_sameCycle a s ha A hh)
    have hc := MapCycles.card_orbits_swap_of_not_sameCycle p
      (a := p e.out) (b := p (a e.out)) (by
        simpa only [sameCycle_apply_left,sameCycle_apply_right] using hn)
    rw [← mul_swap_eq_swap_mul] at hc
    change Nat.card (Orbit (p*swap e.out (a e.out)))+1=Nat.card (Orbit p) at hc
    simp only [submapDefect,Finset.card_insert_of_notMem he,hnew] at ⊢
    change (A.card:ℤ) - _ + 2*(_ : ℤ) - (Nat.card (Orbit p):ℤ) ≤ _
    omega

lemma submapComponents_empty (a s : Perm (Dart n)) :
    submapComponents a s ∅=Nat.card (Orbit s) := by
  have hg : spanningGraph a s (∅ : Finset (Orbit a))=⊥ := by
    ext v w
    simp [spanningGraph]
  rw [submapComponents,hg]
  apply Nat.card_congr
  exact GraphMerge.componentEquiv _ id (Function.surjective_id) (by simp)

lemma submapDefect_empty (a s : Perm (Dart n)) (ha : Function.Involutive a) :
    submapDefect a s ha ∅=0 := by
  simp [submapDefect,submapComponents_empty,partialReversal_empty]
  omega

lemma partialReversal_univ (a : Perm (Dart n)) (ha : Function.Involutive a) :
    partialReversal a ha Finset.univ=a := by
  apply Equiv.ext
  intro d
  simp [partialReversal_apply]

lemma submapDefect_univ (M : LabelledMap n) :
    submapDefect M.val.1 M.val.2 M.property.1 Finset.univ=0 := by
  have hk : submapComponents M.val.1 M.val.2 Finset.univ=1 := by
    dsimp [submapComponents]
    simp only [Finset.coe_univ]
    apply Nat.card_eq_one_iff_unique.mpr
    exact ⟨M.property.2.2.1.preconnected.subsingleton_connectedComponent,
      ⟨(spanningGraph M.val.1 M.val.2 univ).connectedComponentMk (orbit M.val.2 0)⟩⟩
  have he := M.property.2.2.2
  simp only [submapDefect,Finset.card_univ,reversal_card _ M.property.1 M.property.2.1,
    hk,partialReversal_univ]
  omega

/-- Exact planar spanning-subgraph Euler identity. This derives every
subgraph's zero genus from the full-map Euler equality. -/
theorem planar_boundary_card (M : LabelledMap n) (A : Finset (Orbit M.val.1)) :
    Nat.card (Orbit (M.val.2*partialReversal M.val.1 M.property.1 A)) +
      Nat.card (Orbit M.val.2) = 2*submapComponents M.val.1 M.val.2 A+A.card := by
  have hm := submapDefect_monotone M.val.1 M.val.2 M.property.1 M.property.2.1
  have hlo := hm (Finset.empty_subset A)
  have hhi := hm (Finset.subset_univ A)
  rw [submapDefect_empty] at hlo
  rw [submapDefect_univ] at hhi
  simp only [submapDefect] at hlo hhi
  omega

end FKCRT
end


noncomputable section
open scoped BigOperators
namespace FKCRT
variable {n : ℕ}

/-- The source's map marginal, with its common factor sqrt(q) removed. -/
def loopPolynomial (t : ℝ) (M : RootedMap n) : ℝ :=
  ∑ A : Finset (Edge M), t ^ ((Nat.card (Orbit (rotation M *
    partialReversal (reversal M) M.out.property.1 A)) : ℤ)-1)

lemma fkWeight_eq_boundary (q : ℝ) (hq : 0 ≤ q) (M : RootedMap n)
    (A : Finset (Edge M)) :
    fkWeight q M A = Real.sqrt q ^ Nat.card (Orbit (rotation M *
      partialReversal (reversal M) M.out.property.1 A)) := by
  have hh := planar_boundary_card M.out A
  have hh' : (Nat.card (Orbit (rotation M * partialReversal (reversal M) M.out.property.1 A)) : ℝ) +
      (Nat.card (Vertex M) : ℝ) = 2*(clusterCount M A : ℝ)+(A.card : ℝ) := by
    exact_mod_cast hh
  rw [fkWeight,Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hq]
  congr 1
  linarith

/-- Exact finite FK-to-loop normalization, not an asymptotic equivalence. -/
theorem fk_marginal_loopPolynomial (q : ℝ) (hq : 0 < q) (M : RootedMap n) :
    (∑ A : Finset (Edge M),fkWeight q M A) = Real.sqrt q * loopPolynomial (Real.sqrt q) M := by
  rw [loopPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [fkWeight_eq_boundary q hq.le]
  let b := Nat.card (Orbit (rotation M * partialReversal (reversal M) M.out.property.1 A))
  change Real.sqrt q ^ b= Real.sqrt q * Real.sqrt q ^ ((b : ℤ)-1)
  have ht : Real.sqrt q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hq)
  calc
    Real.sqrt q ^ b = Real.sqrt q ^ (1+((b : ℤ)-1)) := by
      rw [show 1+((b : ℤ)-1)=(b : ℤ) by omega,zpow_natCast]
    _ = _ := by rw [zpow_add₀ ht,zpow_one]

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

/-- Exact FK polynomial of the graph with C contracted and R remaining.
Using connected-component counts avoids any relabelling or suppressed-edge
convention for the residual multigraph. -/
def residualWeight (t : ℝ) (a s : Perm (Dart n)) (C B : Finset (Orbit a)) : ℝ :=
  t ^ (2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-
    (submapComponents a s C : ℤ)-1)

def residualPartition (t : ℝ) (a s : Perm (Dart n)) (C R : Finset (Orbit a)) : ℝ :=
  ∑ B∈R.powerset,residualWeight t a s C B

lemma residualPartition_initial (t : ℝ) (M : RootedMap n) :
    residualPartition t (reversal M) (rotation M) ∅ Finset.univ = loopPolynomial t M := by
  simp only [residualPartition,Finset.powerset_univ,loopPolynomial]
  apply Finset.sum_congr rfl
  intro A _
  have hh := planar_boundary_card M.out A
  simp only [residualWeight,Finset.empty_union,submapComponents_empty]
  congr 1
  change Nat.card (Orbit (rotation M*partialReversal (reversal M) M.out.property.1 A)) +
    Nat.card (Orbit (rotation M))=2*submapComponents (reversal M) (rotation M) A+A.card at hh
  omega

lemma residualPartition_terminal (t : ℝ) (a s : Perm (Dart n)) (C : Finset (Orbit a))
    (hC : submapComponents a s C=1) : residualPartition t a s C ∅=1 := by
  simp [residualPartition,residualWeight,hC]

lemma residualWeight_contract (t : ℝ) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C B : Finset (Orbit a)) (e : Orbit a) (he : e∉B)
    (hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualWeight t a s C (insert e B)=residualWeight t a s (insert e C) B := by
  have hk := components_insert_of_not_reachable a s ha C e hn
  simp only [residualWeight,Finset.card_insert_of_notMem he,Finset.union_insert,Finset.insert_union]
  congr 1
  omega

/-- A nonloop edge may be deleted or contracted without a multiplicative
factor; even in the presence of loops and parallel edges. -/
theorem residual_delete_contract (t : ℝ) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=
      residualPartition t a s C R+residualPartition t a s (insert e C) R := by
  rw [residualPartition,Finset.sum_powerset_insert he]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  exact residualWeight_contract t a s ha C B e
    (fun h => he (Finset.mem_powerset.mp hB h)) hn

lemma residualWeight_loop (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C B : Finset (Orbit a)) (e : Orbit a) (he : e∉B)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualWeight t a s C (insert e B)=t*residualWeight t a s C B := by
  have hl' := hl.mono (spanningGraph_mono a s (show (C : Set (Orbit a)) ⊆ (C∪B : Finset (Orbit a)) from
    fun _ h => Finset.mem_union_left _ h))
  have hk := components_insert_of_reachable a s ha (C∪B) e hl'
  simp only [residualWeight,Finset.card_insert_of_notMem he,Finset.union_insert,hk]
  rw [show (2*(submapComponents a s (C∪B) : ℤ)+(↑(B.card+1):ℤ)-(submapComponents a s C : ℤ)-1) =
      1+(2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-(submapComponents a s C : ℤ)-1) by omega,
    zpow_add₀ ht,zpow_one]

/-- A loop has precisely the source factor 1+t. -/
theorem residual_loop (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=(1+t)*residualPartition t a s C R := by
  rw [residualPartition,Finset.sum_powerset_insert he]
  have hh : (∑ B∈R.powerset,residualWeight t a s C (insert e B))=
      t*residualPartition t a s C R := by
    rw [residualPartition,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro B hB
    exact residualWeight_loop t ht a s ha C B e (fun h => he (Finset.mem_powerset.mp hB h)) hl
  rw [hh]
  change residualPartition t a s C R+t*residualPartition t a s C R=_
  ring

lemma residual_bridge_pair (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C R=t*residualPartition t a s (insert e C) R := by
  have hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) :=
    fun h => hb (h.mono (spanningGraph_mono a s (fun _ hx => Finset.mem_union_left _ hx)))
  have hk := components_insert_of_not_reachable a s ha C e hn
  rw [residualPartition,residualPartition,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  have hn' : ¬(spanningGraph a s ((C∪B : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out)) := by
    intro hh
    apply hb
    exact hh.mono (spanningGraph_mono a s (by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (Finset.mem_powerset.mp hB hx)))
  have hk' := components_insert_of_not_reachable a s ha (C∪B) e hn'
  simp only [residualWeight,Finset.insert_union]
  rw [show (2*(submapComponents a s (C∪B) : ℤ)+(B.card : ℤ)-(submapComponents a s C : ℤ)-1)=
    1+(2*(submapComponents a s (insert e (C∪B)) : ℤ)+(B.card : ℤ)-
      (submapComponents a s (insert e C) : ℤ)-1) by omega,zpow_add₀ ht,zpow_one]

/-- A bridge has precisely the source factor 1+t; no residual-map
isomorphism or unproved rank axiom is used. -/
theorem residual_bridge (t : ℝ) (ht : t≠0) (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉R)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) :
    residualPartition t a s C (insert e R)=(1+t)*residualPartition t a s (insert e C) R := by
  have hn : ¬(spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) :=
    fun h => hb (h.mono (spanningGraph_mono a s (fun _ hx => Finset.mem_union_left _ hx)))
  rw [residual_delete_contract t a s ha C R e he hn,residual_bridge_pair t ht a s ha C R e hb]
  ring

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

def Multiforest (a s : Perm (Dart n)) (A : Finset (Orbit a)) : Prop :=
  (spanningGraph a s (A : Set (Orbit a))).IsAcyclic ∧
  (∀ e∈A,orbit s e.out≠orbit s (a e.out)) ∧
  Set.InjOn (edgeEnds a s) (A : Set (Orbit a))

lemma Multiforest.mono {a s : Perm (Dart n)} {A B : Finset (Orbit a)}
    (h : Multiforest a s B) (hab : A⊆B) : Multiforest a s A :=
  ⟨h.1.anti (spanningGraph_mono a s hab),fun e he => h.2.1 e (hab he),h.2.2.mono hab⟩

lemma multiforest_of_tour (M : LabelledMap n) (A : Finset (Orbit M.val.1))
    (h : ∀ d e,(M.val.2*partialReversal M.val.1 M.property.1 A).SameCycle d e) :
    Multiforest M.val.1 M.val.2 A := by
  have ⟨ht,hc⟩ := tour_spanningTree M A h
  obtain ⟨he,hi⟩ := spanningGraph_edgeSet_of_card M.val.1 M.val.2 M.property.1 A hc
  refine ⟨ht.isAcyclic,?_,hi⟩
  intro e heA
  have he' : edgeEnds M.val.1 M.val.2 e∈(spanningGraph M.val.1 M.val.2 (A : Set _)).edgeSet :=
    he.symm ▸ ⟨e,heA,rfl⟩
  exact ((SimpleGraph.mem_edgeSet _).mp he').ne

lemma Multiforest.insert_not_reachable {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} {e : Orbit a} (he : e∉A) (h : Multiforest a s (insert e A)) :
    ¬ (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
  have hedge : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Adj
      (orbit s e.out) (orbit s (a e.out)) := by
    refine ⟨h.2.1 e (Finset.mem_insert_self _ _),Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈insert e A
    rw [show orbit a e.out=e from Quotient.out_eq e]
    exact Finset.mem_insert_self _ _
  have hb := SimpleGraph.isAcyclic_iff_forall_isBridge.mp h.1 ((SimpleGraph.mem_edgeSet _).mpr hedge)
  intro hh
  apply (SimpleGraph.isBridge_iff.mp hb)
  exact hh.mono (spanningGraph_delete_edge_le a s ha e he h.2.2)

/-- The usual forest rank identity includes isolated vertices and does not
silently identify parallel map edges. -/
theorem Multiforest.components_card {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) :
    submapComponents a s A+A.card=Nat.card (Orbit s) := by
  induction A using Finset.induction_on with
  | empty => simp [submapComponents_empty]
  | @insert e A he ih =>
    have hA := h.mono (Finset.subset_insert e A)
    have hi := ih hA
    have hk := components_insert_of_not_reachable a s ha A e (h.insert_not_reachable ha he)
    rw [Finset.card_insert_of_notMem he]
    omega

/-- Every component of a forest has one boundary cycle. Converse to the
always-valid implication from a boundary cycle to graph reachability. -/
theorem Multiforest.sameCycle_iff_reachable {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) (d e : Dart n) :
    (s*partialReversal a ha A).SameCycle d e ↔
      (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s d) (orbit s e) := by
  let G := spanningGraph a s (A : Set (Orbit a))
  let p := s*partialReversal a ha A
  let f : Orbit p → G.ConnectedComponent := Quotient.lift
    (fun x => G.connectedComponentMk (orbit s x)) (by
      intro x y hxy
      exact SimpleGraph.ConnectedComponent.sound (spanningGraph_reachable_of_sameCycle a s ha A hxy))
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨v,rfl⟩ := Quot.mk_surjective c
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective v
    exact ⟨orbit p x,rfl⟩
  have hc : Nat.card (Orbit p)=Nat.card G.ConnectedComponent := by
    have h1 := forest_tour_cycle_card a s ha A h.1 h.2.1 h.2.2
    have h2 := h.components_card ha
    change Nat.card (Orbit p)+A.card=Nat.card (Orbit s) at h1
    change Nat.card G.ConnectedComponent+A.card=Nat.card (Orbit s) at h2
    omega
  have hi := ((Nat.bijective_iff_surjective_and_card f).mpr ⟨hf,hc⟩).1
  refine ⟨spanningGraph_reachable_of_sameCycle a s ha A,fun hr => ?_⟩
  exact Quotient.exact (hi (show f (orbit p d)=f (orbit p e) from
    SimpleGraph.ConnectedComponent.sound hr))

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

lemma spanningGraph_edge_reachable (a s : Perm (Dart n)) (A : Finset (Orbit a))
    (e : Orbit a) (he : e∈A) :
    (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) := by
  by_cases hh : orbit s e.out=orbit s (a e.out)
  · rw [hh]
  · apply SimpleGraph.Adj.reachable
    refine ⟨hh,Or.inl ⟨e.out,?_,rfl,rfl⟩⟩
    change orbit a e.out∈A
    simpa only [show orbit a e.out=e from Quotient.out_eq e] using he

lemma Multiforest.insert {a s : Perm (Dart n)} (ha : Function.Involutive a)
    {A : Finset (Orbit a)} (h : Multiforest a s A) (e : Orbit a)
    (hn : ¬(spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    Multiforest a s (insert e A) := by
  have hne : orbit s e.out≠orbit s (a e.out) := fun hh => hn (hh ▸ SimpleGraph.Reachable.refl _)
  have hends : ∀ f∈A,edgeEnds a s e≠edgeEnds a s f := by
    intro f hf heq
    have hr := spanningGraph_edge_reachable a s A f hf
    rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩|⟨h1,h2⟩
    · exact hn (h1 ▸ h2 ▸ hr)
    · exact hn (h1 ▸ h2 ▸ hr.symm)
  refine ⟨?_,?_,?_⟩
  · rw [spanningGraph_insert a s ha]
    exact h.1.sup_edge_of_not_reachable hn
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl|hf
    · exact hne
    · exact h.2.1 f hf
  · intro f hf g hg hfg
    rcases Finset.mem_insert.mp hf with hfe|hfA
    · subst f
      rcases Finset.mem_insert.mp hg with hge|hgA
      · exact hge.symm
      · exact False.elim (hends g hgA hfg)
    · rcases Finset.mem_insert.mp hg with hge|hgA
      · subst g
        exact False.elim (hends f hfA hfg.symm)
      · exact h.2.2 hfA hgA hfg

/-- The residual graph stays connected when an edge whose endpoints are
already connected is removed. -/
lemma spanningGraph_connected_erase (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (A : Finset (Orbit a)) (e : Orbit a)
    (hc : (spanningGraph a s ((insert e A : Finset (Orbit a)) : Set (Orbit a))).Connected)
    (hr : (spanningGraph a s (A : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    (spanningGraph a s (A : Set (Orbit a))).Connected := by
  rw [spanningGraph_insert a s ha] at hc
  refine {preconnected := ?_,nonempty := hc.nonempty}
  intro x y
  exact (GraphMerge.sup_edge_reachable_of_reachable _ hr x y).mp (hc.preconnected x y)

/-- Genuine multigraph spanning-tree completions of a partial exploration. -/
def treeExtensions (a s : Perm (Dart n)) (C R : Finset (Orbit a)) : Finset (Finset (Orbit a)) := by
  classical
  exact Finset.univ.filter (fun T => C⊆T ∧ T⊆C∪R ∧ Multiforest a s T ∧
    (spanningGraph a s (T : Set (Orbit a))).Connected)

lemma mem_treeExtensions (a s : Perm (Dart n)) (C R T : Finset (Orbit a)) :
    T∈treeExtensions a s C R ↔ C⊆T ∧ T⊆C∪R ∧ Multiforest a s T ∧
      (spanningGraph a s (T : Set (Orbit a))).Connected := by
  simp [treeExtensions]

lemma treeExtensions_terminal (a s : Perm (Dart n)) (C : Finset (Orbit a))
    (hf : Multiforest a s C) (hc : (spanningGraph a s (C : Set (Orbit a))).Connected) :
    treeExtensions a s C ∅={C} := by
  ext T
  rw [mem_treeExtensions,Finset.mem_singleton,Finset.union_empty]
  constructor
  · exact fun h => Finset.Subset.antisymm h.2.1 h.1
  · rintro rfl
    exact ⟨le_rfl,le_rfl,hf,hc⟩

lemma treeExtensions_split (a s : Perm (Dart n)) (C R : Finset (Orbit a)) (e : Orbit a)
    (heC : e∉C) (heR : e∉R) :
    treeExtensions a s C (insert e R) = treeExtensions a s C R ∪ treeExtensions a s (insert e C) R ∧
    Disjoint (treeExtensions a s C R) (treeExtensions a s (insert e C) R) := by
  constructor
  · ext T
    simp only [mem_treeExtensions,Finset.mem_union]
    constructor
    · rintro ⟨hC,hT,hf,hc⟩
      by_cases he : e∈T
      · exact Or.inr ⟨Finset.insert_subset_iff.mpr ⟨he,hC⟩,by simpa [Finset.insert_union,Finset.union_insert] using hT,hf,hc⟩
      · refine Or.inl ⟨hC,?_,hf,hc⟩
        intro x hx
        rcases Finset.mem_union.mp (hT hx) with h|h
        · exact Finset.mem_union_left _ h
        · rcases Finset.mem_insert.mp h with rfl|h
          · exact False.elim (he hx)
          · exact Finset.mem_union_right _ h
    · rintro (⟨hC,hT,hf,hc⟩|⟨hC,hT,hf,hc⟩)
      · exact ⟨hC,hT.trans (by intro x hx; simpa only [Finset.union_insert] using Finset.mem_insert_of_mem hx),hf,hc⟩
      · exact ⟨(Finset.subset_insert e C).trans hC,by simpa [Finset.insert_union,Finset.union_insert] using hT,hf,hc⟩
  · apply Finset.disjoint_left.mpr
    intro T hT hT'
    obtain ⟨_,hsub,_,_⟩ := (mem_treeExtensions a s C R T).mp hT
    obtain ⟨hC,_,_,_⟩ := (mem_treeExtensions a s (insert e C) R T).mp hT'
    have hh := hsub (hC (Finset.mem_insert_self _ _))
    exact (Finset.notMem_union.mpr ⟨heC,heR⟩) hh

lemma treeExtensions_loop (a s : Perm (Dart n)) (ha : Function.Involutive a)
    (C R : Finset (Orbit a)) (e : Orbit a) (he : e∉C)
    (hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))) :
    treeExtensions a s (insert e C) R=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨hC,_,hf,_⟩ := (mem_treeExtensions a s (insert e C) R T).mp hT
  have heT := hC (Finset.mem_insert_self _ _)
  have hCT : C⊆T.erase e := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun h => he (h ▸ hx),hC (Finset.mem_insert_of_mem hx)⟩
  have hf' : Multiforest a s (insert e (T.erase e)) := by rwa [Finset.insert_erase heT]
  exact hf'.insert_not_reachable ha (Finset.notMem_erase _ _)
    (hl.mono (spanningGraph_mono a s hCT))

lemma treeExtensions_bridge (a s : Perm (Dart n))
    (C R : Finset (Orbit a)) (e : Orbit a)
    (hb : ¬(spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Reachable
      (orbit s e.out) (orbit s (a e.out))) : treeExtensions a s C R=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨_,hT,_,hc⟩ := (mem_treeExtensions a s C R T).mp hT
  exact hb ((hc.preconnected _ _).mono (spanningGraph_mono a s hT))

end FKCRT
end


noncomputable section
open Set Equiv Equiv.Perm
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace FKCRT
variable {n : ℕ}

abbrev EdgeSelector (a : Perm (Dart n)) :=
  ∀ (_C R : Finset (Orbit a)), R.Nonempty → {e : Orbit a // e∈R}

/-- Number of forced bridge/loop decisions along the branch belonging to T.
The next edge may depend on the entire previous partial branch, but not T. -/
def explorationActivity (a s : Perm (Dart n)) (select : EdgeSelector a)
    (C R T : Finset (Orbit a)) : ℕ → ℕ
  | 0 => 0
  | k+1 => if hR : R.Nonempty then
      let e := (select C R hR).val
      let R' := R.erase e
      if (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out)) then
        1+explorationActivity a s select C R' T k
      else if ¬(spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Reachable
          (orbit s e.out) (orbit s (a e.out)) then
        1+explorationActivity a s select (insert e C) R' T k
      else explorationActivity a s select (if e∈T then insert e C else C) R' T k
    else 0

lemma explorationActivity_empty (a s : Perm (Dart n)) (select : EdgeSelector a)
    (C T : Finset (Orbit a)) (k : ℕ) : explorationActivity a s select C ∅ T k=0 := by
  cases k <;> simp [explorationActivity]

/-- The source deletion/contraction expansion is valid for arbitrary
history-dependent edge selection. It counts every genuine spanning tree
once, including bridge/loop degeneracies. No activity expansion is assumed. -/
theorem adaptive_activity_expansion (t : ℝ) (ht : t≠0)
    (a s : Perm (Dart n)) (ha : Function.Involutive a) (select : EdgeSelector a)
    (k : ℕ) (C R : Finset (Orbit a)) (hk : R.card≤k)
    (hd : Disjoint C R) (hf : Multiforest a s C)
    (hc : (spanningGraph a s ((C∪R : Finset (Orbit a)) : Set (Orbit a))).Connected) :
    residualPartition t a s C R =
      ∑ T∈treeExtensions a s C R,(1+t)^explorationActivity a s select C R T k := by
  induction k generalizing C R with
  | zero =>
    have hR : R=∅ := Finset.card_eq_zero.mp (by omega)
    subst R
    have hc' : (spanningGraph a s (C : Set (Orbit a))).Connected := by simpa using hc
    have hC : submapComponents a s C=1 := by
      apply Nat.card_eq_one_iff_unique.mpr
      exact ⟨hc'.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (C : Set _)).connectedComponentMk (orbit s 0)⟩⟩
    rw [residualPartition_terminal t a s C hC,treeExtensions_terminal a s C hf hc']
    simp [explorationActivity]
  | succ k ih =>
    by_cases hR : R.Nonempty
    · let e := (select C R hR).val
      let R' := R.erase e
      have heR : e∈R := (select C R hR).property
      have heC : e∉C := fun h => Finset.disjoint_left.mp hd h heR
      have hen : e∉R' := Finset.notMem_erase _ _
      have hins : insert e R'=R := Finset.insert_erase heR
      have hk' : R'.card≤k := by
        have hh := Finset.card_erase_add_one heR
        dsimp [R']
        omega
      have hd0 : Disjoint C R' := hd.mono_right (Finset.erase_subset _ _)
      have hd1 : Disjoint (insert e C) R' := Finset.disjoint_insert_left.mpr ⟨hen,hd0⟩
      have hs := treeExtensions_split a s C R' e heC hen
      rw [hins] at hs
      have hc1 : (spanningGraph a s (((insert e C)∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
        simpa only [Finset.insert_union,← Finset.union_insert,hins] using hc
      by_cases hl : (spanningGraph a s (C : Set (Orbit a))).Reachable (orbit s e.out) (orbit s (a e.out))
      · have hc0 : (spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
          apply spanningGraph_connected_erase a s ha (C∪R') e
          · simpa only [← Finset.union_insert,hins] using hc
          · exact hl.mono (spanningGraph_mono a s (fun _ h => Finset.mem_union_left _ h))
        have hempty := treeExtensions_loop a s ha C R' e heC hl
        have hext : treeExtensions a s C R=treeExtensions a s C R' := by simpa only [hempty,Finset.union_empty] using hs.1
        have hr := residual_loop t ht a s ha C R' e hen hl
        rw [hins] at hr
        rw [hr,ih C R' hk' hd0 hf hc0,hext,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T _
        have heq : explorationActivity a s select C R T (k+1)=
            1+explorationActivity a s select C R' T k := by
          simp only [explorationActivity,dite_eq_left hR]
          change (if _ then _ else _)=_
          rw [ite_eq_left hl]
        rw [heq,pow_add,pow_one]
      · have hf1 := hf.insert ha e hl
        by_cases hb : ¬(spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Reachable
            (orbit s e.out) (orbit s (a e.out))
        · have hempty := treeExtensions_bridge a s C R' e hb
          have hext : treeExtensions a s C R=treeExtensions a s (insert e C) R' := by simpa only [hempty,Finset.empty_union] using hs.1
          have hr := residual_bridge t ht a s ha C R' e hen hb
          rw [hins] at hr
          rw [hr,ih (insert e C) R' hk' hd1 hf1 hc1,hext,Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro T _
          have heq : explorationActivity a s select C R T (k+1)=
              1+explorationActivity a s select (insert e C) R' T k := by
            simp only [explorationActivity,dite_eq_left hR]
            change (if _ then _ else _)=_
            rw [ite_eq_right hl,ite_eq_left hb]
          rw [heq,pow_add,pow_one]
        · have hc0 : (spanningGraph a s ((C∪R' : Finset (Orbit a)) : Set (Orbit a))).Connected := by
            apply spanningGraph_connected_erase a s ha (C∪R') e
            · simpa only [← Finset.union_insert,hins] using hc
            · exact not_not.mp hb
          have hr := residual_delete_contract t a s ha C R' e hen hl
          rw [hins] at hr
          rw [hr,ih C R' hk' hd0 hf hc0,ih (insert e C) R' hk' hd1 hf1 hc1,hs.1,Finset.sum_union hs.2]
          congr 1
          · apply Finset.sum_congr rfl
            intro T hT
            have heT : e∉T := by
              intro h
              have hh := ((mem_treeExtensions a s C R' T).mp hT).2.1 h
              exact (Finset.notMem_union.mpr ⟨heC,hen⟩) hh
            congr 1
            simp only [explorationActivity,dite_eq_left hR]
            change _=(if _ then _ else _)
            rw [ite_eq_right hl,ite_eq_right hb,ite_eq_right heT]
          · apply Finset.sum_congr rfl
            intro T hT
            have heT : e∈T := ((mem_treeExtensions a s (insert e C) R' T).mp hT).1 (Finset.mem_insert_self _ _)
            congr 1
            simp only [explorationActivity,dite_eq_left hR]
            change _=(if _ then _ else _)
            rw [ite_eq_right hl,ite_eq_right hb,ite_eq_left heT]
    · have hemp : R=∅ := Finset.not_nonempty_iff_eq_empty.mp hR
      subst R
      have hc' : (spanningGraph a s (C : Set (Orbit a))).Connected := by simpa using hc
      have hC : submapComponents a s C=1 := by
        apply Nat.card_eq_one_iff_unique.mpr
        exact ⟨hc'.preconnected.subsingleton_connectedComponent,⟨(spanningGraph a s (C : Set _)).connectedComponentMk (orbit s 0)⟩⟩
      rw [residualPartition_terminal t a s C hC,treeExtensions_terminal a s C hf hc']
      simp [explorationActivity_empty]

end FKCRT
end

end OAI
