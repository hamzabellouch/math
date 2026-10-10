import OAI.Combinatorics.Hamiltonian.PairPolynomials

namespace OAI

/-! Common-phase nonvanishing and forest extraction from actual states. -/

namespace Barnette
noncomputable section
open scoped Classical

structure PermutationCoordinates {A : Type*} (p : Equiv.Perm A) (a : A) where
  n : ℕ
  face : Fin (n+3) ↪ A
  step : ∀ i, face (i+1) = p (face i)
  range_eq : Set.range face = {b | p.SameCycle a b}

lemma permutationCoordinates_exists {A : Type*} [Finite A] (p : Equiv.Perm A) (a : A)
    (h1 : p a ≠ a) (h2 : p (p a) ≠ a) : Nonempty (PermutationCoordinates p a) := by
  have hp : 0 < Function.minimalPeriod p a :=
    Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts a)
  have hp1 : Function.minimalPeriod p a ≠ 1 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h1 (by simpa using hh')
  have hp2 : Function.minimalPeriod p a ≠ 2 := by
    intro hh
    have hh' := Function.iterate_minimalPeriod (f := (p : A → A)) (x := a)
    rw [hh] at hh'
    exact h2 (by simpa [Function.iterate_succ_apply] using hh')
  let n := Function.minimalPeriod p a - 3
  have hn : n+3 = Function.minimalPeriod p a := by omega
  let f : Fin (n+3) → A := fun i => (p : A → A)^[i.val] a
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact Function.iterate_injOn_Iio_minimalPeriod (by simpa only [← hn, Set.mem_Iio] using i.isLt)
      (by simpa only [← hn, Set.mem_Iio] using j.isLt) hij
  refine ⟨⟨n,⟨f,hf⟩,?_,?_⟩⟩
  · intro i
    change (p : A → A)^[(i+1).val] a = p ((p : A → A)^[i.val] a)
    have hval : (i+1).val = (i.val+1) % Function.minimalPeriod p a := by
      rw [Fin.val_add]
      simp only [Fin.val_one,hn]
    rw [hval,Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']
  · ext b
    constructor
    · rintro ⟨i,rfl⟩
      change p.SameCycle a ((p : A → A)^[i.val] a)
      rw [← Equiv.Perm.coe_pow]
      exact (Equiv.Perm.SameCycle.refl p a).pow_right
    · intro hb
      obtain ⟨m,hm⟩ := hb.exists_nat_pow_eq
      refine ⟨⟨m % Function.minimalPeriod p a,by rw [hn]; exact Nat.mod_lt _ hp⟩,?_⟩
      change (p : A → A)^[m % Function.minimalPeriod p a] a = b
      rw [Function.iterate_mod_minimalPeriod_eq,← Equiv.Perm.coe_pow,hm]

namespace TriangleSystem.Pair
variable {A V : Type*} {T : TriangleSystem A V} {X : Set V}

lemma next_next_ne (P : @Pair A V T X) (t : A) : P.next (P.next t) ≠ t := by
  intro hh
  have hrt : P.left.val t ≠ P.right.val t := fun he =>
    P.partner t ((State.value_eq_iff _ _ _).mpr he)
  have hru : P.right.val (P.next t) ≠ P.left.val (P.next t) := fun he =>
    P.partner (P.next t) ((State.value_eq_iff _ _ _).mpr he.symm)
  have hx : T.vertex t (P.left.val t) = T.vertex (P.next t) (P.right.val (P.next t)) := by
    change P.left.value t = P.right.value (P.next t)
    rw [← P.value_next,hh]
  have hy : T.vertex t (P.right.val t) = T.vertex (P.next t) (P.left.val (P.next t)) :=
    (P.value_next t).symm
  exact P.next_ne t (T.edge_unique _ _ _ _ _ _ hrt hru hx hy).symm

variable [Fintype A]

def cycleCoordinates (P : @Pair A V T X) (a : A) : PermutationCoordinates P.next a :=
  (permutationCoordinates_exists P.next a (P.next_ne a) (P.next_next_ne a)).some

lemma cycleCoordinates_faces (P : @Pair A V T X) (c : CycleClass P.next) (a : A)
    (ha : classOf P.next a = c) :
    Finset.univ.image (P.cycleCoordinates a).face = P.cycleFaces c := by
  ext b
  simp only [Finset.mem_image,Finset.mem_univ,true_and,mem_cycleFaces]
  change b ∈ Set.range (P.cycleCoordinates a).face ↔ _
  rw [(P.cycleCoordinates a).range_eq]
  change P.next.SameCycle a b ↔ _
  rw [← classOf_eq_iff,ha]
  exact eq_comm

end TriangleSystem.Pair
end
end Barnette
namespace Barnette.Network.ColoredDual
noncomputable section
open scoped Classical
open Barnette.TriangleSystem
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
  {N : Network V E} {D : Network F E} (M : N.ColoredDual D) {root : V}

def pairedCycle (P : (M.system root).Pair (M.nonroots root)) (a : M.Black root) :
    M.StateCycle P.left where
  cycle :=
    { n := (P.cycleCoordinates a).n
      vertex := ⟨fun i => P.left.value ((P.cycleCoordinates a).face i),
        P.left.value_injective.comp (P.cycleCoordinates a).face.injective⟩
      adjacent := by
        intro i
        let t := (P.cycleCoordinates a).face i
        have ht : P.left.value ((P.cycleCoordinates a).face (i+1)) = P.right.value t := by
          rw [(P.cycleCoordinates a).step,P.value_next]
        change D.graph.Adj (P.left.value t) (P.left.value ((P.cycleCoordinates a).face (i+1)))
        rw [ht]
        have hij : P.left.val t ≠ P.right.val t := fun hh =>
          P.partner t ((State.value_eq_iff _ _ _).mpr hh)
        exact ⟨P.partner t,(M.face t.val).side D (P.left.val t) (P.right.val t),
          Sym2.eq_iff.mp ((M.face t.val).side_ends D hij)⟩ }
  face := (P.cycleCoordinates a).face
  corner i := P.right.val ((P.cycleCoordinates a).face i)
  left_eq _ := rfl
  right_eq i := by
    change P.right.value ((P.cycleCoordinates a).face i) =
      P.left.value ((P.cycleCoordinates a).face (i+1))
    rw [(P.cycleCoordinates a).step,P.value_next]

omit [Fintype F] in
lemma pairedCycle_delta (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c) :
    (M.pairedCycle P a).delta = P.cycleDelta c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, indexDelta (P.left.val ((P.cycleCoordinates a).face i))
    (P.right.val ((P.cycleCoordinates a).face i))) =
      ∑ t ∈ P.cycleFaces c, indexDelta (P.left.val t) (P.right.val t)
  rw [← P.cycleCoordinates_faces c a ha]
  exact (Finset.sum_image (f := fun t => indexDelta (P.left.val t) (P.right.val t))
    (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

omit [Fintype F] in
lemma pairedCycle_slope (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (a : M.Black root) (ha : Barnette.classOf P.next a = c)
    (α : E → ℝ) :
    (M.pairedCycle P a).slope α = P.cycleSlope (M.weights α root) c := by
  let : DecidableEq (M.Black root) := Classical.decEq _
  change (∑ i, (M.weights α root ((P.cycleCoordinates a).face i)
    (P.right.val ((P.cycleCoordinates a).face i)) -
      M.weights α root ((P.cycleCoordinates a).face i)
        (P.left.val ((P.cycleCoordinates a).face i)))) =
      (∑ t ∈ P.cycleFaces c, M.weights α root t (P.right.val t)) -
        (∑ t ∈ P.cycleFaces c, M.weights α root t (P.left.val t))
  rw [← P.cycleCoordinates_faces c a ha,Finset.sum_sub_distrib]
  congr 1
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.right.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm
  · exact (Finset.sum_image (f := fun t => M.weights α root t (P.left.val t))
      (s := Finset.univ) (P.cycleCoordinates a).face.injective.injOn).symm

lemma paired_sign (P : (M.system root).Pair (M.nonroots root))
    (c : Barnette.CycleClass P.next) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    (P.cycleDelta c = -3 ∧ 0 < P.cycleSlope (M.weights α root) c) ∨
      (P.cycleDelta c = 3 ∧ P.cycleSlope (M.weights α root) c < 0) := by
  obtain ⟨a,ha⟩ := Barnette.classOf_surjective P.next c
  have hh := (M.pairedCycle P a).signed α hα
  rwa [M.pairedCycle_delta P c a ha,M.pairedCycle_slope P c a ha α] at hh

omit [Fintype F] in
lemma opposite_forward_end {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) (i : Fin (C.cycle.n+3)) :
    (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i))) =
      C.cycle.vertex (i+1) := by
  rcases C.partner_endpoints hrs i with ⟨_,he⟩ | ⟨he,_⟩
  · exact he
  · exact ((C.cycle.adjacent i).1 ((hf i).symm.trans he)).elim

def oppositeForward {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) : M.StateCycle r where
  cycle :=
    { n := C.cycle.n
      vertex := C.cycle.vertex
      adjacent i := by
        have hij : r.val (C.face i) ≠ thirdIndex (r.val (C.face i)) (s.val (C.face i)) :=
          (thirdIndex_distinct _ _ (fun hh => hrs _ ((State.value_eq_iff _ _ _).mpr hh))).1.symm
        have he := (M.face (C.face i).val).side_ends D hij
        change s(D.tail _,D.head _) = s(r.value (C.face i),
          (M.system root).vertex (C.face i) (thirdIndex (r.val (C.face i)) (s.val (C.face i)))) at he
        rw [hf,M.opposite_forward_end C hrs hf] at he
        exact ⟨(C.cycle.adjacent i).1,_,Sym2.eq_iff.mp he⟩ }
  face := C.face
  corner i := thirdIndex (r.val (C.face i)) (s.val (C.face i))
  left_eq := hf
  right_eq := M.opposite_forward_end C hrs hf

omit [Fintype F] in
lemma oppositeForward_delta {s r : M.State root} (C : (M.system root).OppositeCycle s)
    (hrs : (M.system root).Partner r s)
    (hf : ∀ i, r.value (C.face i) = C.cycle.vertex i) :
    (M.oppositeForward C hrs hf).delta = C.cyclicDelta r := rfl

lemma opposite_disk {s : M.State root} (C : (M.system root).OppositeCycle s)
    (r : (M.system root).Partners s) (α : E → ℝ)
    (hα : N.boundary α = whiteCharge M.black root) :
    C.cyclicDelta r.val = 3 ∨ C.cyclicDelta r.val = -3 := by
  rcases C.partner_orientation r.property with hf | hb
  · have hs := (M.oppositeForward C r.property hf).signed α hα
    rw [M.oppositeForward_delta] at hs
    exact hs.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1)
  · let r' := C.reverse r.val r.property
    have hrs' : (M.system root).Partner r' s := C.reverse_partner r.val r.property
    have hf : ∀ i, r'.value (C.face i) = C.cycle.vertex i := by
      intro i
      have hr : r'.value (C.face i) = (M.system root).vertex (C.face i)
          (thirdIndex (r.val.val (C.face i)) (s.val (C.face i))) := by
        change (M.system root).vertex _ (C.changedCorners r.val (C.face i)) = _
        rw [C.changedCorners_image]
      rw [hr]
      rcases C.partner_endpoints r.property i with ⟨he,_⟩ | ⟨_,he⟩
      · exact ((C.cycle.adjacent i).1 (he.symm.trans (hb i))).elim
      · exact he
    have hδ : C.cyclicDelta r' = -C.cyclicDelta r.val := by
      unfold OppositeCycle.cyclicDelta
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change indexDelta (C.changedCorners r.val (C.face i))
        (thirdIndex (C.changedCorners r.val (C.face i)) (s.val (C.face i))) = _
      rw [C.changedCorners_image,thirdIndex_involution,indexDelta_antisymm]
    have hs := (M.oppositeForward C hrs' hf).signed α hα
    rw [M.oppositeForward_delta,hδ] at hs
    rcases hs with ⟨hs,_⟩ | ⟨hs,_⟩
    · left; omega
    · right; omega

theorem forest_pair (hex : Nonempty ((M.system root).Pair (M.nonroots root))) :
    ∃ P : (M.system root).Pair (M.nonroots root), ((M.system root).oppositeGraph P.right).IsAcyclic := by
  obtain ⟨α,hα⟩ := N.boundary_of_sum_zero M.duality.connected
    (whiteCharge M.black root) (whiteCharge_sum M.black root)
  exact Pair.forest_pair_of_disk_circulation hex
    (fun _ C r => M.opposite_disk C r α hα) (M.weights α root)
    (fun P c => M.paired_sign P c α hα)

end
end Barnette.Network.ColoredDual
namespace Barnette.Network
noncomputable section
open scoped Classical
variable {V E : Type*} [Fintype V] [Fintype E] (N : Network V E)
omit [Fintype V] [Fintype E] in
lemma connected_of_kernel_constants [Nonempty V]
    (hc : ∀ f : V → ℝ, N.gradient f = 0 → ∀ v w, f v = f w) : N.graph.Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, inferInstance⟩
  intro v w
  by_contra hw
  let f : V → ℝ := fun z => if N.graph.Reachable v z then 1 else 0
  have hf : N.gradient f = 0 := by
    apply (N.gradient_eq_zero_iff f).mpr
    intro e
    have he := N.edge_reachable e
    have hh : N.graph.Reachable v (N.head e) ↔ N.graph.Reachable v (N.tail e) :=
      ⟨fun h => h.trans he.symm, fun h => h.trans he⟩
    simp only [f, hh]
  have he := hc f hf v w
  simp [f, hw] at he

variable {F : Type*} [Fintype F]
abbrev Components (H : Network F E) := H.graph.ConnectedComponent

instance componentsFintype (H : Network F E) : Fintype H.Components := Fintype.ofFinite _

def componentMap (H : Network F E) : F → H.Components := H.graph.connectedComponentMk

omit [Fintype E] [Fintype F] in
lemma componentMap_surjective (H : Network F E) : Function.Surjective H.componentMap := by
  intro c
  induction c using SimpleGraph.ConnectedComponent.ind with
  | h f => exact ⟨f, rfl⟩

omit [Fintype E] [Fintype F] in
lemma gradient_componentMap (H : Network F E) (f : H.Components → ℝ) :
    H.gradient (pull H.componentMap f) = 0 := by
  apply (H.gradient_eq_zero_iff _).mpr
  intro e
  exact congrArg f (SimpleGraph.ConnectedComponent.sound (H.edge_reachable e)).symm

omit [Fintype E] [Fintype F] in
lemma descends_components (H : Network F E) (g : F → ℝ) (hg : H.gradient g = 0) :
    ∃ f : H.Components → ℝ, pull H.componentMap f = g := by
  refine ⟨Quot.lift g (fun v w h => H.gradient_zero_reachable hg h), ?_⟩
  rfl

end
end Barnette.Network

end OAI
