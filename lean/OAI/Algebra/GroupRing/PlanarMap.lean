import Mathlib
import OAI.Algebra.GroupRing.SeparatorLevels

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.PlanarMap

section
open scoped Classical
open SimpleGraph RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}

def componentVertices (G : SimpleGraph V) (c : G.ConnectedComponent) : Finset V :=
  Finset.univ.filter (fun v=>G.connectedComponentMk v=c)
lemma mem_componentVertices (c : G.ConnectedComponent) (v : V) :
    v∈componentVertices G c↔G.connectedComponentMk v=c := by simp only [componentVertices,Finset.mem_filter,Finset.mem_univ,true_and]
lemma componentVertices_disjoint (c d : G.ConnectedComponent) (h : c≠d) :
    Disjoint (componentVertices G c) (componentVertices G d) := by
  apply Finset.disjoint_left.mpr
  intro v hv hd
  exact h (((mem_componentVertices c v).mp hv).symm.trans ((mem_componentVertices d v).mp hd))

/-- Add the untouched small components to a separator of the unique large
component. The original deletion set and hence its sharp cost are retained. -/
def extendComponent (c : G.ConnectedComponent)
    (P : Split G.Adj (componentVertices G c))
    (hsmall : ∀ d : G.ConnectedComponent,d≠c→3*(componentVertices G d).card≤2*Fintype.card V) :
    Split G.Adj Finset.univ := by
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let others := (Finset.univ.erase c).image (componentVertices G)
  have hother {b : Finset V} : b∈others↔∃d,d≠c ∧ b=componentVertices G d := by
    simp only [others,Finset.mem_image,Finset.mem_erase,Finset.mem_univ,and_true]
    constructor
    · rintro ⟨d,hd,rfl⟩;exact ⟨d,hd,rfl⟩
    · rintro ⟨d,hd,rfl⟩;exact ⟨d,hd,rfl⟩
  have hdisj {b : Finset V} (hb : b∈P.parts) {d : G.ConnectedComponent} (hd : d≠c) :
      Disjoint b (componentVertices G d) :=
    (componentVertices_disjoint c d hd.symm).mono_left ((P.subset hb).trans Finset.sdiff_subset)
  refine {
    remove := P.remove
    parts := P.parts∪others
    remove_subset := Finset.subset_univ _
    cover := ?_
    disjoint := ?_
    closed := ?_
    size := ?_
    cost := ?_ }
  · ext v
    constructor
    · intro hv
      obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
      rcases Finset.mem_union.mp hb with hb|hb
      · exact (Finset.mem_sdiff.mp (P.subset hb hv)).2
      · obtain ⟨d,hd,rfl⟩ := hother.mp hb
        intro hr
        exact Finset.disjoint_left.mp (componentVertices_disjoint c d hd.symm) (P.remove_subset hr) hv
    · intro hv
      have hnr := (Finset.mem_sdiff.mp hv).2
      by_cases hc : G.connectedComponentMk v=c
      · have hc' := (mem_componentVertices c v).mpr hc
        have he := Finset.mem_sdiff.mpr ⟨hc',hnr⟩
        rw [←P.cover] at he
        obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp he
        exact Finset.mem_biUnion.mpr ⟨b,Finset.mem_union_left _ hb,hv⟩
      · exact Finset.mem_biUnion.mpr ⟨componentVertices G (G.connectedComponentMk v),
          Finset.mem_union_right _ (hother.mpr ⟨_,hc,rfl⟩),(mem_componentVertices _ _).mpr rfl⟩
  · intro b hb d hd hbd
    rcases Finset.mem_union.mp hb with hb|hb <;> rcases Finset.mem_union.mp hd with hd|hd
    · exact P.disjoint hb hd hbd
    · obtain ⟨e,he,rfl⟩ := hother.mp hd
      exact hdisj hb he
    · obtain ⟨e,he,rfl⟩ := hother.mp hb
      exact (hdisj hd he).symm
    · obtain ⟨e,_,rfl⟩ := hother.mp hb
      obtain ⟨f,_,rfl⟩ := hother.mp hd
      exact componentVertices_disjoint e f (fun h=>hbd (congrArg (componentVertices G) h))
  · intro b hb v hv w hw he
    rcases Finset.mem_union.mp hb with hb|hb
    · have hvc := (mem_componentVertices c v).mp (Finset.sdiff_subset (P.subset hb hv))
      have hwc : w∈componentVertices G c := (mem_componentVertices c w).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj he).symm.trans hvc)
      exact P.closed b hb v hv w (Finset.mem_sdiff.mpr ⟨hwc,(Finset.mem_sdiff.mp hw).2⟩) he
    · obtain ⟨d,_,rfl⟩ := hother.mp hb
      exact (mem_componentVertices d w).mpr
        ((ConnectedComponent.connectedComponentMk_eq_of_adj he).symm.trans ((mem_componentVertices d v).mp hv))
  · intro b hb
    rw [Finset.card_univ]
    rcases Finset.mem_union.mp hb with hb|hb
    · exact (P.size b hb).trans (Nat.mul_le_mul_left 2 (Finset.card_le_univ _))
    · obtain ⟨d,hd,rfl⟩ := hother.mp hb
      exact hsmall d hd
  · rw [Finset.card_univ]
    exact P.cost.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast Finset.card_le_univ (componentVertices G c)))
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)))

/-- Sharp separator for any finite genus-zero rotation map, including empty
and disconnected graphs. -/
theorem Model.univ_split (M : Model G) : Nonempty (Split G.Adj Finset.univ) := by
  let : Fintype G.ConnectedComponent := Fintype.ofFinite _
  by_cases hbig : ∃c : G.ConnectedComponent,2*Fintype.card V<3*(componentVertices G c).card
  · obtain ⟨c,hc⟩ := hbig
    let : DecidableEq c.supp := Classical.decEq _
    obtain ⟨P⟩ := (M.induced c.supp).connected_split c.connected_toSimpleGraph
    let f : c.supp ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    have he : (Finset.univ : Finset c.supp).map f=componentVertices G c := by
      ext v
      simp only [Finset.mem_map,Finset.mem_univ,true_and,mem_componentVertices]
      constructor
      · rintro ⟨x,rfl⟩;exact x.property
      · intro hv;exact ⟨⟨v,hv⟩,rfl⟩
    have PP : Nonempty (Split G.Adj (componentVertices G c)) := by
      rw [←he]
      exact ⟨P.map f (fun _ _ h=>h)⟩
    obtain ⟨P⟩ := PP
    refine ⟨extendComponent c P ?_⟩
    intro d hd
    have hadd : (componentVertices G c).card+(componentVertices G d).card≤Fintype.card V := by
      rw [←Finset.card_union_of_disjoint (componentVertices_disjoint c d hd.symm)]
      exact Finset.card_le_univ _
    omega
  · push Not at hbig
    refine ⟨Split.of_fibers G.Adj Finset.univ ∅ G.connectedComponentMk (Finset.empty_subset _)
      (fun _ _ _ _ h=>ConnectedComponent.connectedComponentMk_eq_of_adj h) ?_ ?_⟩
    · intro c
      simpa only [Finset.sdiff_empty,Finset.card_univ,componentVertices] using hbig c
    · simp only [Finset.card_empty,Nat.cast_zero]
      positivity

end

open scoped Classical
open RecursiveSeparator
variable {V : Type} [Fintype V] {G : SimpleGraph V}
omit [Fintype V] in
/-- The exact sharp separator on every induced vertex set. -/
theorem Model.split (M : Model G) (S : Finset V) : Nonempty (Split G.Adj S) := by
  let : DecidableEq S := Classical.decEq _
  obtain ⟨P⟩ := (M.induced (S : Set V)).univ_split
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have he : (Finset.univ : Finset S).map f=S := by
    ext v
    simp only [Finset.mem_map,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,rfl⟩;exact x.property
    · intro hv;exact ⟨⟨v,hv⟩,rfl⟩
  rw [←he]
  exact ⟨P.map f (fun _ _ h=>h)⟩
end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.BoundaryRotation
open scoped Classical
open BlockAlignment ComparedBlocks PermutationCycles
variable {T : Type} [Fintype T] (len : T→ℕ) (hpos : ∀t,0<len t)
/-- Actual boundary cycles are exactly the nonempty boundary words. -/
def cyclesEquiv : Cycle (perm len) ≃ T :=
  Equiv.ofBijective (PermutationCycles.lift (perm len) (fun p=>p.1) (first len)) ⟨by
    intro a b he
    obtain ⟨x,rfl⟩ := cycle_surjective (perm len) a
    obtain ⟨y,rfl⟩ := cycle_surjective (perm len) b
    exact (cycle_eq (perm len)).mpr (same_first len he),by
    intro t
    exact ⟨cycle (perm len) ((WordPositions.fin len).symm ⟨t,⟨0,hpos t⟩⟩),rfl⟩⟩
@[simp] lemma cyclesEquiv_cycle (p : Position len) :
    cyclesEquiv len hpos (cycle (perm len) p)=p.1 := rfl

def interaction (α : Equiv.Perm (Position len)) (ha : Function.Involutive α) : SimpleGraph T where
  Adj p q := p≠q ∧ PairingClusters.Rel (fun x=>x.1) α p q
  symm := ⟨by
    rintro p q ⟨hpq,x,hx,hy⟩
    exact ⟨hpq.symm,α x,hy,by rw [ha x];exact hx⟩⟩
  loopless := ⟨fun _ h=>h.1 rfl⟩

def graphIso (α : Equiv.Perm (Position len)) (ha : Function.Involutive α) :
    MapEuler.graph (perm len) α ha ≃g interaction len α ha where
  toEquiv := cyclesEquiv len hpos
  map_rel_iff' := by
    intro a b
    change ((cyclesEquiv len hpos a≠cyclesEquiv len hpos b) ∧
      ∃x,x.1=cyclesEquiv len hpos a ∧ (α x).1=cyclesEquiv len hpos b) ↔
      (a≠b ∧ ∃x,cycle (perm len) x=a ∧ cycle (perm len) (α x)=b)
    constructor
    · rintro ⟨hn,x,hx,hy⟩
      exact ⟨fun h=>hn (congrArg (cyclesEquiv len hpos) h),x,
        (cyclesEquiv len hpos).injective hx,(cyclesEquiv len hpos).injective hy⟩
    · rintro ⟨hn,x,hx,hy⟩
      exact ⟨fun h=>hn ((cyclesEquiv len hpos).injective h),x,
        congrArg (cyclesEquiv len hpos) hx,congrArg (cyclesEquiv len hpos) hy⟩

def model (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) : PlanarMap.Model (interaction len α ha) where
  Dart := Position len
  rotation := perm len
  pairing := α
  involutive := ha
  genus := hz
  iso := graphIso len hpos α ha

include hpos in
/-- The sharp separator for the literal interaction relation, retaining loops
as required by the existing recursive charging theorem. -/
theorem split (α : Equiv.Perm (Position len)) (ha : Function.Involutive α)
    (hz : MapEuler.GenusZero (perm len) α) (S : Finset T) :
    Nonempty (RecursiveSeparator.Split (PairingClusters.Rel (fun x=>x.1) α) S) := by
  obtain ⟨P⟩ := (model len hpos α ha hz).split S
  exact ⟨RecursiveSeparator.Split.of_off_diagonal (fun p q hpq=>by
    change (p≠q ∧ _)↔_
    exact and_iff_right hpq) P⟩
end TorsionFreeZeroDivisors.BoundaryRotation

namespace TorsionFreeZeroDivisors.SampleGraph.Picture
open scoped Classical
open BlockAlignment ComparedBlocks
variable {rep : ℕ} (r : ActualPatternEvent.Match rep) (x : VA rep) (y : VB rep)
  (hL : 2≤GirthAsymptotics.L (TypedGraphs.size rep)) (hd : GraphSample.Diameters rep r)
/-- Discharge the former sharp planar-separator obligation of every reduced
disk picture, using its actual genus-zero segmented interaction map. -/
theorem separator_obligation : SeparatorObligation r x y hL hd := by
  intro z w n a hzw hr hz S _
  let s := system a hzw hr hz
  let cap := FullPairing.U₀*GirthAsymptotics.L (TypedGraphs.size rep)
  let hc : 0<cap := FullPairing.cap_positive hL
  have hp : ∀p,0<BalancedRotation.len s.paths cap hc p := fun p=>
    List.length_pos_iff.mpr (BalancedWords.segment_nonempty s.paths cap hc s.nonempty p)
  obtain ⟨P⟩ := BoundaryRotation.split (BalancedRotation.len s.paths cap hc) hp
    ((pairing a hzw hr hz).α cap hc) ((pairing a hzw hr hz).α_involutive cap hc)
    (segmented_genusZero a hzw hr hz cap hc) S
  exact ⟨(pairing a hzw hr hz).closed_split cap hc (by omega) hd _ S P⟩
end TorsionFreeZeroDivisors.SampleGraph.Picture

/-! The parity argument in source sections/factors.tex. We count reversible
flags, retaining parallel edges instead of identifying them in a simple graph. -/
namespace TorsionFreeZeroDivisors.Factors
open scoped BigOperators Classical

lemma odd_nsmul {R : Type*} [AddCommMonoid R] (h2 : ∀ x : R,x+x=0) {n : ℕ}
    (hn : Odd n) (x : R) : n • x=x := by
  obtain ⟨k,rfl⟩ := hn
  simp only [add_nsmul,mul_nsmul,two_nsmul,one_nsmul]
  rw [h2,nsmul_zero,zero_add]

/-- Odd fibres allow an invariant sum over vertices to be computed over flags.
The fixed-point-free involution of flags then cancels it in characteristic two. -/
theorem odd_fibre_cancellation {P F R : Type*} [Fintype P] [Fintype F]
    [AddCommMonoid R] (h2 : ∀ x : R,x+x=0) (proj : F → P) (rev : F → F)
    (hr : Function.Involutive rev) (hne : ∀ e,rev e≠e)
    (hodd : ∀ p,Odd (Finset.univ.filter (fun e => proj e=p)).card)
    (f : P → R) (hf : ∀ e,f (proj (rev e))=f (proj e)) :
    ∑ p,f p=0 := by
  have hs : ∑ e : F,f (proj e)=∑ p : P,f p := by
    rw [← Finset.sum_fiberwise_of_maps_to' (fun e (_ : e∈(Finset.univ : Finset F)) =>
      Finset.mem_univ (proj e)) f]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_const]
    exact odd_nsmul h2 (hodd p) (f p)
  rw [← hs]
  exact Finset.sum_ninvolution rev
    (fun e => by rw [hf]; exact h2 _)
    (fun e _ => hne e) (fun _ => Finset.mem_univ _) hr

variable {A B T G : Type*} [Fintype A] [Fintype B] [Fintype T] [Group G]
variable (outA : A → Finset T) (outB : B → Finset T)
abbrev DartA := {p : A×T // p.2∈outA p.1}
abbrev DartB := {p : B×T // p.2∈outB p.1}
abbrev Flag := {p : DartA outA×DartB outB // p.1.val.2=p.2.val.2}
def base (e : Flag outA outB) : A×B := (e.val.1.val.1,e.val.2.val.1)

/-- The entire common outgoing set, not a quotient of its parallel steps. -/
def fibreEquiv (p : A×B) : {e : Flag outA outB // base outA outB e=p} ≃
    {t : T // t∈outA p.1∩outB p.2} where
  toFun e := ⟨e.val.val.1.val.2,by
    have ha := e.val.val.1.property
    have hb := e.val.val.2.property
    have h1 := congrArg Prod.fst e.property
    have h2 := congrArg Prod.snd e.property
    change e.val.val.1.val.1=p.1 at h1
    change e.val.val.2.val.1=p.2 at h2
    exact Finset.mem_inter.mpr ⟨by simpa only [h1] using ha,
      by simpa only [h2,← e.val.property] using hb⟩⟩
  invFun t := ⟨⟨(⟨(p.1,t.val),(Finset.mem_inter.mp t.property).1⟩,
      ⟨(p.2,t.val),(Finset.mem_inter.mp t.property).2⟩),rfl⟩,rfl⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg Prod.fst e.property).symm rfl
    · apply Subtype.ext
      exact Prod.ext (congrArg Prod.snd e.property).symm e.val.property
  right_inv _ := rfl

lemma fibre_card (p : A×B) :
    (Finset.univ.filter (fun e : Flag outA outB => base outA outB e=p)).card=
      (outA p.1∩outB p.2).card := by
  have h := Fintype.card_congr (fibreEquiv outA outB p)
  simpa only [Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter] using h

variable (bar : T→T) (rA : DartA outA→DartA outA) (rB : DartB outB→DartB outB)
  (hA : ∀ d,(rA d).val.2=bar d.val.2) (hB : ∀ d,(rB d).val.2=bar d.val.2)
def reverse (e : Flag outA outB) : Flag outA outB :=
  ⟨(rA e.val.1,rB e.val.2),by rw [hA,hB,e.property]⟩
omit [Fintype A] [Fintype B] [Fintype T] in
lemma reverse_involutive (hrA : Function.Involutive rA) (hrB : Function.Involutive rB) :
    Function.Involutive (reverse outA outB bar rA rB hA hB) := by
  intro e
  apply Subtype.ext
  exact Prod.ext (hrA e.val.1) (hrB e.val.2)
omit [Fintype A] [Fintype B] [Fintype T] in
lemma reverse_ne (hbar : ∀ t,bar t≠t) (e : Flag outA outB) :
    reverse outA outB bar rA rB hA hB e≠e := by
  intro he
  have h := congrArg (fun z : Flag outA outB => z.val.1.val.2) he
  exact hbar e.val.1.val.2 ((hA e.val.1).symm.trans h)

include hA hB in
/-- The source factors on full components; compatibility is the literal
path-order rule along every outgoing edge. -/
theorem product_zero
    (hrA : Function.Involutive rA) (hrB : Function.Involutive rB)
    (hbar : ∀ t,bar t≠t) (hodd : ∀ a b,Odd (outA a∩outB b).card)
    (letter : T→G) (g : A→G) (h : B→G)
    (hg : ∀ d : DartA outA,g (rA d).val.1=g d.val.1*letter d.val.2)
    (hh : ∀ d : DartB outB,h (rB d).val.1=h d.val.1*letter d.val.2) :
    (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2)) *
      (∑ b,MonoidAlgebra.single ((h b)⁻¹) (1 : ZMod 2))=0 := by
  have h2 (x : MonoidAlgebra (ZMod 2) G) : x+x=0 := by
    ext z
    exact CharTwo.add_self_eq_zero (x.coeff z)
  have hz := odd_fibre_cancellation h2 (base outA outB)
    (reverse outA outB bar rA rB hA hB)
    (reverse_involutive outA outB bar rA rB hA hB hrA hrB)
    (reverse_ne outA outB bar rA rB hA hB hbar)
    (fun p => by
      convert hodd p.1 p.2 using 1
      convert fibre_card outA outB p using 1
      congr 1
      ext e
      simp)
    (fun p : A×B => MonoidAlgebra.single (g p.1*(h p.2)⁻¹) (1 : ZMod 2)) (by
      intro e
      change MonoidAlgebra.single (g (rA e.val.1).val.1*(h (rB e.val.2).val.1)⁻¹) _ = _
      rw [hg,hh,e.property]
      congr 1
      dsimp only [base]
      group)
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum,MonoidAlgebra.single_mul_single,one_mul]
  simpa only [Fintype.sum_prod_type] using hz

/-- Only the root must have a unique label; no non-root injectivity is needed. -/
theorem sum_nonzero (root : A) (g : A→G) (hroot : g root=1)
    (hunique : ∀ a,g a=1 → a=root) :
    (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2))≠0 := by
  have hv : (∑ a,MonoidAlgebra.single (g a) (1 : ZMod 2)).coeff (1:G)=1 := by
    rw [MonoidAlgebra.coeff_sum,Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single root]
    · simp [hroot]
    · intro a _ ha
      simp only [MonoidAlgebra.coeff_single,Finsupp.single_apply]
      exact ite_eq_right (fun h => ha (hunique a h))
    · simp
  intro hz
  rw [hz] at hv
  exact zero_ne_one hv

end TorsionFreeZeroDivisors.Factors

end

end OAI
