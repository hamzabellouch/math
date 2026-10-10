import Mathlib
import OAI.Algebra.GroupRing.LinkComponents
import OAI.Algebra.GroupRing.WordEstimate

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.StageBlocks
open scoped BigOperators Classical
open StageLabels WordEstimate
variable {I : Type*} [Fintype I] {h : I → ℕ}
variable (L : Links (T := Letter) h)

abbrev Component := L.graph.ConnectedComponent

def translationWords {n : ℕ} (D : BlockConstraints.Translation n) : Finset (Fin n → Letter) :=
  Finset.univ.filter (fun W => ∀ i : D.domain, W (D.target i) = W i.val)

theorem translation_card {n : ℕ} (D : BlockConstraints.Translation n) :
    (translationWords D).card ≤ (Fintype.card Letter)^(n-D.domain.card) := by
  have he : {W : Fin n → Letter // W ∈ translationWords D} ≃
      {W : Fin n → Letter // ∀ i : D.domain, W (D.target i) = W i.val} :=
    Equiv.subtypeEquivRight (fun W => by simp [translationWords])
  have hh := D.word_count (T := Letter)
  rw [← Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_coe] at hh
  exact hh

variable (r : (c : Component L) → c)
variable (D : (c : Component L) → Option (BlockConstraints.Translation (h (r c).val)))
variable (d : I → ℤ)

def rootWords (c : Component L) : Finset (Fin (h (r c).val) → Letter) :=
  match D c with
  | none => binWords _ (d (r c).val)
  | some tr => translationWords tr

def basicCost (s : ℝ) (c : Component L) : ℝ :=
  match D c with
  | none => 2*(d (r c).val : ℝ) - (1/600 : ℝ)*s
  | some _ => 0

def Feasible (W : (i : I) → Fin (h i) → Letter) : Prop :=
  L.Consistent W ∧ (∀ i, W i ∈ binWords (h i) (d i)) ∧
    ∀ c tr, D c = some tr → ∀ k : tr.domain, W (r c).val (tr.target k) = W (r c).val k.val

omit [Fintype I] in
theorem feasible_root {W : (i : I) → Fin (h i) → Letter}
    (hw : Feasible L r D d W) (c : Component L) : W (r c).val ∈ rootWords L r D d c := by
  unfold rootWords
  cases hc : D c with
  | none => exact hw.2.1 _
  | some tr => exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw.2.2 c tr hc⟩

omit [Fintype I] in
theorem root_bound (s : ℝ) (e : ℕ)
    (hlarge : ∀ i, 3002 ≤ h i) (hscale : ∀ i, s+1200 ≤ 2*(h i : ℝ))
    (hself : ∀ c tr, D c = some tr → h (r c).val-tr.domain.card ≤ e)
    (c : Component L) :
    ((rootWords L r D d c).card : ℝ) ≤
      Real.exp (basicCost L r D d s c + (e : ℝ)*Real.log (Fintype.card Letter)) := by
  have halog : 0 ≤ Real.log (Fintype.card Letter) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := Letter))
  have ha : 0 < (Fintype.card Letter : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold rootWords basicCost
  cases hc : D c with
  | none =>
    have hh := bin_card_bound (h (r c).val) (hlarge _) (d (r c).val)
    apply hh.trans
    apply Real.exp_le_exp.mpr
    have hs := hscale (r c).val
    have he := mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) halog
    linarith
  | some tr =>
    have hh : ((translationWords tr).card : ℝ) ≤
        (Fintype.card Letter : ℝ)^(h (r c).val-tr.domain.card) := by
      exact_mod_cast translation_card tr
    calc
      _ ≤ (Fintype.card Letter : ℝ)^(h (r c).val-tr.domain.card) := hh
      _ ≤ (Fintype.card Letter : ℝ)^e := pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := Letter))
        (hself c tr hc)
      _ = Real.exp (0 + (e : ℝ)*Real.log (Fintype.card Letter)) := by
        rw [zero_add,Real.exp_nat_mul,Real.exp_log ha]

/-- Count the actual active projections with bin or self-translation roots.
The error exponent is explicit: twice the missing substring size per block. -/
theorem stage_count (A : Finset I) (s : ℝ) (e : ℕ)
    (hlarge : ∀ i, 3002 ≤ h i) (hscale : ∀ i, s+1200 ≤ 2*(h i : ℝ))
    (hlinks : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e)
    (hself : ∀ c tr, D c = some tr → h (r c).val-tr.domain.card ≤ e) :
    ((StageLabels.stageWords h A (Feasible L r D d)).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents L.graph.connectedComponentMk A,
        basicCost L r D d s c.val) + 2*(e : ℝ)*Fintype.card I*Real.log (Fintype.card Letter)) := by
  have hh := L.stage_exp A r (rootWords L r D d) (Feasible L r D d)
    (fun _ hw => hw.1) (fun _ hw c => feasible_root L r D d hw c) e hlinks
    (fun c => basicCost L r D d s c + (e : ℝ)*Real.log (Fintype.card Letter))
    (root_bound L r D d s e hlarge hscale hself)
  apply hh.trans
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcomp : Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) ≤ Fintype.card I := by
    rw [Fintype.card_coe]
    exact (Finset.card_image_le).trans (Finset.card_le_univ _)
  have hall : (Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) : ℝ) ≤ Fintype.card I :=
    by exact_mod_cast hcomp
  have ha : 0 ≤ Real.log (Fintype.card Letter) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := Letter))
  have he := mul_le_mul_of_nonneg_right hall (mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) ha)
  nlinarith

end TorsionFreeZeroDivisors.StageBlocks

namespace TorsionFreeZeroDivisors.ActualStageLabels

open scoped Classical BigOperators
section
/-- An infeasible complete word has no active projection. -/
theorem projection_empty {I T : Type*} [Fintype I] [Fintype T]
    (h : I → ℕ) (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (hn : ¬∃ W, P W) : StageLabels.stageWords h A P = ∅ := by
  unfold StageLabels.stageWords
  have he : Finset.univ.filter P = ∅ := by
    exact Finset.filter_eq_empty_iff.mpr (fun W _ hW => hn ⟨W,hW⟩)
  rw [he,Finset.image_empty]

/-- Uniform root errors and propagation errors together cost at most twice
one missing substring per underlying block. -/
theorem projection_bound {I T : Type*} [Fintype I] [Fintype T] [Nonempty T]
    {h : I → ℕ} (L : StageLabels.Links (T := T) h) (A : Finset I)
    (r : (c : L.graph.ConnectedComponent) → c)
    (R : (c : L.graph.ConnectedComponent) → Finset (Fin (h (r c).val) → T))
    (P : ((i : I) → Fin (h i) → T) → Prop)
    (hP : ∀ w, P w → L.Consistent w)
    (hroot : ∀ w, P w → ∀ c, w (r c).val ∈ R c)
    (e : ℕ) (he : ∀ i j, L.graph.Adj i j → h i - (L.known i j).card ≤ e)
    (cost : L.graph.ConnectedComponent → ℝ)
    (hcost : ∀ c, ((R c).card : ℝ) ≤ Real.exp (cost c+(e : ℝ)*Real.log (Fintype.card T))) :
    ((StageLabels.stageWords h A P).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents L.graph.connectedComponentMk A, cost c.val) +
        2*(e : ℝ)*Fintype.card I*Real.log (Fintype.card T)) := by
  have hh := L.stage_exp A r R P hP hroot e he
    (fun c => cost c+(e : ℝ)*Real.log (Fintype.card T)) hcost
  apply hh.trans
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hcomp : Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) ≤ Fintype.card I := by
    rw [Fintype.card_coe]
    exact (Finset.card_image_le).trans (Finset.card_le_univ _)
  have hall : (Fintype.card (StageLabels.activeComponents L.graph.connectedComponentMk A) : ℝ) ≤ Fintype.card I :=
    by exact_mod_cast hcomp
  have ha : 0 ≤ Real.log (Fintype.card T) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := T))
  have hel := mul_le_mul_of_nonneg_right hall (mul_nonneg (Nat.cast_nonneg e : (0:ℝ) ≤ e) ha)
  nlinarith
end
open scoped Classical BigOperators
open ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ)
variable (cmp : Comparisons (E := E) (traversalLength len m)) (err : ℕ)

def symbol (e : E) : Letter ≃ Letter :=
  if cmp.reverse e then ⟨inverse,inverse,inverse_inverse,inverse_inverse⟩ else Equiv.refl _

abbrev L := links s hs len m cmp err (symbol len m cmp)
abbrev P := (data s hs len m cmp err).matching
abbrev Component := LinkComponents.Component (multiplicity s len m) (P s hs len m cmp err)

def Comparing (w : C → ℤ → Letter) : Prop :=
  ∀ x e, cmp.side x = some e →
    w x.1.1 x.2.val = if cmp.reverse e then
      inverse (w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val)
    else w (cmp.pairing.partner x).1.1 (cmp.pairing.partner x).2.val

def Immersed (w : C → ℤ → Letter) : Prop :=
  ∀ (i : Underlying s len) q,
    lower s len i ≤ q → q+1 < upper s len i → w i.1 (q+1) ≠ inverse (w i.1 q)

variable (d : Underlying s len → ℤ)

def Feasible (W : (i : Underlying s len) → Fin (height s len i) → Letter) : Prop :=
  (∀ i, W i ∈ binWords (height s len i) (d i)) ∧
    ∃ w : C → ℤ → Letter, Comparing len m cmp w ∧ Immersed s len w ∧ W = word s len w

omit [Fintype C] in
theorem feasible_consistent {W : (i : Underlying s len) → Fin (height s len i) → Letter}
    (hW : Feasible s len m cmp d W) : (L s hs len m cmp err).Consistent W := by
  obtain ⟨_,w,hw,_,rfl⟩ := hW
  apply links_consistent s hs len m cmp err (symbol len m cmp) (fun x => w x.1.1 x.2.val)
  · intro x e he
    have hh := hw x e he
    unfold symbol
    split_ifs with h
    · simpa [h] using hh
    · simpa [h] using hh
  · intro b x
    unfold word
    rw [coordinate_val,sub_add_cancel]
    have ht := ((mem_blockPositions s hs (traversalLength len m)).mp x.property).1
    exact congrArg (fun t : Traversal m => w t.1 x.val.2.val) ht.symm

/-- The source component cost with the actual occurrence matching and its
actual self-links, not a supplied abstract component partition. -/
def cost (c : Component s hs len m cmp err) : ℝ :=
  LinkComponents.componentLabelCost (multiplicity s len m) (P s hs len m cmp err)
    (fun i => (d i : ℝ)) (1/600) s c

theorem root_count
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val))
    (w₀ : C → ℤ → Letter) (hcompare₀ : Comparing len m cmp w₀) (hred₀ : Immersed s len w₀)
    (c : Component s hs len m cmp err) :
    ∃ (r : c) (R : Finset (Fin (height s len r.val) → Letter)),
      (R.card : ℝ) ≤ Real.exp (cost s hs len m cmp err d c + (err : ℝ)*Real.log (Fintype.card Letter)) ∧
      ∀ W, Feasible s len m cmp d W → W r.val ∈ R := by
  have halog : 0 ≤ Real.log (Fintype.card Letter) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := Letter))
  by_cases hc : LinkComponents.HasSelf (multiplicity s len m) (P s hs len m cmp err) c
  · obtain ⟨r,tr,hdef,htr⟩ := self_component_translation s hs len m cmp err inverse
      inverse_inverse inverse_ne w₀ hcompare₀ hred₀ hreduced c hc
    refine ⟨r,StageBlocks.translationWords tr,?_,?_⟩
    · have hb : ((StageBlocks.translationWords tr).card : ℝ) ≤
          (Fintype.card Letter : ℝ)^(height s len r.val-tr.domain.card) := by
        exact_mod_cast StageBlocks.translation_card tr
      have ha : 0 < (Fintype.card Letter : ℝ) := by exact_mod_cast Fintype.card_pos
      calc
        _ ≤ (Fintype.card Letter : ℝ)^(height s len r.val-tr.domain.card) := hb
        _ ≤ (Fintype.card Letter : ℝ)^err :=
          pow_le_pow_right₀ (by exact_mod_cast Fintype.card_pos (α := Letter)) hdef
        _ = _ := by
          simp only [cost,LinkComponents.componentLabelCost,ite_eq_left hc,zero_add]
          rw [Real.exp_nat_mul,Real.exp_log ha]
    · intro W hW
      obtain ⟨_,w,hw,_,rfl⟩ := hW
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htr Letter inverse w hw⟩
  · let r := LinkComponents.minimumRoot (multiplicity s len m) (P s hs len m cmp err)
      (fun i => (d i : ℝ)) c
    refine ⟨r,binWords (height s len r.val) (d r.val),?_,?_⟩
    · have hb := bin_card_bound (height s len r.val) (hlarge r.val) (d r.val)
      apply hb.trans
      apply Real.exp_le_exp.mpr
      have hh := hscale r.val
      have he := mul_nonneg (Nat.cast_nonneg err : (0:ℝ) ≤ err) halog
      simp only [cost,LinkComponents.componentLabelCost,ite_eq_right hc]
      change 2*(d r.val : ℝ)+2-2*(1/600 : ℝ)*(height s len r.val : ℝ) ≤ _
      linarith
    · intro W hW
      exact hW.1 r.val

/-- Counting the actual stage projection. Self-link roots are selected from
one feasible realization; if none exists, the projection is empty. -/
theorem stage_count (A : Finset (Underlying s len))
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val)) :
    ((StageLabels.stageWords (height s len) A (Feasible s len m cmp d)).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk A,
        cost s hs len m cmp err d c.val) +
        2*(err : ℝ)*Fintype.card (Underlying s len)*Real.log (Fintype.card Letter)) := by
  by_cases hex : ∃ W, Feasible s len m cmp d W
  · obtain ⟨W,_,w₀,hw₀,hr₀,_⟩ := hex
    have hroot := root_count s hs len m cmp err d hlarge hscale hreduced w₀ hw₀ hr₀
    choose r R hR hmem using hroot
    exact projection_bound (L s hs len m cmp err) A r R (Feasible s len m cmp d)
      (fun _ hw => feasible_consistent s hs len m cmp err d hw)
      (fun W hw c => hmem c W hw) err
      (links_deficit s hs len m cmp err (symbol len m cmp))
      (cost s hs len m cmp err d) hR
  · rw [projection_empty _ _ _ hex,Finset.card_empty,Nat.cast_zero]
    exact (Real.exp_pos _).le

/-- Stage components are precisely those whose maximum multiplicity exceeds
the zero-based stage number. -/
theorem active_iff (j : ℕ) (c : Component s hs len m cmp err) :
    c ∈ StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) ↔
      j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c := by
  rw [← LinkComponents.active_iff]
  constructor
  · intro hc
    obtain ⟨i,hi,hc⟩ := Finset.mem_image.mp hc
    exact ⟨⟨i,hc⟩,(Finset.mem_filter.mp hi).2⟩
  · rintro ⟨i,hi⟩
    exact Finset.mem_image.mpr ⟨i.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩,i.property⟩

/-- Literal source component sum, now in the form used by stage-cost summation. -/
theorem cost_sum (j : ℕ) :
    (∑ c : StageLabels.activeComponents (L s hs len m cmp err).graph.connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost s hs len m cmp err d c.val) =
    ∑ c : Component s hs len m cmp err,
      if j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c then
        cost s hs len m cmp err d c else 0 := by
  change (∑ c : StageLabels.activeComponents
    (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
    (Finset.univ.filter (fun i => j < multiplicity s len m i)), cost s hs len m cmp err d c.val) = _
  rw [Finset.sum_coe_sort]
  have hset : StageLabels.activeComponents
      (LinkComponents.graph (multiplicity s len m) (P s hs len m cmp err)).connectedComponentMk
      (Finset.univ.filter (fun i => j < multiplicity s len m i)) =
      Finset.univ.filter (fun c : Component s hs len m cmp err =>
        j < LinkComponents.maximum (multiplicity s len m) (P s hs len m cmp err) c) := by
    ext c
    exact (active_iff s hs len m cmp err j c).trans (by simp)
  rw [hset,Finset.sum_filter]

end TorsionFreeZeroDivisors.ActualStageLabels

namespace TorsionFreeZeroDivisors.ChainStageLabels
open scoped Classical BigOperators
section
/-- Direct membership in a finite active projection, with the generic index
instances retained rather than recomputed after specializing the sigma type. -/
theorem stageWords_mem {I T : Type*} [Fintype I] [Fintype T] (h : I → ℕ)
    (A : Finset I) (P : ((i : I) → Fin (h i) → T) → Prop)
    (W : (i : I) → Fin (h i) → T) (hW : P W) :
    (fun i : A => W i.val) ∈ StageLabels.stageWords h A P := by
  apply Finset.mem_image.mpr
  refine ⟨W,?_,rfl⟩
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact hW
end
open scoped Classical BigOperators
open BlockAlignment ComparedBlocks RepeatedBlocks WordEstimate
variable {C E : Type*} [Fintype C] (s : ℝ) (hs : 0 < s) (len m : C → ℕ) (j : ℕ)

abbrev ActiveChain := {c : C // j < m c}
abbrev StagePosition := (c : ActiveChain m j) × positions 0 (len c.val)
abbrev StageTail := (c : ActiveChain m j) × tail s (len c.val)
def activeBlocks : Finset (Underlying s len) := Finset.univ.filter (fun i => j < m i.1)

omit [Fintype C] in
include hs in
theorem tail_subset (ell : ℕ) : tail s ell ⊆ positions 0 ell := by
  intro q hq
  obtain ⟨hlo,hhi⟩ := mem_positions.mp hq
  apply mem_positions.mpr
  exact ⟨le_trans (by positivity : (0:ℝ) ≤ (blockCount s ell : ℝ)*s) hlo,hhi⟩

def blockPoint (i : activeBlocks s len m j) (k : Fin (height s len i.val)) :
    StagePosition len m j :=
  ⟨⟨i.val.1,(Finset.mem_filter.mp i.property).2⟩,
    ⟨((wordCoordinate s len i.val).symm k).val,
      full_subset s hs (len i.val.1) i.val.2 ((wordCoordinate s len i.val).symm k).property⟩⟩

def tailPoint (x : StageTail s len m j) : StagePosition len m j :=
  ⟨x.1,⟨x.2.val,tail_subset s hs (len x.1.val) x.2.property⟩⟩

def blockRestrict (F : StagePosition len m j → Letter) :
    (i : activeBlocks s len m j) → Fin (height s len i.val) → Letter :=
  fun i k => F (blockPoint s hs len m j i k)
def tailRestrict (F : StagePosition len m j → Letter) : StageTail s len m j → Letter :=
  fun x => F (tailPoint s hs len m j x)

def encode (F : StagePosition len m j → Letter) :=
  (blockRestrict s hs len m j F,tailRestrict s hs len m j F)

/-- Full blocks and the literal end fragments determine every active chain
letter, without choosing values on inactive chains. -/
theorem encode_injective : Function.Injective (encode s hs len m j) := by
  intro F G he
  have hb := congrArg Prod.fst he
  have ht := congrArg Prod.snd he
  funext x
  rcases x with ⟨⟨c,hc⟩,q⟩
  obtain ⟨k,hk⟩ | htq := full_or_tail s hs (len c) q.property
  · let i : activeBlocks s len m j := ⟨⟨c,k⟩,by simp [activeBlocks,hc]⟩
    let z : Fin (height s len i.val) := wordCoordinate s len i.val ⟨q.val,hk⟩
    have h := congr_fun (congr_fun hb i) z
    simpa [encode,blockRestrict,blockPoint,z,i] using h
  · have h := congr_fun ht ⟨⟨c,hc⟩,⟨q.val,htq⟩⟩
    exact h

/-- The exact finite extension factor contributed by arbitrary tail letters. -/
theorem extension_count (X : Finset (StagePosition len m j → Letter))
    (Y : Finset ((i : activeBlocks s len m j) → Fin (height s len i.val) → Letter))
    (hX : ∀ F ∈ X, blockRestrict s hs len m j F ∈ Y) :
    X.card ≤ Y.card * (Fintype.card Letter)^Fintype.card (StageTail s len m j) := by
  calc
    X.card = (X.image (encode s hs len m j)).card :=
      (Finset.card_image_of_injective X (encode_injective s hs len m j)).symm
    _ ≤ (Y ×ˢ Finset.univ).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨F,hF,rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_product.mpr ⟨hX F hF,Finset.mem_univ _⟩
    _ = _ := by simp

include hs in
/-- The fragment loss is O(s) per marked chain, with a literal uniform bound. -/
theorem tail_count : (Fintype.card (StageTail s len m j) : ℝ) ≤
    (s+1)*Fintype.card C := by
  simp only [StageTail,Fintype.card_sigma,Fintype.card_coe,Nat.cast_sum]
  calc
    (∑ c : ActiveChain m j, ((tail s (len c.val)).card : ℝ)) ≤
        ∑ _c : ActiveChain m j, (s+1) :=
      Finset.sum_le_sum (fun c _ => tail_bound s hs (len c.val))
    _ = (s+1)*Fintype.card (ActiveChain m j) := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast Fintype.card_subtype_le (fun c : C => j < m c))
      (by positivity)

variable (cmp : Comparisons (E := E) (traversalLength len m)) (d : Underlying s len → ℤ)

def fullWords : Finset (StagePosition len m j → Letter) :=
  Finset.univ.filter (fun F => ∃ w : C → ℤ → Letter,
    ActualStageLabels.Comparing len m cmp w ∧ ActualStageLabels.Immersed s len w ∧
    (∀ i, word s len w i ∈ binWords (height s len i) (d i)) ∧
    F = fun x => w x.1.val x.2.val)

theorem blockRestrict_word (w : C → ℤ → Letter) :
    blockRestrict s hs len m j (fun x => w x.1.val x.2.val) =
      fun i k => word s len w i.val k := by
  funext i k
  have hv := wordCoordinate_val s len i.val ((wordCoordinate s len i.val).symm k)
  rw [Equiv.apply_symm_apply] at hv
  change w i.val.1 ((wordCoordinate s len i.val).symm k).val =
    w i.val.1 ((k.val : ℤ)+lower s len i.val)
  congr 1
  omega

/-- Every literal feasible full-chain assignment projects to feasible blocks. -/
theorem restrict_mem (F : StagePosition len m j → Letter)
    (hF : F ∈ fullWords s len m j cmp d) :
    blockRestrict s hs len m j F ∈ StageLabels.stageWords (height s len)
      (activeBlocks s len m j) (ActualStageLabels.Feasible s len m cmp d) := by
  have hF' : ∃ w : C → ℤ → Letter,
      ActualStageLabels.Comparing len m cmp w ∧ ActualStageLabels.Immersed s len w ∧
      (∀ i, word s len w i ∈ binWords (height s len i) (d i)) ∧
      F = fun x => w x.1.val x.2.val := (Finset.mem_filter.mp hF).2
  obtain ⟨w,hw,hr,hd,rfl⟩ := hF'
  rw [blockRestrict_word]
  have hW : ActualStageLabels.Feasible s len m cmp d (word s len w) := ⟨hd,w,hw,hr,rfl⟩
  exact stageWords_mem (height s len) (activeBlocks s len m j)
    (ActualStageLabels.Feasible s len m cmp d) (word s len w) hW

/-- Numerical extension bound factored independently of the graph types. -/
theorem count_extension_exp (x y k z : ℕ) (cost error bound : ℝ)
    (hxy : x ≤ y*k^z) (hy : (y : ℝ) ≤ Real.exp (cost+error*Real.log k))
    (hz : (z : ℝ) ≤ bound) (hk : 0 < k) :
    (x : ℝ) ≤ Real.exp (cost+(error+bound)*Real.log k) := by
  have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk)
  have hpow : (k : ℝ)^z = Real.exp ((z : ℝ)*Real.log k) := by
    rw [Real.exp_nat_mul,Real.exp_log (by exact_mod_cast hk)]
  have hxy' : (x : ℝ) ≤ (y : ℝ)*(k : ℝ)^z := by exact_mod_cast hxy
  calc
    (x : ℝ) ≤ (y : ℝ)*(k : ℝ)^z := hxy'
    _ ≤ Real.exp (cost+error*Real.log k) * (k : ℝ)^z :=
      mul_le_mul_of_nonneg_right hy (by positivity)
    _ = Real.exp (cost+error*Real.log k+(z : ℝ)*Real.log k) := by simp only [hpow,Real.exp_add]
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hz hlog])

/-- Source stage-label estimate including every tail, not just full blocks. -/
theorem full_stage_count (err : ℕ)
    (hlarge : ∀ i, 3002 ≤ height s len i)
    (hscale : ∀ i, s+1200 ≤ 2*(height s len i : ℝ))
    (hreduced : ∀ x e, cmp.side x = some e →
      (x.1.1,x.2.val) ≠ ((cmp.pairing.partner x).1.1,(cmp.pairing.partner x).2.val)) :
    ((fullWords s len m j cmp d).card : ℝ) ≤
      Real.exp ((∑ c : StageLabels.activeComponents
        (ActualStageLabels.L s hs len m cmp err).graph.connectedComponentMk (activeBlocks s len m j),
        ActualStageLabels.cost s hs len m cmp err d c.val) +
        (2*(err : ℝ)*Fintype.card (Underlying s len)+(s+1)*Fintype.card C)*
          Real.log (Fintype.card Letter)) := by
  have he := extension_count s hs len m j (fullWords s len m j cmp d)
    (StageLabels.stageWords (height s len) (activeBlocks s len m j)
      (ActualStageLabels.Feasible s len m cmp d)) (restrict_mem s hs len m j cmp d)
  have hcard := ActualStageLabels.stage_count s hs len m cmp err d
    (activeBlocks s len m j) hlarge hscale hreduced
  exact count_extension_exp _ _ _ _ _ _ _ he hcard (tail_count s hs len m j)
    (Fintype.card_pos (α := Letter))

end TorsionFreeZeroDivisors.ChainStageLabels

end

end OAI
