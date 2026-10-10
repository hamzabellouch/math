import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.Incident
import OAI.Combinatorics.MatchingCount.Graphs.Height

namespace OAI

namespace MatchingFPRAS.Transport

section

open Finset MatchingFPRAS.Switching

variable {V E : Type*} [Fintype V] [LinearOrder V]

variable (edge : E → Sym2 V) (hnd : ∀ e, ¬(edge e).IsDiag)

local notation "inc" => (fun (e : E) (x : V) => x ∈ edge e)

noncomputable def edgeLow (s : Sym2 V) : V := Sym2.lift ⟨min,min_comm⟩ s

noncomputable def edgeHigh (s : Sym2 V) : V := Sym2.lift ⟨max,max_comm⟩ s

omit [Fintype V] in
@[simp] lemma edgeLow_mk (x y : V) : edgeLow s(x,y)=min x y := rfl

omit [Fintype V] in
@[simp] lemma edgeHigh_mk (x y : V) : edgeHigh s(x,y)=max x y := rfl

omit [Fintype V] in
lemma edgeLow_mem (s : Sym2 V) : edgeLow s ∈ s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [min_def,h]

omit [Fintype V] in
lemma edgeHigh_mem (s : Sym2 V) : edgeHigh s ∈ s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [max_def,h]

omit [Fintype V] in
lemma edge_low_high (s : Sym2 V) : s(edgeLow s,edgeHigh s)=s := by
  induction s using Sym2.inductionOn with
  | hf x y => by_cases h : x≤y <;> simp [min_def,max_def,h,Sym2.eq_swap]

omit [Fintype V] in
lemma edgeLow_lt_high (s : Sym2 V) (hs : ¬s.IsDiag) : edgeLow s < edgeHigh s := by
  induction s using Sym2.inductionOn with
  | hf x y =>
    have hxy : x ≠ y := by simpa using hs
    rcases hxy.lt_or_gt with h | h <;> simp [h.le,h]

variable (Q : Partial (fun (e : E) (x : V) => x ∈ edge e))

omit [Fintype V] in
lemma edgeLow_ne_high (s : Sym2 V) (hs : ¬s.IsDiag) : edgeLow s ≠ edgeHigh s :=
  (edgeLow_lt_high s hs).ne

noncomputable def pickedEdge (x : V) (hx : x ∈ support inc Q.val) : E :=
  Classical.choose (Q.property.2 x hx)

omit [LinearOrder V] in
lemma pickedEdge_spec (x : V) (hx : x ∈ support inc Q.val) :
    pickedEdge edge Q x hx ∈ Q.val ∧ x ∈ edge (pickedEdge edge Q x hx) :=
  (Classical.choose_spec (Q.property.2 x hx)).1

omit [LinearOrder V] in
lemma pickedEdge_unique (x : V) (hx : x ∈ support inc Q.val) (e : E)
    (he : e∈Q.val) (hxe : x ∈ edge e) : e=pickedEdge edge Q x hx :=
  (Classical.choose_spec (Q.property.2 x hx)).2 e ⟨he,hxe⟩

noncomputable def partialMateFun (x : V) : V :=
  if hx : x∈support inc Q.val then Sym2.Mem.other (pickedEdge_spec edge Q x hx).2 else x

lemma partialMateFun_out (x : V) (hx : x∉support inc Q.val) : partialMateFun edge Q x=x := by
  simp [partialMateFun,hx]

include hnd in
lemma partialMateFun_ne (x : V) (hx : x∈support inc Q.val) : partialMateFun edge Q x≠x := by
  simp only [partialMateFun,dite_eq_left hx]
  exact Sym2.other_ne (hnd _) _

lemma partialMateFun_pair (x : V) (hx : x∈support inc Q.val) :
    s(x,partialMateFun edge Q x)=edge (pickedEdge edge Q x hx) := by
  simp only [partialMateFun,dite_eq_left hx]
  exact Sym2.other_spec _

lemma partialMateFun_incident (e : E) (he : e∈Q.val) (x : V) (hx : x∈edge e) :
    s(x,partialMateFun edge Q x)=edge e := by
  have hxQ := (mem_support inc Q.val x).mpr ⟨e,he,hx⟩
  rw [partialMateFun_pair edge Q x hxQ,←pickedEdge_unique edge Q x hxQ e he hx]

lemma partialMateFun_covered (x : V) (hx : x∈support inc Q.val) :
    partialMateFun edge Q x ∈ support inc Q.val := by
  apply (mem_support inc Q.val _).mpr
  refine ⟨pickedEdge edge Q x hx,(pickedEdge_spec edge Q x hx).1,?_⟩
  rw [←partialMateFun_pair edge Q x hx]
  simp

include hnd in
lemma partialMateFun_involutive : Function.Involutive (partialMateFun edge Q) := by
  intro x
  by_cases hx : x∈support inc Q.val
  · have h₁ := partialMateFun_pair edge Q x hx
    have hi : partialMateFun edge Q x ∈ edge (pickedEdge edge Q x hx) := by rw [←h₁]; simp
    have h₂ := partialMateFun_incident edge Q (pickedEdge edge Q x hx)
      (pickedEdge_spec edge Q x hx).1 _ hi
    rcases Sym2.eq_iff.mp (h₂.trans h₁.symm) with h | h
    · exact False.elim (partialMateFun_ne edge hnd Q x hx h.1)
    · exact h.2
  · rw [partialMateFun_out edge Q x hx,partialMateFun_out edge Q x hx]

noncomputable def partialMate : Mate V := ⟨partialMateFun edge Q,partialMateFun_involutive edge hnd Q⟩

lemma partialMate_holes : HasHoles (partialMate edge hnd Q) (support inc Q.val)ᶜ := by
  intro x
  change partialMateFun edge Q x=x ↔ _
  rw [Finset.mem_compl]
  constructor
  · intro h hx; exact partialMateFun_ne edge hnd Q x hx h
  · exact partialMateFun_out edge Q x

lemma partialMate_low (e : E) (he : e∈Q.val) :
    partialMateFun edge Q (edgeLow (edge e))=edgeHigh (edge e) := by
  have h := partialMateFun_incident edge Q e he _ (edgeLow_mem _)
  exact Sym2.congr_right.mp (h.trans (edge_low_high (edge e)).symm)

lemma partial_low_mem (e : E) (he : e∈Q.val) :
    edgeLow (edge e) ∈ univ.filter (fun x => x < (partialMate edge hnd Q).val x) := by
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  change edgeLow (edge e) < partialMateFun edge Q (edgeLow (edge e))
  rw [partialMate_low edge Q e he]
  exact edgeLow_lt_high _ (hnd e)

lemma partial_low_injective (e : E) (he : e∈Q.val) (f : E) (hf : f∈Q.val)
    (h : edgeLow (edge e)=edgeLow (edge f)) : e=f := by
  have hx := edgeLow_mem (edge e)
  exact Q.property.unique (Q.property.1 e he _ hx) he hx hf (h.symm ▸ edgeLow_mem (edge f))

lemma partial_low_surjective (x : V)
    (hx : x ∈ univ.filter (fun x => x < (partialMate edge hnd Q).val x)) :
    ∃ e, ∃ _ : e∈Q.val, edgeLow (edge e)=x := by
  have hx' : x < partialMateFun edge Q x := (Finset.mem_filter.mp hx).2
  have hcov : x∈support inc Q.val := by
    by_contra hn
    rw [partialMateFun_out edge Q x hn] at hx'
    exact lt_irrefl _ hx'
  refine ⟨pickedEdge edge Q x hcov,(pickedEdge_spec edge Q x hcov).1,?_⟩
  rw [←partialMateFun_pair edge Q x hcov,edgeLow_mk,min_eq_left hx'.le]

include hnd in
lemma partial_card : (support inc Q.val).card=2*Q.val.card := by
  have hcard := Finset.card_bij (fun e _ => edgeLow (edge e))
    (partial_low_mem edge hnd Q) (partial_low_injective edge Q)
    (partial_low_surjective edge hnd Q)
  have hmate := mate_edge_count (partialMate edge hnd Q) (support inc Q.val)
    (partialMate_holes edge hnd Q)
  omega

include hnd in
lemma partial_even : Even (support inc Q.val).card := by
  rw [partial_card edge hnd Q]
  exact even_two_mul _

lemma partial_weight (B : V → V → ℝ) :
    (∏ e ∈ Q.val, B (edgeLow (edge e)) (edgeHigh (edge e)))=weight B (partialMate edge hnd Q) := by
  classical
  unfold weight
  rw [←Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => edgeLow (edge e))
    (partial_low_mem edge hnd Q) (partial_low_injective edge Q)
    (partial_low_surjective edge hnd Q)
  intro e he
  change B _ _ = B _ (partialMateFun edge Q _)
  rw [partialMate_low edge Q e he]

theorem partial_height_le_capacity (B : V → V → ℝ) (height : E → ℝ)
    (h0 : ∀ e, 0≤height e)
    (hh : ∀ e, height e ≤ B (edgeLow (edge e)) (edgeHigh (edge e))) :
    (∏ e ∈ Q.val, height e) ≤ pairingCapacity B (support inc Q.val) (partial_even edge hnd Q) := by
  calc
    _ ≤ ∏ e ∈ Q.val, B (edgeLow (edge e)) (edgeHigh (edge e)) :=
      Finset.prod_le_prod₀ (fun e _ => h0 e) (fun e _ => hh e)
    _ = weight B (partialMate edge hnd Q) := partial_weight edge hnd Q B
    _ ≤ _ := Finset.le_sup' (f := weight B) ((mem_matchings _ _).mpr (partialMate_holes edge hnd Q))

end

section

open Finset

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

noncomputable local instance edgeLowCardinalityBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

noncomputable def bagEdgeSigmaEquiv : BagEdge bags ≃
    Σ s : {s : Sym2 V // ¬s.IsDiag}, {l : L // ∀ x, x∈s.val → l∈bags x} where
  toFun e := ⟨⟨e.val.val.1,e.val.property⟩,⟨e.val.val.2,e.property⟩⟩
  invFun a := ⟨⟨(a.1.val,a.2.val),a.1.property⟩,a.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma bag_color_card_le_two (hb : ∀ x,(bags x).card≤2) (s : {s : Sym2 V // ¬s.IsDiag}) :
    Fintype.card {l : L // ∀ x, x∈s.val → l∈bags x} ≤ 2 := by
  let f : {l : L // ∀ x, x∈s.val → l∈bags x} → {l : L // l∈bags (edgeLow s.val)} :=
    fun l => ⟨l.val,l.property _ (edgeLow_mem _)⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun z : {l : L // l∈bags (edgeLow s.val)} => z.val) h
  have := Fintype.card_le_of_injective f hi
  rw [Fintype.card_coe] at this
  exact this.trans (hb _)

theorem bagEdge_card_le_square (hb : ∀ x,(bags x).card≤2) :
    Fintype.card (BagEdge bags) ≤ (Fintype.card V)^2 := by
  classical
  rw [Fintype.card_congr (bagEdgeSigmaEquiv bags),Fintype.card_sigma]
  calc
    _ ≤ ∑ _s : {s : Sym2 V // ¬s.IsDiag}, 2 :=
      Finset.sum_le_sum (fun s _ => bag_color_card_le_two bags hb s)
    _ = 2*(Fintype.card V).choose 2 := by
      rw [Finset.sum_const,Finset.card_univ,smul_eq_mul,Sym2.card_subtype_not_diag,mul_comm]
    _ ≤ Fintype.card V*(Fintype.card V-1) := by rw [Nat.choose_two_right]; omega
    _ ≤ (Fintype.card V)^2 := by
      rw [pow_two]
      exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

end

open Finset MatchingFPRAS.Switching

variable {V L : Type*} [Fintype V] [Fintype L] [LinearOrder V] [DecidableEq L]

variable (bags : V → Finset L)

noncomputable local instance edgeLowInflationBagEdgeFintype : Fintype (BagEdge bags) :=
  Fintype.ofFinite _

def inflationScale (D₀ : ℝ) : ℝ := 100*(Fintype.card V : ℝ)^2*D₀

theorem bag_inflation_of_hole_estimate (hN : 0<Fintype.card V)
    (hb : ∀ x,(bags x).card≤2) (B : V → V → ℝ)
    (height : L → ℝ) (hheight : ∀ l,0≤height l)
    (hcommon : ∀ e : BagEdge bags, height e.val.val.2 ≤ B (edgeLow e.val.val.1) (edgeHigh e.val.val.1))
    (r : BagEdge bags → ℝ) (hr : ∀ e,0≤r e)
    (hz : 0<partitionWeight BagEdge.Incident r univ)
    (D₀ : ℝ) (hD₀ : 0<D₀)
    (hhole : ∀ U : Finset V, ∀ hU : Even U.card,
      partitionWeight BagEdge.Incident r (univ \ U) / partitionWeight BagEdge.Incident r univ *
        pairingCapacity B U hU ≤ 2*D₀^(U.card/2)) :
    let D := inflationScale (V := V) D₀
    1 ≤ partitionWeight BagEdge.Incident (fun e => r e+height e.val.val.2/D) univ /
      partitionWeight BagEdge.Incident r univ ∧
    partitionWeight BagEdge.Incident (fun e => r e+height e.val.val.2/D) univ /
      partitionWeight BagEdge.Incident r univ ≤ 2 := by
  classical
  let D := inflationScale (V := V) D₀
  have hNp : 0<(Fintype.card V:ℝ) := Nat.cast_pos.mpr hN
  have hD : 0<D := by dsimp [D,inflationScale]; positivity
  apply finite_inflation BagEdge.Incident r (fun e => height e.val.val.2/D) hr
    (fun e => div_nonneg (hheight _) hD.le)
    (fun e => ⟨edgeLow e.val.val.1,edgeLow_mem _⟩) hz (D₀/D) (div_nonneg hD₀.le hD.le)
  · have hcard : (Fintype.card (BagEdge bags):ℝ) ≤ (Fintype.card V:ℝ)^2 := by
      exact_mod_cast bagEdge_card_le_square bags hb
    rw [←mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    change (Fintype.card (BagEdge bags):ℝ)*D₀ ≤ 1/100*D
    dsimp [D,inflationScale]
    nlinarith [mul_le_mul_of_nonneg_right hcard hD₀.le]
  · intro Q _
    let edge : BagEdge bags → Sym2 V := fun e => e.val.val.1
    have hnd : ∀ e,¬(edge e).IsDiag := fun e => e.val.property
    have heven := partial_even edge hnd Q
    let g := partitionWeight BagEdge.Incident r (univ \ support BagEdge.Incident Q.val) /
      partitionWeight BagEdge.Incident r univ
    have hg : 0≤g := div_nonneg (partitionWeight_nonneg _ r hr _) hz.le
    have hc := partial_height_le_capacity edge hnd Q B (fun e => height e.val.val.2)
      (fun e => hheight _) hcommon
    have hh := hhole _ heven
    have hcard := partial_card edge hnd Q
    change (support BagEdge.Incident Q.val).card=2*Q.val.card at hcard
    change g * pairingCapacity B (support BagEdge.Incident Q.val) heven ≤ 2*D₀^((support BagEdge.Incident Q.val).card/2) at hh
    have hpow : (support BagEdge.Incident Q.val).card/2=Q.val.card := by omega
    rw [hpow] at hh
    rw [Finset.prod_div_distrib,Finset.prod_const]
    change (∏ e∈Q.val,height e.val.val.2) / D^Q.val.card *
      partitionWeight BagEdge.Incident r (univ \ support BagEdge.Incident Q.val) /
      partitionWeight BagEdge.Incident r univ ≤ _
    calc
      _ = g*(∏ e∈Q.val,height e.val.val.2) / D^Q.val.card := by dsimp [g]; ring
      _ ≤ g*pairingCapacity B (support BagEdge.Incident Q.val) heven / D^Q.val.card :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc hg) (pow_nonneg hD.le _)
      _ ≤ (2*D₀^Q.val.card)/D^Q.val.card := div_le_div_of_nonneg_right hh (pow_nonneg hD.le _)
      _ = 2*(D₀/D)^Q.val.card := by rw [div_pow]; ring

end MatchingFPRAS.Transport

namespace MatchingFPRAS.RealGeometry

open Finset MatchingFPRAS.Subdivision MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

variable (u v : E → V) (m : ℕ)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma edge_incident_internal (q : E × Fin (m+1)) (e : E) (i : Fin m) :
    Sum.inr (e,i) ∈ edge u v m q.1 q.2 ↔ q=(e,i.castSucc) ∨ q=(e,i.succ) := by
  simp only [edge,Sym2.mem_iff,eq_comm (a := Sum.inr _) ]
  rw [atVertex_eq_inr_iff,atVertex_eq_inr_iff]
  simp only [Fin.val_castSucc,Fin.val_succ,Prod.ext_iff]
  constructor
  · rintro (⟨h,h'⟩|⟨h,h'⟩)
    · exact Or.inr ⟨h,Fin.ext h'⟩
    · exact Or.inl ⟨h,Fin.ext (show q.2.val=i.val by omega)⟩
  · rintro (⟨h,h'⟩|⟨h,h'⟩)
    · exact Or.inr ⟨h,by have := congrArg Fin.val h'; simpa using this⟩
    · exact Or.inl ⟨h,by have := congrArg Fin.val h'; simpa using this⟩

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
lemma edge_incident_terminal (q : E × Fin (m+1)) (x : V) :
    Sum.inl x ∈ edge u v m q.1 q.2 ↔
      (q.2=0 ∧ u q.1=x) ∨ (q.2=Fin.last m ∧ v q.1=x) := by
  simp only [edge,Sym2.mem_iff,eq_comm (a := Sum.inl _)]
  rw [first_vertex_terminal,second_vertex_terminal]
  simp only [Fin.ext_iff,Fin.val_zero,Fin.val_last]

noncomputable def selectedSet (b : E → Selection m) : Finset (E × Fin (m+1)) := by
  classical
  exact univ.filter fun q => b q.1 q.2=true

omit [DecidableEq E] in
@[simp] lemma mem_selectedSet (b : E → Selection m) (q : E × Fin (m+1)) :
    q∈selectedSet m b ↔ b q.1 q.2=true := by
  simp [selectedSet]

noncomputable def survivors (R : Finset V) (U : E → Finset (Fin m)) : Finset (Vertex V E m) := by
  classical
  exact univ.filter fun x => match x with
    | Sum.inl x => x∉R
    | Sum.inr (e,i) => i∉U e

omit [DecidableEq V] [DecidableEq E] in
@[simp] lemma mem_survivors_terminal (R : Finset V) (U : E → Finset (Fin m)) (x : V) :
    Sum.inl x ∈ survivors m R U ↔ x∉R := by simp [survivors]

omit [DecidableEq V] [DecidableEq E] in
@[simp] lemma mem_survivors_internal (R : Finset V) (U : E → Finset (Fin m)) (e : E) (i : Fin m) :
    Sum.inr (e,i) ∈ survivors m R U ↔ i∉U e := by simp [survivors]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma internal_unique_iff (b : E → Selection m) (e : E) (i : Fin m) :
    (∃! q, q∈selectedSet m b ∧ Sum.inr (e,i)∈edge u v m q.1 q.2) ↔
      b e i.castSucc ≠ b e i.succ := by
  simp only [mem_selectedSet,edge_incident_internal]
  have hne : i.castSucc≠i.succ := by intro h; have := congrArg Fin.val h; simp at this
  cases h₁ : b e i.castSucc <;> cases h₂ : b e i.succ <;> simp only [ne_eq,Bool.false_eq_true,
    not_false_eq_true,Bool.true_eq_false,not_true_eq_false,iff_false,iff_true]
  · rintro ⟨q,hq,_⟩; rcases hq.2 with rfl|rfl <;> simp_all
  · refine ⟨(e,i.succ),⟨h₂,Or.inr rfl⟩,?_⟩
    rintro ⟨f,j⟩ ⟨hs,hq⟩
    rcases hq with hq|hq
    · cases hq; simp_all
    · exact hq
  · refine ⟨(e,i.castSucc),⟨h₁,Or.inl rfl⟩,?_⟩
    rintro ⟨f,j⟩ ⟨hs,hq⟩
    rcases hq with hq|hq
    · exact hq
    · cases hq; simp_all
  · rintro ⟨q,hq,hu⟩
    have h := (hu (e,i.castSucc) ⟨h₁,Or.inl rfl⟩).trans (hu (e,i.succ) ⟨h₂,Or.inr rfl⟩).symm
    exact hne (congrArg Prod.snd h)

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma terminal_selected_iff (b : E → Selection m) (q : E × Fin (m+1)) (x : V) :
    q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2 ↔
    (q.2=0 ∧ b q.1 0=true ∧ u q.1=x) ∨
      (q.2=Fin.last m ∧ b q.1 (Fin.last m)=true ∧ v q.1=x) := by
  rw [mem_selectedSet,edge_incident_terminal]
  constructor
  · rintro ⟨hs, (⟨h₀,hu⟩|⟨hm,hv⟩)⟩
    · exact Or.inl ⟨h₀,h₀ ▸ hs,hu⟩
    · exact Or.inr ⟨hm,hm ▸ hs,hv⟩
  · rintro (⟨h₀,hs,hu⟩|⟨hm,hs,hv⟩)
    · exact ⟨h₀ ▸ hs,Or.inl ⟨h₀,hu⟩⟩
    · exact ⟨hm ▸ hs,Or.inr ⟨hm,hv⟩⟩

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
lemma terminal_unique_iff (huv : ∀ e,u e≠v e) (b : E → Selection m) (x : V) :
    (∃! q, q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2) ↔
    (∃! e, Uses u v b e x) := by
  constructor
  · rintro ⟨q,hq,hunique⟩
    rw [terminal_selected_iff] at hq
    have huse : Uses u v b q.1 x := by rcases hq with h|h; exact Or.inl h.2; exact Or.inr h.2
    refine ⟨q.1,huse,?_⟩
    intro f hf
    rcases hf with hf|hf
    · exact congrArg Prod.fst (hunique (f,0) ((terminal_selected_iff _ _ _ _ _ _).mpr (Or.inl ⟨rfl,hf⟩)))
    · exact congrArg Prod.fst (hunique (f,Fin.last m) ((terminal_selected_iff _ _ _ _ _ _).mpr (Or.inr ⟨rfl,hf⟩)))
  · rintro ⟨e,he,hu⟩
    have uniq (i : Fin (m+1)) (hi : (e,i)∈selectedSet m b ∧ Sum.inl x∈edge u v m e i)
        (q : E × Fin (m+1)) (hq : q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2) : q=(e,i) := by
      rw [terminal_selected_iff] at hi hq
      have hf : q.1=e := hu q.1 (by rcases hq with h|h; exact Or.inl h.2; exact Or.inr h.2)
      apply Prod.ext hf
      rcases hi with hi|hi <;> rcases hq with hq|hq
      · exact hq.1.trans hi.1.symm
      · exact False.elim (huv e (hi.2.2.trans (hf ▸ hq.2.2).symm))
      · exact False.elim (huv e ((hf ▸ hq.2.2).trans hi.2.2.symm))
      · exact hq.1.trans hi.1.symm
    rcases he with he|he
    · have hi := (terminal_selected_iff u v m b (e,0) x).mpr (Or.inl ⟨rfl,he⟩)
      exact ⟨(e,0),hi,uniq 0 hi⟩
    · have hi := (terminal_selected_iff u v m b (e,Fin.last m) x).mpr (Or.inr ⟨rfl,he⟩)
      exact ⟨(e,Fin.last m),hi,uniq _ hi⟩

omit [DecidableEq V] [DecidableEq E] in
theorem family_iff_matching (huv : ∀ e,u e≠v e) (R : Finset V)
    (U : E → Finset (Fin m)) (b : E → Selection m) :
    FamilyHoles u v m R U b ↔
    MatchingOn (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (selectedSet m b) (survivors m R U) := by
  constructor
  · intro hb
    constructor
    · intro q hq x hx
      cases x with
      | inl x =>
        rw [mem_survivors_terminal]
        intro hr
        have huse : Uses u v b q.1 x := by
          rcases (terminal_selected_iff u v m b q x).mp ⟨hq,hx⟩ with h|h
          · exact Or.inl h.2
          · exact Or.inr h.2
        exact hb.2.1 x hr q.1 huse
      | inr ei =>
        rcases ei with ⟨e,i⟩
        rw [mem_survivors_internal]
        intro hi
        have hd := hb.1 e i
        simp only [hi,ite_eq_left] at hd
        rcases (edge_incident_internal u v m q e i).mp hx with rfl|rfl
        · have h := (mem_selectedSet m b _).mp hq; simp_all
        · have h := (mem_selectedSet m b _).mp hq; simp_all
    · intro x hx
      cases x with
      | inl x => exact (terminal_unique_iff u v m huv b x).mpr (hb.2.2 x ((mem_survivors_terminal m R U x).mp hx))
      | inr ei =>
        rcases ei with ⟨e,i⟩
        apply (internal_unique_iff u v m b e i).mpr
        simpa only [Valid,ite_eq_right ((mem_survivors_internal m R U e i).mp hx)] using hb.1 e i
  · intro hM
    refine ⟨?_,?_,?_⟩
    · intro e i
      split_ifs with hi
      · constructor
        · cases h : b e i.castSucc
          · rfl
          · have hx := hM.1 (e,i.castSucc) ((mem_selectedSet m b _).mpr h) (Sum.inr (e,i))
              ((edge_incident_internal u v m _ e i).mpr (Or.inl rfl))
            exact False.elim (((mem_survivors_internal m R U e i).mp hx) hi)
        · cases h : b e i.succ
          · rfl
          · have hx := hM.1 (e,i.succ) ((mem_selectedSet m b _).mpr h) (Sum.inr (e,i))
              ((edge_incident_internal u v m _ e i).mpr (Or.inr rfl))
            exact False.elim (((mem_survivors_internal m R U e i).mp hx) hi)
      · exact (internal_unique_iff u v m b e i).mp (hM.2 (Sum.inr (e,i)) ((mem_survivors_internal m R U e i).mpr hi))
    · intro x hx e he
      have hq : ∃ q, q∈selectedSet m b ∧ Sum.inl x∈edge u v m q.1 q.2 := by
        rcases he with he|he
        · exact ⟨(e,0),(terminal_selected_iff u v m b _ x).mpr (Or.inl ⟨rfl,he⟩)⟩
        · exact ⟨(e,Fin.last m),(terminal_selected_iff u v m b _ x).mpr (Or.inr ⟨rfl,he⟩)⟩
      obtain ⟨q,hq,hqx⟩ := hq
      exact ((mem_survivors_terminal m R U x).mp (hM.1 q hq _ hqx)) hx
    · intro x hx
      exact (terminal_unique_iff u v m huv b x).mp (hM.2 (Sum.inl x) ((mem_survivors_terminal m R U x).mpr hx))

noncomputable def selectionEquiv : (E → Selection m) ≃ Finset (E × Fin (m+1)) where
  toFun := selectedSet m
  invFun S e i := decide ((e,i)∈S)
  left_inv b := by
    funext e i
    simp [mem_selectedSet]
  right_inv S := by
    ext ⟨e,i⟩
    simp

noncomputable def realMatchingEquiv (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m)) :
    {b : E → Selection m // FamilyHoles u v m R U b} ≃
    Matchings (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (survivors m R U) :=
  (selectionEquiv (E := E) m).subtypeEquiv (family_iff_matching u v m huv R U)

omit [DecidableEq E] in
lemma selectedSet_weight (w : E → Fin (m+1) → ℝ) (b : E → Selection m) :
    (∏ q ∈ selectedSet m b,w q.1 q.2)=∏ e,selectedWeight (w e) (b e) := by
  classical
  simp only [selectedSet,Finset.prod_filter,selectedWeight,Fintype.prod_prod_type]

omit [DecidableEq V] in
theorem realMatching_partition (huv : ∀ e,u e≠v e) (R : Finset V) (U : E → Finset (Fin m))
    (w : E → Fin (m+1) → ℝ) :
    partitionWeight (fun (q : E × Fin (m+1)) x => x∈edge u v m q.1 q.2) (fun q => w q.1 q.2) (survivors m R U)=
      realHolePartition u v m R U w := by
  classical
  let := Fintype.ofFinite {b : E → Selection m // FamilyHoles u v m R U b}
  unfold partitionWeight realHolePartition
  rw [←(realMatchingEquiv u v m huv R U).sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  exact selectedSet_weight m w b.val

end MatchingFPRAS.RealGeometry

end OAI
