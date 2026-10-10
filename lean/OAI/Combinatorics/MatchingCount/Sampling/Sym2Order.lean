import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.RemainingBags

namespace OAI

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

@[instance_reducible] def sym2Order : LinearOrder (Sym2 V) :=
  LinearOrder.lift' (fun e=>toLex (Sym2.sortEquiv e).val)
    (fun _ _ h=>Sym2.sortEquiv.injective (Subtype.ext (toLex.injective h)))

attribute [local instance] sym2Order

@[instance_reducible] def bagEdgeOrder {bags : V → Finset L} : LinearOrder (BagEdge bags) :=
  LinearOrder.lift' (fun e : BagEdge bags=>toLex e.val.val)
    (fun _ _ h=>Subtype.ext (Subtype.ext (toLex.injective h)))

attribute [local instance] bagEdgeOrder

def rationalTierBase (V : Type*) [Fintype V] : ℚ := 1+((Fintype.card V:ℚ)^2)⁻¹

omit [LinearOrder V] in
lemma rationalTierBase_cast : (rationalTierBase V:ℝ)=tierBase V := by
  simp [rationalTierBase,tierBase]

def rationalSlotWeight {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) : ℚ :=
  max ((rationalTierBase V)^tier x)⁻¹ (min ((rationalTierBase V)^tier x) (w e))

omit [LinearOrder V] [Fintype L] [LinearOrder L] in
lemma rationalSlotWeight_cast [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) :
    (rationalSlotWeight w x e:ℝ)=slotWeight (fun e=>(w e:ℝ)) x e := by
  simp [rationalSlotWeight,slotWeight,tierClamp,rationalTierBase_cast]

lemma rationalSlotWeight_pos {bags : V → Finset L} {T q : ℕ} (w : BagEdge bags → ℚ)
    (x : Slot T q) (e : BagEdge bags) : 0<rationalSlotWeight w x e := by
  have h:=slotWeight_pos (fun e=>(w e:ℝ)) x e
  rw [←rationalSlotWeight_cast] at h
  exact_mod_cast h

variable {bags : V → Finset L} {G : SimpleGraph L}

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

attribute [local instance] UnitRefresh.Computable.allowedDec

@[instance_reducible] def bagEdgeFintype : Fintype (BagEdge bags) := Subtype.fintype (Allowed bags)

attribute [local instance] bagEdgeFintype

abbrev BagPM (bags : V → Finset L) := PM (BagEdge.Incident (bags:=bags))

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _

include hbags hG in
lemma parallels_bound (e : BagEdge bags) :
    (univ.filter (fun f : BagEdge bags=>f.val.val.1=e.val.val.1)).card≤2 := by
  have h:=BagEdge.parallels_card_le (label_memberships_le_two hbags hG) e
  unfold BagEdge.parallels at h
  have instances_eq : tierClampBagEdgeFintype (bags:=bags) =
      (inferInstance : Fintype (BagEdge bags)) := Subsingleton.elim _ _
  rw [instances_eq] at h
  exact h

def sampleLadderPair {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (k : ℕ) : (Fin k → Bool) → BagPM bags × BagPM bags :=
  (Sparse.pairStepTable (fun e : BagEdge bags=>e.val.val.1) (fun e=>e.val.property)
    (parallels_bound hbags hG)
    (rationalSlotWeight w x) (rationalSlotWeight w y)
    (rationalSlotWeight_pos w x) (rationalSlotWeight_pos w y) a).draw k

lemma pairProposal_instances {E : Type*} (F₁ F₂ : Fintype E) (D₁ D₂ : DecidableEq E)
    (ends : E → Sym2 V) (hloop : ∀ e,¬(ends e).IsDiag)
    (hp₁ : ∀ e,(@univ E F₁ |>.filter (fun f=>ends f=ends e)).card≤2)
    (hp₂ : ∀ e,(@univ E F₂ |>.filter (fun f=>ends f=ends e)).card≤2) :
    @pairProposal V E _ _ F₁ D₁ ends hloop hp₁ =
      @pairProposal V E _ _ F₂ D₂ ends hloop hp₂ := by
  cases Subsingleton.elim F₁ F₂
  cases Subsingleton.elim D₁ D₂
  rfl

omit [LinearOrder V] in
lemma pairLaw_instances [LinearOrder V] {E : Type*} (F₁ F₂ : Fintype E) (ends : E → Sym2 V)
    (w z : E → ℝ) : @pairLaw V E _ F₁ ends w z = @pairLaw V E _ F₂ ends w z := by
  cases Subsingleton.elim F₁ F₂
  rfl

lemma pairProposal_eq (F : Fintype (BagEdge bags)) (D : DecidableEq (BagEdge bags))
    (hpar : ∀ e : BagEdge bags,(@univ (BagEdge bags) F |>.filter
      (fun f=>f.val.val.1=e.val.val.1)).card≤2) :
    @pairProposal V (BagEdge bags) _ _ F D (fun e=>e.val.val.1) (fun e=>e.val.property)
      hpar = treePairProposal hbags hG := by
  unfold treePairProposal
  exact pairProposal_instances _ _ _ _ _ _ _ _

omit [LinearOrder L] in
lemma pairLaw_eq [LinearOrder L] (F : Fintype (BagEdge bags)) {T q : ℕ} (w : BagEdge bags → ℚ)
    (x y : Slot T q) :
    @pairLaw V (BagEdge bags) _ F (fun e=>e.val.val.1) (slotWeight (fun e=>(w e:ℝ)) x)
      (slotWeight (fun e=>(w e:ℝ)) y) =
    (fun a : BagPM bags × BagPM bags=>slotLaw (fun e=>(w e:ℝ)) x a.1*
      slotLaw (fun e=>(w e:ℝ)) y a.2) := by
  exact pairLaw_instances F (instFintypeBagEdge_5 (bags:=bags))
    (fun e : BagEdge bags=>e.val.val.1) (slotWeight (fun e=>(w e:ℝ)) x)
      (slotWeight (fun e=>(w e:ℝ)) y)

lemma metropolis_eq_capacity (D : DecidableEq (BagPM bags × BagPM bags))
    {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q) (a : BagPM bags × BagPM bags) :
    (@metropolis _ _ D (treePairProposal hbags hG)
      (fun a=>slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2) a)=
      (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
        (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2)) := by
  rw [Subsingleton.elim D (inferInstance : DecidableEq (BagPM bags × BagPM bags))]
  unfold metropolis treeLadderCapacity
  funext b
  congr 2

lemma sampleLadderPair_tv {T q : ℕ} (w : BagEdge bags → ℚ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (k : ℕ) :
    tv (imageLaw (sampleLadderPair hbags hG w x y a k))
      (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
        (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2)) ≤
      4*(8*(Fintype.card (BagEdge bags):ℝ)^2+4*Fintype.card (BagEdge bags)+3)/(2:ℝ)^k := by
  classical
  have ht := Sparse.pairStepTable_tv (fun e : BagEdge bags=>e.val.val.1)
    (fun e=>e.val.property)
    (parallels_bound hbags hG)
    (rationalSlotWeight w x) (rationalSlotWeight w y)
    (rationalSlotWeight_pos w x) (rationalSlotWeight_pos w y) a k
  simp_rw [rationalSlotWeight_cast] at ht
  change tv (imageLaw (sampleLadderPair hbags hG w x y a k)) _ ≤ _ at ht
  erw [pairProposal_eq hbags hG,pairLaw_eq,metropolis_eq_capacity] at ht
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  have ha : (a.1.val.card:ℝ)≤Fintype.card (BagEdge bags) := by exact_mod_cast card_le_univ a.1.val
  have hb : (a.2.val.card:ℝ)≤Fintype.card (BagEdge bags) := by exact_mod_cast card_le_univ a.2.val
  have hc : (a.1.val.card.choose 2:ℝ)≤(a.1.val.card:ℝ)^2 := by exact_mod_cast Nat.choose_le_pow a.1.val.card 2
  have hd : (a.1.val.card:ℝ)^2≤(Fintype.card (BagEdge bags):ℝ)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) ha 2
  nlinarith

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Variation

open Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

omit [Fintype C] in
lemma imageLaw_ignoreRight [Fintype C] [Nonempty B] (f : A → C) :
    imageLaw (fun x : A×B=>f x.1)=imageLaw f := by
  change imageLaw ((fun x : B×A=>f x.2) ∘ Equiv.prodComm A B)=_
  rw [imageLaw_comp_equiv,imageLaw_ignore]

end MatchingFPRAS.Variation

namespace MatchingFPRAS.Transport

open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _

lemma gibbs_one_uniform (A : BagPM bags) : gibbs (fun _ : BagEdge bags=>(1:ℝ)) A=
    uniform (BagPM bags) A := by
  classical
  simp only [gibbs,partition,matchingWeight,prod_const_one,sum_const,nsmul_eq_mul,
    card_univ,mul_one,uniform,Fintype.card_eq_nat_card]

lemma base_slotLaw {T q : ℕ} (w : BagEdge bags → ℚ) (x : Slot T q) (hx : x∈base T q) :
    slotLaw (fun e=>(w e:ℝ)) x=uniform (BagPM bags) := by
  classical
  have he : slotWeight (fun e=>(w e:ℝ)) x=fun _ : BagEdge bags=>(1:ℝ) := by
    funext e
    have ht : tier x=0 := by simp only [tier,(mem_base x).mp hx,Nat.sub_self]
    simp only [slotWeight,tierClamp,ht,pow_zero,inv_one]
    exact max_eq_left (min_le_left _ _)
  unfold slotLaw
  rw [he]
  funext A
  simp only [gibbs,partition,matchingWeight,prod_const_one,sum_const,nsmul_eq_mul,
    card_univ,mul_one,uniform,Fintype.card_eq_nat_card]



open Finset Replica Replica.Ladder Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _

@[instance_reducible] def prodOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A×B) := LinearOrder.lift' toLex toLex.injective

@[instance_reducible] def sumOrder {A B : Type*} [LinearOrder A] [LinearOrder B] :
    LinearOrder (A⊕B) := LinearOrder.lift' toLex toLex.injective

attribute [local instance] prodOrder sumOrder

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p<rank l)

abbrev LocalBits (V : Type*) [Fintype V] (k : ℕ) :=
  (Fin k → Bool) × (Fin (Fintype.card V) → Fin k → Bool)

abbrev ScanBits (V : Type*) [Fintype V] (k : ℕ) := (Fin k → Bool) × LocalBits V k

def pairDraw {T q : ℕ} (w : BagEdge bags → ℚ) (k : ℕ) (x y : Slot T q)
    (a : BagPM bags × BagPM bags) (bits : LocalBits V k) : BagPM bags × BagPM bags :=
  sampleLadderPair hbags hG w x y a k bits.1

def baseDraw (M : BagPM bags) (k : ℕ) (bits : LocalBits V k) : BagPM bags :=
  UnitRefresh.sampleMatching k bags rank parent hb hne hp M bits.2

def ladderScan {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k : ℕ)
    (s : Slot T q → BagPM bags) (bits : ScanBits V k) : Slot T q → BagPM bags :=
  sampleScan guides (base T q) (base_nonempty T q hq) (pairDraw hbags hG w k)
    (fun _=>baseDraw rank parent hb hne hp M k) k s bits

def scanErrorNumerator (V L : Type*) [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L] (bags : V → Finset L)
    (T q : ℕ) : ℕ :=
  2*(1+(T*q^2+q))+
  4*(8*(Fintype.card (BagEdge bags))^2+4*Fintype.card (BagEdge bags)+3)+
  2*(Fintype.card V)^2*Fintype.card L

lemma ladderScan_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k : ℕ)
    (s : Slot T q → BagPM bags) :
    tv (imageLaw (ladderScan hbags hG rank parent hb hne hp hq w M k s))
      (FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s) ≤
      (scanErrorNumerator V L bags T q:ℝ)/(2:ℝ)^k := by
  classical
  let eP : ℝ := 4*(8*(Fintype.card (BagEdge bags):ℝ)^2+4*Fintype.card (BagEdge bags)+3)/(2:ℝ)^k
  let eU : ℝ := 2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k
  have hep : 0≤eP := by dsimp [eP]; positivity
  have heu : 0≤eU := by dsimp [eU]; positivity
  have hpr : ∀ x y : Slot T q,y∈guides x → ∀ a : BagPM bags × BagPM bags,
      tv (imageLaw (pairDraw hbags hG w k x y a))
        (fun b=>(treeLadderCapacity hbags hG (fun e=>(w e:ℝ)) x y).q a b /
          (slotLaw (fun e=>(w e:ℝ)) x a.1*slotLaw (fun e=>(w e:ℝ)) y a.2))≤eP+eU := by
    intro x y _ a
    unfold pairDraw
    rw [imageLaw_ignoreRight]
    exact (sampleLadderPair_tv hbags hG w x y a k).trans (le_add_of_nonneg_right heu)
  have hr : ∀ i : Slot T q,i∈base T q →
      tv (imageLaw (baseDraw rank parent hb hne hp M k)) (slotLaw (fun e=>(w e:ℝ)) i)≤eP+eU := by
    intro i hi
    rw [base_slotLaw w i hi]
    unfold baseDraw
    rw [imageLaw_ignore]
    exact (UnitRefresh.sampleMatching_tv k bags rank parent hb hne hp M).trans
      (le_add_of_nonneg_left hep)
  have ht:= sampleScan_tv_on (slotLaw (fun e=>(w e:ℝ))) (slotLaw_pos _)
    (fun x=>slotLaw_sum _ x M) guides (fun x y hy=>(guides_order x y hy).ne)
    (base T q) (base_nonempty T q hq) (treeLadderCapacity hbags hG (fun e=>(w e:ℝ)))
    (pairDraw hbags hG w k) (fun _=>baseDraw rank parent hb hne hp M k) (eP+eU)
    (add_nonneg hep heu) hpr hr k s
  change tv (imageLaw (ladderScan hbags hG rank parent hb hne hp hq w M k s))
    (FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s) ≤ _ at ht
  convert ht using 1
  have hcount : updateCount (@guides T q) (base T q)=T*q^2+q := updates_count T q
  rw [hcount]
  simp only [scanErrorNumerator,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_one,eP,eU,add_div]
  ring

def ladderRun {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) (bits : Fin n → ScanBits V k) : Slot T q → BagPM bags :=
  runSample (ladderScan hbags hG rank parent hb hne hp hq w M k) s n bits

lemma ladderKernel_nonneg {T q : ℕ} (w : BagEdge bags → ℚ) (s t : Slot T q → BagPM bags) :
    0≤FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s t := by
  apply div_nonneg
  · exact scanFlow_nonneg (slotLaw _) (fun i a=>(slotLaw_pos _ i a).le) _ _ _ s t
  · exact (Finset.prod_pos (fun i _=>slotLaw_pos _ i (s i))).le

lemma ladderKernel_sum {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags)
    (s : Slot T q → BagPM bags) :
    (∑ t,FiniteChain.kernel (ladderLaw (fun e=>(w e:ℝ)) T q)
      (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s t)=1 := by
  unfold FiniteChain.kernel
  rw [←sum_div]
  have hr:=scanFlow_row (slotLaw (fun e=>(w e:ℝ))) (fun i=>slotLaw_sum _ i M)
    guides (base T q) (base_nonempty T q hq) (treeLadderCapacity hbags hG (fun e=>(w e:ℝ))) s
  change (∑ t,ladderFlow hbags hG (fun e=>(w e:ℝ)) T q s t)=_ at hr
  rw [hr]
  exact div_self (Finset.prod_pos (fun i _=>slotLaw_pos _ i (s i))).ne'

lemma ladderRun_walk_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) :
    tv (imageLaw (ladderRun hbags hG rank parent hb hne hp hq w M k n s))
      (FiniteChain.walk (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s n) ≤
      n * (scanErrorNumerator V L bags T q:ℝ)/(2:ℝ)^k := by
  have ht:=runSample_walk_tv _ _ (ladderKernel_nonneg hbags hG w)
    (ladderKernel_sum hbags hG hq w M)
    (ladderScan hbags hG rank parent hb hne hp hq w M k) _
    (ladderScan_tv hbags hG rank parent hb hne hp hq w M k) s n
  change tv (imageLaw (ladderRun hbags hG rank parent hb hne hp hq w M k n s)) _ ≤ _ at ht
  simpa only [mul_div_assoc] using ht

lemma ladderRun_gibbs_tv (height : L → ℝ) (hheight : ∀ l,0<height l)
    (hstep : ∀ a b,G.Adj a b → height a≤2*height b)
    (D K : ℕ) (hD : 1≤D) (hN : 2≤Fintype.card V) (w : BagEdge bags → ℚ)
    (hw : ∀ e,height e.color / D ≤ (w e:ℝ) ∧ (w e:ℝ)≤3*height e.color)
    (hglobal : ∀ e,(D:ℝ)⁻¹≤(w e:ℝ) ∧ (w e:ℝ)≤3*4^K)
    (M : BagPM bags) (T k : ℕ) (ξ : ℝ) (hξ : 0<ξ) (hξ1 : ξ<1)
    (hq : 0<ladderQ (Fintype.card V) D)
    (s : Slot T (ladderQ (Fintype.card V) D) → BagPM bags) :
    tv (imageLaw (ladderRun hbags hG rank parent hb hne hp hq w M k
      (ladderSteps (Fintype.card V) D K T ξ) s))
      (ladderLaw (fun e=>(w e:ℝ)) T (ladderQ (Fintype.card V) D)) ≤
      (ladderSteps (Fintype.card V) D K T ξ : ℝ) *
        scanErrorNumerator V L bags T (ladderQ (Fintype.card V) D)/(2:ℝ)^k+ξ := by
  have hi:=ideal_ladder_sampling hbags hG height hheight hstep D K hD hN
    (fun e=>(w e:ℝ)) hw hglobal M T s ξ hξ hξ1
  have hb:=ladderRun_walk_tv hbags hG rank parent hb hne hp hq w M k
    (ladderSteps (Fintype.card V) D K T ξ) s
  exact (tv_triangle _ _ _).trans (add_le_add hb hi)



open Finset Replica Replica.Ladder Variation

def bitPrecision (R : ℕ) (η : ℚ) : ℕ := Nat.clog 2 (R*⌈η⁻¹⌉₊)

lemma bitPrecision_error (R : ℕ) (η : ℚ) (hη : 0<η) :
    (R:ℝ)/(2:ℝ)^bitPrecision R η ≤ (η:ℝ) := by
  have hp : (R:ℝ)*(⌈η⁻¹⌉₊:ℝ)≤(2:ℝ)^bitPrecision R η := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) (R*⌈η⁻¹⌉₊)
  have hh : (η:ℝ)⁻¹≤(⌈η⁻¹⌉₊:ℝ) := by
    exact_mod_cast Nat.le_ceil (η⁻¹)
  have he : (0:ℝ)<(η:ℝ) := by exact_mod_cast hη
  apply (div_le_iff₀ (by positivity : (0:ℝ)<2^bitPrecision R η)).mpr
  calc
    (R:ℝ) = (η:ℝ)*((R:ℝ)*(η:ℝ)⁻¹) := by field_simp
    _ ≤ (η:ℝ)*((R:ℝ)*(⌈η⁻¹⌉₊:ℝ)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hp he.le

def pairBitsEquiv (m n : ℕ) : (Fin (m+n) → Bool) ≃ ((Fin m → Bool) × (Fin n → Bool)) :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)

def matrixBitsEquiv (m n : ℕ) : (Fin (m*n) → Bool) ≃ (Fin m → Fin n → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

def scanBitCount (N k : ℕ) : ℕ := k+(k+N*k)

def scanBitsEquiv (V : Type*) [Fintype V] (k : ℕ) :
    (Fin (scanBitCount (Fintype.card V) k) → Bool) ≃ ScanBits V k :=
  (pairBitsEquiv k (k+Fintype.card V*k)).trans
    (Equiv.prodCongr (Equiv.refl _) ((pairBitsEquiv k (Fintype.card V*k)).trans
      (Equiv.prodCongr (Equiv.refl _) (matrixBitsEquiv (Fintype.card V) k))))

def runBitsEquiv (V : Type*) [Fintype V] (k n : ℕ) :
    (Fin (n*scanBitCount (Fintype.card V) k) → Bool) ≃ (Fin n → ScanBits V k) :=
  (matrixBitsEquiv n _).trans (Equiv.piCongrRight fun _=>scanBitsEquiv V k)

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

variable {bags : V → Finset L} {G : SimpleGraph L}

attribute [local instance] sym2Order bagEdgeOrder bagEdgeFintype UnitRefresh.Computable.allowedDec

noncomputable local instance : DecidableEq (BagPM bags) := Classical.decEq _

attribute [local instance] prodOrder sumOrder

variable (hbags : ∀ v,∀ a∈bags v,∀ b∈bags v,a=b ∨ G.Adj a b) (hG : G.IsAcyclic)

variable (rank : L → ℕ) (parent : L → Option L)

variable (hb : UnitRefresh.RankedBags bags rank parent) (hne : ∀ v,(bags v).Nonempty)

variable (hp : ∀ l p,parent l=some p → rank p<rank l)

def ladderBitRun {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags) (k n : ℕ)
    (s : Slot T q → BagPM bags) (bits : Fin (n*scanBitCount (Fintype.card V) k) → Bool) :
    Slot T q → BagPM bags :=
  ladderRun hbags hG rank parent hb hne hp hq w M k n s (runBitsEquiv V k n bits)

lemma ladderBitRun_walk_tv {T q : ℕ} (hq : 0<q) (w : BagEdge bags → ℚ) (M : BagPM bags)
    (n : ℕ) (η : ℚ) (hη : 0<η) (s : Slot T q → BagPM bags) :
    let k:=bitPrecision (n*scanErrorNumerator V L bags T q) η
    tv (imageLaw (ladderBitRun hbags hG rank parent hb hne hp hq w M k n s))
      (FiniteChain.walk (ladderLaw (fun e=>(w e:ℝ)) T q)
        (ladderFlow hbags hG (fun e=>(w e:ℝ)) T q) s n) ≤ (η:ℝ) := by
  dsimp only
  unfold ladderBitRun
  change tv (imageLaw (_ ∘ runBitsEquiv V _ n)) _ ≤ _
  rw [imageLaw_comp_equiv]
  exact (ladderRun_walk_tv hbags hG rank parent hb hne hp hq w M _ n s).trans
    (by simpa only [Nat.cast_mul] using bitPrecision_error (n*scanErrorNumerator V L bags T q) η hη)

end MatchingFPRAS.Transport

end OAI
