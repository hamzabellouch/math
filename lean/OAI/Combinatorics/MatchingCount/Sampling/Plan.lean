import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.RankOrder

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

def plan {m : ℕ} (rank : Fin m → ℕ) : List (Fin m) :=
  (List.ofFn (fun l : Fin m => l)).mergeSort (fun a b=>decide (rank b≤rank a))

lemma plan_mem {m : ℕ} (rank : Fin m → ℕ) (a : Fin m) : a∈plan rank := by
  unfold plan
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp

lemma plan_length {m : ℕ} (rank : Fin m → ℕ) : (plan rank).length=m := by
  unfold plan
  rw [(List.mergeSort_perm _ _).length_eq]
  simp

lemma plan_sorted {m : ℕ} (rank : Fin m → ℕ) :
    (plan rank).Pairwise (fun a b=>rank b≤rank a) := by
  let r := fun a b : Fin m => rank b≤rank a
  let : Std.Total r := ⟨fun a b => le_total (rank b) (rank a)⟩
  let : IsTrans (Fin m) r := ⟨fun a b c hab hbc => hbc.trans hab⟩
  exact List.pairwise_mergeSort' r _

lemma plan_legal {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l) :
    LegalPlan bags parent (plan rank) univ := by
  apply rank_order_legal bags rank parent hb hp _ (plan_sorted rank)
  · intro x _; exact hne x
  · intro x _ a _; exact plan_mem rank a

theorem computable_count_eq {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l) :
    count bags parent (plan rank)=Fintype.card (ColoredPairing bags) := by
  rw [coloredPairing_card]
  change count bags parent (plan rank)=assignmentPartition bags (fun _=>pairingCount)
  rw [←active_univ]
  rw [tableDP_correct bags parent _ _ (plan_legal bags rank parent hb hne hp)]
  unfold count
  apply prod_congr rfl
  intro a _
  rw [read_run]
  apply finiteDP_correct
  intro b r hr
  rw [plan_length] at hr
  simp [initial,read_tabulate,hr]

def branchCount {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a b : V) : ℕ :=
  count (residualBags bags a b) parent (plan rank)

lemma branchCount_eq {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a b : V) : branchCount bags rank parent a b=
      Fintype.card (ColoredPairing (residualBags bags a b)) := by
  apply computable_count_eq
  · intro x c hc d hd; exact hb x.val c hc d hd
  · intro x; exact hne x.val
  · exact hp

lemma branchCount_sum {m : ℕ} (bags : V → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : V) : (∑ c : Partner bags a,branchCount bags rank parent a c.val.1)=
      count bags parent (plan rank) := by
  rw [computable_count_eq bags rank parent hb hne hp,
    Fintype.card_congr (ColoredPairing.split a),Fintype.card_sigma]
  apply sum_congr rfl
  intro c _
  exact branchCount_eq bags rank parent hb hne hp a c.val.1



open Finset MatchingFPRAS.FiniteChoice

variable {n m : ℕ}

def validBranch (bags : Fin n → Finset (Fin m)) (a : Fin n) (bc : Fin n × Fin m) : Prop :=
  bc.1≠a ∧ bc.2∈bags a ∧ bc.2∈bags bc.1

instance (bags : Fin n → Finset (Fin m)) (a : Fin n) (bc : Fin n × Fin m) :
    Decidable (validBranch bags a bc) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def edgeCount (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (bc : Fin n × Fin m) : ℕ :=
  if validBranch bags a bc then branchCount bags rank parent a bc.1 else 0

lemma edgeCount_sum (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) : (∑ bc,edgeCount bags rank parent a bc)=count bags parent (plan rank) := by
  rw [←branchCount_sum bags rank parent hb hne hp a]
  change (∑ bc,if validBranch bags a bc then branchCount bags rank parent a bc.1 else 0)=_
  rw [←Finset.sum_filter]
  exact Finset.sum_subtype _ (by intro bc; simp only [Finset.mem_filter,Finset.mem_univ,true_and]; rfl) _

def edgeProbability (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (i : Fin (n*m)) : ℚ :=
  edgeCount bags rank parent a (finProdFinEquiv.symm i)/count bags parent (plan rank)

lemma edgeProbability_nonneg (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) (i : Fin (n*m)) :
    0≤edgeProbability bags rank parent a i := by unfold edgeProbability; positivity

lemma edgeProbability_sum (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) :
    ∑ i,edgeProbability bags rank parent a i=1 := by
  unfold edgeProbability
  rw [←Finset.sum_div,←Nat.cast_sum]
  rw [←finProdFinEquiv.sum_comp (fun i=>edgeCount bags rank parent a (finProdFinEquiv.symm i))]
  simp only [Equiv.symm_apply_apply]
  rw [edgeCount_sum bags rank parent hb hne hp a]
  exact div_self (by exact_mod_cast hz.ne')

def drawEdge (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (k : ℕ) (bits : Fin k → Bool) :
    {c : Partner bags a // 0<branchCount bags rank parent a c.val.1} := by
  let p := edgeProbability bags rank parent a
  have hs := edgeProbability_sum bags rank parent hb hne hp a hz
  let i := chooseBits p hs k bits
  let bc := finProdFinEquiv.symm i
  have hh : 0<edgeCount bags rank parent a bc := by
    have h := chooseBits_pos p hs k bits
    change 0<(edgeCount bags rank parent a bc:ℚ)/(count bags parent (plan rank):ℚ) at h
    have := (div_pos_iff_of_pos_right (by exact_mod_cast hz : (0:ℚ)<count bags parent (plan rank))).mp h
    exact_mod_cast this
  have hv : validBranch bags a bc := by
    by_contra hv
    simp [edgeCount,hv] at hh
  exact ⟨⟨bc,hv⟩,by simpa [edgeCount,hv] using hh⟩

theorem drawEdge_tv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (k : ℕ) :
    let p := edgeProbability bags rank parent a
    let hs := edgeProbability_sum bags rank parent hb hne hp a hz
    (∑ i,|tapeLaw p hs k i-p i|)/2≤2*(n*m)/(2:ℚ)^k := by
  dsimp only
  rw [tapeLaw_eq]
  simpa only [Nat.cast_mul] using fixed_bit_choice _ (edgeProbability_nonneg bags rank parent a) _ k

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh

open Finset

variable {U V L : Type*} [Fintype U] [Fintype V] [Fintype L] [DecidableEq U] [DecidableEq V] [DecidableEq L]

def ColoredPairing.map (bags : V → Finset L) (e : U ≃ V)
    (p : ColoredPairing (fun x=>bags (e x))) : ColoredPairing bags where
  pair := p.pair.map e
  color x := p.color (e.symm x)
  allowed x := by simpa using p.allowed (e.symm x)
  same_color x := by simpa [Pairing.map] using p.same_color (e.symm x)

def ColoredPairing.comap (bags : V → Finset L) (e : U ≃ V)
    (p : ColoredPairing bags) : ColoredPairing (fun x=>bags (e x)) where
  pair := p.pair.map e.symm
  color x := p.color (e x)
  allowed x := p.allowed (e x)
  same_color x := by simpa [Pairing.map] using p.same_color (e x)

def ColoredPairing.equiv (bags : V → Finset L) (e : U ≃ V) :
    ColoredPairing (fun x=>bags (e x)) ≃ ColoredPairing bags where
  toFun := ColoredPairing.map bags e
  invFun := ColoredPairing.comap bags e
  left_inv p := by
    apply ColoredPairing.ext
    · ext x; simp [ColoredPairing.map,ColoredPairing.comap,Pairing.map]
    · funext x; simp [ColoredPairing.map,ColoredPairing.comap]
  right_inv p := by
    apply ColoredPairing.ext
    · ext x; simp [ColoredPairing.map,ColoredPairing.comap,Pairing.map]
    · funext x; simp [ColoredPairing.map,ColoredPairing.comap]

def gapEquiv {n : ℕ} (a : Fin (n+1)) : Fin n ≃ {x : Fin (n+1) // x≠a} :=
  Equiv.optionSubtype a ⟨(finSuccEquiv' a).symm,rfl⟩

def removePairEquiv {n : ℕ} (a b : Fin (n+2)) (hb : b≠a) :
    Fin n ≃ withoutPair a b := by
  let e := gapEquiv a
  let b' := e.symm ⟨b,hb⟩
  let f := gapEquiv b'
  refine {
    toFun := fun i=>⟨(e (f i).val).val,(e (f i).val).property,?_⟩
    invFun := fun x=>f.symm ⟨e.symm ⟨x.val,x.property.1⟩,?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro h
    apply (f i).property
    apply e.injective
    apply Subtype.ext
    simpa [b'] using h
  · intro h
    have hh := congrArg (fun i=>(e i).val) h
    apply x.property.2
    simpa [b'] using hh
  · intro i
    apply f.injective
    simp
  · intro x
    apply Subtype.ext
    simp

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice

variable {m : ℕ}

lemma singleton_count_zero (bags : Fin 1 → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l) :
    count bags parent (plan rank)=0 := by
  rw [computable_count_eq bags rank parent hb hne hp]
  have : IsEmpty (ColoredPairing bags) := ⟨fun p=>p.pair.no_fixed 0 (Subsingleton.elim _ _)⟩
  exact Fintype.card_eq_zero

def sampleUnit (k : ℕ) : (n : ℕ) → (bags : Fin n → Finset (Fin m)) →
    (rank : Fin m → ℕ) → (parent : Fin m → Option (Fin m)) →
    (hb : RankedBags bags rank parent) → (hne : ∀ x,(bags x).Nonempty) →
    (hp : ∀ l p,parent l=some p → rank p<rank l) →
    0<count bags parent (plan rank) → (Fin n → Fin k → Bool) → ColoredPairing bags
  | 0,bags,_,_,_,_,_,_,_ =>
    ⟨⟨fun x=>Fin.elim0 x,fun x=>Fin.elim0 x,fun x=>Fin.elim0 x⟩,
      (fun x=>Fin.elim0 x),(fun x=>Fin.elim0 x),(fun x=>Fin.elim0 x)⟩
  | 1,bags,rank,parent,hb,hne,hp,hz,_ =>
    False.elim (by rw [singleton_count_zero bags rank parent hb hne hp] at hz; omega)
  | n+2,bags,rank,parent,hb,hne,hp,hz,bits => by
    let a : Fin (n+2) := Fin.last (n+1)
    let c := drawEdge bags rank parent hb hne hp a hz k (bits a)
    let e := removePairEquiv a c.val.val.1 c.val.property.1
    let b' : Fin n → Finset (Fin m) := fun x=>bags (e x).val
    have hb' : RankedBags b' rank parent := by
      intro x l hl r hr; exact hb (e x).val l hl r hr
    have hne' : ∀ x,(b' x).Nonempty := fun x=>hne (e x).val
    have hz' : 0<count b' parent (plan rank) := by
      rw [computable_count_eq b' rank parent hb' hne' hp]
      rw [Fintype.card_congr (ColoredPairing.equiv (residualBags bags a c.val.val.1) e)]
      rw [←branchCount_eq bags rank parent hb hne hp]
      exact c.property
    let p := sampleUnit k n b' rank parent hb' hne' hp hz'
      (fun i=>bits i.castSucc.castSucc)
    exact (ColoredPairing.map (residualBags bags a c.val.val.1) e p).insert a c.val



open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

abbrev PositivePartner (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) :=
  {c : Partner bags a // 0<branchCount bags rank parent a c.val.1}

def partnerIndex (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n)
    (c : PositivePartner bags rank parent a) : Fin (n*m) := finProdFinEquiv c.val.val

lemma partnerIndex_injective (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (a : Fin n) :
    Function.Injective (partnerIndex bags rank parent a) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  exact finProdFinEquiv.injective h

lemma drawEdge_index (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (k : ℕ) (bits : Fin k → Bool) :
    partnerIndex bags rank parent a (drawEdge bags rank parent hb hne hp a hz k bits)=
      chooseBits (edgeProbability bags rank parent a) (edgeProbability_sum bags rank parent hb hne hp a hz) k bits := by
  exact finProdFinEquiv.apply_symm_apply _

lemma drawEdge_law (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (k : ℕ)
    (c : PositivePartner bags rank parent a) :
    imageLaw (drawEdge bags rank parent hb hne hp a hz k) c=
      (tapeLaw (edgeProbability bags rank parent a) (edgeProbability_sum bags rank parent hb hne hp a hz) k
        (partnerIndex bags rank parent a c):ℝ) := by
  rw [imageLaw_eq_count]
  simp only [tapeLaw,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,Rat.cast_ofNat,
    Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Nat.cast_pow,Nat.cast_ofNat]
  congr 2
  apply congrArg Finset.card
  ext bits
  simp only [mem_filter,mem_univ,true_and]
  rw [←drawEdge_index]
  exact (partnerIndex_injective bags rank parent a).eq_iff.symm

theorem drawEdge_positive_tv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (k : ℕ) :
    tv (imageLaw (drawEdge bags rank parent hb hne hp a hz k))
      (fun c : PositivePartner bags rank parent a=>(branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank))
      ≤ 2*n*m/(2:ℝ)^k := by
  let idx := partnerIndex bags rank parent a
  let p := edgeProbability bags rank parent a
  let hs := edgeProbability_sum bags rank parent hb hne hp a hz
  have he (c : PositivePartner bags rank parent a) :
      (p (idx c):ℝ)=(branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank) := by
    have hv : validBranch bags a c.val.val := c.val.property
    simp [p,idx,partnerIndex,edgeProbability,edgeCount,hv]
  have hg : ∑ c : PositivePartner bags rank parent a,|(tapeLaw p hs k (idx c):ℝ)-(p (idx c):ℝ)| ≤
      ∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)| := by
    change (∑ c,|(tapeLaw p hs k (partnerIndex bags rank parent a c):ℝ)-(p (partnerIndex bags rank parent a c):ℝ)|)≤_
    rw [←Finset.sum_image (s:=univ) (f:=fun i=>|(tapeLaw p hs k i:ℝ)-(p i:ℝ)|)
      (fun c _ d _ h=>(partnerIndex_injective bags rank parent a) h)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun _=>abs_nonneg _)
  have ht : (∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)|)/2 ≤ 2*(n*m)/(2:ℝ)^k := by
    have hh := drawEdge_tv bags rank parent hb hne hp a hz k
    have hcast := (Rat.cast_le (K:=ℝ)).mpr hh
    push_cast at hcast
    simpa only [p,hs,Nat.cast_mul] using hcast
  unfold tv
  have hg' : (∑ c : PositivePartner bags rank parent a,
      |imageLaw (drawEdge bags rank parent hb hne hp a hz k) c-
        (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank)|)≤
      ∑ i : Fin (n*m),|(tapeLaw p hs k i:ℝ)-(p i:ℝ)| := by
    simpa only [drawEdge_law,he] using hg
  exact (div_le_div_of_nonneg_right hg' (by norm_num)).trans (by simpa only [mul_assoc] using ht)

noncomputable def positiveSplitEquiv (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) :
    (Σ c : PositivePartner bags rank parent a,ColoredPairing (residualBags bags a c.val.val.1)) ≃ ColoredPairing bags := by
  let e : (Σ c : PositivePartner bags rank parent a,ColoredPairing (residualBags bags a c.val.val.1)) ≃
      (Σ c : Partner bags a,ColoredPairing (residualBags bags a c.val.1)) := {
    toFun := fun s=>⟨s.1.val,s.2⟩
    invFun := fun s=>⟨⟨s.1,by
      rw [branchCount_eq bags rank parent hb hne hp]
      exact Fintype.card_pos_iff.mpr ⟨s.2⟩⟩,s.2⟩
    left_inv := fun s=>by rcases s with ⟨⟨c,hc⟩,x⟩; rfl
    right_inv := fun s=>by cases s; rfl }
  exact e.trans (ColoredPairing.split a).symm

lemma positiveSplitEquiv_apply (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (c : PositivePartner bags rank parent a)
    (x : ColoredPairing (residualBags bags a c.val.val.1)) :
    positiveSplitEquiv bags rank parent hb hne hp a ⟨c,x⟩=x.insert a c.val := rfl

theorem unit_self_reduction_law (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin n) (hz : 0<count bags parent (plan rank)) (z : ColoredPairing bags) :
    push (sigmaLift
      (fun c : PositivePartner bags rank parent a=>(branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank))
      (fun c=>uniform (ColoredPairing (residualBags bags a c.val.val.1))))
      (positiveSplitEquiv bags rank parent hb hne hp a) z=uniform (ColoredPairing bags) z := by
  let : Nonempty (ColoredPairing bags) := Fintype.card_pos_iff.mp (by
    rwa [←computable_count_eq bags rank parent hb hne hp])
  simp_rw [branchCount_eq bags rank parent hb hne hp,computable_count_eq bags rank parent hb hne hp]
  exact uniform_sigma (positiveSplitEquiv bags rank parent hb hne hp a) z

end MatchingFPRAS.UnitRefresh.Materialized

end OAI
