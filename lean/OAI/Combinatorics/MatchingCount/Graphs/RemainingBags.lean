import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.Plan

namespace OAI

namespace MatchingFPRAS.UnitRefresh.Materialized

open Finset MatchingFPRAS.FiniteChoice MatchingFPRAS.Variation
open scoped Classical

variable {n m : ℕ}

def remainingBags (bags : Fin (n+2) → Finset (Fin m)) (a : Fin (n+2))
    (c : Partner bags a) : Fin n → Finset (Fin m) :=
  fun x=>bags (removePairEquiv a c.val.1 c.property.1 x).val

lemma remainingRanked (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (a : Fin (n+2)) (c : Partner bags a) : RankedBags (remainingBags bags a c) rank parent := by
  intro x l hl r hr
  exact hb _ l hl r hr

lemma remainingNonempty (bags : Fin (n+2) → Finset (Fin m))
    (hne : ∀ x,(bags x).Nonempty) (a : Fin (n+2)) (c : Partner bags a) :
    ∀ x,(remainingBags bags a c x).Nonempty := fun _=>hne _

lemma remainingCard (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (c : Partner bags a) :
    Fintype.card (ColoredPairing (remainingBags bags a c))=branchCount bags rank parent a c.val.1 := by
  have h := Fintype.card_congr (ColoredPairing.equiv (residualBags bags a c.val.1)
    (removePairEquiv a c.val.1 c.property.1))
  exact h.trans (branchCount_eq bags rank parent hb hne hp _ _).symm

lemma remainingPositive (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) :
    0<count (remainingBags bags a c.val) parent (plan rank) := by
  rw [computable_count_eq _ rank parent (remainingRanked bags rank parent hb a c.val)
    (remainingNonempty bags hne a c.val) hp, remainingCard bags rank parent hb hne hp]
  exact c.property

def assembleEdge (bags : Fin (n+2) → Finset (Fin m)) (a : Fin (n+2)) (c : Partner bags a)
    (p : ColoredPairing (remainingBags bags a c)) : ColoredPairing bags :=
  (ColoredPairing.map (residualBags bags a c.val.1) (removePairEquiv a c.val.1 c.property.1) p).insert a c

def residualSampler (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) (bits : Fin n → Fin k → Bool) : ColoredPairing bags :=
  assembleEdge bags a c.val (sampleUnit k n (remainingBags bags a c.val) rank parent
    (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val) hp
    (remainingPositive bags rank parent hb hne hp a c) bits)

lemma sampleUnit_step (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<count bags parent (plan rank)) (bits : Fin (n+2) → Fin k → Bool) :
    sampleUnit k (n+2) bags rank parent hb hne hp hz bits=
      residualSampler k bags rank parent hb hne hp (Fin.last (n+1))
        (drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k (bits (Fin.last (n+1))))
        (fun i=>bits i.castSucc.castSucc) := rfl

noncomputable def renumberedSplitEquiv (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) :
    (Σ c : PositivePartner bags rank parent a,ColoredPairing (remainingBags bags a c.val)) ≃ ColoredPairing bags :=
  (Equiv.sigmaCongrRight (fun c : PositivePartner bags rank parent a=>
    ColoredPairing.equiv (residualBags bags a c.val.val.1)
      (removePairEquiv a c.val.val.1 c.val.property.1))).trans
    (positiveSplitEquiv bags rank parent hb hne hp a)

lemma renumberedSplitEquiv_apply (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (s : Σ c : PositivePartner bags rank parent a,ColoredPairing (remainingBags bags a c.val)) :
    renumberedSplitEquiv bags rank parent hb hne hp a s=assembleEdge bags a s.1.val s.2 := rfl

lemma sampleUnit_step_law (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<count bags parent (plan rank)) :
    imageLaw (sampleUnit k (n+2) bags rank parent hb hne hp hz)=
      bind (imageLaw (drawEdge bags rank parent hb hne hp (Fin.last (n+1)) hz k))
        (fun c=>imageLaw (residualSampler k bags rank parent hb hne hp (Fin.last (n+1)) c)) := by
  exact imageLaw_fin_skip n _ _ _ (sampleUnit_step k bags rank parent hb hne hp hz)

lemma exact_unit_step (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (hz : 0<count bags parent (plan rank)) :
    bind (fun c : PositivePartner bags rank parent a=>
      (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank))
      (fun c : PositivePartner bags rank parent a=>
        push (uniform (ColoredPairing (remainingBags bags a c.val))) (assembleEdge bags a c.val))=
      uniform (ColoredPairing bags) := by
  let : Nonempty (ColoredPairing bags) := Fintype.card_pos_iff.mp (by
    rwa [←computable_count_eq bags rank parent hb hne hp])
  have h := funext (uniform_sigma (renumberedSplitEquiv bags rank parent hb hne hp a))
  rw [push_sigmaLift] at h
  simpa only [remainingCard bags rank parent hb hne hp,←computable_count_eq bags rank parent hb hne hp,
    renumberedSplitEquiv_apply] using h

open Finset MatchingFPRAS.Variation
open scoped Classical

variable {m n : ℕ}

lemma residualSampler_law (k : ℕ) (bags : Fin (n+2) → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (a : Fin (n+2)) (c : PositivePartner bags rank parent a) :
    imageLaw (residualSampler k bags rank parent hb hne hp a c)=
      push (imageLaw (sampleUnit k n (remainingBags bags a c.val) rank parent
        (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val) hp
        (remainingPositive bags rank parent hb hne hp a c))) (assembleEdge bags a c.val) := by
  exact imageLaw_comp _ _

theorem sampleUnit_tv (k n : ℕ) (bags : Fin n → Finset (Fin m)) (rank : Fin m → ℕ)
    (parent : Fin m → Option (Fin m)) (hb : RankedBags bags rank parent)
    (hne : ∀ x,(bags x).Nonempty) (hp : ∀ l p,parent l=some p → rank p<rank l)
    (hz : 0<count bags parent (plan rank)) :
    tv (imageLaw (sampleUnit k n bags rank parent hb hne hp hz))
      (uniform (ColoredPairing bags)) ≤ 2*(n:ℝ)^2*m/(2:ℝ)^k := by
  induction n using Nat.twoStepInduction with
  | zero =>
    let : Subsingleton (ColoredPairing bags) := ⟨fun p q=>ColoredPairing.ext
      (Pairing.ext (fun x=>Fin.elim0 x)) (funext (fun x=>Fin.elim0 x))⟩
    rw [imageLaw_subsingleton,tv_self]
    simp
  | one =>
    rw [singleton_count_zero bags rank parent hb hne hp] at hz
    omega
  | more n ih _ =>
    let a : Fin (n+2) := Fin.last (n+1)
    let p := imageLaw (drawEdge bags rank parent hb hne hp a hz k)
    let q : PositivePartner bags rank parent a → ℝ := fun c=>
      (branchCount bags rank parent a c.val.val.1:ℝ)/count bags parent (plan rank)
    let u : PositivePartner bags rank parent a → ColoredPairing bags → ℝ := fun c=>
      imageLaw (residualSampler k bags rank parent hb hne hp a c)
    let v : PositivePartner bags rank parent a → ColoredPairing bags → ℝ := fun c=>
      push (uniform (ColoredPairing (remainingBags bags a c.val))) (assembleEdge bags a c.val)
    have hvn (c : PositivePartner bags rank parent a) (y : ColoredPairing bags) : 0 ≤ v c y :=
      push_nonneg _ uniform_nonneg _ _
    have hvs (c : PositivePartner bags rank parent a) : ∑ y,v c y=1 := by
      let : Nonempty (ColoredPairing (remainingBags bags a c.val)) :=
        Fintype.card_pos_iff.mp (by rw [remainingCard bags rank parent hb hne hp]; exact c.property)
      exact push_sum _ uniform_sum _
    have huv (c : PositivePartner bags rank parent a) : tv (u c) (v c) ≤ 2*(n:ℝ)^2*m/(2:ℝ)^k := by
      dsimp only [u,v]
      rw [residualSampler_law]
      exact (push_contraction _ _ _).trans (ih (remainingBags bags a c.val)
        (remainingRanked bags rank parent hb a c.val) (remainingNonempty bags hne a c.val)
        (remainingPositive bags rank parent hb hne hp a c))
    have hpv := bind_perturbation p u v (imageLaw_nonneg _) (imageLaw_sum _)
      (2*(n:ℝ)^2*m/(2:ℝ)^k) huv
    have hpq := bind_contraction p q v hvn hvs
    have hd := drawEdge_positive_tv bags rank parent hb hne hp a hz k
    rw [sampleUnit_step_law,←exact_unit_step bags rank parent hb hne hp a hz]
    change tv (bind p u) (bind q v)≤_
    calc
      _ ≤ tv (bind p u) (bind p v)+tv (bind p v) (bind q v) := tv_triangle _ _ _
      _ ≤ (2*(n:ℝ)^2*m/(2:ℝ)^k)+(2*((n:ℝ)+2)*m/(2:ℝ)^k) := by
        apply add_le_add hpv
        exact hpq.trans (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hd)
      _ ≤ _ := by
        rw [←add_div]
        push_cast
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith [show (0:ℝ)≤n*m by positivity]

end MatchingFPRAS.UnitRefresh.Materialized

namespace MatchingFPRAS.UnitRefresh.Computable

open Finset MatchingFPRAS.Transport

variable {V L : Type*} [Fintype V] [Fintype L] [DecidableEq V] [DecidableEq L]

variable {bags : V → Finset L}

instance edgeDec (e : BagEdge bags) (x : V) : Decidable (e.Incident x) :=
  inferInstanceAs (Decidable (x∈e.val.val.1))

instance allowedDec (e : ColoredEdge V L) : Decidable (Allowed bags e) :=
  inferInstanceAs (Decidable (∀ x,x∈e.val.1 → e.val.2∈bags x))

def edge (M : PM (BagEdge.Incident (bags := bags))) (x : V) : BagEdge bags :=
  M.val.choose (fun e=>e.Incident x) (M.property.2 x (mem_univ x))

omit [Fintype L] [DecidableEq L] in
lemma edge_spec [DecidableEq L] (M : PM (BagEdge.Incident (bags := bags))) (x : V) :
    edge M x∈M.val ∧ (edge M x).Incident x :=
  M.val.choose_spec _ (M.property.2 x (mem_univ x))

lemma edge_eq (M : PM (BagEdge.Incident (bags := bags))) (x : V) : edge M x=chosenEdge M x :=
  chosenEdge_unique M x _ (edge_spec M x).1 (edge_spec M x).2

def mate (M : PM (BagEdge.Incident (bags := bags))) (x : V) : V :=
  Sym2.Mem.other' (edge_spec M x).2

lemma mate_eq (M : PM (BagEdge.Incident (bags := bags))) (x : V) : mate M x=chosenMate M x := by
  have hp : s(x,mate M x)=(edge M x).val.val.1 := Sym2.other_spec' (edge_spec M x).2
  apply (Sym2.congr_right (a:=x)).mp
  exact hp.trans (by rw [edge_eq,←chosenMate_pair])

def fromMatching (M : PM (BagEdge.Incident (bags := bags))) : ColoredPairing bags where
  pair := ⟨mate M,(fun x=>by simpa only [mate_eq] using chosenMate_involutive M x),
    fun x=>by simpa only [mate_eq] using chosenMate_ne M x⟩
  color x := (edge M x).val.color
  allowed x := (edge M x).property x (edge_spec M x).2
  same_color x := by
    simp only [mate_eq,edge_eq]
    exact congrArg (fun e : BagEdge bags=>e.val.color) (chosenEdge_chosenMate M x)

lemma from_eq (M : PM (BagEdge.Incident (bags := bags))) : fromMatching M=fromPM M := by
  apply ColoredPairing.ext
  · apply Pairing.ext; intro x; exact mate_eq M x
  · funext x; exact congrArg (fun e : BagEdge bags=>e.val.color) (edge_eq M x)

def toMatching (p : ColoredPairing bags) : PM (BagEdge.Incident (bags := bags)) :=
  ⟨Finset.univ.image p.edgeAt,by exact p.toPM.property⟩

omit [Fintype L] in
lemma to_eq [Fintype L] (p : ColoredPairing bags) : toMatching p=p.toPM := rfl

def pairingEquiv : PM (BagEdge.Incident (bags := bags)) ≃ ColoredPairing bags where
  toFun := fromMatching
  invFun := toMatching
  left_inv M := by
    rw [from_eq,to_eq]
    exact (coloredPMEquiv (bags:=bags)).left_inv M
  right_inv p := by
    rw [to_eq,from_eq]
    exact (coloredPMEquiv (bags:=bags)).right_inv p

end MatchingFPRAS.UnitRefresh.Computable

namespace MatchingFPRAS.UnitRefresh

open Finset MatchingFPRAS.Variation

def orderedEnum (α : Type*) [Fintype α] [LinearOrder α] : Fin (Fintype.card α) ≃ α :=
  ((univ : Finset α).orderIsoOfFin (card_univ)).toEquiv.trans
    (Equiv.subtypeUnivEquiv (fun _=>mem_univ _))

variable {V L J : Type*} [Fintype V] [DecidableEq V] [Fintype L] [Fintype J] [DecidableEq L] [DecidableEq J]

def ColoredPairing.colorEquiv (bags : V → Finset L) (e : L ≃ J) :
    ColoredPairing bags ≃ ColoredPairing (fun x=>(bags x).map e.toEmbedding) where
  toFun p := {
    pair:=p.pair
    color:=fun x=>e (p.color x)
    allowed:=fun x=>by simpa using p.allowed x
    same_color:=fun x=>congrArg e (p.same_color x) }
  invFun p := {
    pair:=p.pair
    color:=fun x=>e.symm (p.color x)
    allowed:=fun x=>by
      obtain ⟨l,hl,he⟩:=mem_map.mp (p.allowed x)
      simpa only [←he,Equiv.toEmbedding_apply,Equiv.symm_apply_apply] using hl
    same_color:=fun x=>congrArg e.symm (p.same_color x) }
  left_inv p := by
    apply ColoredPairing.ext
    · rfl
    · funext x; exact e.symm_apply_apply _
  right_inv p := by
    apply ColoredPairing.ext
    · rfl
    · funext x; exact e.apply_symm_apply _

open Finset MatchingFPRAS.Variation

variable {V L : Type*} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]

def numberedBags (bags : V → Finset L) : Fin (Fintype.card V) → Finset (Fin (Fintype.card L)) :=
  fun x=>(bags (orderedEnum V x)).map (orderedEnum L).symm.toEmbedding

lemma mem_numberedBags (bags : V → Finset L) (x : Fin (Fintype.card V)) (l : Fin (Fintype.card L)) :
    l∈numberedBags bags x ↔ orderedEnum L l∈bags (orderedEnum V x) := by
  simp [numberedBags]

def numberedRank (rank : L → ℕ) : Fin (Fintype.card L) → ℕ := fun l=>rank (orderedEnum L l)

def numberedParent (parent : L → Option L) : Fin (Fintype.card L) → Option (Fin (Fintype.card L)) :=
  fun l=>(parent (orderedEnum L l)).map (orderedEnum L).symm

lemma numberedParent_iff (parent : L → Option L) (l p : Fin (Fintype.card L)) :
    numberedParent parent l=some p ↔ parent (orderedEnum L l)=some (orderedEnum L p) := by
  simp [numberedParent,Equiv.symm_apply_eq]

lemma numberedRanked (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) :
    RankedBags (numberedBags bags) (numberedRank rank) (numberedParent parent) := by
  intro x a ha b hb' hab
  rcases hb (orderedEnum V x) (orderedEnum L a) ((mem_numberedBags bags x a).mp ha)
    (orderedEnum L b) ((mem_numberedBags bags x b).mp hb')
    (fun h=>hab ((orderedEnum L).injective h)) with ⟨hlt,hp⟩|⟨hlt,hp⟩
  · exact Or.inl ⟨hlt,(numberedParent_iff parent b a).mpr hp⟩
  · exact Or.inr ⟨hlt,(numberedParent_iff parent a b).mpr hp⟩

lemma numberedNonempty (bags : V → Finset L) (hne : ∀ x,(bags x).Nonempty) :
    ∀ x,(numberedBags bags x).Nonempty := fun x=>(hne (orderedEnum V x)).map

lemma numberedDecreasing (rank : L → ℕ) (parent : L → Option L)
    (hp : ∀ l p,parent l=some p → rank p<rank l) :
    ∀ l p,numberedParent parent l=some p → numberedRank rank p<numberedRank rank l := by
  intro l p h; exact hp _ _ ((numberedParent_iff parent l p).mp h)

def numberingEquiv (bags : V → Finset L) :
    ColoredPairing (numberedBags bags) ≃ ColoredPairing bags :=
  (ColoredPairing.colorEquiv (fun x=>bags (orderedEnum V x)) (orderedEnum L).symm).symm.trans
    (ColoredPairing.equiv bags (orderedEnum V))

lemma numbered_count_pos (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (M : ColoredPairing bags) :
    0<Materialized.count (numberedBags bags) (numberedParent parent)
      (Materialized.plan (numberedRank rank)) := by
  rw [Materialized.computable_count_eq _ _ _ (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)]
  exact Fintype.card_pos_iff.mpr ⟨(numberingEquiv bags).symm M⟩

def sampleNumbered (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (M : ColoredPairing bags)
    (bits : Fin (Fintype.card V) → Fin k → Bool) : ColoredPairing bags :=
  numberingEquiv bags (Materialized.sampleUnit k (Fintype.card V) (numberedBags bags)
    (numberedRank rank) (numberedParent parent) (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp M) bits)

theorem sampleNumbered_tv (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l) (M : ColoredPairing bags) :
    tv (imageLaw (sampleNumbered k bags rank parent hb hne hp M))
      (uniform (ColoredPairing bags)) ≤ 2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k := by
  have ht:=Materialized.sampleUnit_tv k (Fintype.card V) (numberedBags bags)
    (numberedRank rank) (numberedParent parent) (numberedRanked bags rank parent hb)
    (numberedNonempty bags hne) (numberedDecreasing rank parent hp)
    (numbered_count_pos bags rank parent hb hne hp M)
  change tv (imageLaw (numberingEquiv bags ∘ _)) _ ≤ _
  rw [imageLaw_comp,←imageLaw_equiv (numberingEquiv bags)]
  exact (push_contraction _ _ _).trans ht

open MatchingFPRAS.Transport

def sampleMatching (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (M : PM (BagEdge.Incident (bags:=bags)))
    (bits : Fin (Fintype.card V) → Fin k → Bool) : PM (BagEdge.Incident (bags:=bags)) :=
  (Computable.pairingEquiv (bags:=bags)).symm
    (sampleNumbered k bags rank parent hb hne hp (Computable.pairingEquiv M) bits)

theorem sampleMatching_tv (k : ℕ) (bags : V → Finset L) (rank : L → ℕ) (parent : L → Option L)
    (hb : RankedBags bags rank parent) (hne : ∀ x,(bags x).Nonempty)
    (hp : ∀ l p,parent l=some p → rank p<rank l)
    (M : PM (BagEdge.Incident (bags:=bags))) :
    tv (imageLaw (sampleMatching k bags rank parent hb hne hp M))
      (uniform (PM (BagEdge.Incident (bags:=bags)))) ≤
      2*(Fintype.card V:ℝ)^2*Fintype.card L/(2:ℝ)^k := by
  have ht:=sampleNumbered_tv k bags rank parent hb hne hp (Computable.pairingEquiv M)
  change tv (imageLaw ((Computable.pairingEquiv (bags:=bags)).symm ∘ _)) _ ≤ _
  rw [imageLaw_comp,←imageLaw_equiv (Computable.pairingEquiv (bags:=bags)).symm]
  exact (push_contraction _ _ _).trans ht

end MatchingFPRAS.UnitRefresh

end OAI
