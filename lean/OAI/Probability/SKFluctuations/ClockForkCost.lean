import Mathlib
import OAI.Probability.SKFluctuations.ClockRootMarginal

namespace OAI

/-! Clock Fork Cost. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 
def forkCost : {as : List PositiveMass} → ClockTree S as → (ℕ → ℝ) → ℝ
  | _, .leaf, _ => 0
  | _, .step _ T, f => T.forkCost (fun j => f (1+j))
  | _, .fork T U, f => f 0 + T.forkCost f + U.forkCost f

 

def edgeBudget (a : ℝ) : List PositiveMass → (ℕ → ℝ) → ℝ
  | [], f => (1-a)*f 0
  | b::as, f => (b.val-a)*f 0 + edgeBudget b.val as (fun j => f (1+j))

theorem forkCost_nonneg {as : List PositiveMass} (T : ClockTree S as)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) : 0 ≤ T.forkCost f := by
  induction T generalizing f with
  | leaf => exact le_refl _
  | step a T ih => exact ih (fun j => hf (1+j))
  | fork T U ihT ihU => exact add_nonneg (add_nonneg (hf 0) (ihT hf)) (ihU hf)

theorem edgeBudget_nonneg {as : List PositiveMass} {a : ℝ} (ha : MassOrdered a as)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) : 0 ≤ edgeBudget a as f := by
  induction as generalizing a f with
  | nil => exact mul_nonneg (sub_nonneg.mpr ha.2) (hf 0)
  | cons b as ih =>
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr ha.2.1) (hf 0))
      (ih ha.2.2 (fun j => hf (1+j)))

theorem single_forkCost (as : List PositiveMass) (f : ℕ → ℝ) :
    (single (S:=S) as).forkCost f = 0 := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

 
theorem split_le_forkCost {as : List PositiveMass} (T : ClockTree S as)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (s t : T.Slot) (hst : s ≠ t) :
    f (T.splitIndex s t) ≤ T.forkCost f := by
  induction T generalizing f with
  | leaf => exact (hst (Subsingleton.elim _ _)).elim
  | step a T ih => exact ih (fun j => hf (1+j)) s t hst
  | fork T U ihT ihU =>
    cases s with
    | inl s => cases t with
      | inl t =>
        have h := ihT hf s t (fun h => hst (congrArg Sum.inl h))
        change f (T.splitIndex s t) ≤ f 0 + T.forkCost f + U.forkCost f
        linarith [hf 0,U.forkCost_nonneg hf]
      | inr t =>
        change f 0 ≤ f 0 + T.forkCost f + U.forkCost f
        linarith [T.forkCost_nonneg hf,U.forkCost_nonneg hf]
    | inr s => cases t with
      | inl t =>
        change f 0 ≤ f 0 + T.forkCost f + U.forkCost f
        linarith [T.forkCost_nonneg hf,U.forkCost_nonneg hf]
      | inr t =>
        have h := ihU hf s t (fun h => hst (congrArg Sum.inr h))
        change f (U.splitIndex s t) ≤ f 0 + T.forkCost f + U.forkCost f
        linarith [hf 0,T.forkCost_nonneg hf]

 
def attachForkExtra : {as : List PositiveMass} → ClockTree S as → ℝ → (ℕ → ℝ) → ℝ
  | _, .leaf, a, f => (1-a)*f 0
  | _, .step b T, a, f => (b.val-a)*f 0 + T.attachForkExtra b.val (fun j => f (1+j))
  | _, .fork T U, a, f => a*f 0 + T.attachForkExtra a f + U.attachForkExtra a f

theorem attachForkExtra_le {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) :
    T.attachForkExtra a f ≤ (T.leaves:ℝ)*edgeBudget a as f + T.forkCost f := by
  induction T generalizing a f with
  | leaf => simp [attachForkExtra,leaves,edgeBudget,forkCost]
  | step b T ih =>
    have h := ih ha.2.2 (fun j => hf (1+j))
    have hr : (1:ℝ) ≤ (T.leaves:ℝ) := by exact_mod_cast T.leaves_pos
    have he := mul_le_mul_of_nonneg_right hr (mul_nonneg (sub_nonneg.mpr ha.2.1) (hf 0))
    simp only [attachForkExtra,leaves,edgeBudget,forkCost]
    nlinarith
  | fork T U ihT ihU =>
    have hT := ihT ha hf
    have hU := ihU ha hf
    have he := mul_le_mul_of_nonneg_right (massOrdered_bounds ha).2 (hf 0)
    simp only [attachForkExtra,leaves,Nat.cast_add,forkCost]
    nlinarith

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 

theorem markedAttach_forkCost {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) (f : ℕ → ℝ) :
    ((T.markedAttach a).map fun p => |p.coeff| *p.tree.forkCost f).sum =
      (2*(T.leaves:ℝ)-a)*T.forkCost f + T.attachForkExtra a f := by
  induction T generalizing a f with
  | leaf =>
    simp only [markedAttach,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      MarkedPlacement.coincide,MarkedPlacement.fresh,forkCost,single,leaves,attachForkExtra]
    rw [abs_of_nonpos (sub_nonpos.mpr ha.2)]
    ring
  | step b T ih =>
    have hb := ih ha.2.2 (fun j => f (1+j))
    have hv := T.markedAttach_variation ha.2.2
    simp only [markedAttach,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      MarkedPlacement.fresh,MarkedPlacement.step,forkCost,single_forkCost,add_zero]
    rw [abs_of_nonpos (sub_nonpos.mpr ha.2.1),hb]
    simp only [leaves,attachForkExtra]
    ring
  | fork T U ihT ihU =>
    have hT := ihT ha f
    have hU := ihU ha f
    have hvT := T.markedAttach_variation ha
    have hvU := U.markedAttach_variation ha
    simp only [markedAttach,List.map_cons,List.sum_cons,List.map_append,List.sum_append,
      List.map_map,Function.comp_def,MarkedPlacement.fresh,MarkedPlacement.left,
      MarkedPlacement.right,forkCost,single_forkCost,add_zero,mul_add,List.sum_map_add,
      List.sum_map_mul_right]
    rw [abs_neg,abs_of_nonneg (massOrdered_bounds ha).1,hT,hU,hvT,hvU]
    simp only [leaves,Nat.cast_add,attachForkExtra]
    ring

 

theorem markedAttach_forkCost_le {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) :
    ((T.markedAttach a).map fun p => |p.coeff| *p.tree.forkCost f).sum ≤
      (2*(T.leaves:ℝ)+1)*(T.forkCost f + edgeBudget a as f) := by
  rw [T.markedAttach_forkCost ha]
  have h := T.attachForkExtra_le ha hf
  have hF := T.forkCost_nonneg hf
  have hB := edgeBudget_nonneg ha hf
  have ha0 := (massOrdered_bounds ha).1
  have hr : (0:ℝ) ≤ T.leaves := Nat.cast_nonneg _
  nlinarith

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
variable {S : Type*}

 
def forkLedger (a : ℝ) (f : ℕ → ℝ) : ℕ → {as : List PositiveMass} → ClockTree S as → ℝ
  | 0, _, T => T.forkCost f
  | k+1, _, T => ((T.markedAttach a).map fun p => |p.coeff| * forkLedger a f k p.tree).sum

def forkVariation : ℕ → ℕ → ℝ
  | _, 0 => 1
  | r, k+1 => (4*(r:ℝ)+1)*forkVariation (r+1) k

theorem forkVariation_nonneg (r k : ℕ) : 0 ≤ forkVariation r k := by
  induction k generalizing r with
  | zero => exact zero_le_one
  | succ k ih => exact mul_nonneg (by positivity) (ih _)

theorem forkLedger_nonneg {as : List PositiveMass} (T : ClockTree S as)
    (a : ℝ) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) (k : ℕ) :
    0 ≤ forkLedger a f k T := by
  induction k generalizing T with
  | zero => exact T.forkCost_nonneg hf
  | succ k ih =>
    exact List.sum_nonneg (by
      intro x hx
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp hx
      exact mul_nonneg (abs_nonneg _) (ih p.tree))

theorem forkLedger_le {as : List PositiveMass} (T : ClockTree S as)
    {a : ℝ} (ha : MassOrdered a as) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {r : ℕ} (hT : T.leaves ≤ r) (k : ℕ) :
    forkLedger a f k T ≤ forkVariation r k*(T.forkCost f + edgeBudget a as f) := by
  induction k generalizing T r with
  | zero =>
    simp only [forkLedger,forkVariation,one_mul]
    exact le_add_of_nonneg_right (edgeBudget_nonneg ha hf)
  | succ k ih =>
    have hC := forkVariation_nonneg (r+1) k
    have hB := edgeBudget_nonneg ha hf
    have hF := T.forkCost_nonneg hf
    have h1 : ((T.markedAttach a).map fun p => |p.coeff| * forkLedger a f k p.tree).sum ≤
        ((T.markedAttach a).map fun p => |p.coeff| *
          (forkVariation (r+1) k*(p.tree.forkCost f+edgeBudget a as f))).sum := by
      apply List.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left
        (ih x.tree ((T.markedAttach_leaves a x hx).trans (Nat.add_le_add_right hT 1)))
        (abs_nonneg _)
    have h2 : ((T.markedAttach a).map fun p => |p.coeff| *
          (forkVariation (r+1) k*(p.tree.forkCost f+edgeBudget a as f))).sum =
        forkVariation (r+1) k *
          (((T.markedAttach a).map fun p => |p.coeff| * p.tree.forkCost f).sum +
            (2*(T.leaves:ℝ)-a)*edgeBudget a as f) := by
      simp only [mul_left_comm _ (forkVariation (r+1) k),List.sum_map_mul_left,mul_add,
        List.sum_map_add,List.sum_map_mul_right,T.markedAttach_variation ha]
    have h3 : ((T.markedAttach a).map fun p => |p.coeff| * p.tree.forkCost f).sum +
            (2*(T.leaves:ℝ)-a)*edgeBudget a as f ≤
        (4*(r:ℝ)+1)*(T.forkCost f+edgeBudget a as f) := by
      have hf1 := T.markedAttach_forkCost_le ha hf
      have hr : (T.leaves:ℝ) ≤ r := by exact_mod_cast hT
      have ha0 := (massOrdered_bounds ha).1
      have hp : (0:ℝ) ≤ T.leaves := Nat.cast_nonneg _
      nlinarith
    exact h1.trans (h2.le.trans (by
      change forkVariation (r+1) k * _ ≤ forkVariation r (k+1) * _
      rw [forkVariation]
      nlinarith [mul_le_mul_of_nonneg_left h3 hC]))

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S]

 

def pairMean (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ) :
    (as : List PositiveMass) → (ℕ → ι → ℝ≥0) → ℕ → (S → S → ℝ) → (ι → ℝ) → ℝ
  | as, q, 0, P, x => singleMean w φ as q (fun s => singleMean w φ as q (P s) x) x
  | [], q, _+1, P, x => singleMean w φ [] q (fun s => singleMean w φ [] q (P s) x) x
  | b::as, q, j+1, P, x =>
    shiftedMean (Measure.pi fun i => gaussianReal 0 (q 0 i)) b.val
      (gaussianHierarchy w φ (clockSteps as (fun j => q (j+1))))
      (pairMean w φ as (fun j => q (j+1)) j P) x

omit [Nonempty S] in
theorem pairMean_zero_symm (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q : ℕ → ι → ℝ≥0) (P : S → S → ℝ) (x : ι → ℝ) :
    pairMean w φ as q 0 (fun s t => P t s) x = pairMean w φ as q 0 P x := by
  simp only [pairMean,singleMean,expect,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

 

theorem expect_pairAtSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0)
    (s t : T.Slot) (hst : s ≠ t) (P : S → S → ℝ) (x : ι → ℝ) :
    T.expect w φ q (fun σ => P (T.atSlot σ s) (T.atSlot σ t)) x =
      pairMean w φ as q (T.splitIndex s t) P x := by
  induction T generalizing a q P x with
  | leaf => exact (hst (Subsingleton.elim _ _)).elim
  | @step b bs T ih =>
    rw [expect_step hw φ b T ho.2.2]
    change _ = pairMean w φ (b::bs) q (1+T.splitIndex s t) P x
    rw [Nat.add_comm 1]
    simp only [pairMean]
    congr 1
    funext y
    exact ih ho.2.2 _ s t hst P y
  | @fork as T U ihT ihU =>
    cases s with
    | inl s => cases t with
      | inl t =>
        rw [expect_fork]
        change T.expect w φ q (fun σ => U.expect w φ q
          (fun _ => P (T.atSlot σ s) (T.atSlot σ t)) x) x = _
        simp only [U.expect_const hw φ ho q]
        exact ihT ho q s t (fun h => hst (congrArg Sum.inl h)) P x
      | inr t =>
        rw [expect_fork]
        change T.expect w φ q (fun σ => U.expect w φ q
          (fun τ => P (T.atSlot σ s) (U.atSlot τ t)) x) x = _
        simp only [U.expect_atSlot hw φ ho q]
        change T.expect w φ q (fun σ => singleMean w φ as q (P (T.atSlot σ s)) x) x =
          pairMean w φ as q 0 P x
        rw [pairMean]
        exact T.expect_atSlot hw φ ho q s (fun z => singleMean w φ as q (P z) x) x
    | inr s => cases t with
      | inl t =>
        rw [expect_fork]
        change T.expect w φ q (fun τ => U.expect w φ q
          (fun σ => P (U.atSlot σ s) (T.atSlot τ t)) x) x = _
        change T.expect w φ q (fun τ => U.expect w φ q
          (fun σ => P (U.atSlot σ s) (T.atSlot τ t)) x) x = pairMean w φ as q 0 P x
        have hi : (fun τ => U.expect w φ q (fun σ => P (U.atSlot σ s) (T.atSlot τ t)) x) =
            (fun τ => singleMean w φ as q (fun z => P z (T.atSlot τ t)) x) :=
          funext fun τ => U.expect_atSlot hw φ ho q s (fun z => P z (T.atSlot τ t)) x
        rw [hi,T.expect_atSlot hw φ ho q t (fun z => singleMean w φ as q (fun y => P y z) x) x]
        simpa only [pairMean] using pairMean_zero_symm w φ as q P x
      | inr t =>
        rw [expect_fork]
        change T.expect w φ q (fun _ => U.expect w φ q
          (fun σ => P (U.atSlot σ s) (U.atSlot σ t)) x) x = _
        rw [T.expect_const hw φ ho q]
        exact ihU ho q s t (fun h => hst (congrArg Sum.inr h)) P x

variable {n : ℕ}

def pairRootMean (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (j : ℕ) (P : S → S → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  ∫ y, pairMean w φ as (fun j i => Real.toNNReal (q j i)) j P (x+y)
    ∂(Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q₀ i)))

theorem rootExpect_pairAtSlot {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (s t : T.Slot) (hst : s ≠ t) (P : S → S → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ (fun σ => P (T.atSlot σ s) (T.atSlot σ t)) q₀ q x =
      pairRootMean w φ as q₀ q (T.splitIndex s t) P x := by
  simp only [rootExpect_eq_integral,T.expect_pairAtSlot hw φ ho _ s t hst,pairRootMean]

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

theorem rootExpect_const {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (c : ℝ) (x : Fin (n+1) → ℝ) : T.rootExpect w φ (fun _ => c) q₀ q x = c := by
  simp only [rootExpect_eq_integral,T.expect_const hw φ ho,integral_const,
    probReal_univ,one_smul]

 

theorem rootExpect_pair_envelope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (E : ℕ → S → S → ℝ) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => |E j σ τ|) x ≤ f j)
    (s t : T.Slot) :
    T.rootExpect w φ (fun σ => |E (T.splitIndex s t) (T.atSlot σ s) (T.atSlot σ t)|) q₀ q x ≤
      T.forkCost f+d := by
  by_cases hst : s = t
  · subst t
    rw [T.splitIndex_self]
    exact (T.rootExpect_mono hw φ ho (fun σ => hdiag (T.atSlot σ s)) q₀ q x).trans
      ((T.rootExpect_const hw φ ho q₀ q d x).le.trans (le_add_of_nonneg_left (T.forkCost_nonneg hf)))
  · rw [T.rootExpect_pairAtSlot hw φ ho q₀ q s t hst
      (fun σ τ => |E (T.splitIndex s t) σ τ|) x]
    exact (he _).trans ((T.split_le_forkCost hf s t hst).trans (le_add_of_nonneg_right hd))

 

theorem profilePairTest_root_envelope {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (P : T.Assignment → ℝ) {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ, |P σ| ≤ C)
    (E : ℕ → S → S → ℝ) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    {d : ℝ} (hd : 0 ≤ d) (hdiag : ∀ σ, |E as.length σ σ| ≤ d)
    (x : Fin (n+1) → ℝ)
    (he : ∀ j, pairRootMean w φ as q₀ q j (fun σ τ => |E j σ τ|) x ≤ f j)
    (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
    r.tree.rootExpect w φ (fun σ => |profilePairTest P E p r σ|) q₀ q x ≤
      C*(r.tree.forkCost f+d) := by
  have hb : ∀ σ, |profilePairTest P E p r σ| ≤
      C*|E (r.tree.splitIndex (r.embed p.mark) r.mark)
        (r.tree.atSlot σ (r.embed p.mark)) (r.tree.atSlot σ r.mark)| := by
    intro σ
    simp only [profilePairTest,abs_mul,p.spin_at,r.restrict_at,r.spin_at]
    exact mul_le_mul_of_nonneg_right (hP _) (abs_nonneg _)
  apply (r.tree.rootExpect_mono hw φ ho hb q₀ q x).trans
  rw [r.tree.rootExpect_const_mul]
  exact mul_le_mul_of_nonneg_left
    (r.tree.rootExpect_pair_envelope hw φ ho q₀ q E hf hd hdiag x he _ _) hC

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

theorem rootExpect_add {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P Q : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ (fun σ => P σ+Q σ) q₀ q x =
      T.rootExpect w φ P q₀ q x+T.rootExpect w φ Q q₀ q x := by
  simp only [rootExpect_eq_integral,expect_realize,ReplicaTree.expect_add]
  exact integral_add (by simpa only [expect_realize] using T.rootExpect_integrable hw φ ho P q₀ q x)
    (by simpa only [expect_realize] using T.rootExpect_integrable hw φ ho Q q₀ q x)

 

theorem rootExpect_mul_sq_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P Q : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    (T.rootExpect w φ (fun σ => P σ*Q σ) q₀ q x)^2 ≤
      T.rootExpect w φ (fun σ => (P σ)^2) q₀ q x*
        T.rootExpect w φ (fun σ => (Q σ)^2) q₀ q x := by
  have hpos (t : ℝ) : 0 ≤
      T.rootExpect w φ (fun σ => (P σ)^2) q₀ q x*(t*t)+
        (2*T.rootExpect w φ (fun σ => P σ*Q σ) q₀ q x)*t+
        T.rootExpect w φ (fun σ => (Q σ)^2) q₀ q x := by
    have h := T.rootExpect_nonneg hw φ ho (fun σ => sq_nonneg (t*P σ+Q σ)) q₀ q x
    have he : (fun σ => (t*P σ+Q σ)^2) =
        (fun σ => (t*t)*(P σ)^2+(2*t)*(P σ*Q σ)+(Q σ)^2) := by funext σ; ring
    rw [he,T.rootExpect_add hw φ ho,T.rootExpect_add hw φ ho,
      T.rootExpect_const_mul,T.rootExpect_const_mul] at h
    nlinarith
  have h := discrim_le_zero hpos
  dsimp only [discrim] at h
  nlinarith

 
theorem rootExpect_abs_mul_le {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P Q : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : T.rootExpect w φ (fun σ => (P σ)^2) q₀ q x ≤ C^2)
    (hQ : T.rootExpect w φ (fun σ => (Q σ)^2) q₀ q x ≤ D^2) :
    T.rootExpect w φ (fun σ => |P σ*Q σ|) q₀ q x ≤ C*D := by
  have h := T.rootExpect_mul_sq_le hw φ ho (fun σ => |P σ|) (fun σ => |Q σ|) q₀ q x
  simp only [sq_abs,← abs_mul] at h
  have hPQ := mul_le_mul hP hQ
    (T.rootExpect_nonneg hw φ ho (fun σ => sq_nonneg (Q σ)) q₀ q x) (sq_nonneg C)
  have hn : 0 ≤ C*D := mul_nonneg hC hD
  nlinarith

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}
attribute [local instance] Classical.propDecidable

theorem rootExpect_finsetSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    {ι : Type*} (s : Finset ι) (P : ι → T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ (fun σ => ∑ i ∈ s, P i σ) q₀ q x =
      ∑ i ∈ s, T.rootExpect w φ (P i) q₀ q x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using T.rootExpect_const hw φ ho q₀ q 0 x
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi,T.rootExpect_add hw φ ho,ih]

 

def plantedWeight (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) (σ : T.Assignment) : ℝ :=
  T.rootExpect w φ (fun τ => if τ=σ then 1 else 0) q₀ q x

theorem plantedWeight_nonneg {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (x : Fin (n+1) → ℝ) (σ : T.Assignment) : 0 ≤ T.plantedWeight w φ q₀ q x σ := by
  apply T.rootExpect_nonneg hw φ ho
  intro τ
  split_ifs <;> norm_num

theorem plantedWeight_sum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    ∑ σ, T.plantedWeight w φ q₀ q x σ = 1 := by
  simp only [plantedWeight]
  rw [← T.rootExpect_finsetSum hw φ ho]
  simpa using T.rootExpect_const hw φ ho q₀ q 1 x

theorem rootExpect_eq_plantedSum {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as) (P : T.Assignment → ℝ)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ P q₀ q x = ∑ σ, T.plantedWeight w φ q₀ q x σ*P σ := by
  have he : P = fun τ => ∑ σ, P σ*(if τ=σ then 1 else 0) := by
    funext τ
    simp
  conv_lhs => rw [he]
  rw [T.rootExpect_finsetSum hw φ ho]
  simp only [T.rootExpect_const_mul,plantedWeight,mul_comm]

 

def plantedPMF {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q₀ : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : PMF T.Assignment :=
  PMF.ofFintype (fun σ => ENNReal.ofReal (T.plantedWeight w φ q₀ q x σ)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun σ _ => T.plantedWeight_nonneg hw φ ho q₀ q x σ),
      T.plantedWeight_sum hw φ ho]
    norm_num)

theorem rootExpect_eq_plantedIntegral {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    [MeasurableSpace T.Assignment] [MeasurableSingletonClass T.Assignment]
    (P : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) :
    T.rootExpect w φ P q₀ q x = ∫ σ, P σ ∂(T.plantedPMF hw φ ho q₀ q x).toMeasure := by
  rw [PMF.integral_eq_sum,T.rootExpect_eq_plantedSum hw φ ho]
  simp only [plantedPMF,PMF.ofFintype_apply,smul_eq_mul,
    ENNReal.toReal_ofReal (T.plantedWeight_nonneg hw φ ho q₀ q x _)]

end SKFluctuations.Hierarchy.ClockTree

 

namespace SKFluctuations.Hierarchy.ClockTree
open MeasureTheory ProbabilityTheory
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem rootExpect_holder {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P Q : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ)
    {p s : ℝ} (hps : p.HolderConjugate s) :
    T.rootExpect w φ (fun σ => |P σ*Q σ|) q₀ q x ≤
      (T.rootExpect w φ (fun σ => |P σ|^p) q₀ q x)^(1/p)*
        (T.rootExpect w φ (fun σ => |Q σ|^s) q₀ q x)^(1/s) := by
  let : MeasurableSpace T.Assignment := ⊤
  let μ := (T.plantedPMF hw φ ho q₀ q x).toMeasure
  have hP : MemLp P (ENNReal.ofReal p) μ := MemLp.of_discrete
  have hQ : MemLp Q (ENNReal.ofReal s) μ := MemLp.of_discrete
  simpa only [T.rootExpect_eq_plantedIntegral hw φ ho,abs_mul,Real.norm_eq_abs]
    using (integral_mul_norm_le_Lp_mul_Lq hps hP hQ)

 
theorem rootExpect_holder_budget {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (P Q : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ)
    {p s C D : ℝ} (hps : p.HolderConjugate s) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hP : T.rootExpect w φ (fun σ => |P σ|^p) q₀ q x ≤ C^p)
    (hQ : T.rootExpect w φ (fun σ => |Q σ|^s) q₀ q x ≤ D^s) :
    T.rootExpect w φ (fun σ => |P σ*Q σ|) q₀ q x ≤ C*D := by
  have hP0 := T.rootExpect_nonneg hw φ ho (fun σ => Real.rpow_nonneg (abs_nonneg (P σ)) p) q₀ q x
  have hQ0 := T.rootExpect_nonneg hw φ ho (fun σ => Real.rpow_nonneg (abs_nonneg (Q σ)) s) q₀ q x
  have h₁ := Real.rpow_le_rpow hP0 hP (div_nonneg zero_le_one hps.nonneg)
  have h₂ := Real.rpow_le_rpow hQ0 hQ (div_nonneg zero_le_one hps.symm.nonneg)
  rw [← Real.rpow_mul hC,mul_one_div_cancel hps.pos.ne',Real.rpow_one] at h₁
  rw [← Real.rpow_mul hD,mul_one_div_cancel hps.symm.pos.ne',Real.rpow_one] at h₂
  exact (T.rootExpect_holder hw φ ho P Q q₀ q x hps).trans
    (mul_le_mul h₁ h₂ (Real.rpow_nonneg hQ0 _) hC)

 

theorem rootExpect_rpow_from_second {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) {as : List PositiveMass}
    (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (E : T.Assignment → ℝ) (q₀ : Fin (n+1) → ℝ)
    (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ)
    {p B D : ℝ} (hp : 2 ≤ p) (hB : 0 ≤ B)
    (hE : ∀ σ, |E σ| ≤ B)
    (h₂ : T.rootExpect w φ (fun σ => (E σ)^2) q₀ q x ≤ D^2) :
    T.rootExpect w φ (fun σ => |E σ|^p) q₀ q x ≤ B^(p-2)*D^2 := by
  have hb (σ : T.Assignment) : |E σ|^p ≤ B^(p-2)*(E σ)^2 := by
    have he := Real.rpow_le_rpow (abs_nonneg (E σ)) (hE σ) (sub_nonneg.mpr hp)
    have hid : |E σ|^p = (E σ)^2*|E σ|^(p-2) := by
      rw [← sq_abs,← Real.rpow_natCast (|E σ|) 2]
      norm_num only [Nat.cast_ofNat]
      rw [← Real.rpow_add_of_nonneg (abs_nonneg (E σ)) (by norm_num : (0:ℝ) ≤ 2)
        (sub_nonneg.mpr hp)]
      congr 1
      ring
    rw [hid,mul_comm (B^(p-2))]
    exact mul_le_mul_of_nonneg_left he (sq_nonneg _)
  apply (T.rootExpect_mono hw φ ho hb q₀ q x).trans
  rw [T.rootExpect_const_mul]
  exact mul_le_mul_of_nonneg_left h₂ (Real.rpow_nonneg hB _)

end SKFluctuations.Hierarchy.ClockTree

end

end OAI
