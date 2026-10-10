import Mathlib
import OAI.Probability.Contingency.RecursiveTransport

namespace OAI

/-! Root Transport. -/

noncomputable section

open scoped BigOperators
open scoped BigOperators
open QuadraticMap

namespace Contingency

universe u

 

noncomputable def allSurplus {ι : Type u} (C : ℕ) :
    (n : ℕ) → ((PairCoords ι n → ℤ) → ℝ) → (ι → ℤ) → ℝ
  | 0, _ => fun _ => 0
  | n+1, f => fun p => balancedMarginal (allBalance C n f) (C+1) p +
      balancedMarginal (allSurplus C n f) C p

section NonnegativeKernels
variable {ι : Type u}

theorem allBalance_nonneg (C n : ℕ) (f : (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∀ p, 0 ≤ allBalance C n f p := by
  induction n generalizing ι with
  | zero => exact hf
  | succ n ih =>
    intro p
    change 0 ≤ balancedMarginal (allBalance C n f) C p
    unfold balancedMarginal
    exact Finset.sum_nonneg (fun j _ => ih f hf _)

theorem allSurplus_nonneg (C n : ℕ) (f : (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) : ∀ p, 0 ≤ allSurplus C n f p := by
  induction n generalizing ι with
  | zero => intro p; exact le_rfl
  | succ n ih =>
    intro p
    exact add_nonneg
      (Finset.sum_nonneg (fun j _ => allBalance_nonneg C n f hf _))
      (Finset.sum_nonneg (fun j _ => ih f hf _))

theorem raisedFull_le_surplus (f : (ι ⊕ Bool → ℤ) → ℝ) (C : ℕ)
    (hf : ∀ x, 0 ≤ f x) (p : ι → ℤ) :
    raisedFull f C p ≤ ((C:ℝ)+1)^2 * balancedMarginal f (C+1) p := by
  unfold raisedFull balancedMarginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hj' : j ≤ C+1 := by exact Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hrj : (j:ℝ) ≤ (C:ℝ)+1 := by exact_mod_cast hj'
  have hj0 : 0 ≤ (j:ℝ) := Nat.cast_nonneg _
  have hC0 : 0 ≤ (C:ℝ)+1 := by positivity
  have hw : (j:ℝ) * ((C:ℝ)+1-j) ≤ ((C:ℝ)+1)^2 := by
    nlinarith [sq_nonneg ((C:ℝ)+1-j)]
  simpa only [Nat.cast_add, Nat.cast_one] using mul_le_mul_of_nonneg_right hw
    (hf (pairAssembly p (j:ℤ) ((C:ℤ)+1-j)))

 

theorem allRaise_le_surplus (C n : ℕ) (f : (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, 0 ≤ f x) (p : ι → ℤ) :
    allRaise C n f p ≤ ((C:ℝ)+1)^2 * allSurplus C n f p := by
  induction n generalizing ι with
  | zero => simp [allRaise, allSurplus]
  | succ n ih =>
    have hfirst := raisedFull_le_surplus (allBalance C n f) C (allBalance_nonneg C n f hf) p
    have hsecond : balancedMarginal (allRaise C n f) C p ≤
        ((C:ℝ)+1)^2 * balancedMarginal (allSurplus C n f) C p := by
      unfold balancedMarginal
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun j _ => ih f hf _)
    change raisedFull (allBalance C n f) C p + balancedMarginal (allRaise C n f) C p ≤ _
    simpa only [allSurplus, mul_add] using add_le_add hfirst hsecond

end NonnegativeKernels

 

noncomputable def rootCoeff (zm zp : ℝ) (b : Bool) : ℝ := if b then 1/zm else -(1/zp)

section Root
variable (n C : ℕ) (f : (PairCoords Bool n → ℤ) → ℝ) (p : Bool → ℤ)

noncomputable def minusMass : ℝ := allBalance C n f (removeOne p true)
noncomputable def plusMass : ℝ := allBalance C n f (removeOne p false)
noncomputable def auxiliaryMass : ℝ := allSurplus C n f (removePair p true false)

theorem root_balance (hm : 0 < minusMass n C f p) (hp : 0 < plusMass n C f p) :
    holeFunctional (allBalance C n f) p
      (rootCoeff (minusMass n C f p) (plusMass n C f p)) = 0 := by
  simp only [holeFunctional, Fintype.sum_bool, rootCoeff, Bool.false_eq_true,
    ite_false, ite_true]
  change minusMass n C f p * (1/minusMass n C f p) +
    plusMass n C f p * (-(1/plusMass n C f p)) = 0
  field_simp [hm.ne', hp.ne']
  norm_num

theorem root_potential (hm : 0 < minusMass n C f p) (hp : 0 < plusMass n C f p) :
    holePotential (allBalance C n f) p
      (rootCoeff (minusMass n C f p) (plusMass n C f p)) =
      1/minusMass n C f p + 1/plusMass n C f p := by
  simp only [holePotential, Fintype.sum_bool, rootCoeff, Bool.false_eq_true,
    ite_false, ite_true]
  change minusMass n C f p * (1/minusMass n C f p)^2 +
    plusMass n C f p * (-(1/plusMass n C f p))^2 = _
  field_simp [hm.ne', hp.ne']

theorem root_test_demand (H : (PairCoords Bool n → ℤ) → ℝ) :
    holeFunctional (allBalance C n (fun x => f x * H x)) p
      (rootCoeff (minusMass n C f p) (plusMass n C f p)) =
      minusMass n C (fun x => f x * H x) p / minusMass n C f p -
      plusMass n C (fun x => f x * H x) p / plusMass n C f p := by
  simp [holeFunctional, rootCoeff, minusMass, plusMass]
  ring

theorem root_quadratic_bound
    (hf : ∀ x, 0 ≤ f x)
    (hm : 0 < minusMass n C f p) (hp : 0 < plusMass n C f p)
    (hnonneg : ∀ x, 0 ≤ allRaise C n f x) :
    -matrixForm (twoRemoval (allRaise C n f) p)
      (rootCoeff (minusMass n C f p) (plusMass n C f p)) ≤
      2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
        (minusMass n C f p * plusMass n C f p) := by
  let zm := minusMass n C f p
  let zp := plusMass n C f p
  let A := allRaise C n f (removePair p true true)
  let B := allRaise C n f (removePair p true false)
  let D := allRaise C n f (removePair p false false)
  have he : matrixForm (twoRemoval (allRaise C n f) p) (rootCoeff zm zp) =
      A*(1/zm)^2 - 2*B*(1/zm)*(1/zp) + D*(1/zp)^2 := by
    simp only [matrixForm_apply, twoRemoval, Fintype.sum_bool, rootCoeff,
      Bool.false_eq_true, ite_false, ite_true]
    rw [removePair_comm p false true]
    dsimp [A,B,D]
    ring
  have hA := mul_nonneg (hnonneg (removePair p true true)) (sq_nonneg (1/zm))
  have hD := mul_nonneg (hnonneg (removePair p false false)) (sq_nonneg (1/zp))
  have hB := allRaise_le_surplus C n f hf (removePair p true false)
  have hm' : 0 ≤ (1/zm) := (one_div_pos.mpr hm).le
  have hp' : 0 ≤ (1/zp) := (one_div_pos.mpr hp).le
  have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 2)) hm') hp'
  change -matrixForm (twoRemoval (allRaise C n f) p) (rootCoeff zm zp) ≤ _
  rw [he]
  have hr : 2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
        (minusMass n C f p * plusMass n C f p) =
      2 * (((C:ℝ)+1)^2 * allSurplus C n f (removePair p true false)) * (1/zm) * (1/zp) := by
    dsimp [zm,zp,auxiliaryMass]
    ring
  rw [hr]
  dsimp only [A,B,D] at *
  nlinarith

instance pairCoordsNonempty (ι : Type u) [Nonempty ι] : (n : ℕ) → Nonempty (PairCoords ι n)
  | 0 => inferInstanceAs (Nonempty ι)
  | n+1 => pairCoordsNonempty (ι ⊕ Bool) n

 

theorem softened_root_transport (hC : 2 ≤ C)
    (H : (PairCoords Bool n → ℤ) → ℝ) (B : Bool → ℤ) (T : ℤ)
    (hf : PositiveSlice f (pairBox C n B) T)
    (hs : HasSignature f (pairBox C n B) T)
    (hb : InBox B p) (ht : (∑ i, p i)+(n:ℤ)*C = T+1)
    (hm : 0 < minusMass n C f p) (hp : 0 < plusMass n C f p)
    (E : Finset (Sym2 (PairCoords Bool n → ℤ)))
    (hE : ∀ a i j, i ≠ j →
      0 < f (removeOne (leafDisplay C n p a) i) →
      0 < f (removeOne (leafDisplay C n p a) j) →
      s(removeOne (leafDisplay C n p a) i, removeOne (leafDisplay C n p a) j) ∈ E) :
    (minusMass n C (fun x => f x * H x) p / minusMass n C f p -
      plusMass n C (fun x => f x * H x) p / plusMass n C f p)^2 ≤
    (1/minusMass n C f p + 1/plusMass n C f p +
      2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
        (minusMass n C f p * plusMass n C f p)) *
      ∑ e ∈ E, edgeEnergy f H e := by
  classical
  have hmaxex (a : Branches C n) : ∃ k : PairCoords Bool n,
      ∀ i, f (removeOne (leafDisplay C n p a) i) ≤ f (removeOne (leafDisplay C n p a) k) := by
    obtain ⟨k,_,hk⟩ := Finset.exists_max_image Finset.univ
      (fun i : PairCoords Bool n => f (removeOne (leafDisplay C n p a) i)) Finset.univ_nonempty
    exact ⟨k, fun i => hk i (Finset.mem_univ _)⟩
  choose hub hmax using hmaxex
  have hflow := recursive_star_transport C hC n f H B T hf hs p hb ht
    (rootCoeff (minusMass n C f p) (plusMass n C f p)) (root_balance n C f p hm hp)
    (fun a => H (removeOne (leafDisplay C n p a) (hub a)))
  rw [root_test_demand, root_potential n C f p hm hp] at hflow
  have hraise : ∀ x, 0 ≤ allRaise C n f x := by
    cases n with
    | zero => intro x; exact le_rfl
    | succ n => exact (allRaise_positive C hC (n+1) (by omega) f B T hf hs).nonneg
  have hroot := root_quadratic_bound n C f p hf.nonneg hm hp hraise
  have henergy := leafStarEnergy_le_graph C n f H hf.nonneg p hub hmax E
    (fun a i hn hi => hE a i (hub a) hn hi (hi.trans_le (hmax a i)))
  have henergy0 : 0 ≤ leafStarEnergy C n f H p
      (fun a => H (removeOne (leafDisplay C n p a) (hub a))) :=
    Finset.sum_nonneg (fun a _ => Finset.sum_nonneg
      (fun i _ => mul_nonneg (hf.nonneg _) (sq_nonneg _)))
  have hc0 : 0 ≤ 1/minusMass n C f p + 1/plusMass n C f p +
      2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
        (minusMass n C f p * plusMass n C f p) := by
    have ha0 : 0 ≤ auxiliaryMass n C f p := allSurplus_nonneg C n f hf.nonneg _
    positivity
  have hcoeff : 1/minusMass n C f p + 1/plusMass n C f p -
      matrixForm (twoRemoval (allRaise C n f) p)
        (rootCoeff (minusMass n C f p) (plusMass n C f p)) ≤
      1/minusMass n C f p + 1/plusMass n C f p +
        2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
          (minusMass n C f p * plusMass n C f p) := by linarith
  exact hflow.trans ((mul_le_mul_of_nonneg_right hcoeff henergy0).trans
    (mul_le_mul_of_nonneg_left henergy hc0))

end Root

end Contingency

 

 

open scoped BigOperators

namespace Contingency
universe u

 

def joinPairHead (ι : Type u) (n : ℕ) :
    ((ι ⊕ Bool) ⊕ (Fin n × Bool)) ≃ (ι ⊕ (Fin (n+1) × Bool)) where
  toFun x := match x with
    | .inl (.inl i) => .inl i
    | .inl (.inr b) => .inr (0,b)
    | .inr (s,b) => .inr (s.succ,b)
  invFun x := match x with
    | .inl i => .inl (.inl i)
    | .inr (s,b) => Fin.cases (.inl (.inr b)) (fun t => .inr (t,b)) s
  left_inv x := by rcases x with (i | b) | ⟨s,b⟩ <;> rfl
  right_inv x := by
    rcases x with i | ⟨s,b⟩
    · rfl
    · refine Fin.cases ?_ (fun t => ?_) s <;> rfl

def pairCoordsEquiv (ι : Type u) : (n : ℕ) → PairCoords ι n ≃ (ι ⊕ (Fin n × Bool))
  | 0 => (Equiv.sumEmpty ι (Fin 0 × Bool)).symm
  | n+1 => (pairCoordsEquiv (ι ⊕ Bool) n).trans (joinPairHead ι n)

@[simp] theorem pairCoordsEquiv_zero (ι : Type u) (i : ι) :
    pairCoordsEquiv ι 0 i = Sum.inl i := rfl

noncomputable def branchValue (C : ℕ) : (n : ℕ) → Branches C n → Fin n → Fin (C+1)
  | 0, _, s => Fin.elim0 s
  | n+1, a, s => Fin.cases a.1 (fun t => branchValue C n a.2 t) s

theorem leafDisplay_base {ι : Type u} (C n : ℕ) (p : ι → ℤ) (a : Branches C n) (i : ι) :
    leafDisplay C n p a ((pairCoordsEquiv ι n).symm (.inl i)) = p i := by
  induction n generalizing ι with
  | zero => rfl
  | succ n ih => exact ih (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ))) a.2 (.inl i)

theorem leafDisplay_slot {ι : Type u} (C n : ℕ) (p : ι → ℤ) (a : Branches C n)
    (s : Fin n) (b : Bool) :
    leafDisplay C n p a ((pairCoordsEquiv ι n).symm (.inr (s,b))) =
      if b then ((branchValue C n a s:ℕ):ℤ) else (C:ℤ)-(branchValue C n a s:ℕ) := by
  induction n generalizing ι with
  | zero => exact Fin.elim0 s
  | succ n ih =>
    refine Fin.cases ?_ (fun t => ?_) s
    · change leafDisplay C n (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ))) a.2
        ((pairCoordsEquiv (ι ⊕ Bool) n).symm (.inl (.inr b))) = _
      rw [leafDisplay_base]
      cases b <;> rfl
    · exact ih (pairAssembly p (a.1:ℕ) ((C:ℤ)-(a.1:ℕ))) a.2 t

 
def smallCoordsTail (n : ℕ) : (Bool ⊕ (Fin n × Bool)) ≃ (Fin (n+1) × Bool) where
  toFun x := match x with
    | .inl b => (0,b)
    | .inr (s,b) => (s.succ,b)
  invFun x := Fin.cases (.inl x.2) (fun s => .inr (s,x.2)) x.1
  left_inv x := by rcases x with b | ⟨s,b⟩ <;> rfl
  right_inv x := by rcases x with ⟨s,b⟩; refine Fin.cases ?_ (fun t => ?_) s <;> rfl

def smallCoords (n : ℕ) : PairCoords Bool n ≃ (Fin (n+1) × Bool) :=
  (pairCoordsEquiv Bool n).trans (smallCoordsTail n)

noncomputable def smallOccupancy (n : ℕ) (X : PairCoords Bool n → ℤ) (s : Fin (n+1)) : ℤ :=
  X ((smallCoords n).symm (s,true)) + X ((smallCoords n).symm (s,false))

@[simp] theorem leaf_occupancy_special (C n : ℕ) (p : Bool → ℤ) (a : Branches C n) :
    smallOccupancy n (leafDisplay C n p a) 0 = p true + p false := by
  unfold smallOccupancy smallCoords
  change leafDisplay C n p a ((pairCoordsEquiv Bool n).symm (.inl true)) +
    leafDisplay C n p a ((pairCoordsEquiv Bool n).symm (.inl false)) = _
  rw [leafDisplay_base,leafDisplay_base]

@[simp] theorem leaf_occupancy_ordinary (C n : ℕ) (p : Bool → ℤ) (a : Branches C n) (s : Fin n) :
    smallOccupancy n (leafDisplay C n p a) s.succ = (C:ℤ) := by
  unfold smallOccupancy smallCoords
  change leafDisplay C n p a ((pairCoordsEquiv Bool n).symm (.inr (s,true))) +
    leafDisplay C n p a ((pairCoordsEquiv Bool n).symm (.inr (s,false))) = _
  rw [leafDisplay_slot,leafDisplay_slot]
  simp

 

def smallPattern (C n : ℕ) (X : PairCoords Bool n → ℤ) : Prop :=
  (∀ s, smallOccupancy n X s = (C:ℤ)) ∨
  ∃ s t : Fin (n+1), s ≠ t ∧ smallOccupancy n X s = (C:ℤ)-1 ∧
    smallOccupancy n X t = (C:ℤ)+1 ∧
    ∀ v, v ≠ s → v ≠ t → smallOccupancy n X v = (C:ℤ)

theorem removeOne_occupancy (n : ℕ) (X : PairCoords Bool n → ℤ)
    (i : PairCoords Bool n) (s : Fin (n+1)) :
    smallOccupancy n (removeOne X i) s = smallOccupancy n X s -
      if s = (smallCoords n i).1 then 1 else 0 := by
  classical
  
  have hi : i = (smallCoords n).symm (smallCoords n i) := by simp
  rw [hi]
  generalize he : smallCoords n i = q
  rcases q with ⟨t,b⟩
  simp only [Equiv.apply_symm_apply]
  unfold smallOccupancy removeOne
  have ht : ((smallCoords n).symm (s,true) = (smallCoords n).symm (t,b)) ↔
      s = t ∧ true = b := by simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  have hf : ((smallCoords n).symm (s,false) = (smallCoords n).symm (t,b)) ↔
      s = t ∧ false = b := by simp only [Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [ht,hf]
  cases b <;> by_cases hh : s = t <;> simp [hh] <;> ring

theorem leaf_hole_pattern (C n : ℕ) (p : Bool → ℤ) (a : Branches C n)
    (hp : p true + p false = (C:ℤ)+1) (i : PairCoords Bool n) :
    smallPattern C n (removeOne (leafDisplay C n p a) i) := by
  have hd (v : Fin (n+1)) : smallOccupancy n (leafDisplay C n p a) v =
      if v = 0 then (C:ℤ)+1 else C := by
    refine Fin.cases ?_ (fun s => ?_) v
    · simpa using hp
    · simp
  by_cases hi : (smallCoords n i).1 = 0
  · left
    intro v
    rw [removeOne_occupancy,hd,hi]
    split_ifs <;> omega
  · right
    refine ⟨(smallCoords n i).1,0,hi,?_,?_,?_⟩
    · rw [removeOne_occupancy,hd]
      simp [hi]
    · rw [removeOne_occupancy,hd]
      simp [Ne.symm hi]
    · intro v hv hv0
      rw [removeOne_occupancy,hd]
      simp [hv,hv0]

theorem pairBox_const {ι : Type u} (C n : ℕ) :
    pairBox C n (fun _ : ι => (C:ℤ)) = fun _ => (C:ℤ) := by
  induction n generalizing ι with
  | zero => rfl
  | succ n ih =>
    have he : pairAssembly (fun _ : ι => (C:ℤ)) (C:ℤ) C = fun _ => (C:ℤ) := by
      funext i
      rcases i with i | b
      · rfl
      · cases b <;> rfl
    rw [pairBox,he]
    exact ih

noncomputable def smallVertexSet (C n : ℕ) : Finset (PairCoords Bool n → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ => Finset.Icc 0 (C:ℤ))).filter (smallPattern C n)

theorem mem_smallVertexSet (C n : ℕ) (X : PairCoords Bool n → ℤ) :
    X ∈ smallVertexSet C n ↔ InBox (fun _ => (C:ℤ)) X ∧ smallPattern C n X := by
  classical
  simp [smallVertexSet,Fintype.mem_piFinset,InBox]

 

noncomputable def smallUnitEdges (C n : ℕ) : Finset (Sym2 (PairCoords Bool n → ℤ)) := by
  classical
  exact (smallVertexSet C n).sym2.filter (fun e => ∃ D i j, i ≠ j ∧
    e = s(removeOne D i, removeOne D j))

theorem leaf_edge_mem (C n : ℕ) (f : (PairCoords Bool n → ℤ) → ℝ)
    (hf : BoxSupported f (fun _ => (C:ℤ))) (p : Bool → ℤ) (a : Branches C n)
    (hp : p true + p false = (C:ℤ)+1) (i j : PairCoords Bool n) (hij : i ≠ j)
    (hi : 0 < f (removeOne (leafDisplay C n p a) i))
    (hj : 0 < f (removeOne (leafDisplay C n p a) j)) :
    s(removeOne (leafDisplay C n p a) i,removeOne (leafDisplay C n p a) j) ∈ smallUnitEdges C n := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨?_,⟨leafDisplay C n p a,i,j,hij,rfl⟩⟩
  have hv (k : PairCoords Bool n) (hk : 0 < f (removeOne (leafDisplay C n p a) k)) :
      removeOne (leafDisplay C n p a) k ∈ smallVertexSet C n := by
    apply (mem_smallVertexSet C n _).mpr
    refine ⟨?_,leaf_hole_pattern C n p a hp k⟩
    by_contra hh
    rw [hf _ hh] at hk
    exact lt_irrefl _ hk
  simp only [Finset.mk_mem_sym2_iff]
  exact ⟨hv i hi,hv j hj⟩

 

theorem small_soft_transport (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f H : (PairCoords Bool n → ℤ) → ℝ)
    (hf : PositiveSlice f (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hs : HasSignature f (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (p : Bool → ℤ) (hb : InBox (fun _ => (C:ℤ)) p)
    (ht : p true+p false = (C:ℤ)+1)
    (hm : 0 < minusMass n C f p) (hp : 0 < plusMass n C f p) :
    (minusMass n C (fun x => f x * H x) p / minusMass n C f p -
      plusMass n C (fun x => f x * H x) p / plusMass n C f p)^2 ≤
    (1/minusMass n C f p + 1/plusMass n C f p +
      2*((C:ℝ)+1)^2*auxiliaryMass n C f p /
        (minusMass n C f p * plusMass n C f p)) *
      ∑ e ∈ smallUnitEdges C n, edgeEnergy f H e := by
  have hb' := hf
  have hs' := hs
  rw [← pairBox_const C n] at hb' hs'
  refine softened_root_transport n C f p hC H (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C)
    hb' hs' hb ?_ hm hp (smallUnitEdges C n) ?_
  · rw [Fintype.sum_bool,ht]
    push_cast
    ring
  · intro a i j hij hi hj
    exact leaf_edge_mem C n f hf.boxSupported p a ht i j hij hi hj

end Contingency

 

 

open scoped BigOperators
open Filter

namespace Contingency
universe u v

section Continuity
variable {ι : Type u} {K : Type v} [TopologicalSpace K]

theorem allBalance_continuous (C n : ℕ) (f : K → (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, Continuous (fun η => f η x)) (p : ι → ℤ) :
    Continuous (fun η => allBalance C n (f η) p) := by
  induction n generalizing ι with
  | zero => exact hf p
  | succ n ih =>
    change Continuous (fun η => ∑ j ∈ Finset.range (C+1),
      allBalance C n (f η) (pairAssembly p (j:ℤ) ((C:ℤ)-j)))
    exact continuous_finsetSum _ (fun j _ => ih f hf _)

theorem allSurplus_continuous (C n : ℕ) (f : K → (PairCoords ι n → ℤ) → ℝ)
    (hf : ∀ x, Continuous (fun η => f η x)) (p : ι → ℤ) :
    Continuous (fun η => allSurplus C n (f η) p) := by
  induction n generalizing ι with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous (fun η => (∑ j ∈ Finset.range (C+1+1),
      allBalance C n (f η) (pairAssembly p (j:ℤ) (((C+1:ℕ):ℤ)-j))) +
      ∑ j ∈ Finset.range (C+1),
      allSurplus C n (f η) (pairAssembly p (j:ℤ) ((C:ℤ)-j)))
    exact (continuous_finsetSum _ (fun j _ => allBalance_continuous C n f hf _)).add
      (continuous_finsetSum _ (fun j _ => ih f hf _))

theorem edgeEnergy_continuous {X : Type*} (f : K → X → ℝ) (hf : ∀ x, Continuous (fun η => f η x))
    (H : X → ℝ) (e : Sym2 X) : Continuous (fun η => edgeEnergy (f η) H e) := by
  induction e using Sym2.ind with
  | _ x y => exact ((hf x).min (hf y)).mul continuous_const

end Continuity

 

theorem root_masses_positive (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : (PairCoords Bool n → ℤ) → ℝ)
    (hf : PositiveSlice f (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hs : HasSignature f (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (p : Bool → ℤ) (hb : InBox (fun _ => (C:ℤ)) p)
    (ht : p true+p false = (C:ℤ)+1) :
    0 < minusMass n C f p ∧ 0 < plusMass n C f p := by
  have hf' := hf
  have hs' := hs
  rw [← pairBox_const C n] at hf' hs'
  have hpos := (allBalance_closure C hC n f (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C) hf' hs').1
  have hT : ((n+1:ℕ):ℤ)*C-(n:ℤ)*C = C := by push_cast; ring
  rw [hT] at hpos
  have hb' (b : Bool) : InBox (fun _ => (C:ℤ)) (removeOne p b) := by
    intro k
    have hb0 := hb false
    have hb1 := hb true
    dsimp at hb0 hb1
    cases b <;> cases k <;> simp only [removeOne, ite_eq_left, Bool.false_eq_true,
      Bool.true_eq_false, ite_false, sub_zero] <;> omega
  have hsum (b : Bool) : (∑ i, removeOne p b i) = (C:ℤ) := by
    rw [Fintype.sum_bool]
    cases b <;> simp only [removeOne, ite_eq_left, Bool.false_eq_true,
      Bool.true_eq_false, ite_false, sub_zero] <;> omega
  exact ⟨hpos.1 _ (hb' true) (hsum true),hpos.1 _ (hb' false) (hsum false)⟩

 

noncomputable def softSequence (j : ℕ) : ℝ := (1 / ((j:ℝ)+1))/2

theorem softSequence_range (j : ℕ) : 0 < softSequence j ∧ softSequence j < 1 := by
  have h : 1 / ((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) j])
  constructor
  · unfold softSequence; positivity
  · unfold softSequence; linarith

theorem softSequence_tendsto : Tendsto softSequence atTop (nhds 0) := by
  change Tendsto (fun j : ℕ => (1 / ((j:ℝ)+1))/2) atTop (nhds 0)
  have h := (@tendsto_one_div_add_atTop_nhds_zero_nat ℝ _ _ _ _).div_const 2
  simpa only [zero_div,softSequence] using h

 

theorem zero_root_transport (C : ℕ) (hC : 2 ≤ C) (n : ℕ)
    (f : ℝ → (PairCoords Bool n → ℤ) → ℝ)
    (hc : ∀ x, Continuous (fun η => f η x))
    (hf : ∀ η, 0 < η → η < 1 → PositiveSlice (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (hs : ∀ η, 0 < η → η < 1 → HasSignature (f η) (fun _ => (C:ℤ)) (((n+1:ℕ):ℤ)*C))
    (H : (PairCoords Bool n → ℤ) → ℝ)
    (p : Bool → ℤ) (hb : InBox (fun _ => (C:ℤ)) p)
    (ht : p true+p false = (C:ℤ)+1)
    (hm : 0 < minusMass n C (f 0) p) (hp : 0 < plusMass n C (f 0) p) :
    (minusMass n C (fun x => f 0 x * H x) p / minusMass n C (f 0) p -
      plusMass n C (fun x => f 0 x * H x) p / plusMass n C (f 0) p)^2 ≤
    (1/minusMass n C (f 0) p + 1/plusMass n C (f 0) p +
      2*((C:ℝ)+1)^2*auxiliaryMass n C (f 0) p /
        (minusMass n C (f 0) p * plusMass n C (f 0) p)) *
      ∑ e ∈ smallUnitEdges C n, edgeEnergy (f 0) H e := by
  have hcm : ContinuousAt (fun η => minusMass n C (f η) p) 0 :=
    (allBalance_continuous C n f hc _).continuousAt
  have hcp : ContinuousAt (fun η => plusMass n C (f η) p) 0 :=
    (allBalance_continuous C n f hc _).continuousAt
  have hcH (x) : Continuous (fun η => f η x * H x) := (hc x).mul continuous_const
  have hnm : ContinuousAt (fun η => minusMass n C (fun x => f η x * H x) p) 0 :=
    (allBalance_continuous C n _ hcH _).continuousAt
  have hnp : ContinuousAt (fun η => plusMass n C (fun x => f η x * H x) p) 0 :=
    (allBalance_continuous C n _ hcH _).continuousAt
  have hca : ContinuousAt (fun η => auxiliaryMass n C (f η) p) 0 :=
    (allSurplus_continuous C n f hc _).continuousAt
  have hce : ContinuousAt (fun η => ∑ e ∈ smallUnitEdges C n, edgeEnergy (f η) H e) 0 :=
    (continuous_finsetSum _ (fun e _ => edgeEnergy_continuous f hc H e)).continuousAt
  have hl := ((hnm.div hcm hm.ne').sub (hnp.div hcp hp.ne')).pow 2
  have hr : ContinuousAt (fun η => (1/minusMass n C (f η) p + 1/plusMass n C (f η) p +
      2*((C:ℝ)+1)^2*auxiliaryMass n C (f η) p /
        (minusMass n C (f η) p * plusMass n C (f η) p)) *
      ∑ e ∈ smallUnitEdges C n, edgeEnergy (f η) H e) 0 :=
    (((continuousAt_const.div hcm hm.ne').add (continuousAt_const.div hcp hp.ne')).add
    ((continuousAt_const.mul hca).div (hcm.mul hcp) (mul_ne_zero hm.ne' hp.ne'))).mul hce
  apply le_of_tendsto_of_tendsto (hl.tendsto.comp softSequence_tendsto)
    (hr.tendsto.comp softSequence_tendsto)
  apply Filter.Eventually.of_forall
  intro j
  have hj := softSequence_range j
  obtain ⟨hm',hp'⟩ := root_masses_positive C hC n (f (softSequence j))
    (hf _ hj.1 hj.2) (hs _ hj.1 hj.2) p hb ht
  exact small_soft_transport C hC n (f (softSequence j)) H
    (hf _ hj.1 hj.2) (hs _ hj.1 hj.2) p hb ht hm' hp'

 

theorem transport_repair_arithmetic (zm zp a E v d U : ℝ)
    (hm : 0 < zm) (hp : 0 < zp) (hE : 0 ≤ E) (_hd : 0 ≤ d)
    (ha : a ≤ d * max zm zp)
    (hv : v ^ 2 ≤ (1/zm + 1/zp + 2*(U+1)^2*a/(zm*zp))*E) :
    min zm zp * v^2 ≤ (2+2*d*(U+1)^2)*E := by
  have hmin : 0 ≤ min zm zp := le_min hm.le hp.le
  have hcoef : min zm zp * (1/zm + 1/zp + 2*(U+1)^2*a/(zm*zp)) ≤
      2+2*d*(U+1)^2 := by
    have h1 : min zm zp / zm ≤ 1 := (div_le_one hm).mpr (min_le_left _ _)
    have h2 : min zm zp / zp ≤ 1 := (div_le_one hp).mpr (min_le_right _ _)
    have h3 : min zm zp * a / (zm*zp) ≤ d := by
      apply (div_le_iff₀ (mul_pos hm hp)).mpr
      calc
        min zm zp * a ≤ min zm zp * (d * max zm zp) := mul_le_mul_of_nonneg_left ha hmin
        _ = d * (min zm zp * max zm zp) := by ring
        _ = d*(zm*zp) := by rw [min_mul_max]
    have hh := mul_le_mul_of_nonneg_left h3 (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) (sq_nonneg (U+1)))
    have he : min zm zp * (1/zm + 1/zp + 2*(U+1)^2*a/(zm*zp)) =
        min zm zp / zm + min zm zp / zp + 2*(U+1)^2 * (min zm zp*a/(zm*zp)) := by ring
    rw [he]
    nlinarith

  calc
    min zm zp * v^2 ≤ min zm zp * ((1/zm + 1/zp + 2*(U+1)^2*a/(zm*zp))*E) :=
      mul_le_mul_of_nonneg_left hv hmin
    _ = (min zm zp * (1/zm + 1/zp + 2*(U+1)^2*a/(zm*zp)))*E := by ring
    _ ≤ (2+2*d*(U+1)^2)*E := mul_le_mul_of_nonneg_right hcoef hE

end Contingency

end

end OAI
