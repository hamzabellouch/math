import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.LabelOrder
import OAI.Combinatorics.MatchingCount.Machines.TreeLabelTable
import OAI.Combinatorics.MatchingCount.Machines.TreeSlotWeight

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

abbrev PowerSearchInput := (Fraction×Fraction)×List Bool

def powerCandidate (x : PowerSearchInput×ℕ) : Bool :=
  !(TreeFraction.less (fuelPower (x.1.1.1,x.1.2.take x.2),x.1.1.2))
def powerCandidateRealizer : Realizer powerCandidate :=
  (composition (composition (pair
    (composition (pair first.fst.fst (composition (pair first.snd second) takeFast)) fuelPowerRealizer)
    first.fst.snd) lessRealizer) boolNot).congr (fun _=>rfl)
lemma polynomial_powerCandidate : PolynomialTime powerCandidateRealizer := by
  unfold powerCandidateRealizer; apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair
      (polynomial_composition
        (polynomial_pair (polynomial_fst (polynomial_fst polynomial_first))
          (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) polynomial_second)
            polynomial_takeFast)) polynomial_fuelPower)
      (polynomial_snd (polynomial_fst polynomial_first))) TreeFraction.polynomial_less) polynomial_boolNot

def findPower (x : PowerSearchInput) : ℕ :=
  listMin ((List.range (x.2.length+1)).filter (fun i=>powerCandidate (x,i)),x.2.length)
def findPowerRealizer : Realizer findPower := by
  let B : Realizer (fun x : PowerSearchInput=>x.2.length) := composition second listLength
  let R := composition (composition B successor) range
  let F := composition (pair identity R) (filterWith powerCandidateRealizer)
  exact (composition (pair F B) listMinRealizer).congr (fun _=>rfl)
lemma polynomial_findPower : PolynomialTime findPowerRealizer := by
  unfold findPowerRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_listMin
  apply polynomial_pair _ (polynomial_composition polynomial_second polynomial_listLength)
  apply polynomial_composition _ (polynomial_filterWithList polynomial_powerCandidate)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength) polynomial_successor)
    (X+1)
  intro x
  have h:=list_length_le_weight x.2
  change x.2.length+1≤(X+1).eval (weight x)
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  rw [weight_prod]
  omega
lemma powerCandidate_repr (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length) :
    powerCandidate (((repr a,repr b),fuel),i)=decide (b≤a^i) := by
  unfold powerCandidate
  rw [fuelPower_repr a ha,List.length_take,min_eq_left hi]
  rw [less_val _ _ (a^i).pos b.pos,
    val_repr (by positivity),val_repr hb]
  apply Bool.eq_iff_iff.mpr
  simp
lemma findPower_le_fuel (x : PowerSearchInput) : findPower x≤x.2.length :=
  listMin_le_default _ _
lemma findPower_le (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length) (hr : b ≤ a ^ i) : findPower ((repr a, repr b), fuel) ≤ i := by
  apply listMin_le
  simp only [List.mem_filter,List.mem_range,powerCandidate_repr a b ha hb fuel i hi,
    decide_eq_true_eq]
  exact ⟨by omega,hr⟩
lemma le_findPower (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length)
    (hmin : ∀ j,j≤fuel.length→b≤a^j→i≤j) : i≤findPower ((repr a,repr b),fuel) := by
  apply le_listMin hi
  intro j hj
  simp only [List.mem_filter,List.mem_range] at hj
  have hj' : j≤fuel.length := by omega
  rw [powerCandidate_repr a b ha hb fuel j hj',decide_eq_true_eq] at hj
  exact hmin j hj' hj.2
lemma findPower_eq (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (T : ℕ)
    (hT : T≤fuel.length) (hr : b≤a^T) (hmin : ∀ j,b≤a^j→T≤j) :
    findPower ((repr a,repr b),fuel)=T :=
  Nat.le_antisymm (findPower_le a b ha hb fuel T hT hr)
    (le_findPower a b ha hb fuel T hT (fun j _ hj=>hmin j hj))

lemma endpoint_le_bound (N D K : ℕ) (hN : 0<N) :
    Transport.endpoint N D K hN≤Transport.tierBound N D K := by
  rw [Transport.endpoint_eq]
  exact Transport.ladderTier_le N D K hN
lemma endpoint_power_spec (N D K : ℕ) (hN : 0<N) :
    max (D:ℚ) (3*4^K)≤(Transport.rationalBase N)^(Transport.endpoint N D K hN) := by
  have h:=Transport.endpoint_reaches N D K hN
  rw [←Transport.rationalBase_cast] at h
  exact_mod_cast h
lemma endpoint_power_min (N D K : ℕ) (hN : 0<N) (t : ℕ)
    (ht : max (D:ℚ) (3*4^K)≤(Transport.rationalBase N)^t) :
    Transport.endpoint N D K hN≤t := by
  rw [Transport.endpoint_eq]
  apply Nat.find_min'
  rw [←Transport.rationalBase_cast]
  exact_mod_cast ht
lemma findPower_endpoint (N D K : ℕ) (hN : 0<N) (fuel : List Bool)
    (hf : Transport.tierBound N D K≤fuel.length) :
    findPower ((repr (Transport.rationalBase N),repr (max (D:ℚ) (3*4^K))),fuel)=
      Transport.endpoint N D K hN := by
  apply findPower_eq
  · unfold Transport.rationalBase; positivity
  · positivity
  · exact (endpoint_le_bound N D K hN).trans hf
  · exact endpoint_power_spec N D K hN
  · exact endpoint_power_min N D K hN
end MatchingFPRAS.OnlineSchedule

end OAI
