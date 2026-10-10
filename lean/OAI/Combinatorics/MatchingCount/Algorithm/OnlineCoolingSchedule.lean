import Mathlib
import OAI.Combinatorics.MatchingCount.Algorithm.EmpiricalDenom
import OAI.Combinatorics.MatchingCount.Complexity.TreeNumericCosts
import OAI.Combinatorics.MatchingCount.Algorithm.OnlinePowerSearch
import OAI.Combinatorics.MatchingCount.Arithmetic.OnlineFractionParam

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

def fuelRealizer : Realizer (fun n : ℕ=>List.replicate n false) :=
  (composition range (map (constant false))).congr (by intro n; simp)
lemma fuel_numeric_work : WorkBound fuelRealizer id :=
  work_congr _ (work_then_polynomial range_numeric_work (polynomial_map (polynomial_constant false)))
lemma work_fuelAfter {A : Type} [Codec A] {f : A→ℕ} {F : Realizer f} {m : A→ℕ}
    (hF : WorkBound F m) (p : Polynomial ℕ) (hf : ∀ a,f a≤p.eval (m a)) :
    WorkBound (composition F fuelRealizer) m := work_composition hF fuel_numeric_work p hf

abbrev CoolingInput := ℕ×Fraction
def scheduleBound (x : CoolingInput) : ℕ := x.1*(x.1*x.1+32*natCeil (inverse x.2))
def scheduleBoundRealizer : Realizer scheduleBound :=
  (first.mulNat ((first.mulNat first).addNat
    ((constant 32).mulNat (composition (composition second inverseRealizer) natCeilRealizer)))).congr (fun _=>rfl)
lemma polynomial_scheduleBound : PolynomialTime scheduleBoundRealizer := by
  unfold scheduleBoundRealizer; apply polynomial_congr
  have := polynomial_inverse
  have := polynomial_natCeil
  simp only [Realizer.addNat,Realizer.mulNat]
  tree_cost
lemma scheduleBound_repr (n : ℕ) (e : ℚ) (he : 0≤e) :
    scheduleBound (n,TreeFraction.repr e)=Counting.schedulePolynomial n e := by
  unfold scheduleBound Counting.schedulePolynomial
  rw [inverse_repr e he,natCeil_repr _ (by positivity)]

abbrev CoolingPowerInput := CoolingInput×List Bool
def coolingPowerPlan (x : CoolingPowerInput) : Fraction×Fraction :=
  (TreeFraction.add ((1,1),TreeFraction.div ((1,1),(x.1.1,1))),
    TreeFraction.div (TreeFraction.mul ((32,1),fuelPower ((x.1.1,1),x.2)),x.1.2))
def coolingPowerPlanRealizer : Realizer coolingPowerPlan :=
  (pair (composition (pair (constant (1,1))
    (composition (pair (constant (1,1)) (pair first.fst (constant 1))) divRealizer)) addRealizer)
    (composition (pair (composition (pair (constant (32,1))
      (composition (pair (pair first.fst (constant 1)) second) fuelPowerRealizer)) mulRealizer)
      first.snd) divRealizer)).congr (fun _=>rfl)
lemma polynomial_coolingPowerPlan : PolynomialTime coolingPowerPlanRealizer := by
  unfold coolingPowerPlanRealizer; apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_div
  have := polynomial_mul
  have := TreeFraction.polynomial_add
  have := polynomial_fuelPower
  tree_cost
lemma coolingPowerPlan_repr (n : ℕ) (e : ℚ) (he : 0≤e) (fuel : List Bool) :
    coolingPowerPlan ((n,TreeFraction.repr e),fuel)=
      (TreeFraction.repr (1+1/(n:ℚ)),TreeFraction.repr (32*(n:ℚ)^fuel.length/e)) := by
  unfold coolingPowerPlan
  rw [←repr_nat n,show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    show ((32,1) : Fraction)=TreeFraction.repr (32:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    fuelPower_repr _ (by positivity),mul_repr (by decide) (by positivity),
    div_repr (by positivity) he]

def coolingSearchInput (x : CoolingInput) : PowerSearchInput :=
  (coolingPowerPlan (x,List.replicate (x.1/2) false),List.replicate (scheduleBound x) false)
def coolingSearchInputRealizer : Realizer coolingSearchInput :=
  pair (composition (pair identity (composition (composition (pair first (constant 2)) quotient) fuelRealizer))
    coolingPowerPlanRealizer) (composition scheduleBoundRealizer fuelRealizer)
def coolingSchedule (x : CoolingInput) : ℕ := findPower (coolingSearchInput x)
def coolingScheduleRealizer : Realizer coolingSchedule := composition coolingSearchInputRealizer findPowerRealizer

def coolingMeasure (x : CoolingInput) : ℕ := x.1+natCeil (inverse x.2)+weight x
lemma weight_le_coolingMeasure (x : CoolingInput) : weight x≤coolingMeasure x := by unfold coolingMeasure; omega
lemma work_coolingSearchInput : WorkBound coolingSearchInputRealizer coolingMeasure := by
  have lift {A : Type} [Codec A] {f : CoolingInput→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F coolingMeasure := work_of_polynomial hF X (fun x=>by simpa using weight_le_coolingMeasure x)
  have hp {A B : Type} [Codec A] [Codec B] {f : CoolingInput→A} {g : CoolingInput→B}
      {F : Realizer f} {G : Realizer g} (hF : WorkBound F coolingMeasure) (hG : WorkBound G coolingMeasure) :
      WorkBound (pair F G) coolingMeasure := work_pair hF hG X (fun x=>by simpa using weight_le_coolingMeasure x)
  unfold coolingSearchInputRealizer
  apply hp
  · apply work_then_polynomial _ polynomial_coolingPowerPlan
    apply hp (lift polynomial_identity)
    apply work_fuelAfter (lift (polynomial_composition
      (polynomial_pair polynomial_first (polynomial_constant 2)) polynomial_quotient)) X
    intro x
    have h:=Nat.div_le_self x.1 2
    simp only [Polynomial.eval_X,Function.comp_apply]
    unfold coolingMeasure
    omega
  · apply work_fuelAfter (lift polynomial_scheduleBound) (X*(X*X+32*X))
    intro x
    have hn : x.1≤coolingMeasure x := by unfold coolingMeasure; omega
    have he : natCeil (inverse x.2)≤coolingMeasure x := by unfold coolingMeasure; omega
    simp only [scheduleBound,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_add,Polynomial.eval_ofNat]
    gcongr
lemma work_coolingSchedule : WorkBound coolingScheduleRealizer coolingMeasure :=
  work_then_polynomial work_coolingSearchInput polynomial_findPower

lemma schedule_power_iff (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) (k : ℕ) :
    Counting.scheduleAdmissible n e k ↔ 32*(n:ℚ)^(n/2)/e≤(1+1/(n:ℚ))^k := by
  have hn0 : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hb : (0:ℚ)<1+1/(n:ℚ) := by positivity
  have hp : (0:ℚ)<(1+1/(n:ℚ))^k := pow_pos hb _
  have hn1 : (1:ℚ)≤(n:ℚ)^(n/2) := one_le_pow₀ (by exact_mod_cast (show 1≤n by omega))
  unfold Counting.scheduleAdmissible
  constructor
  · rintro ⟨_,h⟩
    apply (div_le_iff₀ he).mpr
    have h':=(div_le_iff₀ hp).mp h
    nlinarith
  · intro h
    have h':=(div_le_iff₀ he).mp h
    constructor
    · by_contra hk
      have hk0 : k=0 := by omega
      rw [hk0,pow_zero,one_mul] at h'
      linarith
    · apply (div_le_iff₀ hp).mpr
      nlinarith
lemma coolingSchedule_eq (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    coolingSchedule (n,TreeFraction.repr e)=Counting.leastSchedule n hn e he he1 := by
  unfold coolingSchedule coolingSearchInput
  rw [coolingPowerPlan_repr n e he.le,List.length_replicate,scheduleBound_repr n e he.le]
  apply findPower_eq
  · positivity
  · positivity
  · simpa using Counting.leastSchedule_polynomial n hn e he he1
  · exact (schedule_power_iff n hn e he he1 _).mp (Counting.leastSchedule_spec n hn e he he1)
  · intro k hk
    exact Counting.leastSchedule_le n hn e he he1 k ((schedule_power_iff n hn e he he1 k).mpr hk)
end MatchingFPRAS.OnlineSchedule

end OAI
