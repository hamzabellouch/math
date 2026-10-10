import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.HighPairVariance
import OAI.Combinatorics.RamseyFive.Marking.MarkingClassDomains
import OAI.Combinatorics.RamseyFive.Entropy.HighEndpointCutoffs

namespace OAI

namespace SharpRamseyFive.Marking

section
open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open SharpRamseyFive.CoreGeometry SharpRamseyFive.LowConflict
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  {n : ℕ}

def highThreeLeft (p : Law (FlagPair K V)) (s : ℝ) : Finset (ℙ K V) :=
  highGoodFirst p (32*(Nat.card K:ℝ)^3) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^3) s
def highThreeRight (p : Law (FlagPair K V)) (s : ℝ) : Finset (ℙ K (Dual K V)) :=
  highGoodFirst (swap p) (32*(Nat.card K:ℝ)^3) ((Nat.card K:ℝ)^4) ((Nat.card K:ℝ)^3) s
def highThreeGood (p : Law (Fin n→FlagPair K V)) (s : ℝ)
    (i j : Fin n) (a : ℙ K V) (b : ℙ K (Dual K V)) : Prop :=
  a∈highThreeLeft (tupleMarginal p i) s ∧ b∈highThreeRight (tupleMarginal p j) s ∧ Incident a b

def highCollision (p : Law (Fin n→FlagPair K V)) (s : ℝ) (i j : Fin n) : ℝ :=
  tupleCollision p Projectivization.rep Projectivization.rep (highThreeGood p s) i j

omit [Finite K] [FiniteDimensional K V] in
lemma high_collision_nonneg (p : Law (Fin n→FlagPair K V)) (s : ℝ) (i j : Fin n) :
    0≤highCollision p s i j := tupleCollision_nonneg ..

lemma high_three_core_slack (s : ℝ) (hsmall : Real.log 32+3*s<Real.log (Nat.card K)) :
    Real.log (32*(Nat.card K:ℝ)^3)+3*s<(6-(2:ℝ))*Real.log (Nat.card K) := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  rw [Real.log_mul (by norm_num) (ne_of_gt (pow_pos hq 3)),Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem high_three_collisions (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s M : ℝ) (hs : 2 ≤ s)
    (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀ x,0<p x→TupleIncident x)
    (hocc : ∀ x,0<p x→∀ S : Submodule K (Dual K V),
      (∑ i,if InRectangle S (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    (∑ i,∑ j,highCollision p s i j)≤2*n*M := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  apply high_tuple_collision_bound hdim p Projectivization.rep Projectivization.rep (highThreeGood p s) M
  · intro x hx i
    exact (incident_iff _ _).mp (hinc x hx i)
  · intro i j a y hg
    obtain ⟨ha,hb,hi⟩:=hg
    have ha':= (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).1
    have hb':= (Finset.mem_filter.mp (show y∈highGoodFirst _ _ _ _ _ from hb)).1
    refine ⟨goodFirst_positive _ _ _ _ (by positivity) a ha',?_,(incident_iff _ _).mp hi⟩
    simpa only [first_swap] using (goodFirst_positive (swap (tupleMarginal p j)) _ _ _ (by positivity) y hb')
  · intro i j a y hg
    apply goodFirst_integer_rank hdim (tupleMarginal p i) _ s (by positivity) hs 2
      (high_three_core_slack s hsmall) a
    exact (Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from hg.1)).1
  · intro i j a y hg
    apply goodSecond_integer_rank hdim (tupleMarginal p j) _ s (by positivity) hs 2
      (high_three_core_slack s hsmall) y
    exact (Finset.mem_filter.mp (show y∈highGoodFirst _ _ _ _ _ from hg.2.1)).1
  · exact hocc

omit [Finite K] in
lemma high_three_low_conflict (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j) :
    relationMass (highThreeGood p s i j) (first (tupleMarginal p i)) (second (tupleMarginal p j))≤
      80004*(entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
        entropy (pair p (fun x=>x i) (fun x=>x j))+highCollision p s i j) := by
  apply tuple_low_conflict hdim p Projectivization.rep Projectivization.rep (highThreeGood p s) ?_ i j hij
  intro x hx i j hij hg
  exact (incident_iff _ _).mp (hcons x hx i j hij hg.2.2)

theorem high_three_pair_impossible (hdim : finrank K V=5)
    (p : Law (Fin n→FlagPair K V)) (s ε : ℝ)
    (hcons : ∀ x,0<p x→TupleConsistent x) (i j : Fin n) (hij : i<j)
    (hA : (3:ℝ)/4≤eventMass (first (tupleMarginal p i)) (highThreeLeft (tupleMarginal p i) s))
    (hB : (3:ℝ)/4≤eventMass (second (tupleMarginal p j)) (highThreeRight (tupleMarginal p j) s))
    (hvar : 64*(Nat.card K:ℝ)^5*(Real.exp s/(Nat.card K:ℝ)^3)*(Real.exp s/(Nat.card K:ℝ)^3)≤(1:ℝ)/4)
    (hgood : entropy (tupleMarginal p i)+entropy (tupleMarginal p j)-
      entropy (pair p (fun x=>x i) (fun x=>x j))+highCollision p s i j≤ε)
    (hsmall : 80004*ε<1/(8*(Nat.card K:ℝ))) : False := by
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  have hl:=high_pair_incident_lower hdim (first (tupleMarginal p i)) (second (tupleMarginal p j))
    _ _ (Real.exp s/(Nat.card K:ℝ)^3) (Real.exp s/(Nat.card K:ℝ)^3) (by positivity) (by positivity)
    (by
      intro a ha
      have hh:=(Finset.mem_filter.mp (show a∈highGoodFirst _ _ _ _ _ from ha)).2
      exact (le_div_iff₀ (pow_pos hq 3)).mpr (by simpa only [mul_comm] using hh))
    (by
      intro b hb
      have hh:=(Finset.mem_filter.mp (show b∈highGoodFirst _ _ _ _ _ from hb)).2
      rw [first_swap] at hh
      exact (le_div_iff₀ (pow_pos hq 3)).mpr (by simpa only [mul_comm] using hh)) hA hB hvar
  have hu:=high_three_low_conflict hdim p s hcons i j hij
  exact (hl.trans (hu.trans (mul_le_mul_of_nonneg_left hgood (by norm_num)))).not_gt hsmall
end
end

open Module SharpRamseyFive.ProjectiveIncidence SharpRamseyFive.FiniteEntropy
open scoped Classical LinearAlgebra.Projectivization BigOperators
noncomputable section
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] {N : ℕ}
local instance highMarkedDE : DecidableEq (ℙ K V) := Classical.decEq _
local instance highMarkedDualDE : DecidableEq (ℙ K (Dual K V)) := Classical.decEq _

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem marking_high_endpoint_bad (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (p : Law (FlagPair K V)) (hD : support p ⊆ markingDomain m i)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true)
    (s d : ℝ) (hs : 0<s) (hent : 4*Real.log (Nat.card K)-entropy p≤d) :
    eventMass (first p) (highGoodFirst p
      (32*(Nat.card K:ℝ)^(m.1 i).1.1.2.val) ((Nat.card K:ℝ)^4)
      ((Nat.card K:ℝ)^(m.1 i).1.1.2.val) s)ᶜ≤highBadMass s d 153 ∧
    eventMass (second p) (highGoodFirst (swap p)
      (32*(Nat.card K:ℝ)^(m.1 i).1.1.1.val) ((Nat.card K:ℝ)^4)
      ((Nat.card K:ℝ)^(m.1 i).1.1.1.val) s)ᶜ≤highBadMass s d 153 := by
  have hne : (markingDomain m i).Nonempty := by
    have hp0 : 0<∑ z,p z := by rw [p.sum_one]; norm_num
    obtain ⟨z,hz,hpos⟩:=(Finset.sum_pos_iff_of_nonneg (fun z _=>p.nonneg z)).mp hp0
    exact ⟨z,hD ((mem_support p z).mpr hpos)⟩
  have hc:=marking_popular_caps hdim m i hne hp hp'
  have hq : 0<(Nat.card K:ℝ) := by exact_mod_cast Nat.zero_lt_of_lt (Finite.one_lt_card (α:=K))
  constructor
  · apply high_endpoint_bad_of_domain p (markingDomain m i) hD (Nat.card K) s d 153
      (m.1 i).1.1.2.val hq hs (by have := (m.1 i).1.1.2.isLt; omega)
      hc.2.2.1 (markingDomain_card hdim m i) (marking_popular_partners_first hdim m i hp') hent
  · apply high_endpoint_bad_second_of_domain p (markingDomain m i) hD (Nat.card K) s d 153
      (m.1 i).1.1.1.val hq hs (by have := (m.1 i).1.1.1.isLt; omega)
      hc.2.2.2 (markingDomain_card hdim m i) (marking_popular_partners_second hdim m i hp) hent

omit [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] in
lemma marking_high_three_mass (hdim : finrank K V=5)
    (m : UnionTranscript (Fin N) (FlagPair K V)) (i : Fin N)
    (p : Law (FlagPair K V)) (hD : support p ⊆ markingDomain m i)
    (hp : (m.1 i).1.2.1=true) (hp' : (m.1 i).1.2.2=true)
    (hr : (m.1 i).1.1.1.val=3) (hr' : (m.1 i).1.1.2.val=3)
    (s d : ℝ) (hs : 0<s) (hent : 4*Real.log (Nat.card K)-entropy p≤d)
    (hsmall : highBadMass s d 153≤(1:ℝ)/4) :
    (3:ℝ)/4≤eventMass (first p) (highThreeLeft p s) ∧
      (3:ℝ)/4≤eventMass (second p) (highThreeRight p s) := by
  have h:=marking_high_endpoint_bad hdim m i p hD hp hp' s d hs hent
  rw [hr,hr'] at h
  constructor
  · exact high_endpoint_mass p (Nat.card K) s d 153 3 h.1 hsmall
  · have hcomp:=eventMass_complement (second p) (highThreeRight p s)
    change eventMass (first p) (highThreeLeft p s)ᶜ≤highBadMass s d 153 ∧
      eventMass (second p) (highThreeRight p s)ᶜ≤highBadMass s d 153 at h
    linarith [h.2]
end

end SharpRamseyFive.Marking

end OAI
