import OAI.NumberTheory.Jacobsthal.Analysis.ContinuousReference
import OAI.NumberTheory.Jacobsthal.Primes.BoundaryPrimeStep
import OAI.NumberTheory.Jacobsthal.Primes.ReferenceSourcePrimeSets

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.DiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferencePruning ReferencePrefixRecurrence
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def D (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : ℝ :=
  ∑ ps ∈ (referencePrefixes w P i r).filter (fun ps => ps.length=n),prefixWeight ps

theorem D_nonneg (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : 0 ≤ D n w P i r :=
  Finset.sum_nonneg (fun ps _ => prefixWeight_nonneg ps)

theorem D_sum (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    D n w P i r=∑ ps ∈ decreasingPrefixes P,
      if admitted w i r ps ∧ ps.length=n then prefixWeight ps else 0 := by
  rw [D,referencePrefixes,Finset.filter_filter,Finset.sum_filter]

theorem D_zero (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) : D 0 w P i r=1 := by
  have he : (referencePrefixes w P i r).filter (fun ps => ps.length=0)={[]} := by
    ext ps
    simp only [Finset.mem_filter,List.length_eq_zero_iff,Finset.mem_singleton]
    constructor
    · exact fun h => h.2
    · intro hp
      subst ps
      refine ⟨Finset.mem_filter.mpr ⟨mem_decreasingPrefixes.mpr ⟨by simp,by simp⟩,trivial⟩,rfl⟩
  rw [D,he,Finset.sum_singleton]
  simp [prefixWeight]

theorem D_succ (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) :
    D (n+1) w P i r=∑ p ∈ P,if childAdmitted i r (primeExponent w p) then
      (p:ℝ)⁻¹*D n w (P.filter (fun q => q<p)) i.flip (r-primeExponent w p) else 0 := by
  rw [D_sum,sum_decreasing_by_first]
  have hempty : (if admitted w i r [] ∧ ([]:List ℕ).length=n+1 then prefixWeight [] else 0)=0 := by simp
  rw [hempty,zero_add]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hc : childAdmitted i r (primeExponent w p)
  · rw [ite_eq_left hc,D_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ps _hps
    simp only [admitted,hc,true_and,List.length_cons,Nat.add_right_cancel_iff]
    split_ifs <;> simp [prefixWeight]
  · simp [admitted,hc]

end NumberTheoryLean.DiscreteBoundaryTerms

end

section

namespace NumberTheoryLean.DiscreteBoundaryDepth

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission DiscreteBoundaryTerms
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.PrimePrefixTail ErdosPrimeInputs.HarmonicPrimeMeasure

theorem odd_gate_impossible {w r : ℝ} {p : ℕ} (hp : 1 < primeExponent w p) (hr : r ≤ 4) :
    ¬childAdmitted .odd r (primeExponent w p) := by
  intro h
  have hh := (le_max_right (2*primeExponent w p) (primeExponent w p+2)).trans h
  nlinarith

theorem odd_term_zero (n : ℕ) (w : ℝ) (P : Finset ℕ) {r : ℝ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ 4) : D (n+1) w P .odd r=0 := by
  rw [D_succ]
  apply Finset.sum_eq_zero
  intro p hp
  rw [ite_eq_right (odd_gate_impossible (hP p hp) hr)]

theorem D_two_zero (w : ℝ) (P : Finset ℕ) (i : Side) {r : ℝ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ 1) : D 2 w P i r=0 := by
  cases i with
  | odd => exact odd_term_zero 1 w P hP (by linarith)
  | even =>
    rw [show (2:ℕ)=1+1 from rfl,D_succ]
    apply Finset.sum_eq_zero
    intro p hp
    have ht : D 1 w (P.filter (fun q => q<p)) .odd (r-primeExponent w p)=0 :=
      odd_term_zero 0 w _ (fun q hq => hP q (Finset.mem_filter.mp hq).1) (by have hx := hP p hp; linarith)
    simp only [childAdmitted,ite_true,Side.flip,ht,mul_zero]

theorem D_vanish (n : ℕ) (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ)
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hr : r ≤ (n:ℝ)+1) : D (n+2) w P i r=0 := by
  induction n generalizing P i r with
  | zero => exact D_two_zero w P i hP (by simpa only [Nat.cast_zero,zero_add] using hr)
  | succ n ih =>
    rw [show n+1+2=(n+2)+1 by omega,D_succ]
    apply Finset.sum_eq_zero
    intro p hp
    have hx := hP p hp
    have hr' : r-primeExponent w p ≤ (n:ℝ)+1 := by
      push_cast at hr
      linarith
    have hz := ih (P:=P.filter (fun q => q<p)) (i:=i.flip) (r:=r-primeExponent w p)
      (fun q hq => hP q (Finset.mem_filter.mp hq).1) hr'
    simp only [hz,mul_zero,ite_self]

theorem prefixWeight_positive {w : ℝ} {P : Finset ℕ} {ps : List ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hm : ∀ p ∈ ps,p ∈ P) : 0 < prefixWeight ps := by
  induction ps with
  | nil => simp [prefixWeight]
  | cons p ps ih =>
    have hp := hP p (hm p (by simp))
    have hp0 : p ≠ 0 := by
      intro he
      simp only [he,primeExponent,Nat.cast_zero,Real.log_zero,zero_div] at hp
      linarith
    have hpr : 0 < (p:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp0
    have ht := ih (fun q hq => hm q (by simp [hq]))
    simpa only [prefixWeight,List.map_cons,List.prod_cons] using mul_pos (inv_pos.mpr hpr) ht

theorem D_positive_of_member {w r : ℝ} {P : Finset ℕ} {i : Side} {ps : List ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hp : ps ∈ referencePrefixes w P i r) :
    0 < D ps.length w P i r := by
  apply Finset.sum_pos' (fun qs _ => prefixWeight_nonneg qs)
  refine ⟨ps,Finset.mem_filter.mpr ⟨hp,rfl⟩,?_⟩
  exact prefixWeight_positive hP (mem_decreasingPrefixes.mp (Finset.mem_filter.mp hp).1).2

theorem admitted_length_lt {w r : ℝ} {P : Finset ℕ} {i : Side} {N : ℕ}
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1)
    {ps : List ℕ} (hp : ps ∈ referencePrefixes w P i r) : ps.length<N := by
  by_contra hn
  have hlen : N ≤ ps.length := le_of_not_gt hn
  have hlen2 : 2 ≤ ps.length := hN.trans hlen
  have he : ps.length-2+2=ps.length := Nat.sub_add_cancel hlen2
  have hcast : (N:ℝ) ≤ (ps.length:ℝ) := by exact_mod_cast hlen
  have hecast : ((ps.length-2:ℕ):ℝ)+2=(ps.length:ℝ) := by exact_mod_cast he
  have hr' : r ≤ ((ps.length-2:ℕ):ℝ)+1 := by linarith
  have hz := D_vanish (ps.length-2) w P i r hP hr'
  rw [he] at hz
  have hpos := D_positive_of_member hP hp
  rw [hz] at hpos
  linarith

end NumberTheoryLean.DiscreteBoundaryDepth

end

section

namespace NumberTheoryLean.DiscreteBoundaryExpansion

attribute [local instance] Classical.propDecidable
open _root_.Finset
open FinitePathGeometry ReferenceAdmission DiscreteBoundaryTerms DiscreteBoundaryDepth
open ErdosPrimeInputs.PrimePrefixMass ErdosPrimeInputs.HarmonicPrimeMeasure

theorem referencePolynomial_finite_sum (w : ℝ) (P : Finset ℕ) (i : Side) (r : ℝ) (N : ℕ)
    (hP : ∀ p ∈ P,1 < primeExponent w p) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1) :
    referencePolynomial w P i r=∑ n ∈ Finset.range N,(-1:ℝ)^n*D n w P i r := by
  have hmap : ∀ ps ∈ referencePrefixes w P i r,ps.length ∈ Finset.range N := by
    intro ps hp
    exact Finset.mem_range.mpr (admitted_length_lt hP hN hr hp)
  have hf := Finset.sum_fiberwise_of_maps_to (g:=List.length) hmap
    (fun ps : List ℕ => (-1:ℝ)^ps.length*prefixWeight ps)
  calc
    _ = ∑ n ∈ Finset.range N,∑ ps ∈ (referencePrefixes w P i r).filter (fun ps => ps.length=n),
        (-1:ℝ)^ps.length*prefixWeight ps := hf.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [D,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ps hp
      rw [(Finset.mem_filter.mp hp).2]

end NumberTheoryLean.DiscreteBoundaryExpansion

end

section

namespace NumberTheoryLean.ActualDiscreteBoundaryTerms

attribute [local instance] Classical.propDecidable

open _root_.Finset
open FinitePathGeometry ReferenceAdmission ReferenceProductsBasics ReferenceSourcePrimeSets
open DiscreteBoundaryTerms DiscreteBoundaryDepth DiscreteBoundaryExpansion
open ErdosPrimeInputs.HarmonicPrimeMeasure

noncomputable def actualD (n : ℕ) (w b : ℝ) (closed : Bool) (i : Side) (r : ℝ) : ℝ :=
  D n w (availablePrimes w (w^b) closed) i r

theorem actualD_zero (w b : ℝ) (closed : Bool) (i : Side) (r : ℝ) : actualD 0 w b closed i r=1 :=
  D_zero w _ i r

theorem selected_exponent_bounds {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) {p : ℕ}
    (hp : p ∈ availablePrimes w (w^b) closed) : 1 < primeExponent w p ∧ primeExponent w p ≤ b := by
  obtain ⟨_hp,hlo,hcap⟩ := (sourcePrimes_membership hw b closed p).mp hp
  refine ⟨hlo,?_⟩
  cases closed
  · exact hcap.le
  · exact hcap

theorem selected_available_set {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) {p : ℕ}
    (hp : p ∈ availablePrimes w (w^b) closed) :
    availablePrimes w (w^primeExponent w p) false=
      (availablePrimes w (w^b) closed).filter (fun q => q<p) :=
  sourcePrimes_at_selected hw closed hp

theorem actualD_succ (n : ℕ) {w : ℝ} (hw : 1 < w) (b : ℝ) (closed : Bool) (i : Side) (r : ℝ) :
    actualD (n+1) w b closed i r=
      ∑ p ∈ availablePrimes w (w^b) closed,if childAdmitted i r (primeExponent w p) then
        (p:ℝ)⁻¹*actualD n w (primeExponent w p) false i.flip (r-primeExponent w p) else 0 := by
  unfold actualD
  rw [D_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [selected_available_set hw b closed hp]

theorem boundary_exponent_bounds {w b : ℝ} (hw : 1 < w) (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) (closed : Bool) :
    ∀ p ∈ availablePrimes w (w^b) closed,1 < primeExponent w p ∧ primeExponent w p ≤ 2 := by
  intro p hp
  have h := selected_exponent_bounds hw b closed hp
  exact ⟨h.1,h.2.trans hb2⟩

theorem actualD_vanish (n : ℕ) {w b : ℝ} (hw : 1 < w) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) (hr : r ≤ (n:ℝ)+1) : actualD (n+2) w b closed i r=0 :=
  D_vanish n w _ i r (fun p hp => (boundary_exponent_bounds hw hb1 hb2 closed p hp).1) hr

theorem actual_reference_finite_sum {w b : ℝ} (hw : 1 < w) (hb1 : 1 ≤ b) (hb2 : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) (N : ℕ) (hN : 2 ≤ N) (hr : r ≤ (N:ℝ)-1) :
    referencePolynomial w (availablePrimes w (w^b) closed) i r=
      ∑ n ∈ Finset.range N,(-1:ℝ)^n*actualD n w b closed i r :=
  referencePolynomial_finite_sum w _ i r N (fun p hp => (boundary_exponent_bounds hw hb1 hb2 closed p hp).1) hN hr

end NumberTheoryLean.ActualDiscreteBoundaryTerms

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ReferenceSourcePrimeSets
open NumberTheoryLean.ActualDiscreteBoundaryTerms NumberTheoryLean.HarmonicPrimeAtomicMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem available_boundary_subset {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2) (closed : Bool) :
    availablePrimes w (w^b) closed ⊆ Nat.primesLE ⌊w^(2:ℝ)⌋₊ := by
  intro p hp
  have hpm := (sourcePrimes_membership hw b closed p).mp hp
  have hx := (selected_exponent_bounds hw b closed hp).2.trans hb
  have hpReal := (exponent_le_iff hw (by exact_mod_cast hpm.1.pos)).mp hx
  exact Nat.mem_primesLE.mpr ⟨(Nat.le_floor_iff (Real.rpow_pos_of_pos (by linarith : 0 < w) 2).le).mpr hpReal,hpm.1⟩

theorem boundary_gate_membership {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) {p : ℕ} (hp : p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊) :
    primeExponent w p ∈ boundaryGateSet i r b closed ↔
      p ∈ availablePrimes w (w^b) closed ∧ childAdmitted i r (primeExponent w p) := by
  have hprime := (Nat.mem_primesLE.mp hp).2
  constructor
  · intro h
    refine ⟨(sourcePrimes_membership hw b closed p).mpr ⟨hprime,h.1,?_⟩,h.2.2.2⟩
    exact h.2.2.1
  · rintro ⟨hP,hgate⟩
    have h := (sourcePrimes_membership hw b closed p).mp hP
    have hx2 := (selected_exponent_bounds hw b closed hP).2.trans hb
    exact ⟨h.2.1,hx2,h.2.2,hgate⟩

theorem available_gate_sum {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) (F : ℕ → ℝ) :
    (∑ p ∈ availablePrimes w (w^b) closed,if childAdmitted i r (primeExponent w p) then
      (p:ℝ)⁻¹*F p else 0) =
    ∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
      (p:ℝ)⁻¹*F p else 0 := by
  have hsub := available_boundary_subset hw hb closed
  calc
    _ = ∑ p ∈ availablePrimes w (w^b) closed,if primeExponent w p ∈ boundaryGateSet i r b closed then
        (p:ℝ)⁻¹*F p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have he : primeExponent w p ∈ boundaryGateSet i r b closed ↔ childAdmitted i r (primeExponent w p) := by
        rw [boundary_gate_membership hw hb closed i r (hsub hp)]
        simp only [hp,true_and]
      simp only [he]
    _ = _ := Finset.sum_subset hsub (by
      intro p hp hnot
      apply ite_eq_right
      intro hgate
      exact hnot ((boundary_gate_membership hw hb closed i r hp).mp hgate).1)

theorem actualD_succ_gate_sum (n : ℕ) {w b : ℝ} (hw : 1 < w) (hb : b ≤ 2)
    (closed : Bool) (i : Side) (r : ℝ) :
    actualD (n+1) w b closed i r =
      ∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then
        (p:ℝ)⁻¹*actualD n w (primeExponent w p) false i.flip (r-primeExponent w p) else 0 := by
  rw [actualD_succ n hw b closed i r]
  exact available_gate_sum hw hb closed i r _

theorem prime_gate_sum_difference (w : ℝ) (i : Side) (r b : ℝ) (closed : Bool)
    (F G : ℕ → ℝ) (A : ℝ)
    (hFG : ∀ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,primeExponent w p ∈ boundaryGateSet i r b closed → |F p-G p| ≤ A) :
    |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then (p:ℝ)⁻¹*F p else 0)-
      (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ boundaryGateSet i r b closed then (p:ℝ)⁻¹*G p else 0)| ≤
      A*(primeMeasure w 2).real (boundaryGateSet i r b closed) := by
  rw [primeMeasure_real w 2 (boundaryGateSet_orderConnected i r b closed).measurableSet,Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  by_cases hg : primeExponent w p ∈ boundaryGateSet i r b closed
  · rw [ite_eq_left hg,ite_eq_left hg,ite_eq_left hg,← mul_sub,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (p:ℝ)⁻¹)]
    have h := mul_le_mul_of_nonneg_left (hFG p hp hg) (by positivity : 0 ≤ (p:ℝ)⁻¹)
    simpa only [mul_comm] using h
  · simp only [hg,ite_false,sub_self,abs_zero,mul_zero,le_refl]

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry
open NumberTheoryLean.ActualDiscreteBoundaryTerms NumberTheoryLean.HarmonicPrimeAtomicMeasure
open ErdosPrimeInputs.HarmonicPrimeMeasure

theorem actualD_uniform_approximation : ∃ c C w₀ : ℝ,0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ (n : ℕ) (w : ℝ),w₀ ≤ w → ∀ (i : Side) (r b : ℝ) (closed : Bool),
      1 ≤ b → b ≤ 2 →
      |actualD n w b closed i r-boundaryTerm n i r b| ≤ 15*(n:ℝ)^2*boundaryPrimeError c C w := by
  obtain ⟨c,C,w₀,hc,hC,hw₀,hControl⟩ := boundary_prime_step_control
  refine ⟨c,C,w₀,hc,hC,hw₀,?_⟩
  intro n
  induction n with
  | zero =>
    intro w _hw i r b closed _hb1 _hb2
    rw [actualD_zero]
    norm_num [boundaryTerm]
  | succ n ih =>
    intro w hw i r b closed _hb1 hb2
    have hw1 : 1 < w := hw₀.trans_le hw
    obtain ⟨hMass,hStep⟩ := hControl w hw
    let E := boundaryPrimeError c C w
    have hE : 0 ≤ E := by dsimp [E,boundaryPrimeError]; positivity
    let A := 15*(n:ℝ)^2*E
    have hA : 0 ≤ A := by dsimp [A]; positivity
    let J := boundaryGateSet i r b closed
    let F : ℕ → ℝ := fun p => actualD n w (primeExponent w p) false i.flip (r-primeExponent w p)
    let G : ℕ → ℝ := fun p => boundaryTerm n i.flip (r-primeExponent w p) (primeExponent w p)
    have hFG : ∀ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,primeExponent w p ∈ J → |F p-G p| ≤ A := by
      intro p _hp hJ
      exact ih w hw i.flip (r-primeExponent w p) (primeExponent w p) false hJ.1.le hJ.2.1
    have hsum := prime_gate_sum_difference w i r b closed F G A hFG
    have hM : (primeMeasure w 2).real J ≤ 1 :=
      (measureReal_mono (boundaryGateSet_subset i r b closed)).trans hMass
    have hsum' :
        |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-
          (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0)| ≤ A := by
      exact hsum.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hA)
    have hstep := hStep n i r b closed
    have heq := actualD_succ_gate_sum n hw1 hb2 closed i r
    rw [heq]
    calc
      _ ≤ A+(12*(n:ℝ)+15)*E := by
        have he :
            (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-boundaryTerm (n+1) i r b =
            ((∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-
              (∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0))+
            ((∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*G p else 0)-boundaryTerm (n+1) i r b) := by ring
        change |(∑ p ∈ Nat.primesLE ⌊w^(2:ℝ)⌋₊,if primeExponent w p ∈ J then (p:ℝ)⁻¹*F p else 0)-boundaryTerm (n+1) i r b| ≤ _
        rw [he]
        exact (abs_add_le _ _).trans (add_le_add hsum' hstep)
      _ = (15*(n:ℝ)^2+(12*(n:ℝ)+15))*E := by dsimp [A]; ring
      _ ≤ 15*((n+1:ℕ):ℝ)^2*E := by
        apply mul_le_mul_of_nonneg_right _ hE
        push_cast
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]

end ErdosContinuousBoundary

end

section

open _root_.MeasureTheory _root_.Set _root_.Finset _root_.Filter
open scoped Topology
namespace ErdosContinuousBoundary
attribute [local instance] Classical.propDecidable
open NumberTheoryLean.FinitePathGeometry NumberTheoryLean.ReferenceAdmission
open NumberTheoryLean.ReferenceProductsBasics NumberTheoryLean.ActualDiscreteBoundaryTerms

theorem finite_reference_error {c C w : ℝ} (hC : 0 ≤ C) (hw : 1 < w)
    (hterms : ∀ (n : ℕ) (i : Side) (r b : ℝ) (closed : Bool),1 ≤ b → b ≤ 2 →
      |actualD n w b closed i r-boundaryTerm n i r b| ≤ 15*(n:ℝ)^2*boundaryPrimeError c C w)
    (N : ℕ) (hN : 2 ≤ N) (i : Side) (r b : ℝ) (closed : Bool)
    (hr : r ≤ (N:ℝ)-1) (hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    |referencePolynomial w (availablePrimes w (w^b) closed) i r-boundaryReference i r b| ≤
      15*(N:ℝ)^3*boundaryPrimeError c C w := by
  rw [actual_reference_finite_sum hw hb1 hb2 closed i r N hN hr,
    boundaryReference_eq_truncated N hN i hr,truncatedReference,← Finset.sum_sub_distrib]
  have hE : 0 ≤ boundaryPrimeError c C w := by unfold boundaryPrimeError; positivity
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        |(-1:ℝ)^n*actualD n w b closed i r-(-1:ℝ)^n*boundaryTerm n i r b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ Finset.range N,15*(N:ℝ)^2*boundaryPrimeError c C w := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← mul_sub,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      apply (hterms n i r b closed hb1 hb2).trans
      have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
      gcongr
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]; ring

theorem uniform_boundary_reference_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r b : ℝ) (closed : Bool),
      r ≤ R → 1 ≤ b → b ≤ 2 →
      |referencePolynomial w (availablePrimes w (w^b) closed) i r-boundaryReference i r b| ≤ eps := by
  obtain ⟨c,C,wD,hc,hC,hwD,hD⟩ := actualD_uniform_approximation
  let N := referenceDepth R
  have hN : 2 ≤ N := (referenceDepth_bounds R).1
  have hdepth : R ≤ (N:ℝ)-1 := (referenceDepth_bounds R).2
  have ht := (boundaryPrimeError_tendsto_zero hc C).const_mul (15*(N:ℝ)^3)
  have he := ht.eventually (Iio_mem_nhds (by simpa only [mul_zero] using heps))
  obtain ⟨wE,hwE⟩ := eventually_atTop.mp he
  refine ⟨max wD wE,hwD.trans_le (le_max_left _ _),?_⟩
  intro w hw i r b closed hr hb1 hb2
  have hwd : wD ≤ w := (le_max_left _ _).trans hw
  have hwe := hwE w ((le_max_right _ _).trans hw)
  have hh := finite_reference_error hC.le (hwD.trans_le hwd)
    (fun n j s a cl ha1 ha2 => hD n w hwd j s a cl ha1 ha2)
    N hN i r b closed (hr.trans hdepth) hb1 hb2
  exact hh.trans hwe.le

theorem boundary_two_convergence (R eps : ℝ) (heps : 0 < eps) :
    ∃ w₀ : ℝ,1 < w₀ ∧ ∀ w : ℝ,w₀ ≤ w → ∀ (i : Side) (r : ℝ),r ≤ R →
      |referencePolynomial w (boundaryPrimes w) i r-boundaryReference i r 2| ≤ eps := by
  obtain ⟨w₀,hw₀,h⟩ := uniform_boundary_reference_convergence R eps heps
  refine ⟨w₀,hw₀,?_⟩
  intro w hw i r hr
  simpa only [availablePrimes_closed,boundaryPrimes] using h w hw i r 2 true hr (by norm_num) le_rfl

end ErdosContinuousBoundary

end

end Erdos970

end OAI
