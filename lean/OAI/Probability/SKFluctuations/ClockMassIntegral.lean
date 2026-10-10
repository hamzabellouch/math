import Mathlib
import OAI.Probability.SKFluctuations.ClockZeroRefinement

namespace OAI

/-! Clock Mass Integral. -/

noncomputable section


namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 def massStepFunction : List PositiveMass → (ℕ → ℝ) → ℝ → ℝ
  | [],q,_ => q 0
  | a::as,q,u => if u<a.val then q 0 else massStepFunction as (fun j => q (j+1)) u

 theorem massStepFunction_intervalIntegrable (as : List PositiveMass) (q : ℕ → ℝ)
    (a b : ℝ) : IntervalIntegrable (massStepFunction as q) volume a b := by
  classical
  induction as generalizing q with
  | nil => exact intervalIntegrable_const
  | cons c cs ih =>
    rw [intervalIntegrable_iff]
    exact Integrable.piecewise measurableSet_Iio
      ((intervalIntegrable_const (a := a) (b := b) (μ := volume) (c := q 0)).def'.integrableOn)
      ((ih (fun j => q (j+1))).def'.integrableOn)

 theorem massStepFunction_integral (as : List PositiveMass) (a : ℝ) (q : ℕ → ℝ)
    (ho : MassOrdered a as) :
    (∫ u in a..1, massStepFunction as q u) = massStepSum as a q := by
  induction as generalizing a q with
  | nil => simp [massStepFunction,massStepSum,intervalIntegral.integral_const]
  | cons b bs ih =>
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (massStepFunction_intervalIntegrable (b::bs) q a b.val)
      (massStepFunction_intervalIntegrable (b::bs) q b.val 1)]
    have h₀ : (∫ u in a..b.val, massStepFunction (b::bs) q u) = (b.val-a)*q 0 := by
      calc
        _ = ∫ _ in a..b.val, q 0 := intervalIntegral.integral_congr_Ioo_of_le ho.2.1
          (fun u hu => by simp only [massStepFunction,ite_eq_left hu.2])
        _ = _ := by simp [intervalIntegral.integral_const]
    have h₁ : (∫ u in b.val..1, massStepFunction (b::bs) q u) =
        ∫ u in b.val..1, massStepFunction bs (fun j => q (j+1)) u := by
      exact intervalIntegral.integral_congr_Ioo_of_le (massOrdered_bounds ho.2.2).2
        (fun u hu => by simp only [massStepFunction,ite_eq_right (not_lt.mpr hu.1.le)])
    rw [h₀,h₁,ih b.val _ ho.2.2]
    rfl

 theorem massStepFunction_abs_sub (as : List PositiveMass) (q r : ℕ → ℝ) (u : ℝ) :
    |massStepFunction as q u-massStepFunction as r u| =
      massStepFunction as (fun j => |q j-r j|) u := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih => simp only [massStepFunction]; split_ifs <;> simp only [ih]

 theorem boundaryCost_append_one (a : PositiveMass) (as : List PositiveMass)
    (q r : ℕ → ℝ) (ho : MassOrdered a.val as) :
    boundaryCost ((a::as)++[⟨1,by norm_num⟩]) q r =
      massStepSum as a.val (fun j => |q j-r j|) := by
  induction as generalizing a q r with
  | nil =>
    simp only [List.cons_append,List.nil_append,boundaryCost,massStepSum,add_zero]
    rw [abs_of_nonpos (sub_nonpos.mpr ho.2)]
    ring
  | cons b bs ih =>
    simp only [List.cons_append,boundaryCost]
    have ht := ih b (fun j => q (j+1)) (fun j => r (j+1)) ho.2.2
    simp only [List.cons_append] at ht
    rw [ht,abs_of_nonpos (sub_nonpos.mpr ho.2.1)]
    simp only [massStepSum]
    ring

 theorem rootBoundaryCost_eq_integral (as : List PositiveMass) (q r : ℕ → ℝ)
    (ho : MassOrdered 0 as) :
    rootBoundaryCost (as++[⟨1,by norm_num⟩]) q r =
      ∫ u in (0:ℝ)..1, |massStepFunction as q u-massStepFunction as r u| := by
  simp_rw [massStepFunction_abs_sub]
  rw [massStepFunction_integral as 0 _ ho]
  cases as with
  | nil => simp [rootBoundaryCost,boundaryCost,massStepSum]
  | cons a as =>
    simp only [List.cons_append,rootBoundaryCost]
    have ht := boundaryCost_append_one a as (fun j => q (j+1))
      (fun j => r (j+1)) ho.2.2
    simp only [List.cons_append] at ht
    rw [ht]
    simp only [massStepSum,sub_zero]

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]

 theorem ClockTree.edgeBudget_eq_massStepSum (as : List PositiveMass) (a : ℝ) (f : ℕ → ℝ) :
    ClockTree.edgeBudget a as f=massStepSum as a f := by
  induction as generalizing a f with
  | nil => rfl
  | cons b as ih =>
    simp only [ClockTree.edgeBudget,massStepSum,ih,Nat.add_comm]

 theorem ClockTree.pairDisorder_cumulative_comparison {w : S → ℝ}
    (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (j : ℕ) (P : S → S → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hP : ∀ σ τ, |P σ τ| ≤ C)
    (v : ι → ℝ) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hq₀ : ∀ i, v i ≤ q 0 i) (hr₀ : ∀ i, v i ≤ r 0 i)
    {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j)
    (hE : ∀ j σ τ, |ReplicaTree.coordinateProfile φ (fun j i => r j i-q j i) j σ τ| ≤ f j)
    (x : ι → ℝ) :
    |(ClockTree.pairClock as j).disorderExpect w φ v q
        (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) x -
      (ClockTree.pairClock as j).disorderExpect w φ v r
        (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) x| ≤
      ClockTree.errorJetVariation 2 0 0*C*
        (f (min j as.length)+(∫ u in (0:ℝ)..1, massStepFunction as f u)+f as.length) := by
  have hp : ∀ u ∈ Ioo (0:ℝ) 1, ∀ i, Monotone (fun j => q j i+u*(r j i-q j i)) := by
    intro u hu i j k hjk
    have h₁ := mul_nonneg (sub_nonneg.mpr hu.2.le) (sub_nonneg.mpr (hq i hjk))
    have h₂ := mul_nonneg hu.1.le (sub_nonneg.mpr (hr i hjk))
    nlinarith
  have hv : ∀ u ∈ Ioo (0:ℝ) 1, ∀ i, v i ≤ q 0 i+u*(r 0 i-q 0 i) := by
    intro u hu i
    have h₁ := mul_nonneg (sub_nonneg.mpr hu.2.le) (sub_nonneg.mpr (hq₀ i))
    have h₂ := mul_nonneg hu.1.le (sub_nonneg.mpr (hr₀ i))
    nlinarith
  have hb := ClockTree.pairDisorder_l1_comparison hw φ ho j P hC hP v q
    (fun j i => r j i-q j i) hp hv hf hE x
    (show (0:ℝ) ∈ Icc 0 1 by norm_num) (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [zero_mul,one_mul,add_zero,add_sub_cancel,sub_self,zero_sub,abs_neg,abs_one,
    mul_one,ClockTree.edgeBudget_eq_massStepSum,massStepFunction_integral as 0 f ho] using hb

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*}

 def stepClockFunction (q₀ : ι → ℝ) (L : List (GaussianStep ι)) (u : ℝ) (i : ι) : ℝ :=
  q₀ i+(L.map fun s => if s.1 ≤ u then (s.2 i:ℝ) else 0).sum

 theorem stepClockFunction_cons (q₀ : ι → ℝ) (s : GaussianStep ι)
    (L : List (GaussianStep ι)) (u : ℝ) (i : ι) :
    stepClockFunction q₀ (s::L) u i = if s.1 ≤ u then
      stepClockFunction (fun i => q₀ i+s.2 i) L u i else stepClockFunction q₀ L u i := by
  simp only [stepClockFunction,List.map_cons,List.sum_cons]
  split_ifs <;> ring

 theorem stepClockFunction_before (q₀ : ι → ℝ) {L : List (GaussianStep ι)}
    {a u : ℝ} (ho : OrderedSteps a L) (hu : u<a) (i : ι) :
    stepClockFunction q₀ L u i=q₀ i := by
  induction L generalizing a with
  | nil => simp [stepClockFunction]
  | cons s L ih =>
    rw [stepClockFunction_cons,ite_eq_right (not_le.mpr (hu.trans_le ho.2.1))]
    exact ih ho.2.2.2 (hu.trans_le ho.2.1)

 theorem stepClockFunction_eq (q₀ : ι → ℝ) {L : List (GaussianStep ι)} {a : ℝ}
    (ho : OrderedSteps a L) (u : ℝ) (i : ι) :
    stepClockFunction q₀ L u i = massStepFunction (positiveStepMasses L ho.mem_pos)
      (fun j => stepClockValues q₀ L j i) u := by
  induction L generalizing a q₀ with
  | nil => simp [stepClockFunction,positiveStepMasses,massStepFunction,stepClockValues]
  | cons s L ih =>
    simp only [positiveStepMasses,massStepFunction,stepClockValues]
    rw [stepClockFunction_cons]
    by_cases hu : s.1 ≤ u
    · rw [ite_eq_left hu,ite_eq_right (not_lt.mpr hu)]
      exact ih (fun i => q₀ i+s.2 i) ho.2.2.2
    · rw [ite_eq_right hu,ite_eq_left (lt_of_not_ge hu)]
      exact stepClockFunction_before q₀ ho.2.2.2 (lt_of_not_ge hu) i

 theorem ZeroClockRefinement.clockFunction {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (q₀ : ι → ℝ) :
    stepClockFunction q₀ L=stepClockFunction q₀ M := by
  induction h with
  | refl => rfl
  | insert pre post m hm =>
    funext u i
    simp only [stepClockFunction,List.map_append,List.map_cons,List.sum_append,List.sum_cons,
      Pi.zero_apply,NNReal.coe_zero,ite_self,zero_add]
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

 theorem stepDisorderPressure_l1_comparison [Fintype ι] [Fintype S] [Nonempty S]
    [Nonempty ι] [DecidableEq ι]
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (C D : ι → ℝ) (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (hD : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i)
    (q₀ r₀ : ι → ℝ≥0) (A B : List (GaussianStep ι))
    (hA : OrderedSteps 0 A) (hB : OrderedSteps 0 B) (x : ι → ℝ) :
    |stepDisorderPressure w φ C q₀ A x-stepDisorderPressure w φ C r₀ B x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*(∫ u in (0:ℝ)..1,
        |stepClockFunction (fun i => (q₀ i:ℝ)) A u i-
          stepClockFunction (fun i => (r₀ i:ℝ)) B u i|) := by
  have ht := stepDisorderPressure_comparison hw φ C D hC hD q₀ r₀ A B hA hB x
  have ho := commonClockSteps_ordered A B hA hB
  have hr := commonClockSteps_refines A B hA.mem_pos hB.mem_pos
  have hm := positiveStepMasses_eq ho.1.mem_pos ho.2.mem_pos (commonClockSteps_same_masses A B)
  simp_rw [rootBoundaryCost_eq_integral _ _ _ (positiveStepMasses_ordered ho.1 ho.1.mem_pos)] at ht
  have he : ∀ i u, massStepFunction
      (positiveStepMasses (leftClockSteps (commonClockSteps A B)) ho.1.mem_pos)
      (fun j => stepClockValues (fun i => (r₀ i:ℝ)) (rightClockSteps (commonClockSteps A B)) j i) u =
      stepClockFunction (fun i => (r₀ i:ℝ)) B u i := by
    intro i u
    rw [hm,← stepClockFunction_eq _ ho.2,← hr.2.clockFunction]
  simp_rw [he,← stepClockFunction_eq _ ho.1,← hr.1.clockFunction] at ht
  exact ht

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def clockCoordinateDistance (D : ι → ℝ) (q r : ι → ℝ) : ℝ :=
   ∑ i, |q i-r i| *(D i)^2

omit [Nonempty ι] in
 theorem clockCoordinateDistance_nonneg (D : ι → ℝ) (q r : ι → ℝ) :
    0≤clockCoordinateDistance D q r :=
   Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)

omit [Fintype ι] [Nonempty ι] in
 theorem stepClockValues_append_cut (q₀ : ι → ℝ) (A B : List (GaussianStep ι)) :
    stepClockValues q₀ (A++B) A.length=stepClockValues q₀ A A.length := by
  induction A generalizing q₀ with
  | nil => simp only [List.nil_append,List.length_nil,stepClockValues_zero]
  | cons s A ih => exact ih _

omit [Nonempty ι] in
 theorem massStepFunction_coordinateDistance (as : List PositiveMass) (D : ι → ℝ)
    (q r : ℕ → ι → ℝ) (u : ℝ) :
    massStepFunction as (fun j => clockCoordinateDistance D (q j) (r j)) u =
      clockCoordinateDistance D (fun i => massStepFunction as (fun j => q j i) u)
        (fun i => massStepFunction as (fun j => r j i) u) := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    simp only [massStepFunction]
    split_ifs <;> simp only [ih]

 theorem stepPairDisorder_sameMasses {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ r₀ : ι → ℝ≥0) (A B C E : List (GaussianStep ι))
    (hA : OrderedSteps 0 (A++B)) (hC : OrderedSteps 0 (C++E))
    (hm₁ : A.map Prod.fst=C.map Prod.fst) (hm₂ : B.map Prod.fst=E.map Prod.fst)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPairDisorder w φ q₀ A B P x-stepPairDisorder w φ r₀ C E P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*
        (clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length)
          (stepClockValues (fun i => (r₀ i:ℝ)) C C.length)+
         (∫ u in (0:ℝ)..1, clockCoordinateDistance D
           (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
           (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u))+
         clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
           (stepClockValues (fun i => (r₀ i:ℝ)) (C++E) (C++E).length)) := by
  have hpa : ∀ s ∈ A, 0<s.1 := fun s hs => hA.mem_pos s (List.mem_append_left _ hs)
  have hpb : ∀ s ∈ B, 0<s.1 := fun s hs => hA.mem_pos s (List.mem_append_right _ hs)
  have hpc : ∀ s ∈ C, 0<s.1 := fun s hs => hC.mem_pos s (List.mem_append_left _ hs)
  have hpe : ∀ s ∈ E, 0<s.1 := fun s hs => hC.mem_pos s (List.mem_append_right _ hs)
  have he₁ := positiveStepMasses_eq hpa hpc hm₁
  have he₂ := positiveStepMasses_eq hpb hpe hm₂
  have he : positiveStepMasses (A++B) hA.mem_pos=
      positiveStepMasses A hpa++positiveStepMasses B hpb := positiveStepMasses_append _ _ _ _
  have he' : positiveStepMasses (C++E) hC.mem_pos=
      positiveStepMasses A hpa++positiveStepMasses B hpb := by
    rw [positiveStepMasses_append C E hpc hpe,←he₁,←he₂]
  have hl₁ : A.length=C.length := by simpa only [List.length_map] using congrArg List.length hm₁
  have hl₂ : (A++B).length=(C++E).length := by
    simpa only [List.length_append,List.length_map] using
      congrArg List.length (show (A++B).map Prod.fst=(C++E).map Prod.fst by
        simp only [List.map_append,hm₁,hm₂])
  let as := positiveStepMasses A hpa++positiveStepMasses B hpb
  let q := stepClockValues (fun i => (q₀ i:ℝ)) (A++B)
  let r := stepClockValues (fun i => (r₀ i:ℝ)) (C++E)
  have ho : MassOrdered 0 as := by
    change MassOrdered 0 (positiveStepMasses A hpa++positiveStepMasses B hpb)
    rw [←he]
    exact positiveStepMasses_ordered hA hA.mem_pos
  have hf : ∀ j, 0≤clockCoordinateDistance D (q j) (r j) :=
    fun j => clockCoordinateDistance_nonneg _ _ _
  have henv : ∀ j σ τ, |ReplicaTree.coordinateProfile φ (fun j i => r j i-q j i) j σ τ|≤
      clockCoordinateDistance D (q j) (r j) := by
    intro j σ τ
    simpa only [clockCoordinateDistance,abs_sub_comm] using
      ReplicaTree.coordinateProfile_abs_le_sum φ (fun j i => r j i-q j i) D hD hφ j σ τ
  have hh := ClockTree.pairDisorder_cumulative_comparison hw φ ho
    (positiveStepMasses A hpa).length P hK hP (fun _ => 0) q r
    (stepClockValues_mono _ _) (stepClockValues_mono _ _)
    (fun i => by simp only [q,stepClockValues_zero]; exact (q₀ i).coe_nonneg)
    (fun i => by simp only [r,stepClockValues_zero]; exact (r₀ i).coe_nonneg) hf henv x
  have hmfun (u : ℝ) : massStepFunction as
      (fun j => clockCoordinateDistance D (q j) (r j)) u =
      clockCoordinateDistance D (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
        (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u) := by
    rw [massStepFunction_coordinateDistance]
    congr 1
    · funext i; change massStepFunction (positiveStepMasses A hpa++positiveStepMasses B hpb) _ u = _
      rw [←he,←stepClockFunction_eq _ hA]
    · funext i; change massStepFunction (positiveStepMasses A hpa++positiveStepMasses B hpb) _ u = _
      rw [←he',←stepClockFunction_eq _ hC]
  have hj : min (positiveStepMasses A hpa).length as.length=A.length := by
    simp only [as,List.length_append,positiveStepMasses_length]
    omega
  have hlen : as.length=(A++B).length := by
    change (positiveStepMasses A hpa++positiveStepMasses B hpb).length=_
    rw [←he,positiveStepMasses_length]
  rw [congrFun (ClockTree.pairDisorder_coordinates hw φ A B hpa hpb hA q₀ P) x] at hh
  have hrw := congrFun (ClockTree.pairDisorder_coordinates hw φ C E hpc hpe hC r₀ P) x
  rw [←he₁,←he₂] at hrw
  rw [hrw,hj] at hh
  simp_rw [hmfun] at hh
  rw [hlen] at hh
  dsimp only [q,r] at hh
  rw [stepClockValues_append_cut,hl₁,stepClockValues_append_cut,hl₂] at hh
  simpa only [hl₁,hl₂] using hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι : Type*}

 theorem ZeroClockRefinement.append_right {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (A : List (GaussianStep ι)) :
    ZeroClockRefinement (L++A) (M++A) := by
  induction h with
  | refl => exact .refl _
  | insert pre post m hm =>
    simpa only [List.append_assoc,List.cons_append] using
      ZeroClockRefinement.insert pre (post++A) m hm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

 theorem ZeroClockRefinement.append_left {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (A : List (GaussianStep ι)) :
    ZeroClockRefinement (A++L) (A++M) := by
  induction A with
  | nil => exact h
  | cons s A ih => exact ih.cons s

 theorem ZeroClockRefinement.append {L M A B : List (GaussianStep ι)}
    (h₁ : ZeroClockRefinement L M) (h₂ : ZeroClockRefinement A B) :
    ZeroClockRefinement (L++A) (M++B) :=
  (h₁.append_right A).trans (h₂.append_left M)

 theorem commonClockSteps_mass_le (A B : List (GaussianStep ι)) {u : ℝ}
    (hA : ∀ s ∈ A, s.1≤u) (hB : ∀ s ∈ B, s.1≤u) :
    ∀ s ∈ commonClockSteps A B, s.1≤u := by
  cases A with
  | nil =>
    intro s hs
    simp only [commonClockSteps] at hs
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
    exact hB b hb
  | cons a A =>
    cases B with
    | nil =>
      intro s hs
      simp only [commonClockSteps] at hs
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hs
      exact hA b hb
    | cons b B =>
      rw [commonClockSteps]
      split_ifs with hab
      · intro s hs
        rcases List.mem_cons.mp hs with rfl|hs
        · exact hA a (by simp)
        · exact commonClockSteps_mass_le A (b::B) (fun t ht => hA t (by simp [ht])) hB s hs
      · intro s hs
        rcases List.mem_cons.mp hs with rfl|hs
        · exact hB b (by simp)
        · exact commonClockSteps_mass_le (a::A) B hA (fun t ht => hB t (by simp [ht])) s hs
termination_by A.length+B.length

 theorem commonClockSteps_prepost_ordered (A B C E : List (GaussianStep ι)) {u : ℝ}
    (hu : 0≤u) (hA : OrderedSteps 0 A) (hB : OrderedSteps u B)
    (hC : OrderedSteps 0 C) (hE : OrderedSteps u E)
    (hAu : ∀ s ∈ A, s.1≤u) (hCu : ∀ s ∈ C, s.1≤u) :
    OrderedSteps 0 (leftClockSteps (commonClockSteps A C)++leftClockSteps (commonClockSteps B E)) ∧
    OrderedSteps 0 (rightClockSteps (commonClockSteps A C)++rightClockSteps (commonClockSteps B E)) := by
  have h₁ := commonClockSteps_ordered A C hA hC
  have h₂ := commonClockSteps_ordered B E hB hE
  have hm := commonClockSteps_mass_le A C hAu hCu
  constructor
  · apply h₁.1.append_bound hu _ h₂.1
    intro s hs
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
    exact hm t ht
  · apply h₁.2.append_bound hu _ h₂.2
    intro s hs
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
    exact hm t ht

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

omit [Fintype ι] [Nonempty ι] in
 theorem ZeroClockRefinement.terminal {L M : List (GaussianStep ι)}
    (h : ZeroClockRefinement L M) (q₀ : ι → ℝ) :
    stepClockValues q₀ L L.length=stepClockValues q₀ M M.length := by
  funext i
  simp only [stepClockValues_terminal,h.total_variance]

 theorem stepPairDisorder_l1_comparison {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i)
    (q₀ r₀ : ι → ℝ≥0) (A B C E : List (GaussianStep ι)) {u : ℝ}
    (hu : 0≤u) (hA : OrderedSteps 0 A) (hB : OrderedSteps u B)
    (hC : OrderedSteps 0 C) (hE : OrderedSteps u E)
    (hAu : ∀ s ∈ A, s.1≤u) (hCu : ∀ s ∈ C, s.1≤u)
    (P : S → S → ℝ) {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) (x : ι → ℝ) :
    |stepPairDisorder w φ q₀ A B P x-stepPairDisorder w φ r₀ C E P x| ≤
      ClockTree.errorJetVariation 2 0 0*K*
        (clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) A A.length)
          (stepClockValues (fun i => (r₀ i:ℝ)) C C.length)+
         (∫ u in (0:ℝ)..1, clockCoordinateDistance D
           (stepClockFunction (fun i => (q₀ i:ℝ)) (A++B) u)
           (stepClockFunction (fun i => (r₀ i:ℝ)) (C++E) u))+
         clockCoordinateDistance D (stepClockValues (fun i => (q₀ i:ℝ)) (A++B) (A++B).length)
           (stepClockValues (fun i => (r₀ i:ℝ)) (C++E) (C++E).length)) := by
  have ho := commonClockSteps_prepost_ordered A B C E hu hA hB hC hE hAu hCu
  have hr₁ := commonClockSteps_refines A C hA.mem_pos hC.mem_pos
  have hr₂ := commonClockSteps_refines B E hB.mem_pos hE.mem_pos
  have hh := stepPairDisorder_sameMasses hw φ D hD hφ q₀ r₀
    (leftClockSteps (commonClockSteps A C)) (leftClockSteps (commonClockSteps B E))
    (rightClockSteps (commonClockSteps A C)) (rightClockSteps (commonClockSteps B E))
    ho.1 ho.2 (commonClockSteps_same_masses A C) (commonClockSteps_same_masses B E)
    P hK hP x
  rw [←hr₁.1.pairDisorder hr₂.1,←hr₁.2.pairDisorder hr₂.2,
    ←hr₁.1.terminal,←hr₁.2.terminal,
    ←(hr₁.1.append hr₂.1).terminal,←(hr₁.2.append hr₂.2).terminal,
    ←(hr₁.1.append hr₂.1).clockFunction,←(hr₁.2.append hr₂.2).clockFunction] at hh
  exact hh

end SKFluctuations.Hierarchy

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι]

 theorem hierarchyPairMean_eq_nested {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (P : S → S → ℝ) (L : List (GaussianStep ι))
    {a : ℝ} (ho : OrderedSteps a L) (x : ι → ℝ) :
    hierarchyPairMean w φ P L x = gaussianHierarchyMean w φ
      (fun σ => gaussianHierarchyMean w φ (P σ) L x) L x := by
  rw [gaussianHierarchyMean_atoms hw φ L ho]
  simp_rw [gaussianHierarchyMean_atoms hw φ L ho]
  simp only [hierarchyPairMean,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

 theorem ClockTree.pairMean_eq_levelPairMean {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ι → ℝ≥0) (j : ℕ) (P : S → S → ℝ) :
    pairMean w φ as q j P = levelPairMean w φ P (clockSteps as q) j := by
  induction as generalizing a q j with
  | nil =>
    funext x
    cases j <;> simp only [pairMean,levelPairMean,clockSteps]
    all_goals exact (hierarchyPairMean_eq_nested hw φ P [] ho x).symm
  | cons b bs ih =>
    cases j with
    | zero =>
      funext x
      simp only [pairMean,levelPairMean]
      rw [singleMean_eq_hierarchy hw φ ho]
      simp_rw [singleMean_eq_hierarchy hw φ ho]
      exact (hierarchyPairMean_eq_nested hw φ P _ (clockSteps_ordered ho q) x).symm
    | succ j =>
      funext x
      simp only [pairMean,levelPairMean,clockSteps]
      rw [ih ho.2.2]

 theorem ClockTree.pairDisorder_eq_rootLevelPairMean {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (as : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ι → ℝ) (j : ℕ) (P : S → S → ℝ) :
    (pairClock as j).disorderExpect w φ (fun _ => 0) q
      (fun σ => P (pairSpin as j σ).1 (pairSpin as j σ).2) 0 =
      rootLevelPairMean w φ (fun i => Real.toNNReal (q 0 i)) P
        (diagonalBoundarySteps as (q 0) (fun k => q (k+1))) j := by
  rw [disorderExpect_integral hw φ _ ho]
  have he (c : ℕ → ι → ℝ≥0) : (pairClock as j).expect w φ c
      (fun σ => P (pairSpin as j σ).1 (pairSpin as j σ).2)=pairMean w φ as c j P := by
    funext x
    exact pairClock_expect hw φ as ho c j P x
  rw [he,pairMean_eq_levelPairMean hw φ as ho,clockSteps_cumulative]
  simp only [sub_zero,rootLevelPairMean]

end SKFluctuations.Hierarchy

namespace SKFluctuations
open Hierarchy
 theorem orderedPrefixPair_eq_pairDisorder (n : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (b h : ℕ → ℝ) (P : Spin n → Spin n → ℝ) (j : ℕ) :
    orderedPrefixPair n as b h P j =
      (ClockTree.pairClock as j).disorderExpect (uniformWeight n) (orderedFeature n)
        (fun _ => 0) (orderedClock n b h)
        (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0 :=
  (ClockTree.pairDisorder_eq_rootLevelPairMean (uniformWeight_pos n) (orderedFeature n)
    as ho (orderedClock n b h) j P).symm
end SKFluctuations

 

 

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
attribute [local instance] Classical.propDecidable

 def regularizedClock (q : ℕ → ι → ℝ) (ε : ℝ) (j : ℕ) (i : ι) : ℝ :=
  q j i+ε*(j+1)

omit [Fintype ι] [Nonempty ι] in
 theorem regularizedClock_monotone (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) {ε : ℝ} (hε : 0≤ε) (i : ι) :
    Monotone (fun j => regularizedClock q ε j i) := by
  intro j k hjk
  exact add_le_add (hq i hjk) (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hjk 1) hε)

omit [Fintype ι] [Nonempty ι] in
 theorem regularizedClock_strictMono (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) {ε : ℝ} (hε : 0<ε) (i : ι) :
    StrictMono (fun j => regularizedClock q ε j i) := by
  intro j k hjk
  exact add_lt_add_of_le_of_lt (hq i hjk.le)
    (mul_lt_mul_of_pos_left (by exact_mod_cast Nat.add_lt_add_right hjk 1) hε)

omit [Fintype ι] [Nonempty ι] in
 theorem regularizedClock_affine (q r : ℕ → ι → ℝ) (ε t : ℝ) :
    affineCumulative (regularizedClock q ε) (regularizedClock r ε) t =
      regularizedClock (affineCumulative q r t) ε := by
  funext j i
  simp only [affineCumulative,regularizedClock]
  ring

omit [Fintype ι] [Nonempty ι] in
 theorem affineCumulative_monotone (q r : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (i : ι) :
    Monotone (fun j => affineCumulative q r t j i) := by
  intro j k hjk
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hq i hjk))
  have h₂ := mul_nonneg ht.1 (sub_nonneg.mpr (hr i hjk))
  dsimp [affineCumulative]
  nlinarith

omit [Fintype ι] [Nonempty ι] in
 theorem affineCumulative_nonneg_zero (q r : ℕ → ι → ℝ)
    (hq : ∀ i, 0≤q 0 i) (hr : ∀ i, 0≤r 0 i) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (i : ι) :
    0≤affineCumulative q r t 0 i := by
  have h₁ := mul_nonneg (sub_nonneg.mpr ht.2) (hq i)
  have h₂ := mul_nonneg ht.1 (hr i)
  dsimp [affineCumulative]
  nlinarith

omit [Fintype ι] [Nonempty ι] in
 theorem signedClockSteps_strict (as : List PositiveMass) (q r : ℕ → ι → ℝ)
    (hq : ∀ i, StrictMono (fun j => q j i)) (hr : ∀ i, StrictMono (fun j => r j i)) :
    ∀ st ∈ signedClockSteps as q r, ∀ t ∈ Ioo (0:ℝ) 1, ∀ i, 0<st.2.1 i+t*st.2.2 i := by
  induction as generalizing q r with
  | nil => simp only [signedClockSteps,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
  | cons a as ih =>
    intro st hs t ht i
    rcases List.mem_cons.mp hs with rfl|hs
    · have hqi := hq i (by norm_num : (0:ℕ)<1)
      have hri := hr i (by norm_num : (0:ℕ)<1)
      have h₁ := mul_pos (sub_pos.mpr ht.2) (sub_pos.mpr hqi)
      have h₂ := mul_pos ht.1 (sub_pos.mpr hri)
      dsimp only [Pi.sub_apply]
      nlinarith
    · exact ih _ _ (fun i _ _ hj => hq i (Nat.add_lt_add_right hj 1))
        (fun i _ _ hj => hr i (Nat.add_lt_add_right hj 1)) st hs t ht i

 theorem massStepSum_abs_le (as : List PositiveMass) {a : ℝ} (ha : MassOrdered a as)
    (f : ℕ → ℝ) : |massStepSum as a f|≤ massStepSum as a (fun j => |f j|) := by
  induction as generalizing a f with
  | nil => simp only [massStepSum,abs_mul,abs_of_nonneg (sub_nonneg.mpr ha.2),le_refl]
  | cons b bs ih =>
    apply (abs_add_le _ _).trans
    simp only [massStepSum,abs_mul,abs_of_nonneg (sub_nonneg.mpr ha.2.1)]
    exact add_le_add_right (ih ha.2.2 _) _

 theorem massStepSum_abs_bound (as : List PositiveMass) (ha : MassOrdered 0 as)
    (f : ℕ → ℝ) {C : ℝ} (hC : ∀ j, j≤as.length → |f j|≤C) :
    |massStepSum as 0 f|≤C := by
  apply (massStepSum_abs_le as ha f).trans
  simpa only [massStepSum_const,sub_zero,one_mul] using massStepSum_mono as ha hC

 def cumulativePair (w : S → ℝ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (q : ℕ → ι → ℝ) (j : ℕ) (P : S → S → ℝ) : ℝ :=
  (ClockTree.pairClock as j).disorderExpect w φ (fun _ => 0) q
    (fun σ => P (ClockTree.pairSpin as j σ).1 (ClockTree.pairSpin as j σ).2) 0

 theorem cumulativePair_regularized_bound {w : S → ℝ} (hw : ∀ σ, 0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (D : ι → ℝ) (hD : ∀ i, 0≤D i)
    (hφ : ∀ σ i, |φ σ (Pi.single i 1)|≤D i) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (q : ℕ → ι → ℝ) (hq : ∀ i, Monotone (fun j => q j i)) (hq₀ : ∀ i, 0≤q 0 i)
    {ε : ℝ} (hε : 0≤ε) (j : ℕ) (P : S → S → ℝ)
    {K : ℝ} (hK : 0≤K) (hP : ∀ σ τ, |P σ τ|≤K) :
    |cumulativePair w φ as q j P-cumulativePair w φ as (regularizedClock q ε) j P| ≤
      ClockTree.errorJetVariation 2 0 0*K*(3*ε*(as.length+1)*(∑ i, (D i)^2)) := by
  let f : ℕ → ℝ := fun j => ε*(j+1)*(∑ i, (D i)^2)
  have hf : ∀ j, 0≤f j := by intro j; dsimp [f]; positivity
  have hE (j : ℕ) (σ τ : S) : |ReplicaTree.coordinateProfile φ
      (fun j i => regularizedClock q ε j i-q j i) j σ τ|≤f j := by
    apply (ReplicaTree.coordinateProfile_abs_le_sum φ _ D hD hφ j σ τ).trans
    simp only [regularizedClock,add_sub_cancel_left,abs_of_nonneg (show 0≤ε*(j+1) by positivity)]
    dsimp [f]
    rw [Finset.mul_sum]
  have hb := ClockTree.pairDisorder_cumulative_comparison hw φ ha j P hK hP
    (fun _ => 0) q (regularizedClock q ε) hq (regularizedClock_monotone q hq hε) hq₀
    (fun i => by dsimp [regularizedClock]; nlinarith [hq₀ i]) hf hE 0
  rw [massStepFunction_integral as 0 f ha] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ClockTree.errorJetVariation_nonneg _ _ _) hK)
  have hfbound (k : ℕ) (hk : k≤as.length) : f k≤ε*(as.length+1)*(∑ i, (D i)^2) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hk 1) hε
  have hm := massStepSum_mono as ha hfbound
  rw [massStepSum_const] at hm
  have hj := hfbound (min j as.length) (min_le_right _ _)
  have he := hfbound as.length le_rfl
  nlinarith

end SKFluctuations.Hierarchy

end

end OAI
