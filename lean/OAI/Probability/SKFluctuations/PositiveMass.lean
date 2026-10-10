import Mathlib
import OAI.Probability.SKFluctuations.LinearClockMassDifference

namespace OAI

/-! Positive Mass. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open MeasureTheory Filter Set
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
abbrev PositiveMass := {a : ℝ // 0 < a}

 
noncomputable def HeatJet.boundarySchedule {n : ℕ} (J : HeatJet n) :
    List PositiveMass → ℝ → (ℕ → ℝ) → HeatJet n
  | [],_,_ => J
  | a::as,l,q => (J.boundarySchedule as (q 0) (fun i => q (i+1))).evolve a.property (q 0-l)

 def boundaryCost : List PositiveMass → (ℕ → ℝ) → (ℕ → ℝ) → ℝ
  | [],_,_ => 0
  | [_],_,_ => 0
  | a::b::as,q,r => |a.val-b.val| *|q 0-r 0|+boundaryCost (b::as) (fun i => q (i+1)) (fun i => r (i+1))

 theorem HeatJet.boundarySchedule_gradient_bound {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (as : List PositiveMass) (l : ℝ) (q : ℕ → ℝ) :
    ∀ i x, |(J.boundarySchedule as l q).G i x| ≤ D i := by
  induction as generalizing l q with
  | nil => exact hD
  | cons a as ih =>
    intro i x
    exact clockTest_abs_le (J.boundarySchedule as (q 0) (fun i => q (i+1))).lipschitz
      ((J.boundarySchedule as (q 0) (fun i => q (i+1))).smoothG i)
      (ih (q 0) (fun i => q (i+1)) i) _ _ x

 theorem HeatJet.boundary_head_move {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (a b : PositiveMass) (as : List PositiveMass)
    {l d : ℝ} {q : ℕ → ℝ} (hql : l ≤ q 0) (hq : q 0 ≤ q 1) (hdl : l ≤ d) (hdq : d ≤ q 1)
    (x : Fin (n+1) → ℝ) :
    |(J.boundarySchedule (a::b::as) l q).F x-
      clockContinuation a.val (J.boundarySchedule (b::as) d (fun i => q (i+1))).F (d-l) x| ≤
      (|a.val-b.val| /2*∑ i, (D i)^2)*|q 0-d| := by
  let K := J.boundarySchedule as (q 1) (fun i => q (i+2))
  have ht : ∀ y, (J.boundarySchedule (a::b::as) l q).F y = K.potentialSplit a.val b.property
      (q 1-l) (q 0-l) y := by
    intro y
    simp only [HeatJet.boundarySchedule,HeatJet.evolve,HeatJet.potentialSplit,K]
    congr 2
    ring
  have ht' : ∀ y, clockContinuation a.val (J.boundarySchedule (b::as) d (fun i => q (i+1))).F (d-l) y =
      K.potentialSplit a.val b.property (q 1-l) (d-l) y := by
    intro y
    simp only [HeatJet.boundarySchedule,HeatJet.evolve,HeatJet.potentialSplit,K]
    congr 2
    ring
  rw [ht,ht']
  have hh := K.potentialSplit_stability D (J.boundarySchedule_gradient_bound D hD as _ _) a.property b.property
    (show q 0-l ∈ Icc (0:ℝ) (q 1-l) by constructor <;> linarith)
    (show d-l ∈ Icc (0:ℝ) (q 1-l) by constructor <;> linarith) x
  simpa only [sub_sub_sub_cancel_right] using hh

 

 theorem HeatJet.boundarySchedule_comparison {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (as : List PositiveMass) {l : ℝ} {q r : ℕ → ℝ}
    (hq : Monotone q) (hr : Monotone r) (hql : l ≤ q 0) (hrl : l ≤ r 0)
    (hend : q (as.length-1) = r (as.length-1)) (x : Fin (n+1) → ℝ) :
    |(J.boundarySchedule as l q).F x-(J.boundarySchedule as l r).F x| ≤
      (∑ i, (D i)^2)/2*boundaryCost as q r := by
  induction as generalizing l q r x with
  | nil => simp only [HeatJet.boundarySchedule,boundaryCost,sub_self,abs_zero,mul_zero,le_refl]
  | cons a as ih =>
    cases as with
    | nil =>
      have he : q 0 = r 0 := by simpa only [List.length_cons,List.length_nil,Nat.add_sub_cancel] using hend
      simp only [HeatJet.boundarySchedule,HeatJet.evolve,boundaryCost,he,sub_self,abs_zero,mul_zero,le_refl]
    | cons b as =>
      let d := min (q 0) (r 0)
      let A := (J.boundarySchedule (a::b::as) l q).F x
      let B := clockContinuation a.val (J.boundarySchedule (b::as) d (fun i => q (i+1))).F (d-l) x
      let C := clockContinuation a.val (J.boundarySchedule (b::as) d (fun i => r (i+1))).F (d-l) x
      let E := (J.boundarySchedule (a::b::as) l r).F x
      have hdl : l ≤ d := le_min hql hrl
      have hq01 : q 0 ≤ q 1 := hq (by omega)
      have hr01 : r 0 ≤ r 1 := hr (by omega)
      have hAB : |A-B| ≤ (|a.val-b.val| /2*∑ i, (D i)^2)*|q 0-d| :=
        J.boundary_head_move D hD a b as hql hq01 hdl ((min_le_left _ _).trans hq01) x
      have hCE : |C-E| ≤ (|a.val-b.val| /2*∑ i, (D i)^2)*|r 0-d| := by
        rw [abs_sub_comm]
        exact J.boundary_head_move D hD a b as hrl hr01 hdl ((min_le_right _ _).trans hr01) x
      have hend' : q ((b::as).length-1+1) = r ((b::as).length-1+1) := by
        convert hend using 1 <;> congr 1
      have hBC : |B-C| ≤ (∑ i, (D i)^2)/2*boundaryCost (b::as) (fun i => q (i+1)) (fun i => r (i+1)) := by
        apply clockContinuation_abs_sub_le (J.boundarySchedule (b::as) d (fun i => q (i+1))).lipschitz
          (J.boundarySchedule (b::as) d (fun i => r (i+1))).lipschitz a.property
        intro y
        exact ih (hq.comp (monotone_id.add_const 1)) (hr.comp (monotone_id.add_const 1))
          ((min_le_left _ _).trans hq01) ((min_le_right _ _).trans hr01) hend' y
      have hmin : |q 0-d|+|r 0-d| = |q 0-r 0| := by
        dsimp [d]
        rcases le_total (q 0) (r 0) with he | he
        · rw [min_eq_left he,sub_self,abs_zero,zero_add,abs_sub_comm]
        · rw [min_eq_right he,sub_self,abs_zero,add_zero]
      change |A-E| ≤ _
      have hh := (abs_sub_le A B E).trans (add_le_add hAB ((abs_sub_le B C E).trans (add_le_add hBC hCE)))
      apply hh.trans_eq
      dsimp only [boundaryCost]
      calc
        _ = (∑ i, (D i)^2)/2*(|a.val-b.val| *(|q 0-d|+|r 0-d|)+
            boundaryCost (b::as) (fun i => q (i+1)) (fun i => r (i+1))) := by ring
        _ = _ := by rw [hmin]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 theorem boundaryCost_le {a : PositiveMass} {as : List PositiveMass} {q r : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ho : (a::as).Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ b ∈ a::as, b.val ≤ 1) (hq : ∀ i < (a::as).length, |q i-r i| ≤ M) :
    boundaryCost (a::as) q r ≤ M*(1-a.val) := by
  induction as generalizing a q r with
  | nil =>
    exact (mul_nonneg hM (sub_nonneg.mpr (hu a (by simp only [List.mem_singleton]))))
  | cons b as ih =>
    have hab : a.val ≤ b.val := (List.pairwise_cons.mp ho).1 b (by simp only [List.mem_cons, true_or])
    have hu' : ∀ c ∈ b::as, c.val ≤ 1 := fun c hc => hu c (List.mem_cons_of_mem _ hc)
    have hq' : ∀ i < (b::as).length, |q (i+1)-r (i+1)| ≤ M := by
      intro i hi
      apply hq (i+1)
      simp only [List.length_cons] at hi ⊢
      omega
    have hh := ih (List.pairwise_cons.mp ho).2 hu' hq'
    change |a.val-b.val| *|q 0-r 0|+boundaryCost (b::as) (fun i => q (i+1)) (fun i => r (i+1)) ≤ _
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hmul := mul_le_mul_of_nonneg_left (hq 0 (by simp only [List.length_cons]; omega)) (by linarith : 0 ≤ -(a.val-b.val))
    linarith

 theorem boundaryCost_uniform {as : List PositiveMass} {q r : ℕ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ b ∈ as, b.val ≤ 1) (hq : ∀ i < as.length, |q i-r i| ≤ M) :
    boundaryCost as q r ≤ M := by
  cases as with
  | nil => exact hM
  | cons a as =>
    apply (boundaryCost_le hM ho hu hq).trans
    nlinarith [a.property,mul_nonneg hM a.property.le]

 

 theorem HeatJet.cumulativeClock_uniform {n : ℕ} (J : HeatJet n) (D : Fin (n+1) → ℝ)
    (hD : ∀ i x, |J.G i x| ≤ D i) (as : List PositiveMass) {l M : ℝ} {q r : ℕ → ℝ}
    (hq : Monotone q) (hr : Monotone r) (hql : l ≤ q 0) (hrl : l ≤ r 0)
    (hend : q (as.length-1) = r (as.length-1)) (hM : 0 ≤ M)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ b ∈ as, b.val ≤ 1)
    (hm : ∀ i < as.length, |q i-r i| ≤ M) (x : Fin (n+1) → ℝ) :
    |(J.boundarySchedule as l q).F x-(J.boundarySchedule as l r).F x| ≤
      (∑ i, (D i)^2)/2*M := by
  exact (J.boundarySchedule_comparison D hD as hq hr hql hrl hend x).trans
    (mul_le_mul_of_nonneg_left (boundaryCost_uniform hM ho hu hm) (by positivity))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 

def diagonalBoundarySteps {ι : Type*} : List PositiveMass → (ι → ℝ) → (ℕ → ι → ℝ) → List (GaussianStep ι)
  | [],_,_ => []
  | a::as,l,q => (a.val,fun i => Real.toNNReal (q 0 i-l i))::
      diagonalBoundarySteps as (q 0) (fun j => q (j+1))

 theorem diagonalBoundarySteps_ordered {ι : Type*} (as : List PositiveMass) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ b ∈ as, b.val ≤ 1) (hl : ∀ b ∈ as, a ≤ b.val) (l : ι → ℝ) (q : ℕ → ι → ℝ) :
    OrderedSteps a (diagonalBoundarySteps as l q) := by
  induction as generalizing a l q with
  | nil => exact ⟨ha0,ha1⟩
  | cons b as ih =>
    refine ⟨ha0,hl b List.mem_cons_self,b.property,?_⟩
    exact ih b.property.le (hu b List.mem_cons_self) (List.pairwise_cons.mp ho).2
      (fun c hc => hu c (List.mem_cons_of_mem _ hc)) (List.pairwise_cons.mp ho).1 (q 0) (fun j => q (j+1))

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

noncomputable def diagonalBoundaryPotential (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) : (Fin (n+1) → ℝ) → ℝ :=
  gaussianHierarchy w φ (diagonalBoundarySteps as l q)

 
theorem diagonalBoundary_head_move {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (a b : PositiveMass) (as : List PositiveMass)
    (ho : (b::as).Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ c ∈ b::as, c.val ≤ 1)
    {l d : Fin (n+1) → ℝ} {q : ℕ → Fin (n+1) → ℝ}
    (hdl : ∀ i, l i ≤ d i) (hdq : ∀ i, d i ≤ q 0 i) (hqq : ∀ i, q 0 i ≤ q 1 i)
    (x : Fin (n+1) → ℝ) :
    |diagonalBoundaryPotential w φ (a::b::as) l q x-
      shiftedContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (d i-l i))) a.val
        (diagonalBoundaryPotential w φ (b::as) d (fun j => q (j+1))) x| ≤
      |a.val-b.val|/2*∑ i, (q 0 i-d i)*(D i)^2 := by
  let tail := diagonalBoundarySteps as (q 1) (fun j => q (j+2))
  have ht : OrderedSteps b.val tail :=
    diagonalBoundarySteps_ordered as b.property.le (hu b List.mem_cons_self)
      (List.pairwise_cons.mp ho).2 (fun c hc => hu c (List.mem_cons_of_mem _ hc))
      (List.pairwise_cons.mp ho).1 (q 1) (fun j => q (j+2))
  have huq (i : Fin (n+1)) : Real.toNNReal (d i-l i)+Real.toNNReal (q 0 i-d i) =
      Real.toNNReal (q 0 i-l i) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr (hdl i)),
      Real.coe_toNNReal _ (sub_nonneg.mpr (hdq i)),Real.coe_toNNReal _ (sub_nonneg.mpr ((hdl i).trans (hdq i)))]
    ring
  have huv (i : Fin (n+1)) : Real.toNNReal (q 0 i-d i)+Real.toNNReal (q 1 i-q 0 i) =
      Real.toNNReal (q 1 i-d i) := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add,Real.coe_toNNReal _ (sub_nonneg.mpr (hdq i)),
      Real.coe_toNNReal _ (sub_nonneg.mpr (hqq i)),Real.coe_toNNReal _ (sub_nonneg.mpr ((hdq i).trans (hqq i)))]
    ring
  have hh := gaussianHierarchy_covariance_transfer hw φ ht D hB a.property b.property
    (fun i => Real.toNNReal (d i-l i)) (fun i => Real.toNNReal (q 0 i-d i))
    (fun i => Real.toNNReal (q 1 i-q 0 i)) x
  simp_rw [huq,huv,Real.coe_toNNReal _ (sub_nonneg.mpr (hdq _))] at hh
  exact hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 

theorem diagonalBoundary_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : Fin (n+1) → ℝ} {q r : ℕ → Fin (n+1) → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q (as.length-1) = r (as.length-1)) (x : Fin (n+1) → ℝ) :
    |diagonalBoundaryPotential w φ as l q x-diagonalBoundaryPotential w φ as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*boundaryCost as (fun j => q j i) (fun j => r j i) := by
  induction as generalizing l q r x with
  | nil => simp only [diagonalBoundaryPotential,diagonalBoundarySteps,boundaryCost,mul_zero,Finset.sum_const_zero,
      sub_self,abs_zero,le_refl]
  | cons a as ih =>
    cases as with
    | nil =>
      have he : q 0 = r 0 := by simpa only [List.length_cons,List.length_nil,Nat.add_sub_cancel] using hend
      simp only [diagonalBoundaryPotential,diagonalBoundarySteps,boundaryCost,he,mul_zero,Finset.sum_const_zero,
        sub_self,abs_zero,le_refl]
    | cons b as =>
      let d : Fin (n+1) → ℝ := fun i => min (q 0 i) (r 0 i)
      let μ := Measure.pi fun i => gaussianReal 0 (Real.toNNReal (d i-l i))
      let F := diagonalBoundaryPotential w φ (b::as) d (fun j => q (j+1))
      let G := diagonalBoundaryPotential w φ (b::as) d (fun j => r (j+1))
      let A := diagonalBoundaryPotential w φ (a::b::as) l q x
      let B := shiftedContinuation μ a.val F x
      let C := shiftedContinuation μ a.val G x
      let E := diagonalBoundaryPotential w φ (a::b::as) l r x
      have ho' := (List.pairwise_cons.mp ho).2
      have hu' : ∀ c ∈ b::as, c.val ≤ 1 := fun c hc => hu c (List.mem_cons_of_mem _ hc)
      have hdl (i) : l i ≤ d i := le_min (hql i) (hrl i)
      have hq01 (i) : q 0 i ≤ q 1 i := hq i (by omega)
      have hr01 (i) : r 0 i ≤ r 1 i := hr i (by omega)
      have hAB : |A-B| ≤ |a.val-b.val|/2*∑ i, (q 0 i-d i)*(D i)^2 :=
        diagonalBoundary_head_move hw φ D hB a b as ho' hu' hdl (fun _ => min_le_left _ _) hq01 x
      have hCE : |C-E| ≤ |a.val-b.val|/2*∑ i, (r 0 i-d i)*(D i)^2 := by
        rw [abs_sub_comm]
        exact diagonalBoundary_head_move hw φ D hB a b as ho' hu' hdl (fun _ => min_le_right _ _) hr01 x
      have hend' : q ((b::as).length-1+1) = r ((b::as).length-1+1) := by
        convert hend using 1 <;> congr 1
      have hFo : OrderedSteps 0 (diagonalBoundarySteps (b::as) d (fun j => q (j+1))) :=
        diagonalBoundarySteps_ordered (b::as) (by norm_num) (by norm_num) ho' hu'
          (fun c _ => c.property.le) _ _
      have hGo : OrderedSteps 0 (diagonalBoundarySteps (b::as) d (fun j => r (j+1))) :=
        diagonalBoundarySteps_ordered (b::as) (by norm_num) (by norm_num) ho' hu'
          (fun c _ => c.property.le) _ _
      have hF := (gaussianHierarchy_regular hw φ _ hFo 0).1.choose_spec
      have hG := (gaussianHierarchy_regular hw φ _ hGo 0).1.choose_spec
      have hBC : |B-C| ≤ (1/2:ℝ)*∑ i, (D i)^2 *
          boundaryCost (b::as) (fun j => q (j+1) i) (fun j => r (j+1) i) := by
        apply shiftedContinuation_abs_sub_le a.property
          ((exponentialIncrement_gaussian _).integrable_shift hF a.val)
          ((exponentialIncrement_gaussian _).integrable_shift hG a.val)
        intro y
        exact ih ho' hu' (fun i => (hq i).comp (monotone_id.add_const 1))
          (fun i => (hr i).comp (monotone_id.add_const 1))
          (fun i => (min_le_left _ _).trans (hq01 i)) (fun i => (min_le_right _ _).trans (hr01 i)) hend' y
      have hmin (i : Fin (n+1)) : (q 0 i-d i)+(r 0 i-d i) = |q 0 i-r 0 i| := by
        dsimp [d]
        rcases le_total (q 0 i) (r 0 i) with h | h
        · rw [min_eq_left h,sub_self,zero_add,abs_of_nonpos (sub_nonpos.mpr h)]
          ring
        · rw [min_eq_right h,sub_self,add_zero,abs_of_nonneg (sub_nonneg.mpr h)]
      change |A-E| ≤ _
      have hh := (abs_sub_le A B E).trans (add_le_add hAB ((abs_sub_le B C E).trans (add_le_add hBC hCE)))
      apply hh.trans_eq
      rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
      rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [boundaryCost]
      calc
        _ = (1/2:ℝ)*(D i)^2*(|a.val-b.val| *((q 0 i-d i)+(r 0 i-d i))+
          boundaryCost (b::as) (fun j => q (j+1) i) (fun j => r (j+1) i)) := by ring
        _ = _ := by rw [hmin]; ring

 

theorem diagonalBoundary_uniform {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (D M : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : Fin (n+1) → ℝ} {q r : ℕ → Fin (n+1) → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q (as.length-1) = r (as.length-1)) (hM : ∀ i, 0 ≤ M i)
    (hm : ∀ i j, j < as.length → |q j i-r j i| ≤ M i) (x : Fin (n+1) → ℝ) :
    |diagonalBoundaryPotential w φ as l q x-diagonalBoundaryPotential w φ as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*M i := by
  exact (diagonalBoundary_comparison hw φ D hB as ho hu hq hr hql hrl hend x).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (boundaryCost_uniform (hM i) ho hu (hm i)) (sq_nonneg _)) (by norm_num))

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {ν : Measure E} [IsProbabilityMeasure ν]

omit [NormedSpace ℝ E] in
 

theorem shiftedContinuation_tendsto_zero_mass {F : E → ℝ} {C : ℝ≥0}
    (hF : LipschitzWith C F) (hν : ExponentialIncrement ν) (x : E) :
    Tendsto (fun m : ℝ => shiftedContinuation ν m F x) (𝓝[>] 0)
      (𝓝 (zeroContinuation ν F x)) := by
  have hs : integrableExpSet (fun z => F (x+z)) ν = univ := by
    ext m
    change Integrable (fun z => Real.exp (m*F (x+z))) ν ↔ True
    exact iff_true_intro (hν.integrable_shift hF m x)
  have h0 : (0:ℝ) ∈ interior (integrableExpSet (fun z => F (x+z)) ν) := by rw [hs,interior_univ]; trivial
  have hd := (analyticAt_cgf h0).differentiableAt.hasDerivAt
  rw [deriv_cgf_zero h0] at hd
  have hh := hd.tendsto_slope_zero_right
  simpa [slope,cgf,mgf,shiftedContinuation,zeroContinuation,div_eq_mul_inv,mul_comm] using hh

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
noncomputable def diagonalRootBoundary (w : S → ℝ) (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ)
    (as : List PositiveMass) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ) (x : Fin (n+1) → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun i => gaussianReal 0 (Real.toNNReal (q 0 i-l i)))
    (diagonalBoundaryPotential w φ as (q 0) (fun j => q (j+1))) x

 

theorem diagonalRoot_uniform {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (D M : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : Fin (n+1) → ℝ} {q r : ℕ → Fin (n+1) → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q as.length = r as.length) (hM : ∀ i, 0 ≤ M i)
    (hm : ∀ i j, j ≤ as.length → |q j i-r j i| ≤ M i) (x : Fin (n+1) → ℝ) :
    |diagonalRootBoundary w φ as l q x-diagonalRootBoundary w φ as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*M i := by
  cases as with
  | nil =>
    have he : q 0 = r 0 := hend
    simp only [diagonalRootBoundary,diagonalBoundaryPotential,diagonalBoundarySteps,he,sub_self,abs_zero]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hM i))
  | cons a as =>
    have hFo : OrderedSteps 0 (diagonalBoundarySteps (a::as) (q 0) (fun j => q (j+1))) :=
      diagonalBoundarySteps_ordered (a::as) (by norm_num) (by norm_num) ho hu (fun c _ => c.property.le) _ _
    have hGo : OrderedSteps 0 (diagonalBoundarySteps (a::as) (r 0) (fun j => r (j+1))) :=
      diagonalBoundarySteps_ordered (a::as) (by norm_num) (by norm_num) ho hu (fun c _ => c.property.le) _ _
    have hF := (gaussianHierarchy_regular hw φ _ hFo 0).1.choose_spec
    have hG := (gaussianHierarchy_regular hw φ _ hGo 0).1.choose_spec
    have hqne := shiftedContinuation_tendsto_zero_mass hF
      (exponentialIncrement_gaussian (fun i => Real.toNNReal (q 0 i-l i))) x
    have hrne := shiftedContinuation_tendsto_zero_mass hG
      (exponentialIncrement_gaussian (fun i => Real.toNNReal (r 0 i-l i))) x
    apply le_of_tendsto (hqne.sub hrne).abs
    filter_upwards [self_mem_nhdsWithin, (Iio_mem_nhds a.property : Iio a.val ∈ 𝓝 (0:ℝ)) |> mem_nhdsWithin_of_mem_nhds] with e he hea
    have hep : 0 < e := he
    let c : PositiveMass := ⟨e,hep⟩
    have hoc : (c::a::as).Pairwise (fun a b => a.val ≤ b.val) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_,ho⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le
      · exact hea.le.trans ((List.pairwise_cons.mp ho).1 b hb)
    have huc : ∀ b ∈ c::a::as, b.val ≤ 1 := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le.trans (hu a List.mem_cons_self)
      · exact hu b hb
    exact diagonalBoundary_uniform hw φ D M hB (c::a::as) hoc huc hq hr hql hrl
      (by simpa only [List.length_cons,Nat.add_sub_cancel] using hend) hM
      (fun i j hj => hm i j (by simpa only [List.length_cons,Nat.lt_add_one_iff] using hj)) x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

omit [Fintype S] [Nonempty S] in
theorem finiteLinear_eq_sum (φ : (ι → ℝ) →L[ℝ] ℝ) (y : ι → ℝ) :
    φ y = ∑ i, y i*φ (Pi.single i 1) := by
  classical
  have he : y = ∑ i, y i • Pi.single i (1:ℝ) := by
    simp only [← Pi.single_smul,smul_eq_mul,mul_one,Finset.univ_sum_single]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

omit [Fintype S] [Nonempty S] in
theorem integral_exp_finiteLinear (φ : (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) :
    (∫ z, Real.exp (φ z) ∂Measure.pi fun i => gaussianReal 0 (q i)) =
      Real.exp ((1/2:ℝ)*∑ i, (q i:ℝ)*(φ (Pi.single i 1))^2) := by
  classical
  have he : (fun z => Real.exp (φ z)) = (fun z => ∏ i, Real.exp (z i*φ (Pi.single i 1))) := by
    funext z
    rw [finiteLinear_eq_sum φ z,Real.exp_sum]
  rw [he]
  rw [integral_fintype_prod_eq_prod (fun i z => Real.exp (z*φ (Pi.single i 1)))]
  have hi (i : ι) : (∫ z, Real.exp (z*φ (Pi.single i 1)) ∂gaussianReal 0 (q i)) =
      Real.exp ((q i:ℝ)*(φ (Pi.single i 1))^2/2) := by
    simpa only [mgf,zero_mul,zero_add,mul_comm] using
      congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := q i)) (φ (Pi.single i 1))
  simp_rw [hi]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

 

theorem spinLogPartition_mass_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (C : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i) (x : ι → ℝ) :
    shiftedContinuation (Measure.pi fun i => gaussianReal 0 (q i)) 1 (spinLogPartition w φ) x =
      spinLogPartition w φ x+(1/2:ℝ)*∑ i, (q i:ℝ)*C i := by
  classical
  have hi (σ : S) : Integrable (fun z => w σ * Real.exp (φ σ (x+z)))
      (Measure.pi fun i => gaussianReal 0 (q i)) := by
    exact ((exponentialIncrement_gaussian q).integrable_shift (φ σ).lipschitzWith 1 x |>.congr
      (by filter_upwards [] with z; simp only [one_mul])).const_mul _
  simp only [shiftedContinuation,one_mul,div_one,spinLogPartition,Real.exp_log (spinPartition_pos hw φ _)]
  simp only [spinPartition]
  rw [integral_finsetSum _ (fun σ _ => hi σ)]
  have he (σ : S) : (∫ z, w σ * Real.exp (φ σ (x+z)) ∂Measure.pi fun i => gaussianReal 0 (q i)) =
      w σ * Real.exp (φ σ x) * Real.exp ((1/2:ℝ)*∑ i, (q i:ℝ)*C i) := by
    simp_rw [map_add,Real.exp_add]
    rw [integral_const_mul,integral_const_mul,integral_exp_finiteLinear]
    simp_rw [hC]
    ring
  simp_rw [he]
  rw [← Finset.sum_mul]
  change Real.log (spinPartition w φ x*Real.exp _) = Real.log (spinPartition w φ x)+_
  rw [Real.log_mul (spinPartition_pos hw φ x).ne' (Real.exp_ne_zero _),Real.log_exp]

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {ι S : Type*} [Fintype ι] [DecidableEq ι] [Fintype S] [Nonempty S]

 

theorem gaussianHierarchy_append_mass_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (q : ι → ℝ≥0) (C : ι → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (steps : List (GaussianStep ι)) {a : ℝ} (ho : OrderedSteps a steps) (x : ι → ℝ) :
    gaussianHierarchy w φ (steps++[(1,q)]) x =
      gaussianHierarchy w φ steps x+(1/2:ℝ)*∑ i, (q i:ℝ)*C i := by
  induction steps generalizing a x with
  | nil => exact spinLogPartition_mass_one hw φ q C hC x
  | cons s steps ih =>
    rcases s with ⟨m,v⟩
    simp only [List.cons_append,gaussianHierarchy]
    rw [show gaussianHierarchy w φ (steps++[(1,q)]) =
      (fun y => gaussianHierarchy w φ steps y+(1/2:ℝ)*∑ i, (q i:ℝ)*C i) from funext (ih ho.2.2.2)]
    exact shiftedContinuation_add_const ho.2.2.1.ne'
      (gaussianHierarchy_integrable hw φ steps ho.2.2.2 m v) _ x

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators

 
def diagonalPointSteps {ι : Type*} (as : List PositiveMass) (q : ℕ → ι → ℝ) : List (GaussianStep ι) :=
  diagonalBoundarySteps as (q 0) (fun j => q (j+1))

theorem diagonalPointSteps_cons {ι : Type*} (a : PositiveMass) (as : List PositiveMass) (q : ℕ → ι → ℝ) :
    diagonalPointSteps (a::as) q = (a.val,fun i => Real.toNNReal (q 1 i-q 0 i))::
      diagonalPointSteps as (fun j => q (j+1)) := by
  simp only [diagonalPointSteps,diagonalBoundarySteps,Nat.zero_add,Nat.add_assoc]

theorem diagonalPointSteps_congr {ι : Type*} (as : List PositiveMass) {q r : ℕ → ι → ℝ}
    (h : ∀ j, j ≤ as.length → q j = r j) : diagonalPointSteps as q = diagonalPointSteps as r := by
  induction as generalizing q r with
  | nil => rfl
  | cons a as ih =>
    rw [diagonalPointSteps_cons,diagonalPointSteps_cons,h 0 (by simp),h 1 (by simp)]
    congr 1
    apply ih
    intro j hj
    exact h (j+1) (by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hj)

theorem diagonalPointSteps_append {ι : Type*} (as bs : List PositiveMass) (q : ℕ → ι → ℝ) :
    diagonalPointSteps (as++bs) q = diagonalPointSteps as q++
      diagonalPointSteps bs (fun j => q (j+as.length)) := by
  induction as generalizing q with
  | nil => simp only [List.nil_append,List.length_nil,Nat.add_zero,diagonalPointSteps,diagonalBoundarySteps]
  | cons a as ih =>
    rw [List.cons_append,diagonalPointSteps_cons,diagonalPointSteps_cons,ih,List.cons_append]
    congr 2

 
def extendBoundary {ι : Type*} (q : ℕ → ι → ℝ) (N : ℕ) (t : ι → ℝ) : ℕ → ι → ℝ :=
  fun j => if j ≤ N then q j else t

theorem extendBoundary_le {ι : Type*} (q : ℕ → ι → ℝ) (N : ℕ) (t : ι → ℝ) {j : ℕ} (hj : j ≤ N) :
    extendBoundary q N t j = q j := by simp only [extendBoundary,ite_eq_left hj]

theorem extendBoundary_gt {ι : Type*} (q : ℕ → ι → ℝ) (N : ℕ) (t : ι → ℝ) {j : ℕ} (hj : N < j) :
    extendBoundary q N t j = t := by simp only [extendBoundary,ite_eq_right (not_le.mpr hj)]

theorem extendBoundary_monotone {ι : Type*} {q : ℕ → ι → ℝ} {N : ℕ} {t : ι → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (ht : ∀ i, q N i ≤ t i) (i : ι) :
    Monotone (fun j => extendBoundary q N t j i) := by
  intro j k hjk
  change extendBoundary q N t j i ≤ extendBoundary q N t k i
  by_cases hk : k ≤ N
  · rw [extendBoundary_le q N t hk,extendBoundary_le q N t (hjk.trans hk)]
    exact hq i hjk
  · rw [extendBoundary_gt q N t (lt_of_not_ge hk)]
    by_cases hj : j ≤ N
    · rw [extendBoundary_le q N t hj]
      exact (hq i hj).trans (ht i)
    · rw [extendBoundary_gt q N t (lt_of_not_ge hj)]

variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 theorem diagonalRoot_append_one {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (C : Fin (n+1) → ℝ)
    (hC : ∀ σ i, (φ σ (Pi.single i 1))^2 = C i)
    (as : List PositiveMass) (ho : as.Pairwise (fun a b => a.val ≤ b.val))
    (hu : ∀ a ∈ as, a.val ≤ 1) (l : Fin (n+1) → ℝ) (q : ℕ → Fin (n+1) → ℝ)
    (t : Fin (n+1) → ℝ) (ht : ∀ i, q as.length i ≤ t i) (x : Fin (n+1) → ℝ) :
    diagonalRootBoundary w φ (as++[⟨1,by norm_num⟩]) l (extendBoundary q as.length t) x =
      diagonalRootBoundary w φ as l q x+(1/2:ℝ)*∑ i, (t i-q as.length i)*C i := by
  let v : Fin (n+1) → ℝ≥0 := fun i => Real.toNNReal (t i-q as.length i)
  have hv : ∀ i, (v i:ℝ) = t i-q as.length i := fun i => Real.coe_toNNReal _ (sub_nonneg.mpr (ht i))
  have hs : diagonalPointSteps (as++[⟨1,by norm_num⟩]) (extendBoundary q as.length t) =
      diagonalPointSteps as q++[(1,v)] := by
    rw [diagonalPointSteps_append,diagonalPointSteps_congr as (fun j hj => extendBoundary_le q as.length t hj)]
    congr 1
    simp only [diagonalPointSteps,diagonalBoundarySteps,Nat.zero_add]
    rw [extendBoundary_le q as.length t le_rfl,extendBoundary_gt q as.length t (show as.length < 1+as.length by omega)]
  have ho' : OrderedSteps 0 (diagonalPointSteps as q) :=
    diagonalBoundarySteps_ordered as (by norm_num) (by norm_num) ho hu (fun a _ => a.property.le) _ _
  have he := gaussianHierarchy_append_mass_one hw φ v C hC (diagonalPointSteps as q) ho'
  have hF := (gaussianHierarchy_regular hw φ (diagonalPointSteps as q) ho' 0).1.choose_spec
  have hi := (exponentialIncrement_gaussian (fun i => Real.toNNReal (q 0 i-l i))).integrable_lipschitz hF x
  change zeroContinuation _ (gaussianHierarchy w φ (diagonalPointSteps (as++[⟨1,by norm_num⟩]) _)) x = _
  rw [hs,extendBoundary_le q as.length t (Nat.zero_le _)]
  simp_rw [zeroContinuation,he,hv]
  rw [integral_add hi (integrable_const _)]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
  rfl

end SKFluctuations.Hierarchy

namespace SKFluctuations.Hierarchy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal BigOperators
variable {S : Type*} [Fintype S] [Nonempty S] {n : ℕ}

 
def rootBoundaryCost (as : List PositiveMass) (q r : ℕ → ℝ) : ℝ :=
  match as with
  | [] => 0
  | a::bs => a.val*|q 0-r 0|+boundaryCost (a::bs) (fun j => q (j+1)) (fun j => r (j+1))

 
theorem diagonalRoot_comparison {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (Fin (n+1) → ℝ) →L[ℝ] ℝ) (D : Fin (n+1) → ℝ)
    (hB : ∀ i σ, |φ σ (Pi.single i 1)| ≤ D i) (as : List PositiveMass)
    (ho : as.Pairwise (fun a b => a.val ≤ b.val)) (hu : ∀ a ∈ as, a.val ≤ 1)
    {l : Fin (n+1) → ℝ} {q r : ℕ → Fin (n+1) → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hr : ∀ i, Monotone (fun j => r j i))
    (hql : ∀ i, l i ≤ q 0 i) (hrl : ∀ i, l i ≤ r 0 i)
    (hend : q as.length = r as.length) (x : Fin (n+1) → ℝ) :
    |diagonalRootBoundary w φ as l q x-diagonalRootBoundary w φ as l r x| ≤
      (1/2:ℝ)*∑ i, (D i)^2*rootBoundaryCost as (fun j => q j i) (fun j => r j i) := by
  cases as with
  | nil =>
    have he : q 0 = r 0 := hend
    simp only [diagonalRootBoundary,diagonalBoundaryPotential,diagonalBoundarySteps,he,sub_self,abs_zero,
      rootBoundaryCost,mul_zero,Finset.sum_const_zero,le_refl]
  | cons a as =>
    have hFo : OrderedSteps 0 (diagonalBoundarySteps (a::as) (q 0) (fun j => q (j+1))) :=
      diagonalBoundarySteps_ordered (a::as) (by norm_num) (by norm_num) ho hu (fun c _ => c.property.le) _ _
    have hGo : OrderedSteps 0 (diagonalBoundarySteps (a::as) (r 0) (fun j => r (j+1))) :=
      diagonalBoundarySteps_ordered (a::as) (by norm_num) (by norm_num) ho hu (fun c _ => c.property.le) _ _
    have hF := (gaussianHierarchy_regular hw φ _ hFo 0).1.choose_spec
    have hG := (gaussianHierarchy_regular hw φ _ hGo 0).1.choose_spec
    have hqne := shiftedContinuation_tendsto_zero_mass hF
      (exponentialIncrement_gaussian (fun i => Real.toNNReal (q 0 i-l i))) x
    have hrne := shiftedContinuation_tendsto_zero_mass hG
      (exponentialIncrement_gaussian (fun i => Real.toNNReal (r 0 i-l i))) x
    apply le_of_tendsto (hqne.sub hrne).abs
    filter_upwards [self_mem_nhdsWithin, (Iio_mem_nhds a.property : Iio a.val ∈ 𝓝 (0:ℝ)) |> mem_nhdsWithin_of_mem_nhds] with e he hea
    have hep : 0 < e := he
    let c : PositiveMass := ⟨e,hep⟩
    have hoc : (c::a::as).Pairwise (fun a b => a.val ≤ b.val) := by
      apply List.pairwise_cons.mpr
      refine ⟨?_,ho⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le
      · exact hea.le.trans ((List.pairwise_cons.mp ho).1 b hb)
    have huc : ∀ b ∈ c::a::as, b.val ≤ 1 := by
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hea.le.trans (hu a List.mem_cons_self)
      · exact hu b hb
    have hb := diagonalBoundary_comparison hw φ D hB (c::a::as) hoc huc hq hr hql hrl
      (by simpa only [List.length_cons,Nat.add_sub_cancel] using hend) x
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simp only [boundaryCost,rootBoundaryCost]
    apply add_le_add _ le_rfl
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    change |e-a.val| ≤ a.val
    rw [abs_of_nonpos (sub_nonpos.mpr (show e ≤ a.val from hea.le))]
    linarith

end SKFluctuations.Hierarchy

end

end OAI
