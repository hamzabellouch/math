import Mathlib
import OAI.Combinatorics.Chromatic.QuantumTorus.TorusContinuity

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries LaurentPrecision ElementaryPositivity.PowerSeriesSplit
noncomputable section
variable {M I ι : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ)
variable (C : (I → ℤ) →+ M) (l : Filter ι)
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup
local instance : Sub (Torus v Ω) := (Torus.instRing v Ω).toSub
attribute [local instance] Classical.propDecidable

def SeriesConverges (f : ι → PowerSeries (Torus v Ω)) (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,TorusConverges v Ω l (fun i=>coeff n (f i)) (coeff n F)

def SeriesGraded (F : PowerSeries (Torus v Ω)) : Prop :=
  ∀n,coeff n F∈rootGrade v Ω C n

lemma seriesConverges_const (F : PowerSeries (Torus v Ω)) :
    SeriesConverges v Ω l (fun _=>F) F := fun _=>torusConverges_const v Ω l _

lemma SeriesConverges.sub {f g : ι → PowerSeries (Torus v Ω)} {F G : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : SeriesConverges v Ω l g G) :
    SeriesConverges v Ω l (fun i=>f i-g i) (F-G) := by
  intro n
  exact (hf n).sub v Ω l (hg n)

lemma SeriesConverges.mul {f g : ι → PowerSeries (Torus v Ω)} {F G : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F) (hg : SeriesConverges v Ω l g G)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hgg : ∀i,SeriesGraded v Ω C (g i))
    (hF : SeriesGraded v Ω C F) (hG : SeriesGraded v Ω C G) :
    SeriesConverges v Ω l (fun i=>f i*g i) (F*G) := by
  intro n
  simp only [coeff_mul]
  apply TorusConverges.sum
  intro p hp
  exact (hf p.1).mul_graded v Ω C l (hg p.2) p.1 p.2
    (fun i=>hfg i p.1) (fun i=>hgg i p.2) (hF p.1) (hG p.2)

lemma filter_pair_graded (p : M → Prop) (F : PowerSeries (Torus v Ω))
    (hF : SeriesGraded v Ω C F) (n : ℕ) :
    (pairCoefficients (Finsupp.filterAddHom p) F n).1∈rootGrade v Ω C n ∧
    (pairCoefficients (Finsupp.filterAddHom p) F n).2∈rootGrade v Ω C n := by
  have H := factors_graded (Finsupp.filterAddHom p) (rootGrade v Ω C)
    (rootGrade_one v Ω C) (rootGrade_mul v Ω C)
    (fun n x hx=>rootGrade_filter v Ω C p n x hx) F hF
  simpa only [leftFactor,rightFactor,coeff_mk] using And.intro (H.1 n) (H.2 n)

lemma filter_pair_converges (p : M → Prop)
    {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) (n : ℕ) :
    TorusConverges v Ω l (fun i=>(pairCoefficients (Finsupp.filterAddHom p) (f i) n).1)
      (pairCoefficients (Finsupp.filterAddHom p) F n).1 ∧
    TorusConverges v Ω l (fun i=>(pairCoefficients (Finsupp.filterAddHom p) (f i) n).2)
      (pairCoefficients (Finsupp.filterAddHom p) F n).2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [pairCoefficients] using
        And.intro (torusConverges_const v Ω l 1) (torusConverges_const v Ω l 1)
    | succ n =>
      let P : Torus v Ω →+ Torus v Ω := Finsupp.filterAddHom p
      have hprod : TorusConverges v Ω l
          (fun i=>∑j : Fin n,(pairCoefficients P (f i) (j.val+1)).1 *
            (pairCoefficients P (f i) (n-j.val)).2)
          (∑j : Fin n,(pairCoefficients P F (j.val+1)).1 *
            (pairCoefficients P F (n-j.val)).2) := by
        apply TorusConverges.sum
        intro j hj
        exact (ih (j.val+1) (by omega)).1.mul_graded v Ω C l
          (ih (n-j.val) (by omega)).2 (j.val+1) (n-j.val)
          (fun i=>(filter_pair_graded v Ω C p (f i) (hfg i) _).1)
          (fun i=>(filter_pair_graded v Ω C p (f i) (hfg i) _).2)
          (filter_pair_graded v Ω C p F hF _).1
          (filter_pair_graded v Ω C p F hF _).2
      have hr := (hf (n+1)).sub v Ω l hprod
      have hp := hr.filter v Ω l p
      constructor
      · unfold pairCoefficients
        exact hp
      · unfold pairCoefficients
        exact hr.sub v Ω l hp

lemma filter_factors_converge (p : M → Prop)
    {f : ι → PowerSeries (Torus v Ω)} {F : PowerSeries (Torus v Ω)}
    (hf : SeriesConverges v Ω l f F)
    (hfg : ∀i,SeriesGraded v Ω C (f i)) (hF : SeriesGraded v Ω C F) :
    SeriesConverges v Ω l (fun i=>leftFactor (Finsupp.filterAddHom p) (f i))
      (leftFactor (Finsupp.filterAddHom p) F) ∧
    SeriesConverges v Ω l (fun i=>rightFactor (Finsupp.filterAddHom p) (f i))
      (rightFactor (Finsupp.filterAddHom p) F) := by
  constructor
  · intro n
    simpa only [leftFactor,coeff_mk] using (filter_pair_converges v Ω C l p hf hfg hF n).1
  · intro n
    simpa only [rightFactor,coeff_mk] using (filter_pair_converges v Ω C l p hf hfg hF n).2

theorem chart_three_converge (h : M →+ ℝ)
    {f : ι → CompletedPositive v Ω C} {F : CompletedPositive v Ω C}
    (hf : SeriesConverges v Ω l (fun i=>(f i).val) F.val) :
    SeriesConverges v Ω l (fun i=>(chartPositive v Ω C h (f i)).val)
      (chartPositive v Ω C h F).val ∧
    SeriesConverges v Ω l (fun i=>(chartZero v Ω C h (f i)).val)
      (chartZero v Ω C h F).val ∧
    SeriesConverges v Ω l (fun i=>(chartNegative v Ω C h (f i)).val)
      (chartNegative v Ω C h F).val := by
  have H := filter_factors_converge v Ω C l (fun m=>0<h m) hf
    (fun i=>(f i).property.2) F.property.2
  refine ⟨H.1,?_⟩
  exact filter_factors_converge v Ω C l (fun m=>h m=0) H.2
    (fun i=>(chartRemainder v Ω C h (f i)).property.2)
    (chartRemainder v Ω C h F).property.2

end
end ElementaryPositivity.QuantumTorus

end

end OAI
