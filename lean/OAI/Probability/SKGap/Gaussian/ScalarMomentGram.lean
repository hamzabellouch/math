import Mathlib
import OAI.Probability.SKGap.Entropy.WeightedScalarMoments
import OAI.Probability.SKGap.Localization.EmpiricalLaw

namespace OAI

section
noncomputable section
namespace SKGap
open Real Matrix MeasureTheory ProbabilityTheory Set
open scoped BigOperators Matrix.Norms.Frobenius

def gramCoordinates (d s y : ℝ) : Fin 3 → ℝ := ![1,tanh y,(y-d)/s]

def scalarMomentGram (P : ProbabilityMeasure ℝ) (d s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let M := fun k l => ∫ y,weightedScalarMoment k l y ∂P
  !![M 0 0,M 0 1,(M 1 0-d*M 0 0)/s;
     M 0 1,M 0 2,(M 1 1-d*M 0 1)/s;
     (M 1 0-d*M 0 0)/s,(M 1 1-d*M 0 1)/s,
       (M 2 0-2*d*M 1 0+d^2*M 0 0)/s^2]

lemma scalarMomentGram_integral (P : ProbabilityMeasure ℝ) (d s : ℝ) :
    scalarMomentGram P d s = fun i k => ∫ y,
      (1-tanh y^2)*gramCoordinates d s y i*gramCoordinates d s y k ∂P := by
  have hi (k l : Fin 3) := (weightedScalarMoment k l).integrable (μ := (P : Measure ℝ))
  have h00 : (∫ y,(1-tanh y^2) ∂P)=∫ y,weightedScalarMoment 0 0 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]
  have h01 : (∫ y,(1-tanh y^2)*tanh y ∂P)=∫ y,weightedScalarMoment 0 1 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]; ring
  have h02 : (∫ y,(1-tanh y^2)*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 1 0 y ∂P)-d*(∫ y,weightedScalarMoment 0 0 y ∂P))/s := by
    calc
      _ = ∫ y,(weightedScalarMoment 1 0 y-d*weightedScalarMoment 0 0 y)/s ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by rw [integral_div,integral_sub (hi 1 0) ((hi 0 0).const_mul d),integral_const_mul]
  have h11 : (∫ y,(1-tanh y^2)*tanh y*tanh y ∂P)=∫ y,weightedScalarMoment 0 2 y ∂P := by
    congr 1; funext y; simp [weightedScalarMoment]; ring
  have h12 : (∫ y,(1-tanh y^2)*tanh y*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 1 1 y ∂P)-d*(∫ y,weightedScalarMoment 0 1 y ∂P))/s := by
    calc
      _ = ∫ y,(weightedScalarMoment 1 1 y-d*weightedScalarMoment 0 1 y)/s ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by rw [integral_div,integral_sub (hi 1 1) ((hi 0 1).const_mul d),integral_const_mul]
  have h22 : (∫ y,(1-tanh y^2)*((y-d)/s)*((y-d)/s) ∂P)=
      ((∫ y,weightedScalarMoment 2 0 y ∂P)-2*d*(∫ y,weightedScalarMoment 1 0 y ∂P)+
        d^2*(∫ y,weightedScalarMoment 0 0 y ∂P))/s^2 := by
    calc
      _ = ∫ y,(weightedScalarMoment 2 0 y-2*d*weightedScalarMoment 1 0 y+
          d^2*weightedScalarMoment 0 0 y)/s^2 ∂P := by
        congr 1; funext y; simp [weightedScalarMoment]; ring
      _ = _ := by
        rw [integral_div,integral_add (show Integrable (fun y => weightedScalarMoment 2 0 y-2*d*weightedScalarMoment 1 0 y) (P : Measure ℝ) from
          (hi 2 0).sub ((hi 1 0).const_mul (2*d))) ((hi 0 0).const_mul (d^2)),
          integral_sub (hi 2 0) ((hi 1 0).const_mul (2*d))]
        simp only [integral_const_mul]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [scalarMomentGram,gramCoordinates]
  all_goals first | exact h00.symm | exact h01.symm | exact h02.symm |
    exact h11.symm | exact h12.symm | exact h22.symm |
    (convert h12.symm using 1; congr 1; funext y; ring)

lemma continuousAt_scalarMomentGram {p : ProbabilityMeasure ℝ × (ℝ × ℝ)} (hs : p.2.2 ≠ 0) :
    ContinuousAt (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => scalarMomentGram p.1 p.2.1 p.2.2) p := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro k
  have hm (i k : Fin 3) : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) =>
      ∫ y,weightedScalarMoment i k y ∂p.1) :=
    (continuous_weightedScalarMoment_integral i k).comp continuous_fst
  have hd : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => p.2.1) := continuous_fst.comp continuous_snd
  have hss : Continuous (fun p : ProbabilityMeasure ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.comp continuous_snd
  fin_cases i <;> fin_cases k <;>
    simp only [scalarMomentGram, Matrix.of_apply, Matrix.cons_val,Fin.isValue,Fin.reduceFinMk]
  all_goals first | exact (hm _ _).continuousAt |
    exact ((hm _ _).continuousAt.sub (hd.continuousAt.mul (hm _ _).continuousAt)).div hss.continuousAt hs |
    exact (((hm _ _).continuousAt.sub
      ((continuousAt_const.mul hd.continuousAt).mul (hm _ _).continuousAt)).add
      ((hd.continuousAt.pow 2).mul (hm _ _).continuousAt)).div
      (hss.continuousAt.pow 2) (pow_ne_zero _ hs)

lemma scalarMomentGram_empirical {n : ℕ} [NeZero n] (y : Fin n → ℝ) (d s : ℝ) :
    scalarMomentGram (empiricalLaw y) d s = fun i k =>
      (n:ℝ)⁻¹*∑ l,(1-tanh (y l)^2)*gramCoordinates d s (y l) i*gramCoordinates d s (y l) k := by
  rw [scalarMomentGram_integral]
  ext i k
  simp only [integral_empiricalLaw,Fintype.card_fin]
end SKGap
end
end

end OAI
