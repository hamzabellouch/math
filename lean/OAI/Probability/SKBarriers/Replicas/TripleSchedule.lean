import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixChain
import OAI.Probability.SKBarriers.Replicas.TripleClockAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

abbrev TripleMiddleIncrement := ProductIncrement (E:=ℝ × ℝ) (F:=ℝ)

def rawVariance (l : List (ℝ × ℝ)) : ℝ := (l.map (fun p => p.2^2)).sum

def rawPenalty (l : List (ℝ × ℝ)) (q : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2^2))) q

def rawArea (l : List (ℝ × ℝ)) : ℝ := (l.map (fun p => p.1*p.2^2)).sum

def weightedCross (l : List (ℝ × (ℝ × ℝ))) : ℝ := (l.map (fun p => p.2.1*p.2.2)).sum

def weightedVariance (l : List (ℝ × (ℝ × ℝ))) : ℝ := (l.map (fun p => p.2.2^2)).sum

def weightedCrossPenalty (l : List (ℝ × (ℝ × ℝ))) (g : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2.1*p.2.2))) g

def weightedVariancePenalty (l : List (ℝ × (ℝ × ℝ))) (G : ℝ) : ℝ :=
  chainPotentialPenalty (fun x : ℝ => x^2) (l.map (fun p => (p.1,p.2.2^2))) G

def weightedUnderlying (l : List (ℝ × (ℝ × ℝ))) : List (ℝ × ℝ) := l.map (fun p => (p.1,p.2.1))

def tripleCommonSchedule (l : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (p.1/3,![p.2,p.2,p.2]))

def tripleMiddleVector (δ : ℝ) : TripleMiddleIncrement → Fin 3 → ℝ
  | .inl p => ![p.2.1,δ*p.2.2,-δ*p.2.2]
  | .inr p => ![0,p.2,p.2]

def tripleMiddleSchedule (δ : ℝ) (l : List TripleMiddleIncrement) : List (ℝ × (Fin 3 → ℝ)) :=
  l.map (fun p => (productMass p,tripleMiddleVector δ p))

def tripleTailBlock (p : ℝ × ℝ) : List (ℝ × (Fin 3 → ℝ)) :=
  [(p.1,![p.2,0,0]),(p.1,![0,p.2,0]),(p.1,![0,0,p.2])]

def tripleTailSchedule (l : List (ℝ × ℝ)) : List (ℝ × (Fin 3 → ℝ)) := l.flatMap tripleTailBlock

@[simp] theorem matrixChainCovariance_nil {d : ℕ} : matrixChainCovariance ([] : List (ℝ × (Fin d → ℝ)))=0 := rfl
@[simp] theorem matrixChainCovariance_cons {d : ℕ} (p : ℝ × (Fin d → ℝ)) (l : List (ℝ × (Fin d → ℝ))) :
    matrixChainCovariance (p::l)=rankOneMatrix p.2+matrixChainCovariance l := rfl

theorem matrixChainCovariance_append {d : ℕ} (l r : List (ℝ × (Fin d → ℝ))) :
    matrixChainCovariance (l++r)=matrixChainCovariance l+matrixChainCovariance r := by
  simp only [matrixChainCovariance,List.map_append,chainSum_append]

@[simp] theorem matrixChainPenalty_nil {d : ℕ} (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty [] Q=0 := rfl
@[simp] theorem matrixChainPenalty_cons {d : ℕ} (p : ℝ × (Fin d → ℝ)) (l : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty (p::l) Q=p.1*(matrixSquare d (Q+rankOneMatrix p.2)-matrixSquare d Q)+
      matrixChainPenalty l (Q+rankOneMatrix p.2) := rfl

theorem matrixChainPenalty_append {d : ℕ} (l r : List (ℝ × (Fin d → ℝ))) (Q : Fin d → Fin d → ℝ) :
    matrixChainPenalty (l++r) Q=matrixChainPenalty l Q+matrixChainPenalty r (Q+matrixChainCovariance l) := by
  simp only [matrixChainPenalty,List.map_append,chainPotentialPenalty_append,matrixChainCovariance]

theorem tripleCommonSchedule_covariance (l : List (ℝ × ℝ)) (r : ℝ) :
    tripleClockMatrix r r r r r+matrixChainCovariance (tripleCommonSchedule l)=
      tripleClockMatrix (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) (r+rawVariance l) := by
  induction l generalizing r with
  | nil => simp [tripleCommonSchedule,rawVariance]
  | cons p l ih =>
    simp only [tripleCommonSchedule] at ih
    simp only [tripleCommonSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
    change (fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j)+_=_
    rw [tripleClockPerturbed_common,ih]
    simp only [rawVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleCommonSchedule_penalty (l : List (ℝ × ℝ)) (r : ℝ) :
    matrixChainPenalty (tripleCommonSchedule l) (tripleClockMatrix r r r r r)=3*rawPenalty l r := by
  induction l generalizing r with
  | nil => simp [tripleCommonSchedule,rawPenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleCommonSchedule] at ih
    simp only [tripleCommonSchedule,List.map_cons,matrixChainPenalty_cons]
    change p.1/3*(matrixSquare 3 ((fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j))-_)+
      matrixChainPenalty _ (fun i j => tripleClockMatrix r r r r r i j+(![p.2,p.2,p.2] : Fin 3 → ℝ) i*(![p.2,p.2,p.2] : Fin 3 → ℝ) j)=_
    rw [tripleClockPerturbed_common,ih,tripleClockMatrix_square,tripleClockMatrix_square]
    simp only [rawPenalty,List.map_cons,chainPotentialPenalty]
    ring

theorem tripleMiddleSchedule_covariance (δ : ℝ) (l : List TripleMiddleIncrement) (a b r g G : ℝ) :
    tripleClockPerturbed a b b r b δ g G+matrixChainCovariance (tripleMiddleSchedule δ l)=
      tripleClockPerturbed (a+rawVariance (weightedUnderlying (productLeft l)))
        (b+rawVariance (productRight l)) (b+rawVariance (productRight l)) r
        (b+rawVariance (productRight l)) δ (g+weightedCross (productLeft l)) (G+weightedVariance (productLeft l)) := by
  induction l generalizing a b g G with
  | nil => simp [tripleMiddleSchedule,productLeft,productRight,weightedUnderlying,rawVariance,weightedCross,weightedVariance]
  | cons p l ih =>
    simp only [tripleMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => tripleClockPerturbed a b b r b δ g G i j+
        (![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) i*(![p.2.1,δ*p.2.2,-δ*p.2.2] : Fin 3 → ℝ) j)+_=_
      rw [tripleClockPerturbed_singleton,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]
    | inr p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainCovariance_cons,← add_assoc]
      change (fun i j => tripleClockPerturbed a b b r b δ g G i j+
        (![0,p.2,p.2] : Fin 3 → ℝ) i*(![0,p.2,p.2] : Fin 3 → ℝ) j)+_=_
      rw [tripleClockPerturbed_pair,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawVariance,weightedCross,weightedVariance,List.map_cons,List.sum_cons,add_assoc]

theorem tripleMiddleSchedule_penalty (δ : ℝ) (l : List TripleMiddleIncrement) (a b r g G : ℝ) :
    matrixChainPenalty (tripleMiddleSchedule δ l) (tripleClockPerturbed a b b r b δ g G)=
      rawPenalty (weightedUnderlying (productLeft l)) a+2*rawPenalty (productRight l) b+
      4*δ^2*weightedCrossPenalty (productLeft l) g+4*δ^4*weightedVariancePenalty (productLeft l) G := by
  induction l generalizing a b g G with
  | nil => simp [tripleMiddleSchedule,productLeft,productRight,weightedUnderlying,rawPenalty,
      weightedCrossPenalty,weightedVariancePenalty,chainPotentialPenalty]
  | cons p l ih =>
    simp only [tripleMiddleSchedule] at ih
    cases p with
    | inl p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := tripleClockPerturbed_singleton a b b r b δ g G p.2.1 p.2.2
      change tripleClockPerturbed a b b r b δ g G+rankOneMatrix (tripleMiddleVector δ (.inl p))=_ at he
      rw [he]
      change p.1*(_-_)+_=_
      rw [tripleClockPerturbed_middle_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,weightedVariancePenalty,List.map_cons,chainPotentialPenalty]
      ring
    | inr p =>
      simp only [tripleMiddleSchedule,List.map_cons,matrixChainPenalty_cons]
      have he := tripleClockPerturbed_pair a b b r b δ g G p.2
      change tripleClockPerturbed a b b r b δ g G+rankOneMatrix (tripleMiddleVector δ (.inr p))=_ at he
      rw [he]
      change p.1/2*(_-_)+_=_
      rw [tripleClockPerturbed_pair_penalty,ih]
      simp only [productLeft,productRight,List.filterMap_cons,weightedUnderlying,rawPenalty,
        weightedCrossPenalty,weightedVariancePenalty,List.map_cons,chainPotentialPenalty]
      ring

end SK.Analytic

end
end

end OAI
