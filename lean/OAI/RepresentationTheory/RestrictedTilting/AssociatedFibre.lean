import OAI.RepresentationTheory.RestrictedTilting.PlaneFibre
import OAI.RepresentationTheory.RestrictedTilting.AssociatedNumerator
import OAI.RepresentationTheory.RestrictedTilting.XChartLineEval

namespace OAI

namespace FiberFunctorProof
universe u
noncomputable section
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))
variable (P : Matrix ι ι (Polynomial k))
variable (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
variable (d : ℕ) (hd : ∀ i j, (P i j).natDegree ≤ d)
local notation "N" => associatedSectionsSubmodule k ι ρ
local notation "A" => MvPolynomial (Fin 2) k

def associatedE1Equiv : (N ⧸ planeFibreRelations (k := k) N ![1,0]) ≃ₗ[k] (ι → k) :=
  (planeFibreEquivOfSplit (k := k) N (ι → A) ![1,0]
    (associatedNumeratorLinear k ι ρ P hP d hd) (associatedDenominatorLinear k ι ρ P hP d hd)
    ((MvPolynomial.X 0)^(d+d)) (by simp)
    (associatedDenominator_numerator k ι ρ P hP d hd)
    (associatedNumerator_denominator k ι ρ P hP d hd)).trans
      (planeFreeFibreEquiv (k := k) ι ![1,0])

omit [Infinite k] in
lemma planeLineEval_one (F : A) : planeLineEval k (1 : kˣ) F = MvPolynomial.eval ![1,0] F := by
  have he : (fun i : Fin 2 => if i = 0 then ((1 : kˣ) : k) else 0) = ![1,0] := by
    ext i; fin_cases i <;> simp
  simp only [planeLineEval, he, MvPolynomial.aeval_def]
  rfl

lemma associatedNumerator_e1 (f : N) :
    planeVectorEval ι ![1,0] (associatedNumeratorLinear k ι ρ P hP d hd f) =
      regularVectorEvaluation k ι 1 f.val := by
  funext i
  have he := congrArg (chartLineEval k 1) (associatedNumeratorLinear_spec k ι ρ P hP d hd f i)
  rw [chartLineEval_algebraMap, planeLineEval_one, map_mul, map_pow,
    chartLineEval_coordinate, ite_eq_left rfl, Units.val_one, one_pow, one_mul] at he
  change MvPolynomial.eval ![1,0] _ = _
  rw [he]
  have hh := congrFun (associatedXChart_line k ι ρ (1 : kˣ) f) i
  simpa only [map_one] using hh

lemma associatedE1Equiv_mk (f : N) :
    associatedE1Equiv k ι ρ P hP d hd ((planeFibreRelations (k := k) N ![1,0]).mkQ f) =
      regularVectorEvaluation k ι 1 f.val := by
  change planeVectorEval ι ![1,0] (associatedNumeratorLinear k ι ρ P hP d hd f) = _
  exact associatedNumerator_e1 k ι ρ P hP d hd f

lemma associatedE1Equiv_unipotent (t : k) (f : N) :
    associatedE1Equiv k ι ρ P hP d hd ((planeFibreRelations (k := k) N ![1,0]).mkQ
      (associatedSectionsRepresentation k ι ρ (unipotent k t) f)) =
      ρ (Multiplicative.ofAdd t) (associatedE1Equiv k ι ρ P hP d hd
        ((planeFibreRelations (k := k) N ![1,0]).mkQ f)) := by
  rw [associatedE1Equiv_mk, associatedE1Equiv_mk]
  simpa only [map_one, Units.val_one, one_pow, div_one] using
    associatedSections_line_unipotent k ι ρ (1 : kˣ) t f
end
end FiberFunctorProof

end OAI
