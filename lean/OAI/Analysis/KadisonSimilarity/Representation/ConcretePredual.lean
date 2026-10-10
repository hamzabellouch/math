import OAI.Analysis.KadisonSimilarity.Representation.WeakOperatorCompactness
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! The Banach predual of a concrete von Neumann algebra, constructed as the
closed span of its vector functionals. The double commutant property makes
every bounded functional on this space evaluation at an algebra element. -/

noncomputable section
namespace KadisonSimilarity

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (M : VonNeumannAlgebra H)

/-- A vector functional restricted to the concrete algebra. -/
def normalCoefficient (x y : H) : StrongDual ℂ M.toStarSubalgebra :=
  LinearMap.mkContinuous
    { toFun := fun a => inner ℂ y ((a : H →L[ℂ] H) x)
      map_add' := by intros; simp [inner_add_right]
      map_smul' := by intros; simp [inner_smul_right] }
    (‖x‖ * ‖y‖) (fun a => by
      calc
        ‖inner ℂ y ((a : H →L[ℂ] H) x)‖ ≤ ‖y‖ * ‖(a : H →L[ℂ] H) x‖ :=
          norm_inner_le_norm _ _
        _ ≤ ‖y‖ * (‖a‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left ((a : H →L[ℂ] H).le_opNorm x) (norm_nonneg y)
        _ = (‖x‖ * ‖y‖) * ‖a‖ := by ring)

@[simp] theorem normalCoefficient_apply (x y : H) (a : M.toStarSubalgebra) :
    normalCoefficient M x y a = inner ℂ y ((a : H →L[ℂ] H) x) := rfl

theorem normalCoefficient_norm_le (x y : H) :
    ‖normalCoefficient M x y‖ ≤ ‖x‖ * ‖y‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _

/-- Normal functionals, with their operator-dual norm. -/
def normalFunctionalSpace : ClosedSubmodule ℂ (StrongDual ℂ M.toStarSubalgebra) :=
  (Submodule.span ℂ (Set.range fun xy : H × H => normalCoefficient M xy.1 xy.2)).closure

def ConcretePredual : Type _ := normalFunctionalSpace M

instance : NormedAddCommGroup (ConcretePredual M) :=
  inferInstanceAs (NormedAddCommGroup (normalFunctionalSpace M))

instance : NormedSpace ℂ (ConcretePredual M) :=
  inferInstanceAs (NormedSpace ℂ (normalFunctionalSpace M))

instance : CompleteSpace (ConcretePredual M) :=
  inferInstanceAs (CompleteSpace (normalFunctionalSpace M))

instance : CoeOut (ConcretePredual M) (StrongDual ℂ M.toStarSubalgebra) := ⟨Subtype.val⟩

def predualCoefficient (x y : H) : ConcretePredual M :=
  ⟨normalCoefficient M x y, Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (x, y)))⟩

@[simp] theorem predualCoefficient_apply (x y : H) (a : M.toStarSubalgebra) :
    (predualCoefficient M x y : StrongDual ℂ M.toStarSubalgebra) a =
      inner ℂ y ((a : H →L[ℂ] H) x) := rfl

theorem predualCoefficient_add_left (x y z : H) :
    predualCoefficient M (x + y) z = predualCoefficient M x z + predualCoefficient M y z := by
  apply Subtype.ext
  ext a
  change inner ℂ z ((a : H →L[ℂ] H) (x + y)) =
    inner ℂ z ((a : H →L[ℂ] H) x) + inner ℂ z ((a : H →L[ℂ] H) y)
  simp [inner_add_right]

theorem predualCoefficient_smul_left (c : ℂ) (x y : H) :
    predualCoefficient M (c • x) y = c • predualCoefficient M x y := by
  apply Subtype.ext
  ext a
  change inner ℂ y ((a : H →L[ℂ] H) (c • x)) =
    c * inner ℂ y ((a : H →L[ℂ] H) x)
  simp [inner_smul_right]

theorem predualCoefficient_add_right (x y z : H) :
    predualCoefficient M x (y + z) = predualCoefficient M x y + predualCoefficient M x z := by
  apply Subtype.ext
  ext a
  change inner ℂ (y + z) ((a : H →L[ℂ] H) x) =
    inner ℂ y ((a : H →L[ℂ] H) x) + inner ℂ z ((a : H →L[ℂ] H) x)
  simp [inner_add_left]

theorem predualCoefficient_smul_right (c : ℂ) (x y : H) :
    predualCoefficient M x (c • y) = star c • predualCoefficient M x y := by
  apply Subtype.ext
  ext a
  change inner ℂ (c • y) ((a : H →L[ℂ] H) x) =
    star c * inner ℂ y ((a : H →L[ℂ] H) x)
  simp [inner_smul_left]

theorem predualCoefficient_norm_le (x y : H) :
    ‖predualCoefficient M x y‖ ≤ ‖x‖ * ‖y‖ := normalCoefficient_norm_le M x y

private def predualForm (F : StrongDual ℂ (ConcretePredual M)) (x y : H) : ℂ :=
  star (F (predualCoefficient M x y))

private theorem predualForm_isOperatorForm (F : StrongDual ℂ (ConcretePredual M)) :
    IsOperatorForm (predualForm M F) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y z
    simp [predualForm, predualCoefficient_add_left]
  · intro c x y
    simp [predualForm, predualCoefficient_smul_left]
  · intro x y z
    simp [predualForm, predualCoefficient_add_right]
  · intro c x y
    simp [predualForm, predualCoefficient_smul_right]

private theorem predualForm_bound (F : StrongDual ℂ (ConcretePredual M)) (x y : H) :
    ‖predualForm M F x y‖ ≤ ‖F‖ * ‖x‖ * ‖y‖ := by
  rw [predualForm, norm_star]
  exact (F.le_opNorm _).trans (by
    calc
      ‖F‖ * ‖predualCoefficient M x y‖ ≤ ‖F‖ * (‖x‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (predualCoefficient_norm_le M x y) (norm_nonneg F)
      _ = _ := by ring)

/-- Riesz reconstruction from a bounded functional on the vector predual. -/
def operatorOfPredual (F : StrongDual ℂ (ConcretePredual M)) : H →L[ℂ] H :=
  operatorOfForm (predualForm M F) (predualForm_isOperatorForm M F) ‖F‖
    (predualForm_bound M F)

@[simp] theorem operatorOfPredual_coefficient (F : StrongDual ℂ (ConcretePredual M))
    (x y : H) : inner ℂ y (operatorOfPredual M F x) = F (predualCoefficient M x y) := by
  rw [← inner_conj_symm, operatorOfPredual, operatorOfForm_inner]
  exact star_star _

theorem operatorOfPredual_norm_le (F : StrongDual ℂ (ConcretePredual M)) :
    ‖operatorOfPredual M F‖ ≤ ‖F‖ :=
  norm_operatorOfForm_le _ _ _ (norm_nonneg _) _

/-- Commutant elements give identical vector functionals on the algebra. -/
theorem predualCoefficient_commutant (S : H →L[ℂ] H) (hS : S ∈ M.commutant)
    (x y : H) : predualCoefficient M (S x) y = predualCoefficient M x (S.adjoint y) := by
  apply Subtype.ext
  ext a
  change inner ℂ y ((a : H →L[ℂ] H) (S x)) =
    inner ℂ (S.adjoint y) ((a : H →L[ℂ] H) x)
  rw [ContinuousLinearMap.adjoint_inner_left]
  have hc := (VonNeumannAlgebra.mem_commutant_iff.mp hS) a a.property
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ y (T x)) hc

/-- Riesz reconstruction belongs to the original double commutant. -/
theorem operatorOfPredual_mem (F : StrongDual ℂ (ConcretePredual M)) :
    operatorOfPredual M F ∈ M := by
  apply (show M.commutant.commutant ≤ M from le_of_eq M.commutant_commutant)
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro S hS
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  change inner ℂ y (S (operatorOfPredual M F x)) =
    inner ℂ y (operatorOfPredual M F (S x))
  rw [← ContinuousLinearMap.adjoint_inner_left, operatorOfPredual_coefficient,
    operatorOfPredual_coefficient, predualCoefficient_commutant M S hS]

end KadisonSimilarity

end

end OAI
