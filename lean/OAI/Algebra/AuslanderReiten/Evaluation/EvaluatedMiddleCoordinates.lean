import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedMiddleNaturality
import OAI.Algebra.AuslanderReiten.Evaluation.EvaluatedQuotientCubic

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "R₀" => A k q
local notation "X" => A.simpleFiniteModule q
local notation "D" => bimoduleTwoConeData q
local notation "hf" => bimodule_term_finite_k q
local notation "τ" => AFrobeniusTrace k q
local notation "Q" => HomotopyCategory.quotient (ModuleCat R₀) (ComplexShape.up ℤ)

local instance middleCoordinateBaseScalar (n : ℕ) : Module k (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).scalar
local instance middleCoordinateBaseTower (n : ℕ) : IsScalarTower k (R₀ ⊗[k] R₀ᵐᵒᵖ)
    (TwoCone.baseCokernelModule D hf n).carrier :=
  (TwoCone.baseCokernelModule D hf n).tower
local instance middleCoordinateScalar (n : ℕ) : Module k (TwoCone.middleCokernelModule D hf n).carrier :=
  (TwoCone.middleCokernelModule D hf n).scalar
local instance middleCoordinateTower (n : ℕ) : IsScalarTower k (R₀ ⊗[k] R₀ᵐᵒᵖ)
    (TwoCone.middleCokernelModule D hf n).carrier :=
  (TwoCone.middleCokernelModule D hf n).tower

theorem evaluatedSingletonFst_eq (n : ℕ) :
    evaluatedSingletonFst q n = FiniteLeftModule.evaluationMap X
      (TwoCone.middleProjection D hf true n) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  rfl

theorem evaluatedSingletonSnd_eq (n : ℕ) :
    evaluatedSingletonSnd q n = FiniteLeftModule.evaluationMap X
      (TwoCone.middleProjection D hf false n) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  rfl

theorem evaluatedRow_coordinates (n : ℕ) :
    FiniteLeftModule.evaluationMap X
      (M := TwoCone.middleCokernelModule D hf (n+1))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.rowCokernelMap D n) =
    (FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+3))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.firstCokernelMap D n)).comp
        (evaluatedSingletonFst q (n+1)) +
    (FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+3))
      (N := TwoCone.baseCokernelModule D hf n) (TwoCone.secondCokernelMap D n)).comp
        (evaluatedSingletonSnd q (n+1)) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D n b.value.1 + TwoCone.secondCokernelMap D n b.value.2⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x =
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D n b.value.1⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x +
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.secondCokernelMap D n b.value.2⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf n).carrier) x
  exact BalancedTensor.add_tmul _ _ _

theorem evaluatedColumn_fst (n : ℕ) :
    (evaluatedSingletonFst q n).comp
      (FiniteLeftModule.evaluationMap X
        (M := TwoCone.baseCokernelModule D hf (n+5))
        (N := TwoCone.middleCokernelModule D hf n) (-(TwoCone.columnCokernelMap D n))) =
    -(FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+5))
      (N := TwoCone.baseCokernelModule D hf (n+2)) (TwoCone.secondCokernelMap D (n+2))) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨-(TwoCone.secondCokernelMap D (n+2) b.value)⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x =
    -BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.secondCokernelMap D (n+2) b.value⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x
  change BalancedTensor.tmul (k := k) (R := R₀) (-_) x = _
  simp [BalancedTensor.tmul, TensorProduct.neg_tmul]

theorem evaluatedColumn_snd (n : ℕ) :
    (evaluatedSingletonSnd q n).comp
      (FiniteLeftModule.evaluationMap X
        (M := TwoCone.baseCokernelModule D hf (n+5))
        (N := TwoCone.middleCokernelModule D hf n) (-(TwoCone.columnCokernelMap D n))) =
    FiniteLeftModule.evaluationMap X
      (M := TwoCone.baseCokernelModule D hf (n+5))
      (N := TwoCone.baseCokernelModule D hf (n+2)) (TwoCone.firstCokernelMap D (n+2)) := by
  apply BalancedTensor.leftHom_ext (k := k) (R := R₀)
  intro b x
  change BalancedTensor.tmul (k := k) (R := R₀)
      (⟨-(-(TwoCone.firstCokernelMap D (n+2) b.value))⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x =
    BalancedTensor.tmul (k := k) (R := R₀)
      (⟨TwoCone.firstCokernelMap D (n+2) b.value⟩ :
        EnvelopingBimodule k R₀ (TwoCone.baseCokernelModule D hf (n+2)).carrier) x
  rw [neg_neg]

end ArExplicit.T

end

end OAI
