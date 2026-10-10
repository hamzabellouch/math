import OAI.NumberTheory.DukePrimeDegree.Geometry.NeutralTransverseCoordinates

namespace OAI

/-! # Move the neutral coordinate to the right of the root coordinate

The parametrization is now lower-unitriangular, upper-unipotent, diagonal.
Consequently right translation by the diagonal group is translation in the
last coordinate, with the other two coordinates fixed.
-/

noncomputable section
open Matrix Set
open scoped Topology BigOperators
namespace DukePrimeDegree
open PrimeDegreePackets

namespace EliminationChain

theorem continuous_rootDilation {n : ℕ} {P : Finset (Fin n × Fin n)}
    {D : Finset (Fin n)} (c : EliminationChain P D)
    {Y : Type*} [TopologicalSpace Y]
    (ell : Y → Fin n → ℝ) (r : Y → ℝ) (u : Y → c.Time)
    (hell : Continuous ell) (hr : Continuous r) (hu : Continuous u) :
    Continuous (fun y => c.rootDilation (ell y) (r y) (u y)) := by
  induction c with
  | done => exact hu
  | step a b hab hP hb tail ih =>
      change Continuous (fun y =>
        (tail.rootDilation (ell y) (r y) (u y).1,
          Real.exp (((ell y) a-(ell y) b)*r y)*(u y).2))
      exact (ih _ hu.fst).prodMk
        ((Real.continuous_exp.comp ((((continuous_apply a).comp hell).sub
          ((continuous_apply b).comp hell)).mul hr)).mul hu.snd)

end EliminationChain

def neutralUpperRootParam (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n)) : G n :=
  z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter z.2.2.val z.2.2.prop 1

lemma neutralUpperRootParam_eq (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n)) :
    neutralUpperRootParam n z =
      upperRootParam n ((transverseNeutralReconstruct (z.1,z.2.2)).val,
        (completeRootChain n).rootDilation z.2.2.val (-1) z.2.1) := by
  rw [upperRootParam_eq_mul,(completeRootChain n).word_rootDilation _ z.2.2.prop]
  change z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter z.2.2.val z.2.2.prop 1 =
    (z.1.val.val*diagonalOneParameter z.2.2.val z.2.2.prop 1)*
      (diagonalOneParameter z.2.2.val z.2.2.prop (-1)*
        (completeRootChain n).word z.2.1*
          diagonalOneParameter z.2.2.val z.2.2.prop (-(-1)))
  rw [neg_neg,diagonalOneParameter_neg]
  group

lemma continuous_neutralUpperRootParam (n : ℕ) : Continuous (neutralUpperRootParam n) := by
  have hd : Continuous (fun v : transverseNeutralSpace n =>
      diagonalOneParameter v.val v.prop 1) := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    change Continuous (fun v : transverseNeutralSpace n =>
      Matrix.diagonal (fun k => Real.exp (v.val k*1)) i j)
    by_cases hij : i=j
    · subst j
      simp only [Matrix.diagonal_apply_eq,mul_one]
      exact Real.continuous_exp.comp ((continuous_apply i).comp continuous_subtype_val)
    · simp only [Matrix.diagonal_apply_ne _ hij]
      exact continuous_const
  have h₁ : Continuous (fun z : UnitDiagonalTransverse n ×
      (UpperRootTime n × transverseNeutralSpace n) => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have h₂ : Continuous (fun z : UnitDiagonalTransverse n ×
      (UpperRootTime n × transverseNeutralSpace n) => z.1.val.val) :=
    continuous_subtype_val.comp h₁
  have hw : Continuous (completeRootChain n).word :=
    (upperRootWordHomeomorph n).continuous.subtype_val
  exact (h₂.mul (hw.comp continuous_snd.fst)).mul (hd.comp continuous_snd.snd)

lemma neutralUpperRootParam_translate (n : ℕ)
    (z : UnitDiagonalTransverse n × (UpperRootTime n × transverseNeutralSpace n))
    (v : transverseNeutralSpace n) :
    neutralUpperRootParam n (z.1,(z.2.1,z.2.2+v)) =
      neutralUpperRootParam n z*diagonalOneParameter v.val v.prop 1 := by
  change z.1.val.val*(completeRootChain n).word z.2.1*
    diagonalOneParameter (z.2.2.val+v.val) _ 1 = _
  rw [diagonalOneParameter_add_weights]
  exact (mul_assoc _ _ _).symm

end DukePrimeDegree

end

end OAI
