import OAI.Analysis.LiebThirring.FormCongruence

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology

/-- The self-adjoint realization of `-d²/dx²-W`, obtained by inverting the
coercively shifted H¹ form. The graph identity below characterizes it without
reference to the choice of potential decomposition or shift. -/
def operator {W : ℝ → ℝ} (d : PotentialData W) : L2C →ₗ.[ℂ] L2C :=
  inverseShift (resolvent d) (resolvent_injective d) (d.b+1)

lemma operator_selfAdjoint {W : ℝ → ℝ} (d : PotentialData W) :
    IsSelfAdjoint (operator d) :=
  inverseShift_selfAdjoint _ (resolvent_injective d) (resolvent_symmetric d)
    (resolvent_dense d) (d.b+1)

lemma operator_dense {W : ℝ → ℝ} (d : PotentialData W) :
    Dense ((operator d).domain : Set L2C) := resolvent_dense d

lemma operator_graph {W : ℝ → ℝ} (d : PotentialData W) (f g : L2C) :
    (∃ hf : f ∈ (operator d).domain, operator d ⟨f,hf⟩ = g) ↔
      ∃ u : H1C, valL u = f ∧
        ∀ v : H1C, schrodingerForm W (toH1 v) (toH1 u) = inner ℂ (valL v) g := by
  constructor
  · rintro ⟨hf,hg⟩
    obtain ⟨x,rfl⟩ := hf
    have ha := inverseShift_apply (resolvent d) (resolvent_injective d) (d.b+1) x
    have he : x-((d.b+1 : ℝ):ℂ) • resolvent d x = g := ha.symm.trans hg
    refine ⟨solveL d x,rfl,fun v ↦ ?_⟩
    rw [← he,inner_sub_right,inner_smul_right]
    have h := solve_form d x v
    simpa only [Complex.ofReal_add,Complex.ofReal_one] using eq_sub_of_add_eq h
  · rintro ⟨u,rfl,hq⟩
    let x := g+((d.b+1 : ℝ):ℂ) • valL u
    have hb : shiftedFormMap d u = valL.adjoint x := by
      apply ext_inner_left ℂ
      intro v
      rw [shiftedFormMap_inner,← form_eq_inner d v u,hq v,
        ContinuousLinearMap.adjoint_inner_right]
      dsimp only [x]
      rw [inner_add_right,inner_smul_right]
      simp only [Complex.ofReal_add,Complex.ofReal_one]
    have hs : solveL d x = u := (shiftedFormMap_bijective d).1
      ((shifted_solve d x).trans hb.symm)
    have hr : resolvent d x = valL u := congrArg valL hs
    refine ⟨⟨x,hr⟩,?_⟩
    have ha := inverseShift_apply (resolvent d) (resolvent_injective d) (d.b+1) x
    calc
      operator d ⟨valL u,⟨x,hr⟩⟩ =
          inverseShift (resolvent d) (resolvent_injective d) (d.b+1)
            ⟨resolvent d x,⟨x,rfl⟩⟩ := by
        apply congrArg (operator d)
        exact Subtype.ext hr.symm
      _ = x-((d.b+1 : ℝ):ℂ) • resolvent d x := ha
      _ = g := by rw [hr]; dsimp only [x]; abel

lemma operator_associated {W : ℝ → ℝ} (d : PotentialData W) :
    IsAssociated W (operator d) :=
  (isAssociated_iff_graph W (operator d)).mpr (operator_graph d)

end SharpLiebThirring.OperatorProof

end

end OAI
