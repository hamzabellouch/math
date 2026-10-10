import OAI.Analysis.LiebThirring.FreeForm

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set
open scoped Topology

/-- Standard bounded-resolvent condition for a partially defined operator:
`R` is a bounded everywhere-defined inverse of `A-e` on its full domain.
The graph equivalence includes both inverse identities and domain membership. -/
def HasBoundedResolventAt (A : L2C →ₗ.[ℂ] L2C) (e : ℝ) : Prop :=
  ∃ R : L2C →L[ℂ] L2C, ∀ f g : L2C,
    (∃ hf : f ∈ A.domain, A ⟨f,hf⟩ = (e:ℂ) • f+g) ↔ R g = f

lemma hasBoundedResolventAt_not_eigenvalue {A : L2C →ₗ.[ℂ] L2C} {e : ℝ}
    (h : HasBoundedResolventAt A e) :
    ¬ ∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction A e f := by
  obtain ⟨R,hR⟩ := h
  rintro ⟨f,hf,haf,hv⟩
  have he : R 0 = f := (hR f 0).mp ⟨haf,by simpa only [add_zero] using hv⟩
  exact hf (he.symm.trans (map_zero R))

lemma energy_operator_graph {W : ℝ → ℝ} (d : PotentialData W) (a : ℝ) (f g : L2C) :
    (∃ hf : f ∈ (operator d).domain, operator d ⟨f,hf⟩ = (-a:ℂ) • f+g) ↔
      ∃ u : H1C, valL u = f ∧ energyFormMap d a u = valL.adjoint g := by
  rw [operator_graph]
  constructor
  · rintro ⟨u,hu,hq⟩
    refine ⟨u,hu,?_⟩
    apply ext_inner_left ℂ
    intro v
    rw [energyFormMap_inner,hq v,ContinuousLinearMap.adjoint_inner_right,hu,
      inner_add_right,inner_smul_right]
    ring
  · rintro ⟨u,hu,hq⟩
    refine ⟨u,hu,fun v ↦ ?_⟩
    have hh := congrArg (fun t ↦ inner ℂ v t) hq
    rw [energyFormMap_inner,ContinuousLinearMap.adjoint_inner_right] at hh
    rw [inner_add_right,inner_smul_right,← hu]
    linear_combination hh

lemma energyFormMap_bijective_resolvent {W : ℝ → ℝ} (d : PotentialData W) (a : ℝ)
    (h : Function.Bijective (energyFormMap d a)) : HasBoundedResolventAt (operator d) (-a) := by
  let E : H1C ≃L[ℂ] H1C := ContinuousLinearEquiv.ofBijective (energyFormMap d a)
    (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2)
  let R : L2C →L[ℂ] L2C := valL.comp (E.symm.toContinuousLinearMap.comp valL.adjoint)
  refine ⟨R,fun f g ↦ ?_⟩
  rw [Complex.ofReal_neg,energy_operator_graph]
  constructor
  · rintro ⟨u,hu,hq⟩
    have he : E u = valL.adjoint g := hq
    change valL (E.symm (valL.adjoint g)) = f
    rw [← he,ContinuousLinearEquiv.symm_apply_apply,hu]
  · intro hr
    refine ⟨E.symm (valL.adjoint g),hr,?_⟩
    exact E.apply_symm_apply _

lemma energyFormMap_alternative {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ)
    (hW : Admissible γ W) (d : PotentialData W) {a : ℝ} (ha : 0 < a) :
    (∃ u : H1C, u ≠ 0 ∧ energyFormMap d a u = 0) ∨
      Function.Bijective (energyFormMap d a) := by
  have hC : IsCompactOperator ((weightedL d).adjoint.comp (weightedL d)) :=
    (weightedL_compact hγ hW d).clm_comp (weightedL d).adjoint
  exact compact_perturbation_alternative (freeFormEquiv ha)
    ((weightedL d).adjoint.comp (weightedL d)) hC

/-- Below zero there is no continuous or residual spectrum: each real negative
energy is an actual eigenvalue, or has a bounded inverse on the full L² space. -/
theorem negative_resolvent_or_eigenvalue {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ)
    (hW : Admissible γ W) (d : PotentialData W) {e : ℝ} (he : e < 0) :
    HasBoundedResolventAt (operator d) e ∨
      ∃ f : L2C, f ≠ 0 ∧ IsOperatorEigenfunction (operator d) e f := by
  have ha : 0 < -e := neg_pos.mpr he
  rcases energyFormMap_alternative hγ hW d ha with ⟨u,hu,hq⟩ | hb
  · right
    refine ⟨valL u,fun hz ↦ hu (valL_injective (hz.trans (map_zero valL).symm)),?_⟩
    have hg := (energy_operator_graph d (-e) (valL u) 0).mpr
      ⟨u,rfl,by simpa only [map_zero] using hq⟩
    simpa only [IsOperatorEigenfunction,neg_neg,Complex.ofReal_neg,add_zero] using hg
  · left
    simpa only [neg_neg] using energyFormMap_bijective_resolvent d (-e) hb

end SharpLiebThirring.OperatorProof

end

end OAI
