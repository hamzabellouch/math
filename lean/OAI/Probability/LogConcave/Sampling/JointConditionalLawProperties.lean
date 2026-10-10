import Mathlib
import OAI.Probability.LogConcave.Sampling.MaterialScalar

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory
open scoped Topology Classical BigOperators NNReal RealInnerProductSpace

lemma jointConditionalLaw_properties_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1) (y : Point d) :
    IsProbabilityMeasure (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) ∧
      Appell.HasExpMoments (jointConditionalLaw F x r ρ y ((lam:ℝ)*r)) := by
  let L : ℝ≥0 := lam*(NNReal.mk r hr.le)
  have hL : L≠0 := mul_ne_zero hlam.ne' (by intro h; exact hr.ne' (congrArg (fun t : ℝ≥0 => (t:ℝ)) h))
  have hK := jointImage_lipschitz (primitiveField_lipschitz hF x hr.le) hL
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  change IsProbabilityMeasure ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) ∧ _
  exact ⟨inferInstance,
    (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y).map_lipschitz hK⟩

lemma conditionalU_normalized_jet_sq {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2≤1/2) (hρ : ρ^2<1)
    {ι : Type*} (v : ι → Point d) (l : List ι) (u y : Point d) :
    conditionalU F x r ρ y u ((lam:ℝ)*r) v l=
      ((1-ρ^2)^l.length)⁻¹*JetCalculus.jet v l
        (Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y))
          (fun z => inner ℝ u (primitiveField F x r z))) 0 := by
  obtain ⟨hp,hJ⟩ := jointConditionalLaw_properties_sq hF x hr hlam hl hρ y
  let := hp
  let := conditionalLaw_probability_sq hF x hr.le hl hρ y
  have hc : Continuous (fun z => inner ℝ u (primitiveField F x r z)) :=
    continuous_const.inner (primitiveField_contDiff hF x r).continuous
  have hg := primitiveField_inner_growth hF x u hr.le
  have hC := Appell.smooth_normalizedLaplace (conditionalLaw_hasExpMoments_sq hF x hr.le hl hρ y) hc hg
  have hJC := Appell.smooth_normalizedLaplace hJ
    (show Continuous (fun z : JointPoint d => inner ℝ (jointField d u) z) by fun_prop)
    (Appell.HasGrowth.linear (innerSL ℝ (jointField d u)))
  have hh := congrFun (JetCalculus.jet_comp_affine hJC (jointPosition d) 0 v l) 0
  simp only [add_zero,map_zero] at hh
  have hf : (fun z => Appell.normalizedLaplace (jointConditionalLaw F x r ρ y ((lam:ℝ)*r))
      (fun z => inner ℝ (jointField d u) z) (jointPosition d z))=fun z =>
      ((lam:ℝ)*r)⁻¹*Appell.normalizedLaplace (gibbs (conditionalPotential F x r ρ y))
        (fun z => inner ℝ u (primitiveField F x r z)) z := by
    funext z
    exact joint_normalizedLaplace (primitiveField_contDiff hF x r).continuous _ _ z
  rw [hf,JetCalculus.jet_const_mul hC] at hh
  unfold conditionalU
  rw [Appell.dir_log_laplace hJ,←hh]
  dsimp only at hh
  have hL : (lam:ℝ)*r≠0 := by positivity
  field_simp [hL]

end LogConcaveSampling

end

end

end

end OAI
