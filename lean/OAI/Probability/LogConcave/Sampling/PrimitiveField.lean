import Mathlib
import OAI.Probability.LogConcave.Analysis.ConditionalPotential

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace LogConcaveSampling
open MeasureTheory

lemma conditionalLaw_hasExpMoments {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    Appell.HasExpMoments (gibbs (conditionalPotential F x r ρ y)) := by
  obtain ⟨ha,ha1⟩ := probability_time hρ0 hρ1
  have hs := conditional_smallness hl ha ha1
  have hsmall : (lam:ℝ)*(r*Real.sqrt (1-ρ^2))^2 < 1 := by linarith
  have hrad : 0≤r*Real.sqrt (1-ρ^2) := mul_nonneg hr (Real.sqrt_nonneg _)
  rw [← conditionalLaw_map hF x r ρ y ha]
  apply (hF.hasExpMoments (x+r • (ρ • y)) hrad hsmall).map_lipschitz
    (K := ⟨Real.sqrt (1-ρ^2),Real.sqrt_nonneg _⟩)
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simp only [dist_eq_norm,add_sub_add_left_eq_sub,← smul_sub,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rfl
end LogConcaveSampling

namespace LogConcaveSampling
open MeasureTheory
open scoped RealInnerProductSpace

def primitiveField {d : ℕ} (F : Point d → ℝ) (x : Point d) (r : ℝ) (z : Point d) : Point d :=
  gradient F (x+r • z)

abbrev JointPoint (d : ℕ) := EuclideanSpace ℝ (Fin d ⊕ Fin d)

def jointImage {d : ℕ} (f : Point d → Point d) (L : ℝ) (z : Point d) : JointPoint d :=
  EuclideanSpace.sumEquivProd.symm (z,L⁻¹ • f z)

lemma jointImage_norm_sq {d : ℕ} (u v : Point d) :
    ‖(EuclideanSpace.sumEquivProd.symm (u,v) : JointPoint d)‖^2=‖u‖^2+‖v‖^2 := by
  simp [EuclideanSpace.sumEquivProd,WithLp.prod_norm_sq_eq_of_L2]

lemma jointImage_contDiff {d : ℕ} {f : Point d → Point d} (hf : ContDiff ℝ 1 f) (L : ℝ) :
    ContDiff ℝ 1 (jointImage f L) := by
  exact EuclideanSpace.sumEquivProd.symm.contDiff.comp
    (contDiff_id.prodMk (show ContDiff ℝ 1 (fun z => L⁻¹ • f z) by fun_prop))

lemma jointImage_lipschitz {d : ℕ} {f : Point d → Point d} {L : ℝ≥0}
    (hf : LipschitzWith L f) (hL : L≠0) : LipschitzWith 2 (jointImage f L) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have he : jointImage f L u-jointImage f L v=
      EuclideanSpace.sumEquivProd.symm (u-v,(L:ℝ)⁻¹ • (f u-f v)) := by
    rw [jointImage,jointImage,← map_sub]
    congr 1
    simp only [Prod.mk_sub_mk,smul_sub]
  have hL0 : (L:ℝ)≠0 := by exact_mod_cast hL
  have hb : ‖(L:ℝ)⁻¹ • (f u-f v)‖ ≤ ‖u-v‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr L.coe_nonneg)]
    have hh := mul_le_mul_of_nonneg_left (hf.dist_le_mul u v) (inv_nonneg.mpr L.coe_nonneg)
    simpa only [dist_eq_norm,← mul_assoc,inv_mul_cancel₀ hL0,one_mul] using hh
  rw [dist_eq_norm,he]
  have hs := jointImage_norm_sq (u-v) ((L:ℝ)⁻¹ • (f u-f v))
  have hbs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hb
  simp only [NNReal.coe_ofNat,dist_eq_norm]
  nlinarith [norm_nonneg (EuclideanSpace.sumEquivProd.symm
    (u-v,(L:ℝ)⁻¹ • (f u-f v)) : JointPoint d),norm_nonneg (u-v),sq_nonneg ‖u-v‖]

lemma primitiveField_contDiff {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) (r : ℝ) :
    ContDiff ℝ 1 (primitiveField F x r) :=
  (Trapezoid.contDiff_gradient hF.smooth).comp (show ContDiff ℝ 1 (fun z : Point d => x+r • z) by fun_prop)

lemma primitiveField_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0≤r) :
    LipschitzWith (lam*(NNReal.mk r hr)) (primitiveField F x r) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hh := hF.gradient_lipschitz.dist_le_mul (x+r • u) (x+r • v)
  change _ ≤ ((lam:ℝ)*r)*dist u v
  simpa only [primitiveField,dist_add_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr,
    mul_assoc] using hh

def jointConditionalLaw {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ)
    (y : Point d) (L : ℝ) : Measure (JointPoint d) :=
  (gibbs (conditionalPotential F x r ρ y)).map (jointImage (primitiveField F x r) L)

lemma jointConditionalLaw_properties {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0<r)
    (hlam : 0<lam) (hl : (lam:ℝ)*r^2 ≤ 1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) (y : Point d) :
    let μ := jointConditionalLaw F x r ρ y ((lam:ℝ)*r)
    IsProbabilityMeasure μ ∧ Appell.HasExpMoments μ ∧
      HasPoincare μ (2*Real.pi^2*(1-ρ^2)) := by
  let L : ℝ≥0 := lam*(NNReal.mk r hr.le)
  have hL : L≠0 := mul_ne_zero hlam.ne' (by intro h; exact hr.ne' (congrArg (fun t : ℝ≥0 => (t:ℝ)) h))
  have hK := jointImage_lipschitz (primitiveField_lipschitz hF x hr.le) hL
  have hS := jointImage_contDiff (primitiveField_contDiff hF x r) (L:ℝ)
  have hp : IsProbabilityMeasure (gibbs (conditionalPotential F x r ρ y)) :=
    conditionalLaw_probability hF x hr.le hl hρ0 hρ1 y
  change IsProbabilityMeasure ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) ∧ _
  refine ⟨inferInstance,?_,?_⟩
  · exact (conditionalLaw_hasExpMoments hF x hr.le hl hρ0 hρ1 y).map_lipschitz hK
  · have hh := (conditionalLaw_hasPoincare hF x hr.le hl hρ0 hρ1 y).map
      (by obtain ⟨ha,_⟩ := probability_time hρ0 hρ1; positivity) hS hK
    change HasPoincare ((gibbs (conditionalPotential F x r ρ y)).map
      (jointImage (primitiveField F x r) (L:ℝ))) _
    convert hh using 1; norm_num; ring

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
