import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarCuspQuotient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspDisjointness

namespace OAI

/-! The scalar cutoff is supported in its actual cusp and equals one
above twice its scale. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups ContDiff
namespace CubicFirstMoment

lemma cubicThetaScalarCuspQuotient_cusp (δ : SL(2,Eisenstein)) (N : ℝ) (p : CubicThetaPoint) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap (δ • p))=cubicThetaScalarCusp N p.val := by
  rw [cubicThetaScalarCuspQuotient_apply]
  simp only [cubicThetaScalarCuspAt,inv_smul_smul]

lemma cubicThetaScalarCuspQuotient_support (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    {q : CubicThetaQuotient} (hq : cubicThetaScalarCuspQuotient δ N q≠0) :
    q∈cubicThetaCuspNeighborhood δ N := by
  let x := cubicThetaQuotientLift q
  let y := δ⁻¹ • x
  have ht : ∃ r, cubicThetaScalarCuspTerm N r y.val≠0 := by
    by_contra! hz
    apply hq
    change (∑' r, cubicThetaScalarCuspTerm N r y.val)=0
    simp only [hz,tsum_zero]
  obtain ⟨r,hr⟩ := ht
  let g := r.completion
  let p := g • y
  have hh : N<r.height y.val := by
    by_contra hn
    exact hr (cubicThetaScalarCuspTerm_zero N (by linarith) r (le_of_not_gt hn))
  have hp : N<cubicThetaPointHeight p := by
    change N<(cubicThetaMobius (cubicThetaPrincipalComplex g) y.val).2
    rwa [← cubicThetaBottomRow_height,r.completion_row]
  have he : δ • p=cubicThetaPrincipalConjugate δ⁻¹ g • x := by
    change δ • (g.val • (δ⁻¹ • x))=((δ⁻¹)⁻¹*g.val*δ⁻¹) • x
    simp only [inv_inv,mul_smul]
  apply (cubicThetaCuspNeighborhood_mem_iff δ N q).mpr
  refine ⟨p,hp,?_⟩
  rw [he,cubicThetaQuotient_covering.map_smul]
  exact cubicThetaQuotientLift_map q

lemma cubicThetaScalarCuspQuotient_high (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N)
    {q : CubicThetaQuotient} (hq : q∈cubicThetaCuspNeighborhood δ (2*N)) :
    cubicThetaScalarCuspQuotient δ N q=1 := by
  obtain ⟨p,hp,hpq⟩ := (cubicThetaCuspNeighborhood_mem_iff δ (2*N) q).mp hq
  rw [← hpq,cubicThetaScalarCuspQuotient_cusp]
  exact cubicThetaScalarCusp_high hN hp.le

lemma cubicThetaScalarCuspQuotient_coordinates (δ : SL(2,Eisenstein)) (N : ℝ)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaScalarCuspQuotient δ N (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))=
      cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y) := by
  rw [cubicThetaScalarCuspQuotient_apply]
  unfold cubicThetaScalarCuspAt
  rw [cubicThetaFullPointAction_apply]
  congr 1
  exact congrArg (cubicThetaMobius (cubicThetaFullComplex δ⁻¹))
    (cubicThetaPointInclusion.right_inv (by rwa [cubicThetaPointInclusion_target]))

lemma cubicThetaScalarCuspQuotient_smooth (δ : SL(2,Eisenstein)) {N : ℝ} (hN : 1≤N) :
    ContDiffOn ℝ ∞ (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y))) {y : ℂ × ℝ | 0<y.2} := by
  intro y hy
  have hM := cubicThetaMobius_contDiffAt (cubicThetaFullComplex δ⁻¹) hy
  have hs := (cubicThetaScalarCusp_smooth hN).contDiffAt
    ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (cubicThetaMobius_height_pos (cubicThetaFullComplex δ⁻¹) hy))
  have he : (fun y => cubicThetaScalarCuspQuotient δ N
      (cubicThetaQuotientMap (cubicThetaPointInclusion.symm y)))=ᶠ[𝓝 y]
      (fun y => cubicThetaScalarCusp N (cubicThetaMobius (cubicThetaFullComplex δ⁻¹) y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy] with z hz
    exact cubicThetaScalarCuspQuotient_coordinates δ N hz
  exact ((hs.comp y hM).congr_of_eventuallyEq he).contDiffWithinAt

end CubicFirstMoment

end

end OAI
