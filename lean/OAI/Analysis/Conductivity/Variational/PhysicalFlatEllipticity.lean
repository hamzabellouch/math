import Mathlib
import OAI.Analysis.Conductivity.Flux.CentralCylinderGreen

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma sourceFlatTensor_positive (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i j : Fin 4) {x : Fin 3 → ℝ}
    (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100))
    {v : Fin 3 → ℝ} (hv : v≠0) : 0<v ⬝ᵥ (sourceFlatTensor s i j x*ᵥv) := by
  let C := sourceCartesianGradientMatrix i j x
  let u := C⁻¹*ᵥv
  have hC := isUnit_iff_ne_zero.mpr (sourceCartesianGradientMatrix_det_ne_zero i j hx)
  have hu : C*ᵥu=v := by
    change C*ᵥ(C⁻¹*ᵥv)=v
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ hC,Matrix.one_mulVec]
  have hn : u≠0 := by
    intro h
    rw [h,Matrix.mulVec_zero] at hu
    exact hv hu.symm
  have hex : ∃ k,u k≠0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨k,hk⟩ := hex
  have hsum : 0<∑ a : Fin 3,(u a)^2 :=
    (sq_pos_of_ne_zero hk).trans_le (Finset.single_le_sum
      (fun a _ => sq_nonneg (u a)) (Finset.mem_univ k))
  have he := sourceFlatTensor_energy s i j hx u u
  change (C*ᵥu) ⬝ᵥ (sourceFlatTensor s i j x*ᵥ(C*ᵥu))=_ at he
  rw [hu] at he
  rw [he]
  exact mul_pos (sourceFlatDensity_pos i j hx)
    ((mul_pos (by norm_num : (0:ℝ)<1/2) hsum).trans_le (flatCylinderMatrix_coercive s hs u))

lemma continuousOn_sourceFlatDensity (i j : Fin 4) :
    ContinuousOn (sourceFlatDensity i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  intro x hx
  exact ((continuous_sourceFaceAngleMatrix i j).matrix_det.continuousAt.div
    ((continuous_sourceCollarJacobian i j).matrix_det.abs.continuousAt)
      (abs_ne_zero.mpr (sourceCollarJacobian_extended_ne_zero i j hx))).continuousWithinAt

lemma continuousOn_sourceFlatTensor (s : Fin 3 → ℝ) (i j : Fin 4) :
    ContinuousOn (sourceFlatTensor s i j) (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
  have hi : ContinuousOn (fun x => (sourceCartesianGradientMatrix i j x)⁻¹)
      (sourceExtendedBox (-(1:ℝ)/100) (1/100)) := by
    intro x hx
    have hn := sourceCartesianGradientMatrix_det_ne_zero i j hx
    exact (continuousAt_matrix_inv _ (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hn)).comp_continuousWithinAt
        (continuousOn_sourceCartesianGradientMatrix i j x hx)
  exact (continuousOn_sourceFlatDensity i j).smul
    ((((continuous_id.matrix_transpose :
        Continuous (fun A : Matrix (Fin 3) (Fin 3) ℝ => Aᵀ)).comp_continuousOn hi).mul
          continuousOn_const).mul hi)

lemma compact_matrix_energy_bounds {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (A : X → Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ContinuousOn A K)
    (hpos : ∀ x∈K,∀ v : Fin 3 → ℝ,v≠0 → 0<v ⬝ᵥ (A x*ᵥv)) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ x∈K,∀ v : Fin 3 → ℝ,
      c*‖v‖^2≤v ⬝ᵥ (A x*ᵥv) ∧ v ⬝ᵥ (A x*ᵥv)≤C*‖v‖^2 := by
  let S := K×ˢMetric.sphere (0 : Fin 3 → ℝ) 1
  let g : X×(Fin 3 → ℝ) → ℝ := fun z => z.2 ⬝ᵥ (A z.1*ᵥz.2)
  have hS : IsCompact S := hK.prod (isCompact_sphere _ _)
  have hAc : ContinuousOn (fun z : X×(Fin 3 → ℝ) => A z.1) S :=
    hA.comp continuous_fst.continuousOn (fun z hz => hz.1)
  have hg : ContinuousOn g S := by
    unfold g Matrix.mulVec dotProduct
    apply continuousOn_finsetSum
    intro k _
    apply ((continuous_apply k).comp continuous_snd).continuousOn.mul
    apply continuousOn_finsetSum
    intro l _
    exact ((continuous_apply_apply k l).comp_continuousOn hAc).mul
      ((continuous_apply l).comp continuous_snd).continuousOn
  have hn (v : Fin 3 → ℝ) (hv : v∈Metric.sphere (0:Fin 3 → ℝ) 1) : ‖v‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using hv
  have hgp : ∀ z∈S,0<g z := by
    intro z hz
    apply hpos z.1 hz.1 z.2
    intro hv
    have h := hn z.2 hz.2
    rw [hv,norm_zero] at h
    norm_num at h
  obtain ⟨c,hc,hcg⟩ := hS.exists_forall_le' hg hgp
  obtain ⟨B,hB⟩ := hS.exists_bound_of_continuousOn hg
  refine ⟨c,max B (c+1),hc,lt_of_lt_of_le (by linarith) (le_max_right _ _),?_⟩
  intro x hx v
  by_cases hv : v=0
  · subst v
    simp
  have hnzero : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hun : ‖u‖=1 := by
    simp [u,norm_smul,hnzero]
  have hxu : (x,u)∈S := ⟨hx,by simpa only [Metric.mem_sphere,dist_zero_right] using hun⟩
  have he : g (x,u)*‖v‖^2=v ⬝ᵥ (A x*ᵥv) := by
    simp only [g,u,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    field_simp
  constructor
  · rw [←he]
    exact mul_le_mul_of_nonneg_right (hcg _ hxu) (sq_nonneg _)
  · rw [←he]
    exact mul_le_mul_of_nonneg_right
      (((le_abs_self _).trans (hB _ hxu)).trans (le_max_left _ _)) (sq_nonneg _)

theorem sourceFlatTensor_elliptic (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i j : Fin 4) :
    ∃ c C : ℝ,0<c ∧ c<C ∧ ∀ x∈sourceExtendedBox (-(1:ℝ)/100) (1/100),
      ∀ v : Fin 3 → ℝ,c*‖v‖^2≤v ⬝ᵥ (sourceFlatTensor s i j x*ᵥv) ∧
        v ⬝ᵥ (sourceFlatTensor s i j x*ᵥv)≤C*‖v‖^2 :=
  compact_matrix_energy_bounds isCompact_Icc _ (continuousOn_sourceFlatTensor s i j)
    (fun _ hx _ hv => sourceFlatTensor_positive s hs i j hx hv)

end ScalarConductivity

end

end OAI
