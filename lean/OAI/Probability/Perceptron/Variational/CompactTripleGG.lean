import Mathlib
import OAI.Probability.Perceptron.Sphere.SphereKernel
import OAI.Probability.Perceptron.Variational.CovarianceMatrix

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped BigOperators Topology BoundedContinuousFunction NNReal ContDiff

lemma compact_two_edge_law {K : Type*} [TopologicalSpace K] [MeasurableSpace K]
    [BorelSpace K] [MetrizableSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (hGG : ∀ (F : CompactBlock K 2→ᵇℝ) (g : K→ᵇℝ),compactGGDefect μ 2 0 F g=0) :
    (μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 2))=
      (1/2:ℝ≥0) • (((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))+
      (1/2:ℝ≥0) • ((μ : Measure (CompactArray K)).map (fun Q=>(Q 0 1,Q 0 1))) := by
  have h := compactGG_joint_law μ (n:=2) (by norm_num) 0 hGG
  have hm : Measurable (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2)) := by fun_prop
  have he := congrArg (Measure.map (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2))) h
  simp only [Finset.univ_fin2,Finset.erase_insert,Finset.mem_singleton,Fin.zero_ne_one,not_false_eq_true,
    Finset.sum_singleton] at he
  rw [Measure.map_map hm ((compactBlock_continuous 2).measurable.prodMk (by fun_prop)),Measure.map_smul _ hm.aemeasurable,Measure.map_add _ _ hm,Measure.map_map hm ((compactBlock_continuous 2).measurable.prodMk (by fun_prop))] at he
  have hp : Measure.map (fun p : CompactBlock K 2×K=>(p.1 0 1,p.2))
      (((μ : Measure (CompactArray K)).map (compactBlock 2)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)))=
      ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)).prod
        ((μ : Measure (CompactArray K)).map (fun Q=>Q 0 1)) := by
    change Measure.map (Prod.map (fun A : CompactBlock K 2 => A 0 1) id) _ = _
    rw [←Measure.map_prod_map _ _ (by fun_prop) measurable_id,Measure.map_id]
    rw [Measure.map_map (by fun_prop) (compactBlock_continuous 2).measurable]
    rfl
  rw [hp] at he
  simpa [one_div,smul_add,compactBlock,Function.comp_def] using he

lemma ultrametric_tangent_algebra {r s t : ℝ} (h : UltrametricTriangle r s t)
    (a : ℝ→ℝ) :
    a s*t=r*a s-max (r-s) 0*a s+a r*max (t-r) 0 := by
  rcases lt_trichotomy s r with hs|hs|hs
  · have ht : t=s := by
      have h' : UltrametricTriangle s r t := ⟨by simpa [min_comm] using h.1,h.2.2,h.2.1⟩
      exact ultrametric_triangle_small_eq h' hs
    subst t
    rw [max_eq_left (by linarith : 0≤r-s),max_eq_right (by linarith : s-r≤0)]
    ring
  · subst s
    have hr : r≤t := by simpa using h.1
    rw [sub_self,max_self,max_eq_left (by linarith : 0≤t-r)]
    ring
  · have ht := ultrametric_triangle_small_eq h hs
    subst t
    rw [max_eq_right (by linarith : r-s≤0),sub_self,max_self]
    ring

lemma boundedAbs_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (f : Ω→ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x,|f x|≤C) :
    Integrable f P := Integrable.of_bound hf.aestronglyMeasurable C
      (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma two_edge_integral {Ω K : Type*} [MeasurableSpace Ω] [MeasurableSpace K]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure K) [IsProbabilityMeasure ν]
    (r s : Ω→K) (hr : Measurable r) (hs : Measurable s)
    (hlaw : P.map (fun x=>(r x,s x))=(1/2:ℝ≥0) • (ν.prod ν)+(1/2:ℝ≥0) • (ν.map fun x=>(x,x)))
    (H : K×K→ℝ) (hH : Measurable H) (C : ℝ) (hb : ∀ x,|H x|≤C) :
    (∫ x,H (r x,s x) ∂P)=(1/2:ℝ)*((∫ x,∫ y,H (x,y) ∂ν ∂ν)+(∫ x,H (x,x) ∂ν)) := by
  have hi : Integrable H (ν.prod ν) := boundedAbs_integrable _ _ hH C hb
  have hd : Integrable H (ν.map fun x=>(x,x)) := boundedAbs_integrable _ _ hH C hb
  rw [←integral_map (hr.prodMk hs).aemeasurable hH.aestronglyMeasurable,hlaw,
    integral_add_measure (hi.smul_measure_nnreal) (hd.smul_measure_nnreal),
    integral_smul_nnreal_measure,integral_smul_nnreal_measure,
    integral_map (show Measurable (fun x : K=>(x,x)) from measurable_id.prodMk measurable_id).aemeasurable hH.aestronglyMeasurable,
    integral_prod _ hi]
  simp only [NNReal.smul_def,NNReal.coe_div,NNReal.coe_one,NNReal.coe_ofNat,smul_eq_mul]
  ring

lemma time_abs_le_one (r : Time) : |(r:ℝ)|≤1 := by
  rw [abs_of_nonneg r.property.1]
  exact r.property.2

lemma sphereKernel_abs_le_one (r s : Time) : |sphereKernel r s|≤1 := by
  rw [abs_of_nonneg (sphereKernel_nonneg r s)]
  unfold sphereKernel
  have := min_le_left (r:ℝ) (s:ℝ)
  have := mul_nonneg r.property.1 s.property.1
  linarith [r.property.2]

lemma time_pospart_le_one (r s : Time) : |max ((s:ℝ)-r) 0|≤1 := by
  rw [abs_of_nonneg (le_max_right _ _),max_le_iff]
  exact ⟨by linarith [s.property.2,r.property.1],by norm_num⟩

lemma sphereKernel_tangent_algebra (r s t : Time)
    (h : UltrametricTriangle (r:ℝ) (s:ℝ) (t:ℝ)) (a : Time→ℝ) :
    a s*((t:ℝ)-(r:ℝ)*s)=sphereKernel r s*a s+a r*max ((t:ℝ)-r) 0 := by
  let A : ℝ→ℝ := fun x=>a (Set.projIcc 0 1 zero_le_one x)
  have he := ultrametric_tangent_algebra h A
  simp only [A,Set.projIcc_of_mem zero_le_one r.property,Set.projIcc_of_mem zero_le_one s.property,
    Subtype.coe_eta] at he
  have hm : (r:ℝ)-max ((r:ℝ)-s) 0=min (r:ℝ) (s:ℝ) := by
    rcases le_total (r:ℝ) (s:ℝ) with h|h
    · rw [max_eq_right (sub_nonpos.mpr h),min_eq_left h,sub_zero]
    · rw [max_eq_left (sub_nonneg.mpr h),min_eq_right h]; ring
  unfold sphereKernel
  rw [←hm]
  nlinarith only [he]

lemma sphereTail_pospart (ν : Measure Time) [IsProbabilityMeasure ν] (r : Time) :
    sphereTail ν r=1-(r:ℝ)-(∫ s,max ((s:ℝ)-r) 0 ∂ν) := by
  have hi := boundedAbs_integrable ν (fun s : Time=>max ((s:ℝ)-r) 0) (by fun_prop) 1 (time_pospart_le_one r)
  have he (s : Time) : 1-max (r:ℝ) (s:ℝ)=1-(r:ℝ)-max ((s:ℝ)-r) 0 := by
    rcases le_total (r:ℝ) (s:ℝ) with h|h
    · rw [max_eq_right h,max_eq_left (sub_nonneg.mpr h)]; ring
    · rw [max_eq_left h,max_eq_right (sub_nonpos.mpr h),sub_zero]
  simp_rw [sphereTail,he]
  rw [integral_sub (integrable_const _) hi,integral_const]
  simp

lemma compact_test_smooth_approx {a b : ℝ} (hab : a≤b) (F : Icc a b→ᵇℝ)
    {ε : ℝ} (hε : 0<ε) :
    ∃ G : ℝ→ᵇℝ, ContDiff ℝ ∞ (G : ℝ→ℝ) ∧ ∀ r : Icc a b,|G r.val-F r|≤ε := by
  let f : ℝ→ℝ := fun x=>F (Set.projIcc a b hab x)
  have hu : UniformContinuous f :=
    (CompactSpace.uniformContinuous_of_continuous F.continuous).comp (LipschitzWith.projIcc hab).uniformContinuous
  obtain ⟨g,hg,hgb⟩ := hu.exists_contDiff_dist_le hε
  have hb (x : ℝ) : |g x|≤ε+‖F‖ := by
    have he := (hgb x).le
    rw [Real.dist_eq] at he
    have := F.norm_coe_le_norm (Set.projIcc a b hab x)
    change |f x|≤‖F‖ at this
    calc
      |g x|=|g x-f x+f x| := by rw [sub_add_cancel]
      _ ≤ |g x-f x|+|f x| := abs_add_le _ _
      _ ≤ ε+‖F‖ := add_le_add he this
  let G : ℝ→ᵇℝ := BoundedContinuousFunction.mkOfBound ⟨g,hg.continuous⟩ (2*(ε+‖F‖)) (by
    intro x y
    change dist (g x) (g y)≤_
    rw [Real.dist_eq]
    exact (abs_sub _ _).trans (by linarith [hb x,hb y]))
  refine ⟨G,hg,fun r => ?_⟩
  change |g r.val-F r|≤ε
  have he := (hgb r.val).le
  simpa only [Real.dist_eq,f,Set.projIcc_of_mem hab r.property,Subtype.coe_eta] using he

lemma smooth_compact_test_extend {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {a b : ℝ} (hab : a≤b)
    (p : Ω→Icc a b) (hp : Measurable p) (Z : Ω→ℝ) (hZ : Measurable Z)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x,|Z x|≤C)
    (hz : ∀ G : ℝ→ᵇℝ,ContDiff ℝ 1 (G : ℝ→ℝ)→(∫ x,G (p x).val*Z x ∂P)=0)
    (F : Icc a b→ᵇℝ) : (∫ x,F (p x)*Z x ∂P)=0 := by
  have hFi : Integrable (fun x=>F (p x)*Z x) P :=
    Integrable.of_bound ((F.measurable.comp hp).mul hZ).aestronglyMeasurable (‖F‖*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (F.norm_coe_le_norm _) (hb _) (abs_nonneg _) (norm_nonneg F))
  apply abs_nonpos_iff.mp
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨G,hG,hGF⟩ := compact_test_smooth_approx hab F hδ
  have hGi : Integrable (fun x=>G (p x).val*Z x) P :=
    Integrable.of_bound ((G.measurable.comp (measurable_subtype_coe.comp hp)).mul hZ).aestronglyMeasurable (‖G‖*C)
      (ae_of_all _ fun x => by
        simpa only [Real.norm_eq_abs,abs_mul] using mul_le_mul (G.norm_coe_le_norm _) (hb _) (abs_nonneg _) (norm_nonneg G))
  have he : (∫ x,F (p x)*Z x ∂P)=(∫ x,(F (p x)-G (p x).val)*Z x ∂P) := by
    simp_rw [sub_mul]
    rw [integral_sub hFi hGi,hz G (hG.of_le (by norm_num)),sub_zero]
  rw [he]
  have hb' : ∀ x,‖(F (p x)-G (p x).val)*Z x‖≤δ*C := by
    intro x
    rw [Real.norm_eq_abs,abs_mul,abs_sub_comm]
    exact mul_le_mul (hGF _) (hb _) (abs_nonneg _) hδ.le
  have hi := norm_integral_le_of_norm_le_const (ae_of_all P hb')
  simp [Real.norm_eq_abs,Measure.real] at hi
  have hd : δ*(C+1)=ε := div_mul_cancel₀ ε (by linarith)
  linarith

end SphericalPerceptronFreeEnergy
end

end OAI
