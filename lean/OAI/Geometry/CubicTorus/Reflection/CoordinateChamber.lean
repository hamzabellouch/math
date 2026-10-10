import Mathlib
import OAI.Geometry.CubicTorus.Reflection.TorusCylinders

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma congruentAE_of_translated {E F C : Set Torus} {b : Torus}
    (he : F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E)) (hc : CongruentAE F C) :
    CongruentAE E C := by
  obtain ⟨φ,hφ⟩ := hc
  refine ⟨φ.trans (IsometryEquiv.addRight b),?_⟩
  have hh := (measurePreserving_add_right torusVolume (-b)).quasiMeasurePreserving.preimage_ae_eq
    (he.symm.trans hφ)
  filter_upwards [hh] with x hx
  change (x+ -b+b∈E)=(x+ -b∈φ '' C) at hx
  rw [neg_add_cancel_right] at hx
  rw [hx]
  apply propext
  constructor
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change φ y+b=x
    rw [he]; abel
  · rintro ⟨y,hy,he⟩
    refine ⟨y,hy,?_⟩
    change φ y+b=x at he
    rw [← he]; abel

theorem isMinimizerAt_standard_or_strict_reflection {V : ℝ} (hV : V∈Ioc 0 (1/2))
    {E : Set Torus} (hmE : IsMinimizerAt V E) :
    SmallStandardRegion V E ∨
    ∃ (b : Torus) (F : Set Torus) (μ : FiniteMeasure NormalBundle) (N : Cover → Cover)
      (_ : ContDiff ℝ (⊤ : ℕ∞) N) (_ : ∀ m x,N (x+latticeVector m)=N x),
      MeasurableSet F ∧ F =ᵐ[torusVolume] ((fun z => z+b) ⁻¹' E) ∧ IsMinimizerAt V F ∧
      IsPreconnected (frontier (openRepresentative F)) ∧
      IsNormalMeasure F μ ∧ (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ i : Fin 3,coordinateReflection i ⁻¹' F =ᵐ[torusVolume] F) ∧
      (∀ a : Torus,(∀ i,coordinateSine i (representative a)=0) → a∉frontier (openRepresentative F)) ∧
      ∀ i : Fin 3,
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,0<N (representative a) i) ∨
        (∀ a∈frontier (openRepresentative F)∩coordinateHalf i 0,N (representative a) i<0) := by
  have hV' : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  rcases Periodic.isMinimizerAt_connected_or_standard_slab hV' hmE with hc|hs
  · obtain ⟨b,F,μ,N,hN,hp,hF,he,hmF,hcF,hμ,hae,href,hvert,hsg⟩ :=
      isMinimizerAt_connected_reflection_geometry hV' hmE hc
    by_cases hz : ∃ i : Fin 3,∀ a∈frontier (openRepresentative F),N (representative a) i=0
    · obtain ⟨i,hi⟩ := hz
      obtain ⟨c,r,hr0,hr,hbd⟩ := isMinimizerAt_zero_coordinate_cylindrical hV' hF hmF hcF hμ hN hp hae i hi
      obtain ⟨hlow,hupp,hcong⟩ := isMinimizerAt_cylindrical_standard_tube hV hF hmF i hr0 hr hbd
      exact Or.inl (Or.inr (Or.inl ⟨hlow,hupp,congruentAE_of_translated he hcong⟩))
    · refine Or.inr ⟨b,F,μ,N,hN,hp,hF,he,hmF,hcF,hμ,hae,href,hvert,?_⟩
      intro i
      exact (hsg i).resolve_left (fun hi => hz ⟨i,hi⟩)
  · exact Or.inl (by simpa only [StandardRegionAt,ite_eq_left hV.2] using hs.2.2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalMeasure_test_translation_nonneg {E : Set Torus}
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) {a : Cover}
    (hpos : ∀ t∈Icc (0 : ℝ) 1,∀ᵐ z ∂(μ : Measure NormalBundle),
      0≤f (z.1+t • a)*⟪(z.2 : Cover),a⟫) :
    0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x+a)-f x := by
  have hdc := hf.continuous_fderiv (by simp)
  have hd := hf.differentiable (by simp)
  have hderiv (x t) : HasDerivAt (fun s : ℝ => f (x+s • a))
      (fderiv ℝ f (x+t • a) a) t := by
    simpa only [Function.comp_def,Pi.add_apply,id_eq,one_smul,zero_add] using
      (hd (x+t • a)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const a))
  have hFTC (x : Cover) : (∫ t in Ioc (0 : ℝ) 1,fderiv ℝ f (x+t • a) a)=f (x+a)-f x := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
    have hc : Continuous (fun t : ℝ => fderiv ℝ f (x+t • a) a) :=
      (hdc.comp (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hderiv x t) (hc.intervalIntegrable 0 1)
  obtain ⟨M,_,hM⟩ := periodic_bounded hdc (fderiv_periodic hp)
  have hc : Continuous (fun z : Cover × ℝ => fderiv ℝ f (z.1+z.2 • a) a) :=
    (hdc.comp (continuous_fst.add (continuous_snd.smul continuous_const))).clm_apply continuous_const
  have hi : Integrable (fun z : Cover × ℝ => fderiv ℝ f (z.1+z.2 • a) a)
      ((volume.restrict (fundamentalCube∩quotientMap ⁻¹' E)).prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    apply Integrable.of_bound hc.aestronglyMeasurable (M*‖a‖)
    exact Eventually.of_forall fun z => ((fderiv ℝ f (z.1+z.2 • a)).le_opNorm a).trans
      (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg a))
  have ht (t : ℝ) (ht : t∈Ioc (0 : ℝ) 1) :
      0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,fderiv ℝ f (x+t • a) a := by
    let g : Cover → ℝ := fun x => f (x+t • a)
    have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
    have hgp : ∀ m x,g (x+latticeVector m)=g x := by
      intro m x; dsimp [g]; rw [add_right_comm,hp]
    have heq := periodic_normal_flux hμ (hg.smul_const a) (fun m x => by rw [hgp])
    simp only [real_inner_smul_right,divergence_smul_const (hg.differentiable (by simp)).differentiableAt,
      g,fderiv_comp_add_right] at heq
    rw [← heq]
    exact integral_nonneg_of_ae (hpos t ⟨ht.1.le,ht.2⟩)
  calc
    0≤∫ t in Ioc (0 : ℝ) 1,∫ x in fundamentalCube∩quotientMap ⁻¹' E,
        fderiv ℝ f (x+t • a) a :=
      integral_nonneg_of_ae (ae_restrict_of_forall_mem measurableSet_Ioc ht)
    _ = _ := by rw [← integral_integral_swap hi]; simp_rw [hFTC]

theorem isMinimizerAt_monotone_translation_test {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {f : Cover → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hp : ∀ m x,f (x+latticeVector m)=f x) (hf0 : ∀ x,0≤f x)
    (hsupp : ∀ t∈Icc (0 : ℝ) 1,∀ x : Cover,f (x+t • a)≠0 → quotientMap x∈U) :
    0≤∫ x in fundamentalCube∩quotientMap ⁻¹' E,f (x+a)-f x := by
  apply normalMeasure_test_translation_nonneg hμ hf hp
  intro t ht
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmE).symm)
  filter_upwards [hbd,hae] with z hz hNz
  by_cases hzero : f (z.1+t • a)=0
  · rw [hzero,zero_mul]
  · rw [← hNz]
    exact mul_nonneg (hf0 _) (hsg z.1 ⟨hz,hsupp t ht z.1 hzero⟩)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma exists_open_swept_neighborhood {U : Set Torus} (hU : IsOpen U)
    (y : Torus) (a : Cover)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    ∃ W : Set Torus,IsOpen W ∧ y∈W ∧ ∀ z∈W,∀ t∈Icc (0 : ℝ) 1,z-quotientMap (t • a)∈U := by
  let O : Set (Torus × ℝ) := {z | z.1-quotientMap (z.2 • a)∈U}
  have hO : IsOpen O := hU.preimage
    (continuous_fst.sub (continuous_quotientMap.comp (continuous_snd.smul continuous_const)))
  have hs : ({y} : Set Torus) ×ˢ Icc (0 : ℝ) 1 ⊆ O := by
    rintro ⟨z,t⟩ ⟨hz,ht⟩
    rw [mem_singleton_iff] at hz
    change z=y at hz
    subst z
    exact hpath t ht
  obtain ⟨W,J,hW,hJ,hy,hI,hsub⟩ := generalized_tube_lemma isCompact_singleton isCompact_Icc hO hs
  exact ⟨W,hW,hy (mem_singleton y),fun z hz t ht => show (z,t)∈O from hsub ⟨hz,hI ht⟩⟩

theorem isMinimizerAt_no_reverse_crossing {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus} (hU : IsOpen U)
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {y : Torus} (hy : y∈openRepresentative E)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    y-quotientMap a∈closure (openRepresentative E) := by
  by_contra hx
  let F := openRepresentative E
  have hF : IsOpen F := isOpen_openRepresentative E
  have heF : F =ᵐ[torusVolume] E := isMinimizerAt_openRepresentative_ae hV hE hmE
  have hmF : IsMinimizerAt V F := (isMinimizerAt_congr_ae heF).mpr hmE
  have hμF : IsNormalMeasure F μ := hμ.congr_ae heF.symm
  obtain ⟨W,hW,hyW,hWs⟩ := exists_open_swept_neighborhood hU y a hpath
  let O := W∩F∩(fun z : Torus => z-quotientMap a) ⁻¹' (closure F)ᶜ
  have hO : IsOpen O := (hW.inter hF).inter
    (isClosed_closure.isOpen_compl.preimage (continuous_id.sub continuous_const))
  have hyO : y∈O := ⟨⟨hyW,hy⟩,hx⟩
  obtain ⟨f,hf,hp,hb,⟨T,hT,hyT,hone⟩,hzero⟩ := exists_periodic_local_cutoff y hO hyO
  have hsupp : ∀ t∈Icc (0 : ℝ) 1,∀ x : Cover,f (x+t • a)≠0 → quotientMap x∈U := by
    intro t ht x hx
    have hqx : quotientMap (x+t • a)∈O := by
      by_contra hn
      exact hx ((hzero _ hn).self_of_nhds)
    have hh := hWs _ hqx.1.1 t ht
    simpa only [quotientMap_add,add_sub_cancel_right] using hh
  have hflux := isMinimizerAt_monotone_translation_test hV hF.measurableSet hmF hμF hae
    (U := U) (by
      intro x hx
      rw [openRepresentative_congr_ae heF] at hx
      exact hsg x hx) hf hp (fun x => (hb x).1) hsupp
  let g : Torus → ℝ := fun z => f (representative z)
  have hg : Continuous g := continuous_periodic_descent hf.continuous hp
  have hgb (z : Torus) : |g z|≤1 := by
    rw [abs_of_nonneg (hb _).1]
    exact (hb _).2
  have heq : (∫ x in F,g (x+quotientMap a)-g x ∂torusVolume)=
      ∫ x in fundamentalCube∩quotientMap ⁻¹' F,f (x+a)-f x := by
    rw [setIntegral_lift_measurable (f := fun x : Torus => g (x+quotientMap a)-g x) (hg.measurable.comp (measurable_id.add_const _) |>.sub hg.measurable) hF.measurableSet]
    apply setIntegral_congr_fun (measurableSet_fundamentalCube.inter
      (hF.measurableSet.preimage measurable_quotientMap))
    intro x hx
    simp only [g,← quotientMap_add,periodic_representative hp]
  rw [← heq,integral_difference_test hF.measurableSet hg.measurable hgb] at hflux
  have hid (z : Torus) : (characteristic F (z-quotientMap a)-characteristic F z)*g z= -g z := by
    by_cases hz : g z=0
    · simp only [hz,mul_zero,neg_zero]
    have hzO : z∈O := by
      by_contra hn
      apply hz
      exact (hzero (representative z) (by rwa [quotientMap_representative])).self_of_nhds
    have hzF := hzO.1.2
    have hxF : z-quotientMap a∉F := fun h => hzO.2 (subset_closure h)
    simp only [characteristic,indicator_of_mem hzF,indicator_of_notMem hxF,zero_sub,neg_mul,one_mul]
  simp_rw [hid] at hflux
  rw [integral_neg] at hflux
  have hpos : 0<∫ z,g z ∂torusVolume := by
    apply integral_pos_of_integrable_nonneg_nonzero hg
      (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun z => (hb _).1) (x := y)
    have hy1 : g y=1 := (hone (representative y) (by rwa [quotientMap_representative])).self_of_nhds
    rw [hy1]
    norm_num
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma isMinimizerAt_regular_openRepresentative {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E) :
    interior (closure (openRepresentative E))=openRepresentative E := by
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmEc := (isMinimizerAt_compl ⟨hV.1.le,hV.2.le⟩).mpr hmE
  have he : openRepresentative E=(closure (openRepresentative Eᶜ))ᶜ := by
    rw [isMinimizerAt_closure_openRepresentative hVc hE.compl hmEc]
    rfl
  rw [he,closure_compl,interior_compl]
  congr 1
  apply Subset.antisymm
  · exact closure_minimal interior_subset isClosed_closure
  · exact closure_mono (isOpen_openRepresentative Eᶜ).subset_interior_closure

theorem isMinimizerAt_monotone_segment {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus} (hU : IsOpen U)
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {y : Torus} (hy : y∈openRepresentative E)
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    y-quotientMap a∈openRepresentative E := by
  obtain ⟨W,hW,hyW,hWs⟩ := exists_open_swept_neighborhood hU y a hpath
  let S : Set Torus := (fun z => z-quotientMap a) '' (W∩openRepresentative E)
  have hS : IsOpen S := (Homeomorph.subRight (quotientMap a)).isOpenMap _
    (hW.inter (isOpen_openRepresentative E))
  have hs : S⊆closure (openRepresentative E) := by
    rintro _ ⟨z,⟨hz,hzE⟩,rfl⟩
    exact isMinimizerAt_no_reverse_crossing hV hE hmE hμ hae hU hsg hzE (hWs z hz)
  have hx : y-quotientMap a∈S := ⟨y,⟨hyW,hy⟩,rfl⟩
  have hi := interior_mono hs (show y-quotientMap a∈interior S by rwa [hS.interior_eq])
  rwa [isMinimizerAt_regular_openRepresentative hV hE hmE] at hi

theorem isMinimizerAt_monotone_segment_closure {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {a : Cover} {U : Set Torus} (hU : IsOpen U)
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩U → 0≤⟪N x,a⟫)
    {y : Torus} (hy : y∈closure (openRepresentative E))
    (hpath : ∀ t∈Icc (0 : ℝ) 1,y-quotientMap (t • a)∈U) :
    y-quotientMap a∈closure (openRepresentative E) := by
  obtain ⟨W,hW,hyW,hWs⟩ := exists_open_swept_neighborhood hU y a hpath
  have hy' : y∈closure (W∩openRepresentative E) := hW.inter_closure ⟨hyW,hy⟩
  have hs : W∩openRepresentative E⊆(fun z : Torus => z-quotientMap a) ⁻¹' closure (openRepresentative E) := by
    intro z hz
    exact isMinimizerAt_no_reverse_crossing hV hE hmE hμ hae hU hsg hz.2 (hWs z hz.1)
  exact closure_minimal hs (isClosed_closure.preimage (continuous_id.sub continuous_const)) hy'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinateChamber (s : Fin 3 → Bool) : Set Torus :=
  ⋂ i,coordinateHalf i (if s i then 0 else 1/2)

def chamberCorner (s : Fin 3 → Bool) : Cover :=
  WithLp.toLp 2 (fun i => if s i then (1/2 : ℝ) else 0)

lemma coordinateChamber_open (s : Fin 3 → Bool) : IsOpen (coordinateChamber s) := by
  apply isOpen_iInter_of_finite
  intro i
  cases hs : s i
  · simp only [Bool.false_eq_true,ite_false]
    rw [← coordinateReflection_preimage_half]
    exact (coordinateHalf_open i).preimage (coordinateReflection_continuous i)
  · simpa only [hs,ite_true] using coordinateHalf_open i

lemma mem_chamber_of_coordinates (s : Fin 3 → Bool) {x : Cover}
    (hx : ∀ i,chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2) :
    quotientMap x∈coordinateChamber s := by
  rw [coordinateChamber,mem_iInter]
  intro i
  rw [mem_coordinateHalf_quotient]
  have hh := hx i
  cases hs : s i
  · simp only [chamberCorner,hs,Bool.false_eq_true,ite_false,zero_add] at hh
    simp only [Bool.false_eq_true,ite_false]
    apply Real.sin_neg_of_neg_of_neg_pi_lt
    · nlinarith [Real.pi_pos,hh.2]
    · nlinarith [Real.pi_pos,hh.1]
  · simp only [chamberCorner,hs,ite_true] at hh
    simp only [ite_true,sub_zero]
    have hr := Real.sin_neg_of_neg_of_neg_pi_lt
      (show 2*Real.pi*x i-2*Real.pi<0 by nlinarith [Real.pi_pos,hh.2])
      (show -Real.pi<2*Real.pi*x i-2*Real.pi by nlinarith [Real.pi_pos,hh.1])
    simpa only [Real.sin_sub_two_pi] using hr

lemma isMinimizerAt_normal_positive_opposite_half {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (hneg : ∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0) :
    ∀ a∈frontier (openRepresentative E)∩coordinateHalf i (1/2),0<N (representative a) i := by
  intro a ha
  have hb : coordinateReflection i a∈frontier (openRepresentative E) := by
    change a∈coordinateReflection i ⁻¹' frontier (openRepresentative E)
    rw [frontier_reflection_invariant hE i hs]
    exact ha.1
  have hh : coordinateReflection i a∈coordinateHalf i 0 := by
    change a∈coordinateReflection i ⁻¹' coordinateHalf i 0
    rw [coordinateReflection_preimage_half]
    exact ha.2
  have hn := hneg _ ⟨hb,hh⟩
  have he := congrArg (fun x : Cover => x i) (isMinimizerAt_normal_reflection hV hE hmE hμ hN hp hae i hs
    (representative a) (by rw [quotientMap_representative]; exact ha.1))
  simp only [coverCoordinateReflection_apply,ite_true] at he
  have hep : N (coverCoordinateReflection i (representative a))=N (representative (coordinateReflection i a)) := by
    rw [← periodic_representative hp (coverCoordinateReflection i (representative a)),
      quotientMap_coordinateReflection,quotientMap_representative]
  rw [hep] at he
  linarith

theorem isMinimizerAt_exists_positive_chamber {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    (hs : ∀ i,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    (hsg : ∀ i : Fin 3,
      (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,0<N (representative a) i) ∨
      (∀ a∈frontier (openRepresentative E)∩coordinateHalf i 0,N (representative a) i<0)) :
    ∃ s : Fin 3 → Bool,∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0<N x i := by
  classical
  have hg : ∀ i : Fin 3,∃ b : Bool,∀ a∈frontier (openRepresentative E)∩coordinateHalf i (if b then 0 else 1/2),
      0<N (representative a) i := by
    intro i
    rcases hsg i with hi|hi
    · exact ⟨true,hi⟩
    · exact ⟨false,isMinimizerAt_normal_positive_opposite_half hV hE hmE hμ hN hp hae i (hs i) hi⟩
  choose s hs' using hg
  refine ⟨s,?_⟩
  intro x hx i
  have hh := hs' i (quotientMap x) ⟨hx.1,mem_iInter.mp hx.2 i⟩
  rwa [periodic_representative hp] at hh

theorem isMinimizerAt_chamber_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    {x y : Cover} (hx : ∀ i,chamberCorner s i<x i ∧ x i<chamberCorner s i+1/2)
    (hy : ∀ i,chamberCorner s i<y i ∧ y i<chamberCorner s i+1/2)
    (hxy : ∀ i,x i≤y i) (hyE : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E := by
  have hpos : ∀ z : Cover,quotientMap z∈frontier (openRepresentative E)∩coordinateChamber s → 0≤⟪N z,y-x⟫ := by
    intro z hz
    rw [PiLp.inner_apply]
    exact Finset.sum_nonneg fun i _ => by
      simp only [RCLike.inner_apply,conj_trivial,PiLp.sub_apply]
      exact mul_nonneg (sub_nonneg.mpr (hxy i)) (hsg z hz i)
  have hpath : ∀ t∈Icc (0 : ℝ) 1,quotientMap y-quotientMap (t • (y-x))∈coordinateChamber s := by
    intro t ht
    rw [← quotientMap_sub]
    apply mem_chamber_of_coordinates
    intro i
    simp only [PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul]
    constructor
    · nlinarith [hx i,hy i,mul_nonneg ht.1 (sub_nonneg.mpr (hxy i)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hxy i))]
    · nlinarith [hx i,hy i,mul_nonneg ht.1 (sub_nonneg.mpr (hxy i)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (hxy i))]
  have hh := isMinimizerAt_monotone_segment hV hE hmE hμ hae (coordinateChamber_open s) hpos hyE hpath
  simpa only [← quotientMap_sub,sub_sub_cancel] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def openHalfBox (c : Cover) : Set Cover := {x | ∀ i,c i<x i ∧ x i<c i+1/2}
def closedHalfBox (c : Cover) : Set Cover := {x | ∀ i,c i≤x i ∧ x i≤c i+1/2}

lemma closure_openHalfBox (c : Cover) : closure (openHalfBox c)=closedHalfBox c := by
  let e := PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)
  have ho : openHalfBox c=e ⁻¹' (univ.pi fun i => Ioo (c i) (c i+1/2)) := by
    ext x; change (∀ i,c i<x i ∧ x i<c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Ioo (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Ioo]
  have hc : closedHalfBox c=e ⁻¹' (univ.pi fun i => Icc (c i) (c i+1/2)) := by
    ext x; change (∀ i,c i≤x i ∧ x i≤c i+1/2) ↔ ∀ i∈(univ : Set (Fin 3)),x i∈Icc (c i) (c i+1/2)
    simp only [mem_univ,true_implies,mem_Icc]
  rw [ho,hc]
  rw [← e.preimage_closure,closure_pi_set]
  congr 1
  apply pi_congr rfl
  intro i _
  exact closure_Ioo (by linarith)

lemma isOpen_openHalfBox (c : Cover) : IsOpen (openHalfBox c) := by
  rw [openHalfBox,ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact (isOpen_lt continuous_const (PiLp.continuous_apply _ _ i)).inter
    (isOpen_lt (PiLp.continuous_apply _ _ i) continuous_const)

lemma halfBox_downset_closure {c : Cover} {F : Set Cover}
    (hdown : ∀ x∈openHalfBox c,∀ y∈F∩openHalfBox c,(∀ i,x i≤y i) → x∈F)
    {x y : Cover} (hx : x∈closedHalfBox c)
    (hy : y∈closure (F∩openHalfBox c)) (hxy : ∀ i,x i≤y i) : x∈closure F := by
  let g : Cover × ℝ → Cover := fun z => WithLp.toLp 2 (fun i =>
    min ((1-z.2)*x i+z.2*(c i+1/4)) (z.1 i))
  have hg : Continuous g := (PiLp.continuous_toLp _ _).comp (continuous_pi fun i =>
    (((continuous_const.sub continuous_snd).mul continuous_const).add
      (continuous_snd.mul continuous_const)).min ((PiLp.continuous_apply _ _ i).comp continuous_fst))
  have hy0 : (y,(0 : ℝ))∈closure ((F∩openHalfBox c) ×ˢ Ioo (0 : ℝ) 1) := by
    rw [closure_prod_eq,closure_Ioo (by norm_num : (0 : ℝ)≠1)]
    exact ⟨hy,by norm_num⟩
  have himg : g '' ((F∩openHalfBox c) ×ˢ Ioo (0 : ℝ) 1)⊆F := by
    rintro _ ⟨⟨z,t⟩,⟨hz,ht⟩,rfl⟩
    apply hdown _ ?_ z hz
    · intro i
      change min _ (z i)≤z i
      exact min_le_right _ _
    · intro i
      change c i < min _ (z i) ∧ min _ (z i)<c i+1/2
      have hc : c i<(1-t)*x i+t*(c i+1/4) ∧
          (1-t)*x i+t*(c i+1/4)<c i+1/2 := by
        have ht0 : 0<t := ht.1
        have ht1 : t<1 := ht.2
        constructor
        · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hx i).1)]
        · nlinarith [mul_nonneg (sub_nonneg.mpr ht1.le) (sub_nonneg.mpr (hx i).2)]
      exact ⟨lt_min hc.1 (hz.2 i).1,(min_le_right _ _).trans_lt (hz.2 i).2⟩
  have hh := closure_mono himg (mem_closure_image hg.continuousAt hy0)
  have he : g (y,0)=x := by
    ext i
    change min ((1-0)*x i+0*(c i+1/4)) (y i)=x i
    simpa only [sub_zero,one_mul,zero_mul,add_zero] using min_eq_left (hxy i)
  rwa [he] at hh

theorem isMinimizerAt_chamber_closed_downset_of_open {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyE : quotientMap y∈openRepresentative E) :
    quotientMap x∈closure (openRepresentative E) := by
  let F := quotientMap ⁻¹' openRepresentative E
  have hF : IsOpen F := (isOpen_openRepresentative E).preimage continuous_quotientMap
  have hy' : y∈closure (F∩openHalfBox (chamberCorner s)) := hF.inter_closure
    ⟨hyE,by rwa [closure_openHalfBox]⟩
  have hx' : x∈closure F := halfBox_downset_closure (fun z hz w hw hzw =>
    isMinimizerAt_chamber_downset hV hE hmE hμ hae hsg hz hw.2 hzw hw.1) hx hy' hxy
  exact continuous_quotientMap.closure_preimage_subset (openRepresentative E) hx'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def foldCoordinate (i : Fin 3) (d : ℝ) (upper : Bool) (x : Cover) : Cover :=
  x+((if upper then d-|x i-d| else d+|x i-d|)-x i) • EuclideanSpace.single i 1

lemma foldCoordinate_apply (i : Fin 3) (d : ℝ) (upper : Bool) (x : Cover) (j : Fin 3) :
    foldCoordinate i d upper x j=if j=i then
      (if upper then d-|x i-d| else d+|x i-d|) else x j := by
  by_cases hj : j=i
  · subst j; simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply]
  · simp [foldCoordinate,PiLp.add_apply,PiLp.smul_apply,hj]

lemma foldCoordinate_continuous (i : Fin 3) (d : ℝ) (upper : Bool) :
    Continuous (foldCoordinate i d upper) := by
  cases upper <;> unfold foldCoordinate <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;>
    fun_prop

lemma quotientMap_centered_reflection (i : Fin 3) {d : ℝ}
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (x+(2*d-2*x i) • EuclideanSpace.single i 1)=coordinateReflection i (quotientMap x) := by
  obtain ⟨k,hk⟩ := hd
  have he : x+(2*d-2*x i) • EuclideanSpace.single i 1=
      coverCoordinateReflection i x+latticeVector (Pi.single i k) := by
    ext j
    by_cases hj : j=i
    · subst j
      simp [PiLp.add_apply,PiLp.smul_apply,latticeVector]
      linarith
    · simp [PiLp.add_apply,PiLp.smul_apply,latticeVector,hj]
  rw [he,quotientMap_add,quotientMap_latticeVector,add_zero,quotientMap_coordinateReflection]

lemma foldCoordinate_quotient_alternative (i : Fin 3) {d : ℝ} (upper : Bool)
    (hd : ∃ k : ℤ,2*d=(k : ℝ)) (x : Cover) :
    quotientMap (foldCoordinate i d upper x)=quotientMap x ∨
    quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
  have hsame (h : (if upper then d-|x i-d| else d+|x i-d|)=x i) :
      quotientMap (foldCoordinate i d upper x)=quotientMap x := by
    simp only [foldCoordinate,h,sub_self,zero_smul,add_zero]
  have href (h : (if upper then d-|x i-d| else d+|x i-d|)-x i=2*d-2*x i) :
      quotientMap (foldCoordinate i d upper x)=coordinateReflection i (quotientMap x) := by
    simp only [foldCoordinate,h,quotientMap_centered_reflection i hd]
  cases upper
  · by_cases hx : 0≤x i-d
    · exact Or.inl (hsame (by simp only [Bool.false_eq_true,ite_false,abs_of_nonneg hx]; ring))
    · exact Or.inr (href (by simp only [Bool.false_eq_true,ite_false,abs_of_neg (lt_of_not_ge hx)]; ring))
  · by_cases hx : x i-d≤0
    · exact Or.inl (hsame (by simp only [ite_true,abs_of_nonpos hx]; ring))
    · exact Or.inr (href (by simp only [ite_true,abs_of_pos (lt_of_not_ge hx)]; ring))

def localFoldCoordinate (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) (x : Cover) : Cover :=
  if y i=chamberCorner s i then foldCoordinate i (chamberCorner s i) false x
  else if y i=chamberCorner s i+1/2 then foldCoordinate i (chamberCorner s i+1/2) true x else x

def localChamberFold (s : Fin 3 → Bool) (y x : Cover) : Cover :=
  localFoldCoordinate s y 2 (localFoldCoordinate s y 1 (localFoldCoordinate s y 0 x))

lemma localFoldCoordinate_apply (s : Fin 3 → Bool) (y : Cover) (i j : Fin 3) (x : Cover) :
    localFoldCoordinate s y i x j=if j=i then
      (if y i=chamberCorner s i then chamberCorner s i+|x i-chamberCorner s i|
       else if y i=chamberCorner s i+1/2 then chamberCorner s i+1/2-|x i-(chamberCorner s i+1/2)| else x i)
      else x j := by
  unfold localFoldCoordinate
  split_ifs <;> simp_all only [foldCoordinate_apply,Bool.false_eq_true,ite_false,ite_true]

lemma localChamberFold_apply (s : Fin 3 → Bool) (y x : Cover) (i : Fin 3) :
    localChamberFold s y x i=
      if y i=chamberCorner s i then chamberCorner s i+|x i-chamberCorner s i|
      else if y i=chamberCorner s i+1/2 then chamberCorner s i+1/2-|x i-(chamberCorner s i+1/2)| else x i := by
  fin_cases i <;> simp [localChamberFold,localFoldCoordinate_apply]

lemma localFoldCoordinate_continuous (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) :
    Continuous (localFoldCoordinate s y i) := by
  unfold localFoldCoordinate
  split_ifs <;> first | exact foldCoordinate_continuous _ _ _ | exact continuous_id

lemma localChamberFold_continuous (s : Fin 3 → Bool) (y : Cover) : Continuous (localChamberFold s y) :=
  (localFoldCoordinate_continuous s y 2).comp
    ((localFoldCoordinate_continuous s y 1).comp (localFoldCoordinate_continuous s y 0))

lemma localChamberFold_fixed (s : Fin 3 → Bool) (y : Cover) : localChamberFold s y y=y := by
  ext i
  rw [localChamberFold_apply]
  split_ifs with h₁ h₂
  · rw [h₁,sub_self,abs_zero,add_zero]
  · rw [h₂,sub_self,abs_zero,sub_zero]
  · rfl

lemma localChamberFold_mem_eventually (s : Fin 3 → Bool) {y : Cover}
    (hy : y∈closedHalfBox (chamberCorner s)) :
    ∀ᶠ x in 𝓝 y,localChamberFold s y x∈closedHalfBox (chamberCorner s) := by
  change ∀ᶠ x in 𝓝 y,∀ i,chamberCorner s i≤localChamberFold s y x i ∧
    localChamberFold s y x i≤chamberCorner s i+1/2
  rw [Filter.eventually_all]
  intro i
  have hc : ContinuousAt (fun x => localChamberFold s y x i) y :=
    ((PiLp.continuous_apply _ _ i).comp (localChamberFold_continuous s y)).continuousAt
  by_cases hlo : y i=chamberCorner s i
  · have hh : localChamberFold s y y i<chamberCorner s i+1/2 := by rw [localChamberFold_fixed,hlo]; linarith
    filter_upwards [hc.eventually_lt continuous_const.continuousAt hh] with x hx
    refine ⟨?_,hx.le⟩
    rw [localChamberFold_apply,ite_eq_left hlo]
    exact le_add_of_nonneg_right (abs_nonneg _)
  · by_cases hup : y i=chamberCorner s i+1/2
    · have hh : chamberCorner s i<localChamberFold s y y i := by rw [localChamberFold_fixed,hup]; linarith
      filter_upwards [continuous_const.continuousAt.eventually_lt hc hh] with x hx
      refine ⟨hx.le,?_⟩
      rw [localChamberFold_apply,ite_eq_right hlo,ite_eq_left hup]
      exact sub_le_self _ (abs_nonneg _)
    · have hh₁ : chamberCorner s i<localChamberFold s y y i := by
        rw [localChamberFold_fixed]; exact lt_of_le_of_ne (hy i).1 (Ne.symm hlo)
      have hh₂ : localChamberFold s y y i<chamberCorner s i+1/2 := by
        rw [localChamberFold_fixed]; exact lt_of_le_of_ne (hy i).2 hup
      filter_upwards [continuous_const.continuousAt.eventually_lt hc hh₁,
        hc.eventually_lt continuous_const.continuousAt hh₂] with x h₁ h₂
      exact ⟨h₁.le,h₂.le⟩

lemma localFoldCoordinate_preserves {F : Set Torus}
    (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y : Cover) (i : Fin 3) {x : Cover} (hx : quotientMap x∈F) :
    quotientMap (localFoldCoordinate s y i x)∈F := by
  have hbase : ∃ k : ℤ,2*chamberCorner s i=(k : ℝ) := by
    cases hs : s i
    · exact ⟨0,by simp [chamberCorner,hs]⟩
    · exact ⟨1,by simp [chamberCorner,hs]⟩
  have htop : ∃ k : ℤ,2*(chamberCorner s i+1/2)=(k : ℝ) := by
    obtain ⟨k,hk⟩ := hbase
    exact ⟨k+1,by push_cast; linarith⟩
  have hh {d : ℝ} (b : Bool) (hd : ∃ k : ℤ,2*d=(k : ℝ)) : quotientMap (foldCoordinate i d b x)∈F := by
    rcases foldCoordinate_quotient_alternative i b hd x with he|he
    · rwa [he]
    · rw [he]
      change quotientMap x∈coordinateReflection i ⁻¹' F
      rwa [hF i]
  unfold localFoldCoordinate
  split_ifs
  · exact hh false hbase
  · exact hh true htop
  · exact hx

lemma localChamberFold_preserves {F : Set Torus}
    (hF : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y : Cover) {x : Cover} (hx : quotientMap x∈F) :
    quotientMap (localChamberFold s y x)∈F :=
  localFoldCoordinate_preserves hF s y 2
    (localFoldCoordinate_preserves hF s y 1 (localFoldCoordinate_preserves hF s y 0 hx))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma quotientMap_isOpenMap : IsOpenMap quotientMap := by
  intro U hU
  rw [Metric.isOpen_iff]
  rintro a ⟨x,hx,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine ⟨r,hr,?_⟩
  rw [← quotientMap_image_ball]
  exact image_mono hball

lemma openRepresentative_reflection_invariant {E : Set Torus} (hE : MeasurableSet E) (i : Fin 3)
    (hs : coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E) :
    coordinateReflection i ⁻¹' openRepresentative E=openRepresentative E := by
  rw [← openRepresentative_coordinateReflection hE i,openRepresentative_congr_ae hs]

lemma chamber_closure_from_interior {F : Set Torus} (hF : IsOpen F)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) {y : Cover} (hy : y∈closedHalfBox (chamberCorner s))
    (hyF : quotientMap y∈closure F) :
    y∈closure ((quotientMap ⁻¹' F)∩openHalfBox (chamberCorner s)) := by
  have hyl : y∈closure (quotientMap ⁻¹' F) := by
    rw [← quotientMap_isOpenMap.preimage_closure_eq_closure_preimage continuous_quotientMap]
    exact hyF
  have hfreq := (mem_closure_iff_frequently.mp hyl).and_eventually
    (localChamberFold_mem_eventually s hy)
  have hh : ∃ᶠ x in 𝓝 y,localChamberFold s y x∈
      closure ((quotientMap ⁻¹' F)∩openHalfBox (chamberCorner s)) := by
    apply hfreq.mono
    rintro x ⟨hx,hxc⟩
    apply (hF.preimage continuous_quotientMap).inter_closure
    exact ⟨localChamberFold_preserves hs s y hx,by rwa [closure_openHalfBox]⟩
  have ht : Tendsto (localChamberFold s y) (𝓝 y) (𝓝 y) := by
    have hc := (localChamberFold_continuous s y).continuousAt (x := y)
    change Tendsto (localChamberFold s y) (𝓝 y) (𝓝 (localChamberFold s y y)) at hc
    rwa [localChamberFold_fixed] at hc
  exact isClosed_closure.mem_of_frequently_of_tendsto hh ht

theorem isMinimizerAt_chamber_closed_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyE : quotientMap y∈closure (openRepresentative E)) :
    quotientMap x∈closure (openRepresentative E) := by
  have hy' := chamber_closure_from_interior (isOpen_openRepresentative E)
    (fun i => openRepresentative_reflection_invariant hE i (hs i)) s hy hyE
  have hx' := halfBox_downset_closure (fun z hz w hw hzw =>
    isMinimizerAt_chamber_downset hV hE hmE hμ hae hsg hz hw.2 hzw hw.1) hx hy' hxy
  exact continuous_quotientMap.closure_preimage_subset (openRepresentative E) hx'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma localChamberFold_mem_iff {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    (s : Fin 3 → Bool) (y x : Cover) :
    quotientMap (localChamberFold s y x)∈F ↔ quotientMap x∈F := by
  constructor
  · intro hx
    by_contra hn
    have hsc : ∀ i : Fin 3,coordinateReflection i ⁻¹' Fᶜ=Fᶜ := by
      intro i; rw [preimage_compl,hs i]
    exact localChamberFold_preserves hsc s y hn hx
  · exact localChamberFold_preserves hs s y

lemma reflection_invariant_closure {F : Set Torus}
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F) :
    ∀ i : Fin 3,coordinateReflection i ⁻¹' closure F=closure F := by
  intro i
  change (coordinateReflectionEquiv i).toHomeomorph ⁻¹' closure F=closure F
  rw [(coordinateReflectionEquiv i).toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage
    (coordinateReflection_continuous i)]
  change closure (coordinateReflection i ⁻¹' F)=closure F
  rw [hs i]

lemma chamber_open_downset_of_closed {F : Set Torus} (hF : IsOpen F)
    (hr : interior (closure F)=F)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' F=F)
    {s : Fin 3 → Bool}
    (hd : ∀ {x y : Cover},x∈closedHalfBox (chamberCorner s) →
      y∈closedHalfBox (chamberCorner s) → (∀ i,x i≤y i) →
      quotientMap y∈closure F → quotientMap x∈closure F)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyF : quotientMap y∈F) : quotientMap x∈F := by
  let g : Cover → Cover := fun z => WithLp.toLp 2 (fun i => max (y i) (localChamberFold s x z i))
  have hg : Continuous g := (PiLp.continuous_toLp _ _).comp (continuous_pi fun i =>
    continuous_const.max ((PiLp.continuous_apply _ _ i).comp (localChamberFold_continuous s x)))
  have he : g x=y := by
    ext i
    change max (y i) (localChamberFold s x x i)=y i
    rw [localChamberFold_fixed,max_eq_left (hxy i)]
  have hgf : ∀ᶠ z in 𝓝 x,quotientMap (g z)∈F := by
    apply ((hF.preimage continuous_quotientMap).preimage hg).mem_nhds
    change quotientMap (g x)∈F
    rwa [he]
  have hh : ∀ᶠ z in 𝓝 x,quotientMap z∈closure F := by
    filter_upwards [hgf,localChamberFold_mem_eventually s hx] with z hz hzc
    have hgz : g z∈closedHalfBox (chamberCorner s) := by
      intro i
      exact ⟨(hy i).1.trans (le_max_left _ _),max_le (hy i).2 (hzc i).2⟩
    have horder : ∀ i,localChamberFold s x z i≤g z i := fun i => le_max_right _ _
    exact (localChamberFold_mem_iff (reflection_invariant_closure hs) s x z).mp
      (hd hzc hgz horder (subset_closure hz))
  have hi : x∈interior (quotientMap ⁻¹' closure F) := mem_interior_iff_mem_nhds.mpr hh
  have hqi := quotientMap_isOpenMap.interior_preimage_subset_preimage_interior hi
  change quotientMap x∈interior (closure F) at hqi
  rwa [hr] at hqi

theorem isMinimizerAt_chamber_open_downset {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmE : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {s : Fin 3 → Bool}
    (hsg : ∀ x : Cover,quotientMap x∈frontier (openRepresentative E)∩coordinateChamber s →
      ∀ i : Fin 3,0≤N x i)
    (hs : ∀ i : Fin 3,coordinateReflection i ⁻¹' E =ᵐ[torusVolume] E)
    {x y : Cover} (hx : x∈closedHalfBox (chamberCorner s))
    (hy : y∈closedHalfBox (chamberCorner s)) (hxy : ∀ i,x i≤y i)
    (hyE : quotientMap y∈openRepresentative E) :
    quotientMap x∈openRepresentative E :=
  chamber_open_downset_of_closed (isOpen_openRepresentative E)
    (isMinimizerAt_regular_openRepresentative hV hE hmE)
    (fun i => openRepresentative_reflection_invariant hE i (hs i))
    (fun hx hy hxy hyE => isMinimizerAt_chamber_closed_downset hV hE hmE hμ hae hsg hs hx hy hxy hyE)
    hx hy hxy hyE

end CubicTorus

end
end

end OAI
