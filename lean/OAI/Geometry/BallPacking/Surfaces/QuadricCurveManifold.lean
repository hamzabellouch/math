import Mathlib
import OAI.Geometry.BallPacking.Surfaces.DiagonalQuadric

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Manifold
open Filter
section
variable {m : ℕ} (a : Fin m → ℂ) [ha : Fact (Injective a)] [ha0 : Fact (∀ j,a j≠0)]

def normalChartAt (x : locus a) : NormalChart a :=
  (exists_normalChart_at ha.out ha0.out x).choose

theorem mem_normalChartAt (x : locus a) : (x : Affine m)∈(normalChartAt a x).ambient.source :=
  (exists_normalChart_at ha.out ha0.out x).choose_spec

instance curveChartedSpace : ChartedSpace ℂ (locus a) where
  atlas := range (fun x => (normalChartAt a x).sliceChart x)
  chartAt x := (normalChartAt a x).sliceChart x
  mem_chart_source x := mem_normalChartAt a x
  chart_mem_atlas x := mem_range_self x

instance curveComplexManifold : IsManifold 𝓘(ℂ,ℂ) ∞ (locus a) := by
  apply isManifold_of_contDiffOn 𝓘(ℂ,ℂ) ∞ (locus a)
  rintro e f ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [mfld_simps] using
    (normalChartAt a x).transition_smooth x (normalChartAt a y) y

theorem curve_inclusion_contMDiff :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,Affine m) ∞ (Subtype.val : locus a → Affine m) := by
  intro x
  have he : chartAt ℂ x=(normalChartAt a x).sliceChart x := rfl
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · have h := (normalChartAt a x).sliceChart_inverse_smooth x
    have hx : (chartAt ℂ x x)∈((normalChartAt a x).sliceChart x).target :=
      ((normalChartAt a x).sliceChart x).map_source (mem_normalChartAt a x)
    have ho := ((normalChartAt a x).sliceChart x).open_target
    have hc := (h _ hx).contDiffAt (ho.mem_nhds hx)
    simpa only [mfld_simps,chartAt_self_eq,he,OpenPartialHomeomorph.refl_apply,
      Function.id_comp,Function.comp_def,chartAt,curveChartedSpace] using hc.contDiffWithinAt

abbrev RealModel := ℝ × ℝ

def realChart (x : locus a) : OpenPartialHomeomorph (locus a) RealModel :=
  ((normalChartAt a x).sliceChart x).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem realChart_source (x : locus a) :
    (realChart a x).source=((normalChartAt a x).sliceChart x).source := by
  simp [realChart]

instance realSurfaceChartedSpace : ChartedSpace RealModel (locus a) where
  atlas := range (realChart a)
  chartAt := realChart a
  mem_chart_source x := by rw [realChart_source]; exact mem_normalChartAt a x
  chart_mem_atlas x := mem_range_self x

theorem real_transition_smooth (x y : locus a) :
    ContDiffOn ℝ ∞ ((realChart a x).symm.trans (realChart a y))
      ((realChart a x).symm.trans (realChart a y)).source := by
  let e := (normalChartAt a x).sliceChart x
  let f := (normalChartAt a y).sliceChart y
  have hc := ((normalChartAt a x).transition_smooth x (normalChartAt a y) y).restrict_scalars ℝ
  have hd := Complex.equivRealProdCLM.contDiff.comp_contDiffOn
    (hc.comp Complex.equivRealProdCLM.symm.contDiff.contDiffOn (mapsTo_preimage _ _))
  apply hd.mono
  intro z hz
  exact ⟨hz.1.2,hz.2.1⟩

instance realSurfaceManifold : IsManifold 𝓘(ℝ,RealModel) ∞ (locus a) := by
  apply isManifold_of_contDiffOn 𝓘(ℝ,RealModel) ∞ (locus a)
  rintro e f ⟨x,rfl⟩ ⟨y,rfl⟩
  simpa only [mfld_simps] using real_transition_smooth a x y

theorem real_inclusion_contMDiff :
    ContMDiff 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine m) ∞ (Subtype.val : locus a → Affine m) := by
  intro x
  have he : chartAt RealModel x=realChart a x := rfl
  rw [contMDiffAt_iff]
  constructor
  · exact continuous_subtype_val.continuousAt
  · have hs := ((normalChartAt a x).sliceChart_inverse_smooth x).restrict_scalars ℝ
    have hp : (chartAt ℂ x x)∈((normalChartAt a x).sliceChart x).target :=
      ((normalChartAt a x).sliceChart x).map_source (mem_normalChartAt a x)
    have ht := (hs _ hp).contDiffAt (((normalChartAt a x).sliceChart x).open_target.mem_nhds hp)
    have hc := ht.comp (x := Complex.equivRealProdCLM (chartAt ℂ x x))
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt
    have heC : chartAt ℂ x=(normalChartAt a x).sliceChart x := rfl
    simpa only [mfld_simps,he,heC,realChart,chartAt_self_eq,
      OpenPartialHomeomorph.refl_apply,Function.comp_def,
      ContinuousLinearEquiv.coe_toHomeomorph,
      ← ContinuousLinearEquiv.toHomeomorph_symm] using hc.contDiffWithinAt

end
section

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

section Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : E → locus a} {s : Set E} {x : E}

theorem curve_contMDiffWithinAt_of_ambient
    (hf : ContDiffWithinAt ℂ ∞ (fun t => (f t : Affine m)) s x) :
    ContMDiffWithinAt 𝓘(ℂ,E) 𝓘(ℂ,ℂ) ∞ f s x := by
  rw [contMDiffWithinAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousWithinAt,?_⟩
  have he : chartAt ℂ (f x)=(normalChartAt a (f x)).sliceChart (f x) := rfl
  have hc := (curveCoordinate (normalChartAt a (f x)).coordinate).contDiff.comp_contDiffWithinAt hf
  apply contMDiffWithinAt_iff_contDiffWithinAt.mpr
  simpa only [mfld_simps,he,NormalChart.sliceChart_apply,Function.comp_def] using hc

end Complex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : E → locus a} {s : Set E} {x : E}

theorem real_contMDiffWithinAt_of_ambient
    (hf : ContDiffWithinAt ℝ ∞ (fun t => (f t : Affine m)) s x) :
    ContMDiffWithinAt 𝓘(ℝ,E) 𝓘(ℝ,RealModel) ∞ f s x := by
  rw [contMDiffWithinAt_iff_target]
  refine ⟨tendsto_subtype_rng.mpr hf.continuousWithinAt,?_⟩
  have he : chartAt RealModel (f x)=realChart a (f x) := rfl
  have hc := Complex.equivRealProdCLM.contDiff.comp_contDiffWithinAt
    (((curveCoordinate (normalChartAt a (f x)).coordinate).contDiff.restrict_scalars ℝ).comp_contDiffWithinAt hf)
  apply contMDiffWithinAt_iff_contDiffWithinAt.mpr
  simpa only [mfld_simps,he,realChart,NormalChart.sliceChart_apply,
    ContinuousLinearEquiv.coe_toHomeomorph,Function.comp_def] using hc

end
section

variable {m : ℕ} (a : Fin m → ℂ) (ε : Fin m → Bool)

 def infinityBranch : Set (locus a) := {x | x.val.1≠0 ∧
    x.val.1⁻¹∈infinityRegion a ∧ ∀ j,0<(endSign (ε j)*(x.val.1⁻¹*x.val.2 j)).re}

 theorem normalized_coordinate_sq {x : locus a} (hx : x.val.1≠0) (j : Fin m) :
    (x.val.1⁻¹*x.val.2 j)^2=1-a j*(x.val.1⁻¹)^2 := by
  rw [mul_pow,mem_locus.mp x.property j]
  field_simp

 theorem infinityPoint_inverse {x : locus a} (hx : x∈infinityBranch a ε) :
    infinityPoint a ε x.val.1⁻¹=x.val := by
  apply Prod.ext (inv_inv _)
  funext j
  have hs : (endSign (ε j)*(x.val.1⁻¹*x.val.2 j))^2=1-a j*(x.val.1⁻¹)^2 := by
    rw [mul_pow,endSign_sq,one_mul,normalized_coordinate_sq a hx.1]
  change (x.val.1⁻¹)⁻¹*(endSign (ε j)*Complex.sqrt (1-a j*(x.val.1⁻¹)^2))=x.val.2 j
  rw [← hs,sqrt_of_sq_pos (hx.2.2 j),← mul_assoc (endSign (ε j)),endSign_mul_self,one_mul,inv_inv]
  field_simp [hx.1]

 def infinityFallback : locus a := ⟨(0,fun j => Complex.sqrt (-a j)),by
   apply mem_locus.mpr
   intro j
   dsimp only
   rw [sqrt_sq_complex,zero_pow (by decide : (2 : ℕ)≠0),zero_sub]⟩

 def infinityInverse (s : ℂ) : locus a := by
  classical
  exact if h : s≠0 then ⟨infinityPoint a ε s,infinityPoint_mem a ε h⟩ else infinityFallback a

@[simp] theorem infinityInverse_val {s : ℂ} (hs : s≠0) :
    (infinityInverse a ε s).val=infinityPoint a ε s := by
  simp only [infinityInverse,dite_eq_left hs]

 theorem infinityBranch_open : IsOpen (infinityBranch a ε) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  have ht : Continuous (fun x : locus a => x.val.1) := continuous_fst.comp continuous_subtype_val
  have hi : ContinuousAt (fun x : locus a => x.val.1⁻¹) x := ht.continuousAt.inv₀ hx.1
  have H : ∀ᶠ y in 𝓝 x,y.val.1≠0 := (isOpen_ne_fun ht continuous_const).mem_nhds hx.1
  have R : ∀ᶠ y in 𝓝 x,y.val.1⁻¹∈infinityRegion a :=
    hi.preimage_mem_nhds ((infinityRegion_open a).mem_nhds hx.2.1)
  have W : ∀ j,∀ᶠ y in 𝓝 x,0<(endSign (ε j)*(y.val.1⁻¹*y.val.2 j)).re := by
    intro j
    have hw : ContinuousAt (fun x : locus a => x.val.2 j) x := by fun_prop
    have hc : ContinuousAt (fun x : locus a =>
        (endSign (ε j)*(x.val.1⁻¹*x.val.2 j)).re) x :=
      Complex.continuous_re.continuousAt.comp
        (continuousAt_const.mul (hi.mul hw))
    exact hc.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hx.2.2 j))
  filter_upwards [H,R,Filter.eventually_all.mpr W] with y hy hr hw
  exact ⟨hy,hr,hw⟩

 def infinityChart : OpenPartialHomeomorph (locus a) ℂ where
  toFun x := x.val.1⁻¹
  invFun := infinityInverse a ε
  source := infinityBranch a ε
  target := infinityDomain a
  map_source' _ hx := ⟨inv_ne_zero hx.1,hx.2.1⟩
  map_target' s hs := by
    change (infinityInverse a ε s).val.1≠0 ∧ _
    rw [infinityInverse_val a ε hs.1]
    refine ⟨inv_ne_zero hs.1,?_,?_⟩
    · change (s⁻¹)⁻¹∈infinityRegion a
      simpa only [inv_inv] using hs.2
    · intro j
      change 0<(endSign (ε j)*((s⁻¹)⁻¹*(s⁻¹*infinityRoot a ε s j))).re
      rw [inv_inv,← mul_assoc s,mul_inv_cancel₀ hs.1,one_mul]
      exact infinityRoot_positive a ε hs.2 j
  left_inv' x hx := by
    apply Subtype.ext
    rw [infinityInverse_val a ε (inv_ne_zero hx.1)]
    exact infinityPoint_inverse a ε hx
  right_inv' s hs := by
    rw [infinityInverse_val a ε hs.1,infinityPoint_coordinate]
  open_source := infinityBranch_open a ε
  open_target := infinityDomain_open a
  continuousOn_toFun := by
    intro x hx
    exact (((continuous_fst.comp continuous_subtype_val).continuousAt).inv₀ hx.1).continuousWithinAt
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (infinityPoint a ε) (infinityDomain a) :=
      fun s hs => (infinityPoint_contDiffAt a ε hs).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun s => (infinityInverse_val a ε s.property.1).symm

@[simp] theorem infinityChart_apply (x : locus a) : infinityChart a ε x=x.val.1⁻¹ := rfl
@[simp] theorem infinityChart_source : (infinityChart a ε).source=infinityBranch a ε := rfl
@[simp] theorem infinityChart_target : (infinityChart a ε).target=infinityDomain a := rfl

end

variable {m : ℕ} (a : Fin m → ℂ)

theorem re_ne_zero_of_sq_re_pos {z : ℂ} (hz : 0<(z^2).re) : z.re≠0 := by
  intro h
  have hi := sq_nonneg z.im
  simp only [pow_two,Complex.mul_re,h,zero_mul] at hz
  nlinarith

theorem endSign_positive_unique {z : ℂ} {b c : Bool}
    (hb : 0<(endSign b*z).re) (hc : 0<(endSign c*z).re) : b=c := by
  cases b <;> cases c <;> simp_all [endSign]
  <;> linarith

theorem exists_positive_endSign {z : ℂ} (hz : z.re≠0) : ∃ b : Bool,0<(endSign b*z).re := by
  rcases lt_or_gt_of_ne hz with h|h
  · exact ⟨true,by simpa [endSign] using neg_pos.mpr h⟩
  · exact ⟨false,by simpa [endSign] using h⟩

theorem infinityBranch_disjoint {ε η : Fin m → Bool} (h : ε≠η) :
    Disjoint (infinityBranch a ε) (infinityBranch a η) := by
  rw [Set.disjoint_left]
  intro x hx hy
  apply h
  funext j
  exact endSign_positive_unique (hx.2.2 j) (hy.2.2 j)

theorem exists_infinityBranch {x : locus a} (hx : x.val.1≠0)
    (hr : x.val.1⁻¹∈infinityRegion a) : ∃ ε : Fin m → Bool,x∈infinityBranch a ε := by
  have h : ∀ j,∃ b : Bool,0<(endSign b*(x.val.1⁻¹*x.val.2 j)).re := by
    intro j
    apply exists_positive_endSign
    apply re_ne_zero_of_sq_re_pos
    rw [normalized_coordinate_sq a hx]
    exact hr j
  choose ε hε using h
  exact ⟨ε,hx,hr,hε⟩

theorem infinityBranch_cover :
    (⋃ ε : Fin m → Bool,infinityBranch a ε)={x : locus a | x.val.1≠0 ∧ x.val.1⁻¹∈infinityRegion a} := by
  ext x
  constructor
  · intro hx
    obtain ⟨ε,hε⟩ := mem_iUnion.mp hx
    exact ⟨hε.1,hε.2.1⟩
  · rintro ⟨hx,hr⟩
    obtain ⟨ε,hε⟩ := exists_infinityBranch a hx hr
    exact mem_iUnion.mpr ⟨ε,hε⟩

theorem large_coordinate_in_end {r : ℝ} (hr : 0<r)
    (hD : Metric.ball (0 : ℂ) r⊆infinityRegion a) {x : locus a}
    (hx : r⁻¹<‖x.val.1‖) : ∃ ε : Fin m → Bool,x∈infinityBranch a ε := by
  have hn : 0<‖x.val.1‖ := lt_trans (inv_pos.mpr hr) hx
  have hz : x.val.1≠0 := norm_pos_iff.mp hn
  apply exists_infinityBranch a hz
  apply hD
  rw [Metric.mem_ball,dist_zero_right,norm_inv]
  exact (inv_lt_comm₀ hn hr).mpr hx

@[simp] theorem infinity_end_count : Fintype.card (Fin m → Bool)=2^m := by simp

end PackingSufficiencySupport.DiagonalQuadrics

namespace PackingSufficiencySupport
open Function
open scoped Topology
open Set Filter

theorem complex_real_conjugate_det (L : ℂ →L[ℂ] ℂ) :
    (Complex.equivRealProdCLM.toContinuousLinearMap.comp
      ((L.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toContinuousLinearMap)).det=
      Complex.normSq L.det := by
  change LinearMap.det
    (Complex.equivRealProdCLM.toLinearEquiv.toLinearMap.comp
      ((L.toLinearMap.restrictScalars ℝ).comp Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap))=_
  have h := LinearMap.det_conj (L.toLinearMap.restrictScalars ℝ)
    Complex.equivRealProdCLM.toLinearEquiv
  exact h.trans (by rw [LinearMap.det_restrictScalars,Algebra.norm_complex_eq]; rfl)

theorem holomorphic_plane_det_nonneg {f : ℂ → ℂ} {y : ℝ × ℝ}
    (hf : DifferentiableAt ℂ f (Complex.equivRealProdCLM.symm y)) :
    0≤(fderiv ℝ (Complex.equivRealProdCLM ∘ f ∘ Complex.equivRealProdCLM.symm) y).det := by
  have hd := Complex.equivRealProdCLM.hasFDerivAt.comp y
    ((hf.hasFDerivAt.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.hasFDerivAt)
  rw [hd.fderiv,complex_real_conjugate_det]
  exact Complex.normSq_nonneg _

theorem partialHomeomorph_fderiv_det_ne_zero
    (e : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ)) {x : ℝ × ℝ} (hx : x∈e.source)
    (hf : DifferentiableAt ℝ e x) (hg : DifferentiableAt ℝ e.symm (e x)) :
    (fderiv ℝ e x).det≠0 := by
  have hd := hg.hasFDerivAt.comp x hf.hasFDerivAt
  have heq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hi : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)=ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    have hh := hd.congr_of_eventuallyEq heq.symm
    simpa only [fderiv_id] using hh.fderiv.symm
  have hdet := congrArg ContinuousLinearMap.det hi
  change LinearMap.det ((fderiv ℝ e.symm (e x)).toLinearMap.comp
    (fderiv ℝ e x).toLinearMap)=LinearMap.det (LinearMap.id : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) at hdet
  rw [LinearMap.det_comp,LinearMap.det_id] at hdet
  exact right_ne_zero_of_mul_eq_one hdet

theorem holomorphic_partialHomeomorph_orientation
    (e : OpenPartialHomeomorph ℂ ℂ) {y : ℝ × ℝ}
    (hy : Complex.equivRealProdCLM.symm y∈e.source)
    (hf : DifferentiableAt ℂ e (Complex.equivRealProdCLM.symm y))
    (hg : DifferentiableAt ℂ e.symm (e (Complex.equivRealProdCLM.symm y))) :
    0<(fderiv ℝ (Complex.equivRealProdCLM ∘ e ∘ Complex.equivRealProdCLM.symm) y).det := by
  let d := (Complex.equivRealProdCLM.symm.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
    Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph
  have hd : DifferentiableAt ℝ d y :=
    Complex.equivRealProdCLM.differentiableAt.comp y
      ((hf.restrictScalars ℝ).comp y Complex.equivRealProdCLM.symm.differentiableAt)
  have hs : DifferentiableAt ℝ d.symm (d y) := by
    have h0 := Complex.equivRealProdCLM.differentiableAt.comp (d y)
      ((hg.restrictScalars ℝ).comp (d y) Complex.equivRealProdCLM.symm.differentiableAt)
    convert h0 using 1
    rfl
  have hn := partialHomeomorph_fderiv_det_ne_zero d (by exact ⟨⟨mem_univ _,hy⟩,mem_univ _⟩) hd hs
  exact lt_of_le_of_ne (holomorphic_plane_det_nonneg hf) (Ne.symm hn)

end PackingSufficiencySupport
end

end OAI
