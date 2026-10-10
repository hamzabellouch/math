import OAI.Analysis.IntegralMeans.ExpectedTransport

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma differentiableOn_classReciprocal (g : DiskClass) :
    DifferentiableOn ℂ (reciprocalDeriv (classFun g)) halfPlane :=
  fun _ hz => (hasDerivAt_reciprocalDeriv (classFun_schlicht g).1 hz).differentiableAt.differentiableWithinAt

lemma continuous_classReciprocal_eval :
    Continuous (fun p : DiskClass × halfPlane => reciprocalDeriv (classFun p.1) p.2) := by
  have hd : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
  exact hd.inv₀ (fun p => univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.2)

def reciprocalJet (n : ℕ) (g : DiskClass) : C(halfPlane,ℂ) :=
  ⟨fun z => iteratedDeriv n (reciprocalDeriv (classFun g)) z, continuousOn_iff_continuous_domRestrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_halfPlane (differentiableOn_classReciprocal g) n).continuousOn⟩

lemma continuous_reciprocalJet (n : ℕ) : Continuous (reciprocalJet n) := by
  have hc : Continuous (reciprocalJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_classReciprocal_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn (fun a => reciprocalDeriv (classFun a))
      (reciprocalDeriv (classFun g)) (𝓝 g) halfPlane :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_halfPlane h
      (Eventually.of_forall differentiableOn_classReciprocal) n)

lemma continuous_reciprocalJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × halfPlane => iteratedDeriv n (reciprocalDeriv (classFun p.1)) p.2) :=
  continuous_eval.comp ((continuous_reciprocalJet n).prodMap continuous_id)

lemma classReciprocal_at_I (g : DiskClass) : reciprocalDeriv (classFun g) Complex.I = 1 := by
  rw [reciprocalDeriv,(classFun_schlicht g).2.2,inv_one]

lemma hasDerivAt_integral_compact.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F F' : ℝ → X → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ x ∈ U, Continuous (F x))
    (hc : ContinuousOn (fun p : ℝ × X => F' p.1 p.2) (U ×ˢ univ))
    (hd : ∀ x ∈ U, ∀ a, HasDerivAt (fun t => F t a) (F' x a) x)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' x a ∂μ) x := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr2 : 0 < r/2 := half_pos hr
  have hsub' : Metric.closedBall x (r/2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  have hk : IsCompact (Metric.closedBall x (r/2) ×ˢ (univ : Set X)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn (hc.mono (Set.prod_mono hsub' Subset.rfl))
  have hc0 : Continuous (F' x) := by
    have hs : Continuous (fun a : X => (x,a)) := continuous_const.prodMk continuous_id
    exact continuousOn_univ.mp
      (hc.comp hs.continuousOn (fun a _ => ⟨hx,mem_univ a⟩))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball x (r/2)) (bound := fun _ : X => C) (Metric.ball_mem_nhds _ hr2)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hF y hy).aestronglyMeasurable
  · exact (hF x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hc0.aestronglyMeasurable
  · exact Eventually.of_forall (fun a y hy => hC (y,a) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le,mem_univ a⟩)
  · exact integrable_const C
  · exact Eventually.of_forall (fun a y hy => hd y (hsub' (Metric.ball_subset_closedBall hy)) a)

lemma complex_line_deriv {Q : ℂ → ℂ} {z d v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => Q (z+(s : ℂ)*v)) (d*v) t := by
  have hv : HasDerivAt (fun s : ℝ => z+(s : ℂ)*v) v t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt.mul_const v).const_add z :
      HasDerivAt (fun s : ℝ => z+Complex.ofRealCLM s*v) (Complex.ofRealCLM 1*v) t)
  convert HasDerivAt.comp (𝕜 := ℝ) t hQ hv using 1
  rfl

def normFirst (q d v : ℂ) : ℝ := 2*inner ℝ q (d*v)

def normSecond (q d e v : ℂ) : ℝ :=
  2*(inner ℝ (d*v) (d*v)+inner ℝ q ((e*v)*v))

lemma norm_line_hasDerivAt {Q : ℂ → ℂ} {z d v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => ‖Q (z+(s : ℂ)*v)‖^2)
      (normFirst (Q (z+(t : ℂ)*v)) d v) t :=
  (complex_line_deriv hQ).norm_sq

lemma norm_first_hasDerivAt {Q D : ℂ → ℂ} {z d e v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v))
    (hD : HasDerivAt D e (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => normFirst (Q (z+(s : ℂ)*v)) (D (z+(s : ℂ)*v)) v)
      (2*(inner ℝ (d*v) (D (z+(t : ℂ)*v)*v)+inner ℝ (Q (z+(t : ℂ)*v)) ((e*v)*v))) t := by
  simpa only [normFirst, add_comm] using ((complex_line_deriv hQ).inner ℝ ((complex_line_deriv hD).mul_const v)).const_mul 2

lemma norm_first_one (d : ℂ) : normFirst 1 d 1 = 2*d.re := by
  simp [normFirst,Complex.inner]

lemma norm_first_I (d : ℂ) : normFirst 1 d Complex.I = -2*d.im := by
  simp [normFirst,Complex.inner]

lemma norm_second_laplacian (q d e : ℂ) :
    normSecond q d e 1+normSecond q d e Complex.I = 4*‖d‖^2 := by
  simp only [normSecond,mul_one]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul,Complex.norm_I,mul_one]
  have he : (e*Complex.I)*Complex.I = -e := by rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
  rw [he,inner_neg_right]
  ring

lemma continuous_normFirst : Continuous (fun p : ℂ × ℂ × ℂ => normFirst p.1 p.2.1 p.2.2) := by
  unfold normFirst
  fun_prop

lemma continuous_normSecond : Continuous (fun p : ℂ × ℂ × ℂ × ℂ => normSecond p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold normSecond
  fun_prop

def complexLine (v : ℂ) (t : ℝ) : ℂ := Complex.I+(t : ℂ)*v

def lineDomain (v : ℂ) : Set ℝ := {t | 0 < 1+t*v.im}

lemma isOpen_lineDomain (v : ℂ) : IsOpen (lineDomain v) :=
  isOpen_lt continuous_const (by fun_prop)

lemma complexLine_im (v : ℂ) (t : ℝ) : (complexLine v t).im = 1+t*v.im := by
  simp [complexLine,Complex.mul_im]

lemma complexLine_mem {v : ℂ} {t : ℝ} (ht : t ∈ lineDomain v) :
    0 < (complexLine v t).im := (complexLine_im v t).symm ▸ ht

@[simp] lemma complexLine_zero (v : ℂ) : complexLine v 0 = Complex.I := by simp [complexLine]
lemma zero_mem_lineDomain (v : ℂ) : (0 : ℝ) ∈ lineDomain v := by simp [lineDomain]

lemma continuousOn_complexLine.{u_1} {X : Type u_1} [TopologicalSpace X] (G : X → ℂ → ℂ)
    (hG : Continuous (fun p : X × {z : ℂ | 0 < z.im} => G p.1 p.2)) (v : ℂ) :
    ContinuousOn (fun p : ℝ × X => G p.2 (complexLine v p.1)) (lineDomain v ×ˢ univ) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let H : (lineDomain v ×ˢ (univ : Set X)) → X × {z : ℂ | 0 < z.im} :=
    fun p => (p.val.2,⟨complexLine v p.val.1,complexLine_mem p.2.1⟩)
  have hH : Continuous H := by
    apply Continuous.prodMk
    · exact continuous_snd.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_const.add (((Complex.continuous_ofReal.comp continuous_fst).comp continuous_subtype_val).mul continuous_const)
  exact hG.comp hH

lemma continuous_prod_section.{u_1} {X : Type u_1} [TopologicalSpace X]
    {U : Set ℝ} {G : ℝ × X → ℝ} (hG : ContinuousOn G (U ×ˢ univ)) {t : ℝ} (ht : t ∈ U) :
    Continuous (fun a => G (t,a)) :=
  continuousOn_univ.mp (hG.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht,mem_univ _⟩))

lemma continuousOn_normFirst_line.{u_1} {X : Type u_1} [TopologicalSpace X]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2)) (v : ℂ) :
    ContinuousOn (fun p : ℝ × X => normFirst (Q p.2 (complexLine v p.1)) (D p.2 (complexLine v p.1)) v) (lineDomain v ×ˢ univ) := by
  unfold normFirst
  exact continuousOn_const.mul ((continuousOn_complexLine Q hQc v).inner ((continuousOn_complexLine D hDc v).mul continuousOn_const))

lemma integral_norm_line_derivative.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    HasDerivAt (fun s => ∫ a, ‖Q a (complexLine v s)‖^2 ∂μ)
      (∫ a, normFirst (Q a (complexLine v t)) (D a (complexLine v t)) v ∂μ) t := by
  refine hasDerivAt_integral_compact μ
    (fun s a => ‖Q a (complexLine v s)‖^2)
    (fun s a => normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v)
    (isOpen_lineDomain v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section ((continuousOn_complexLine Q hQc v).norm.pow 2) hs
  · exact continuousOn_normFirst_line Q D hQc hDc v
  · intro s hs a
    exact norm_line_hasDerivAt (hD a _ (complexLine_mem hs))

lemma integral_normFirst_line_derivative.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    HasDerivAt (fun s => ∫ a, normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v ∂μ)
      (∫ a, normSecond (Q a (complexLine v t)) (D a (complexLine v t)) (E a (complexLine v t)) v ∂μ) t := by
  refine hasDerivAt_integral_compact μ
    (fun s a => normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v)
    (fun s a => normSecond (Q a (complexLine v s)) (D a (complexLine v s)) (E a (complexLine v s)) v)
    (isOpen_lineDomain v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section (continuousOn_normFirst_line Q D hQc hDc v) hs
  · have hcQ := continuousOn_complexLine Q hQc v
    have hcD := continuousOn_complexLine D hDc v
    have hcE := continuousOn_complexLine E hEc v
    unfold normSecond
    exact continuousOn_const.mul (((hcD.mul continuousOn_const).inner (hcD.mul continuousOn_const)).add
      (hcQ.inner ((hcE.mul continuousOn_const).mul continuousOn_const)))
  · intro s hs a
    exact norm_first_hasDerivAt (hD a _ (complexLine_mem hs)) (hE a _ (complexLine_mem hs))

lemma normFirst_expected.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    (∫ a, normFirst (Q a (complexLine v t)) (D a (complexLine v t)) v ∂μ) =
      v.im*(-β)*(1+t*v.im)^(-β-1) := by
  have hdR := (((hasDerivAt_id t).mul_const v.im).const_add 1).rpow_const
    (p := -β) (Or.inl (ne_of_gt ht))
  simp only [one_mul,id_eq] at hdR
  apply (integral_norm_line_derivative μ Q D hQc hDc hD v ht).unique
  apply hdR.congr_of_eventuallyEq
  filter_upwards [(isOpen_lineDomain v).mem_nhds ht] with s hs
  exact (hmean (complexLine v s) (complexLine_mem hs)).trans
    (congrArg (fun x : ℝ => x^(-β)) (complexLine_im v s))

lemma compact_holomorphic_line_moments.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v : ℂ) :
    (∫ a, normFirst (Q a Complex.I) (D a Complex.I) v ∂μ) = -β*v.im ∧
    (∫ a, normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) v ∂μ) =
      β*(β+1)*v.im^2 := by
  have hm' {t : ℝ} (ht : t ∈ lineDomain v) := normFirst_expected μ Q D hQc hDc hD β hmean v ht
  constructor
  · simpa only [complexLine_zero,zero_mul,add_zero,Real.one_rpow,mul_one,mul_comm,mul_zero] using hm' (zero_mem_lineDomain v)
  · have hdR := (((((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add 1).rpow_const
        (p := -β-1) (Or.inl (by norm_num))).const_mul (v.im*(-β)))
    have he : (∫ a, normSecond (Q a (complexLine v 0)) (D a (complexLine v 0)) (E a (complexLine v 0)) v ∂μ) =
        v.im*(-β)*(1*v.im*(-β-1)*(1+0*v.im)^((-β-1)-1)) := by
      apply (integral_normFirst_line_derivative μ Q D E hQc hDc hEc hD hE v (zero_mem_lineDomain v)).unique
      apply hdR.congr_of_eventuallyEq
      filter_upwards [(isOpen_lineDomain v).mem_nhds (zero_mem_lineDomain v)] with s hs
      exact hm' hs
    simp only [complexLine_zero,one_mul,zero_mul,add_zero,Real.one_rpow,mul_one] at he
    exact he.trans (by ring)

lemma compact_holomorphic_moments.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (hQ1 : ∀ a, Q a Complex.I = 1)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β)) :
    (∫ a, (Complex.I*D a Complex.I).re ∂μ) = -β/2 ∧
    (∫ a, (Complex.I*D a Complex.I).im ∂μ) = 0 ∧
    (∫ a, ‖Complex.I*D a Complex.I‖^2 ∂μ) = β*(β+1)/4 := by
  obtain ⟨hx,hxx⟩ := compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean 1
  obtain ⟨hy,hyy⟩ := compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean Complex.I
  have hx' := hx
  have hy' := hy
  simp_rw [hQ1,norm_first_one] at hx'
  simp_rw [hQ1,norm_first_I] at hy'
  rw [integral_const_mul] at hx' hy'
  simp only [Complex.one_im,Complex.I_im,mul_zero,mul_one] at hx' hy' hxx hyy
  have hDc0 : Continuous (fun a => D a Complex.I) :=
    hDc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hQc0 : Continuous (fun a => Q a Complex.I) :=
    hQc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hEc0 : Continuous (fun a => E a Complex.I) :=
    hEc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hi (v : ℂ) : Integrable (fun a => normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) v) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_normSecond.comp (hQc0.prodMk (hDc0.prodMk (hEc0.prodMk continuous_const)))
  have hsum : 4*(∫ a, ‖D a Complex.I‖^2 ∂μ) = β*(β+1) := by
    rw [← integral_const_mul]
    calc
      _ = ∫ a, normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) 1+
          normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) Complex.I ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun a => (norm_second_laplacian _ _ _).symm)
      _ = _ := by rw [integral_add (hi 1) (hi Complex.I),hxx,hyy]; norm_num
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_sub,zero_add,Complex.norm_mul,Complex.norm_I]
  rw [integral_neg]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma class_logarithmicJet_I (g : DiskClass) :
    logarithmicJet (classFun g) Complex.I = Complex.I*deriv (reciprocalDeriv (classFun g)) Complex.I := by
  simp only [logarithmicJet,Complex.I_im,Complex.ofReal_one,mul_one,classReciprocal_at_I,div_one]

lemma continuous_root_logarithmicJet : Continuous (fun g : DiskClass => logarithmicJet (classFun g) Complex.I) := by
  simp_rw [class_logarithmicJet_I]
  have hc : Continuous (fun p : DiskClass × halfPlane => deriv (reciprocalDeriv (classFun p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_reciprocalJet_eval 1
  exact (hc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp [halfPlane]⟩ : halfPlane))))).const_mul _

lemma root_logarithmicJet_bounded : ∃ C : ℝ, ∀ g : DiskClass, ‖logarithmicJet (classFun g) Complex.I‖ ≤ C := by
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn continuous_root_logarithmicJet.continuousOn
  exact ⟨C,fun g => hC g (mem_univ g)⟩

lemma weighted_law_moments (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-β)*(∫ g, f g ∂(P : Measure DiskClass))) :
    (∫ g, (logarithmicJet (classFun g) Complex.I).re ∂(P : Measure DiskClass)) = -β/2 ∧
    (∫ g, (logarithmicJet (classFun g) Complex.I).im ∂(P : Measure DiskClass)) = 0 ∧
    (∫ g, ‖logarithmicJet (classFun g) Complex.I‖^2 ∂(P : Measure DiskClass)) = β*(β+1)/4 := by
  have hcD : Continuous (fun p : DiskClass × halfPlane => deriv (reciprocalDeriv (classFun p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_reciprocalJet_eval 1
  have hcE : Continuous (fun p : DiskClass × halfPlane => deriv (deriv (reciprocalDeriv (classFun p.1))) p.2) := by
    simpa only [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using continuous_reciprocalJet_eval 2
  have hm (z : ℂ) (hz : 0 < z.im) :
      (∫ g, ‖reciprocalDeriv (classFun g) z‖^2 ∂(P : Measure DiskClass)) = z.im^(-β) := by
    simpa only [classWeight,ContinuousMap.one_apply,mul_one,integral_const,ProbabilityMeasure.coeFn_univ,
      probReal_univ,smul_eq_mul,one_mul] using hP ⟨z,hz⟩ 1
  have hE (g : DiskClass) (z : ℂ) (hz : 0 < z.im) :
      HasDerivAt (deriv (reciprocalDeriv (classFun g)))
        (deriv (deriv (reciprocalDeriv (classFun g))) z) z :=
    ((differentiableOn_classReciprocal g).analyticOnNhd isOpen_halfPlane z hz).deriv.differentiableAt.hasDerivAt
  simp_rw [class_logarithmicJet_I]
  exact compact_holomorphic_moments (P : Measure DiskClass)
    (fun g => reciprocalDeriv (classFun g)) (fun g => deriv (reciprocalDeriv (classFun g)))
    (fun g => deriv (deriv (reciprocalDeriv (classFun g))))
    continuous_classReciprocal_eval hcD hcE
    (fun g z hz => hasDerivAt_reciprocalDeriv (classFun_schlicht g).1 hz)
    hE classReciprocal_at_I β hm

lemma jacobian_expectation_nonpos (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : HasWeightedLaw P β) (hβ : 1 < β) :
    (∫ g, normalizedJacobian (classFun g) ((β+3)/4) Complex.I ∂(P : Measure DiskClass)) ≤ 0 := by
  have hk : 0 < (β+3)/4 := by linarith
  have hg : ∀ᵐ g ∂(P : Measure DiskClass), ∀ᵐ ξ : ℂ, GoodPair (classFun g) ((β+3)/4) ξ := by
    filter_upwards [weightedInverseArea_ae_finite P β hP] with g hg
    apply class_ae_goodPairs g hβ
    have he : weightedInverseArea β g = (∫⁻ z in outsideCore,
        ENNReal.ofReal (z.im^(β+1)*‖classFun g z‖⁻¹^4)) := by
      simp only [weightedInverseArea,inverseDensity]
      apply setLIntegral_congr_fun measurableSet_outsideCore
      intro z hz
      dsimp only
      rw [planeClassValue_eq g hz.1,ENNReal.ofReal_mul (Real.rpow_nonneg hz.1.le _)]
    exact he ▸ hg
  have hi := jacobian_positive_le_negative P β hP hk (by ring) hg
  have hc : Continuous (fun g : DiskClass => normalizedJacobian (classFun g) ((β+3)/4) Complex.I) :=
    (continuous_class_normalizedJacobian _).comp
      (continuous_id.prodMk (continuous_const (y := halfOne)))
  have hInt := hc.integrable_of_hasCompactSupport (μ := (P : Measure DiskClass)) (HasCompactSupport.of_compactSpace _)
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  have ht := ENNReal.toReal_mono (rootJac_integral_lt_top P ((β+3)/4) (-1)).ne hi
  simpa only [rootJac,one_mul,neg_one_mul,sub_nonpos] using ht

lemma jacobian_expectation_value (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-β)*(∫ g, f g ∂(P : Measure DiskClass)))
    {k : ℝ} (hk : k ≠ 0) :
    k^2 * (∫ g, normalizedJacobian (classFun g) k Complex.I ∂(P : Measure DiskClass)) =
      k*(k-1) - (2*k-1)*β/2 + β*(β+1)/4 := by
  obtain ⟨hr,-,hs⟩ := weighted_law_moments P β hP
  have hiR : Integrable (fun g : DiskClass => (2*k-1)*(logarithmicJet (classFun g) Complex.I).re) (P : Measure DiskClass) :=
    (continuous_const.mul (Complex.continuous_re.comp continuous_root_logarithmicJet)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (fun g : DiskClass => ‖logarithmicJet (classFun g) Complex.I‖^2) (P : Measure DiskClass) :=
    (continuous_root_logarithmicJet.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul]
  calc
    _ = ∫ g, k*(k-1)+(2*k-1)*(logarithmicJet (classFun g) Complex.I).re+
        ‖logarithmicJet (classFun g) Complex.I‖^2 ∂(P : Measure DiskClass) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun g => normalizedJacobian_formula (classFun_schlicht g).1 (by simp [halfPlane]) k hk)
    _ = _ := by
      have h1 := integral_add ((integrable_const (k*(k-1))).add hiR) hiS
      have h2 := integral_add (integrable_const (k*(k-1))) hiR
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,hr,hs]
      ring

theorem transferRho_le_two : transferRho ≤ 2 := by
  by_contra! hρ
  obtain ⟨P,hP⟩ := exists_weighted_continuous_law hρ
  have hPb : HasWeightedLaw P transferBeta := by
    intro z f hf
    exact weighted_lintegral_of_continuous (P : Measure DiskClass) (weightAt z)
      (fun g => (classWeight_pos g z).le) (actionAt z) ((z.val.im)^(-transferBeta))
      (Real.rpow_nonneg z.2.le _) (hP z) f hf
  have hβ := transferBeta_gt_one hρ
  have hn := jacobian_expectation_nonpos P transferBeta hPb hβ
  have hv := jacobian_expectation_value P transferBeta hP (k := (transferBeta+3)/4) (by linarith)
  have hp : 0 < ((transferBeta+3)/4)*((transferBeta+3)/4-1) := mul_pos (by linarith) (by linarith)
  have he : ((transferBeta+3)/4)*((transferBeta+3)/4-1) -
      (2*((transferBeta+3)/4)-1)*transferBeta/2 + transferBeta*(transferBeta+1)/4 =
      ((transferBeta+3)/4)*((transferBeta+3)/4-1) := by ring
  rw [he] at hv
  have hnon := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((transferBeta+3)/4)) hn
  linarith

end Brennan

end

end OAI
