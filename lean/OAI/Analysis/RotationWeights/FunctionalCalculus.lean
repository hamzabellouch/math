import OAI.Analysis.RotationWeights.FiberActions

namespace OAI

noncomputable section

namespace ContinuousCircleWeight

universe uX uι uE uA

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace

section
open Set Filter
open scoped Topology

lemma lp_diagonal_stronglyMeasurable {X : Type uX} [MeasurableSpace X]
    (d : X → ℤ → ℂ) (C : ℝ≥0) (hd : ∀ x k, ‖d x k‖≤C)
    (hm : ∀ k, Measurable (fun x => d x k)) (u : FiberHilbert) :
    StronglyMeasurable (fun x => lpDiagonal (d x) C (hd x) u) := by
  let v : Finset ℤ → FiberHilbert := fun s => ∑ k∈s,lp.single 2 k (u k)
  have hv : Tendsto v atTop (𝓝 u) := lp.hasSum_single (by norm_num) u
  apply stronglyMeasurable_of_tendsto atTop (f:=fun s x => lpDiagonal (d x) C (hd x) (v s))
  · intro s
    have he : (fun x => lpDiagonal (d x) C (hd x) (v s)) =
        (fun x => ∑ k∈s,(d x k*u k) • lp.single 2 k 1) := by
      funext x
      simp only [v,map_sum]
      apply Finset.sum_congr rfl
      intro k _
      ext j
      by_cases hj : j=k
      · subst j; simp [lpDiagonal,lp.single_apply]
      · simp [lpDiagonal,lp.single_apply,hj]
    rw [he]
    convert Finset.stronglyMeasurable_sum s (fun k _ => ((hm k).mul_const (u k)).stronglyMeasurable.smul_const (lp.single 2 k 1 : FiberHilbert)) using 1
    ext x; simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact ((lpDiagonal (d x) C (hd x)).continuous.tendsto u).comp hv

def boundedPiField (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C)
    (x : CircleX) : FiberOperator := lpDiagonal (fun k => g (x+k•θ)) C (fun _k => hg _)
@[simp] lemma boundedPiField_apply (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C)
    (x : CircleX) (u : FiberHilbert) (k : ℤ) : boundedPiField θ g C hg x u k=g (x+k•θ)*u k := rfl
lemma boundedPiField_bound (θ : CircleX) (g : CircleX → ℂ) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (x : CircleX) :
    ‖boundedPiField θ g C hg x‖ ≤ C := lpDiagonal_norm_le _ _
lemma boundedPiField_measurable (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (u : FiberHilbert) :
    StronglyMeasurable (fun x => boundedPiField θ g C hg x u) :=
  lp_diagonal_stronglyMeasurable _ C (fun _x _k => hg _) (fun _k => hm.comp (measurable_id.add_const _)) u

def boundedPi (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) : CircleFiberOperator :=
  fieldMulL2 AddCircle.haarAddCircle (boundedPiField θ g C hg)
    (fun u => (boundedPiField_measurable θ g hm C hg u).aestronglyMeasurable)
    C (Eventually.of_forall (boundedPiField_bound θ g C hg))
lemma boundedPi_coe (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (u : CircleFiberL2) :
    boundedPi θ g hm C hg u =ᵐ[AddCircle.haarAddCircle] fun x => boundedPiField θ g C hg x (u x) :=
  fieldMulL2_coe _ _ _ _ _ _
lemma boundedPi_norm_le (θ : CircleX) (g : CircleX → ℂ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) : ‖boundedPi θ g hm C hg‖ ≤ C :=
  fieldMulL2_norm_le _ _ _ _ _ C.property

lemma norm_tendsto_zero_of_sq {ι : Type uι} {E : Type uE} [NormedAddCommGroup E] {l : Filter ι}
    (u : ι → E) (h : Tendsto (fun i => ‖u i‖^2) l (𝓝 0)) : Tendsto (fun i => ‖u i‖) l (𝓝 0) := by
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp h

lemma lpDiagonal_tendsto (d : ℕ → ℤ → ℂ) (e : ℤ → ℂ) (C : ℝ≥0)
    (hd : ∀ n k,‖d n k‖≤C) (he : ∀ k,‖e k‖≤C)
    (hlim : ∀ k,Tendsto (fun n => d n k) atTop (𝓝 (e k))) (u : FiberHilbert) :
    Tendsto (fun n => lpDiagonal (d n) C (hd n) u) atTop (𝓝 (lpDiagonal e C he u)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply norm_tendsto_zero_of_sq
  have hs : Summable (fun k => (2*(C:ℝ))^2*‖u k‖^2) := by
    have := (lp.memℓp u).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using this.mul_left ((2*(C:ℝ))^2)
  have hh := tendsto_tsum_of_dominated_convergence hs (g:=fun _ : ℤ => (0:ℝ))
    (f:=fun n k => ‖(d n k-e k)*u k‖^2) (fun k => by simpa using (((hlim k).sub_const (e k)).mul_const (u k)).norm.pow 2) (Eventually.of_forall (fun n k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),norm_mul,mul_pow]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      apply pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (by linarith [hd n k,he k]))))
  simp only [tsum_zero] at hh
  convert hh using 1
  funext n
  have hn := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal)
    (lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u)
  have hn' : ‖lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u‖^2 =
      ∑' k, ‖(lpDiagonal (d n) C (hd n) u-lpDiagonal e C he u) k‖^2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hn
  rw [hn']
  apply tsum_congr
  intro k
  change ‖d n k*u k-e k*u k‖^2=‖(d n k-e k)*u k‖^2
  rw [sub_mul]

lemma L2_tendsto_of_dominated {X : Type uX} {E : Type uE} [MeasurableSpace X] (μ : Measure X)
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ) (b : X → ℝ)
    (hb : Integrable (fun x => b x^2) μ)
    (hu : ∀ n,∀ᵐ x ∂μ,‖u n x-v x‖≤b x)
    (hl : ∀ᵐ x ∂μ,Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto u atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply norm_tendsto_zero_of_sq
  have he (n : ℕ) : ‖u n-v‖^2=∫ x,‖u n x-v x‖^2 ∂μ := by
    rw [←inner_self_eq_norm_sq (𝕜:=ℂ),L2.inner_def,←integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) v] with x hx
    simp only [hx,inner_self_eq_norm_sq,Pi.sub_apply]
  simp_rw [he]
  convert tendsto_integral_of_dominated_convergence (fun x => b x^2)
    (fun n => ((Lp.aestronglyMeasurable (u n)).sub (Lp.aestronglyMeasurable v)).norm.pow 2)
    hb (fun n => (hu n).mono (fun x hx => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2))
    (hl.mono (fun x hx => by simpa using (hx.sub_const (v x)).norm.pow 2)) using 1; simp

lemma boundedPi_tendsto (θ : CircleX) (g : ℕ → CircleX → ℂ) (h : CircleX → ℂ)
    (hm : ∀ n,Measurable (g n)) (hhm : Measurable h) (C : ℝ≥0)
    (hg : ∀ n x,‖g n x‖≤C) (hh : ∀ x,‖h x‖≤C)
    (hl : ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => g n x) atTop (𝓝 (h x)))
    (u : CircleFiberL2) :
    Tendsto (fun n => boundedPi θ (g n) (hm n) C (hg n) u) atTop (𝓝 (boundedPi θ h hhm C hh u)) := by
  have hl' : ∀ᵐ x ∂AddCircle.haarAddCircle,∀ k : ℤ,Tendsto (fun n => g n (x+k•θ)) atTop (𝓝 (h (x+k•θ))) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_add_right AddCircle.haarAddCircle (k•θ)).quasiMeasurePreserving.ae
      (p:=fun x : CircleX => Tendsto (fun n => g n x) atTop (𝓝 (h x))) hl
  apply L2_tendsto_of_dominated (AddCircle.haarAddCircle : Measure CircleX)
    (E:=FiberHilbert) (fun n => boundedPi θ (g n) (hm n) C (hg n) u)
    (boundedPi θ h hhm C hh u) (fun x => 2*(C:ℝ)*‖u x‖)
  · have hi : Integrable (fun x : CircleX => ‖u x‖^2) AddCircle.haarAddCircle :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)
    have hj : Integrable (fun x : CircleX => (2*(C:ℝ))^2*‖u x‖^2) AddCircle.haarAddCircle := hi.const_mul _
    convert hj using 1
    funext x
    exact mul_pow _ _ _
  · intro n
    filter_upwards [boundedPi_coe θ (g n) (hm n) C (hg n) u,boundedPi_coe θ h hhm C hh u] with x h1 h2
    rw [h1,h2]
    apply (norm_sub_le _ _).trans
    have h3 := ((boundedPiField θ (g n) C (hg n) x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (boundedPiField_bound θ (g n) C (hg n) x) (norm_nonneg _))
    have h4 := ((boundedPiField θ h C hh x).le_opNorm (u x)).trans
      (mul_le_mul_of_nonneg_right (boundedPiField_bound θ h C hh x) (norm_nonneg _))
    linarith
  · filter_upwards [ae_all_iff.mpr (fun n => boundedPi_coe θ (g n) (hm n) C (hg n) u),boundedPi_coe θ h hhm C hh u,hl'] with x h1 h2 hx
    simp_rw [h1,h2]
    exact lpDiagonal_tendsto _ _ C (fun n k => hg n _) (fun k => hh _) hx (u x)
end

section
open Set Metric

def complexCircleMap (f : C(CircleX,ℝ)) : C(CircleX,ℂ) :=
  ⟨fun x ↦ (f x : ℂ),Complex.continuous_ofReal.comp f.continuous⟩

lemma circleFunction_circle (f : C(CircleX,ℝ)) (z : Circle) :
    circleFunction f z = (f (circleIdentification.symm z) : ℂ) := by
  simp only [circleFunction,Circle.norm_coe,dite_eq_left]
  congr 2

lemma circleFunction_fourier_one (f : C(CircleX,ℝ)) (x : CircleX) :
    circleFunction f (fourier 1 x) = (f x : ℂ) := by
  rw [fourier_one,circleFunction_circle]
  have he : (AddCircle.toCircle x) = circleIdentification x := by
    exact (AddCircle.homeomorphCircle_apply _ _).symm
  rw [he,Homeomorph.symm_apply_apply]

lemma circleFunction_continuousOn (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (sphere (0:ℂ) 1) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun z : Circle ↦ circleFunction f z)
  simp_rw [circleFunction_circle]
  exact Complex.continuous_ofReal.comp (f.continuous.comp circleIdentification.symm.continuous)

lemma circleFunction_continuousOn_spectrum (f : C(CircleX,ℝ)) :
    ContinuousOn (circleFunction f) (spectrum ℂ (fourier (T := (1:ℝ)) 1)) := by
  apply (circleFunction_continuousOn f).mono
  rw [ContinuousMap.spectrum_eq_range]
  rintro z ⟨x,rfl⟩
  rw [fourier_one]
  exact (AddCircle.toCircle x).property

lemma circle_cfc (f : C(CircleX,ℝ)) :
    cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) = complexCircleMap f := by
  ext x
  have he := (ContinuousMap.evalStarAlgHom ℂ ℂ x).map_cfc (circleFunction f)
    (fourier (T := (1:ℝ)) 1) (circleFunction_continuousOn_spectrum f)
  change cfc (circleFunction f) (fourier (T := (1:ℝ)) 1) x = (f x : ℂ)
  change (cfc (circleFunction f) (fourier (T := (1:ℝ)) 1)) x = cfc (circleFunction f) (fourier 1 x) at he
  rw [he]
  have hz : cfc (circleFunction f) (fourier 1 x) = circleFunction f (fourier 1 x) := by
    simpa only [Algebra.algebraMap_self_apply] using
      (cfc_algebraMap (A := ℂ) (fourier 1 x) (circleFunction f))
  exact hz.trans (circleFunction_fourier_one f x)

variable {A : Type uA} [CStarAlgebra A]
lemma circle_cfc_hom (φ : C(CircleX,ℂ) →⋆ₐ[ℂ] A) (hφ : Continuous φ)
    (f : C(CircleX,ℝ)) :
    φ (complexCircleMap f) = cfc (circleFunction f) (φ (fourier 1)) := by
  have hn : IsStarNormal (φ (fourier 1)) := by
    constructor
    change star (φ _) * φ _ = φ _ * star (φ _)
    rw [← map_star,← map_mul,← map_mul,mul_comm]
  rw [← circle_cfc f]
  exact φ.map_cfc _ _ (circleFunction_continuousOn_spectrum f) hφ
end

open Set Filter
open scoped Topology

lemma bounded_real_continuous_approx (g : CircleX → ℝ) (hm : Measurable g)
    (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    ∃ f : ℕ → C(CircleX,ℝ), (∀ n x,‖f n x‖≤C) ∧
      ∀ᵐ x ∂AddCircle.haarAddCircle,Tendsto (fun n => f n x) atTop (𝓝 (g x)) := by
  let μ : Measure CircleX := AddCircle.haarAddCircle
  have hgLp : MemLp g 2 μ := MemLp.of_bound hm.aestronglyMeasurable C (Eventually.of_forall hg)
  have hd := ContinuousMap.toLp_denseRange ℝ μ ℝ (p:=2) (by norm_num)
  obtain ⟨u,hu,hl⟩ := mem_closure_iff_seq_limit.mp (hd (hgLp.toLp g))
  choose f hf using hu
  have hfl : Tendsto (fun n => ContinuousMap.toLp 2 μ ℝ (f n)) atTop (𝓝 (hgLp.toLp g)) := by
    simpa only [hf] using hl
  obtain ⟨ns,_hns,hns⟩ := (tendstoInMeasure_of_tendsto_Lp hfl).exists_seq_tendsto_ae
  let clip : ℝ → ℝ := fun t => max (-(C:ℝ)) (min (C:ℝ) t)
  have hclip : Continuous clip := continuous_const.max (continuous_const.min continuous_id)
  let F : ℕ → C(CircleX,ℝ) := fun n => ⟨clip ∘ f (ns n),hclip.comp (f (ns n)).continuous⟩
  refine ⟨F,?_,?_⟩
  · intro n x
    rw [Real.norm_eq_abs,abs_le]
    exact ⟨le_max_left _ _,max_le (by linarith [C.property]) (min_le_left _ _)⟩
  · filter_upwards [hns,ae_all_iff.mpr (fun n => ContinuousMap.coeFn_toLp μ (p:=2) (𝕜:=ℝ) (f (ns n))),hgLp.coeFn_toLp] with x hx hf hxg
    have hcg : clip (g x)=g x := by
      have h := abs_le.mp (hg x)
      exact max_eq_right (h.1.trans_eq (min_eq_right h.2).symm) |>.trans (min_eq_right h.2)
    have hh : Tendsto (fun n => f (ns n) x) atTop (𝓝 (g x)) := by
      simpa only [hf,hxg] using hx
    simpa only [F,ContinuousMap.coe_mk,Function.comp_def,hcg] using (hclip.tendsto (g x)).comp hh

lemma boundedPi_eq_continuousPi (θ : CircleX) (g : C(CircleX,ℂ)) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    boundedPi θ g g.continuous.measurable C hg=continuousPi θ g := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedPi_coe θ g g.continuous.measurable C hg u,continuousPi_coe θ g u] with x h1 h2
  rw [h1,h2]
  ext k
  rfl

lemma boundedPi_congr (θ : CircleX) (g h : CircleX → ℂ) (hgm : Measurable g) (hhm : Measurable h)
    (C D : ℝ≥0) (hg : ∀ x,‖g x‖≤C) (hh : ∀ x,‖h x‖≤D)
    (he : g=ᵐ[AddCircle.haarAddCircle] h) : boundedPi θ g hgm C hg=boundedPi θ h hhm D hh := by
  have he' : ∀ᵐ x ∂AddCircle.haarAddCircle,∀ k : ℤ,g (x+k•θ)=h (x+k•θ) := by
    rw [ae_all_iff]
    intro k
    exact (measurePreserving_add_right AddCircle.haarAddCircle (k•θ)).quasiMeasurePreserving.ae
      (p:=fun x : CircleX => g x=h x) he
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [boundedPi_coe θ g hgm C hg u,boundedPi_coe θ h hhm D hh u,he'] with x h1 h2 hx
  rw [h1,h2]
  ext k
  simp only [boundedPiField_apply,hx]

lemma commute_boundedPi_real (θ : CircleX) (B : CircleFiberOperator)
    (hB : ∀ f : C(CircleX,ℝ),Commute (continuousPi θ (complexCircleMap f)) B)
    (g : CircleX → ℝ) (hm : Measurable g) (C : ℝ≥0) (hg : ∀ x,‖g x‖≤C) :
    Commute (boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp hm) C
      (fun x => by simpa using hg x)) B := by
  obtain ⟨f,hf,hl⟩ := bounded_real_continuous_approx g hm C hg
  let F : ℕ → C(CircleX,ℂ) := fun n => complexCircleMap (f n)
  have hF (n : ℕ) (x : CircleX) : ‖F n x‖≤C := by simpa [F,complexCircleMap] using hf n x
  have hgl (x : CircleX) : ‖(g x:ℂ)‖≤C := by simpa using hg x
  have hlim (u : CircleFiberL2) : Tendsto (fun n => continuousPi θ (F n) u) atTop
      (𝓝 (boundedPi θ (fun x => (g x:ℂ)) (Complex.measurable_ofReal.comp hm) C hgl u)) := by
    have h := boundedPi_tendsto θ (fun n x => F n x) (fun x => (g x:ℂ))
      (fun n => (F n).continuous.measurable) (Complex.measurable_ofReal.comp hm) C hF hgl
      (hl.mono (fun x hx => Complex.continuous_ofReal.continuousAt.tendsto.comp hx)) u
    simpa only [boundedPi_eq_continuousPi] using h
  change _ * B = B * _
  apply ContinuousLinearMap.ext
  intro u
  exact tendsto_nhds_unique (hlim (B u))
    (by
      have he : (fun n => continuousPi θ (F n) (B u)) = (fun n => B (continuousPi θ (F n) u)) := by
        funext n
        exact DFunLike.congr_fun (hB (f n)).eq u
      rw [he]
      exact (B.continuous.tendsto _).comp (hlim u))


end ContinuousCircleWeight

end

end OAI
