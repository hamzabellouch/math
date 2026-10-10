import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch
import OAI.Analysis.Conductivity.Fourier.AnalyticNullEuclidean
import OAI.Analysis.Conductivity.Fourier.TorusPoissonContinuous
import OAI.Analysis.Conductivity.Fourier.AnalyticDerivativeBounds

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory UnitAddTorus

lemma flatFourier_factorial_bound {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B δ : ℝ} (ha : ∀ h,|a h|≤B) (hδ : 0<δ)
    (n : ℕ) {x : Coord3} (hx : δ≤x 0) :
    ‖iteratedFDeriv ℝ n (flatFourier s a phase) x‖≤
      (B*(∑' h : Fin 2 → ℤ,exp (-(δ/2)*torusRate s h)))*
        (3/(δ/2))^n*(n.factorial : ℝ) := by
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  have he := torusRate_exp_summable hs (by positivity : 0<δ/2)
  have hmode := (flatMode_derivative_summable hs n hδ).mul_left B
  have hb (h : Fin 2 → ℤ) :
      B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h))≤
        (B*((3:ℝ)^n*((n.factorial : ℝ)/(δ/2)^n)))*exp (-(δ/2)*torusRate s h) := by
    have hl := torusRate_lower hs h
    have hlam : 0≤torusRate s h := sqrt_nonneg _
    calc
      _ ≤ B * ((3:ℝ)^n*(((n.factorial : ℝ)/(δ/2)^n)*exp (-(δ/2)*torusRate s h))) := by
        apply mul_le_mul_of_nonneg_left _ hB
        calc
          _≤(3*torusRate s h)^n*exp (-δ*torusRate s h) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (add_nonneg hlam (torusSize_nonneg h)) (by linarith) _) (exp_nonneg _)
          _=3^n*((torusRate s h)^n*exp (-δ*torusRate s h)) := by rw [mul_pow]; ring
          _≤3^n*(((n.factorial : ℝ)/(δ/2)^n)*exp (-(δ/2)*torusRate s h)) :=
            mul_le_mul_of_nonneg_left (pow_mul_exp_bound n hδ hlam) (by positivity)
      _ = _ := by ring
  calc
    _≤∑' h,B*((torusRate s h+torusSize h)^n*exp (-δ*torusRate s h)) :=
      flatFourier_iterated_norm hs ha hδ n hx
    _≤∑' h,(B*((3:ℝ)^n*((n.factorial : ℝ)/(δ/2)^n)))*exp (-(δ/2)*torusRate s h) :=
      hmode.tsum_le_tsum hb (he.mul_left _)
    _=_ := by
      rw [tsum_mul_left]
      generalize δ/2 = θ
      rw [div_pow]
      ring

lemma flatFourier_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2 → ℤ) → ℝ} {B : ℝ} (ha : ∀ h,|a h|≤B) :
    AnalyticOnNhd ℝ (flatFourier s a phase) {x | 0<x 0} := by
  intro x hx
  change 0<x 0 at hx
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp
    ((axial_halfspace_open (x 0/2)).mem_nhds (by change x 0/2<x 0; linarith))
  have hB : 0≤B := (abs_nonneg (a 0)).trans (ha 0)
  apply analyticAt_of_factorial_bound hR
    (M:=B*(∑' h : Fin 2 → ℤ,exp (-(x 0/2/2)*torusRate s h)))
    (C:=3/(x 0/2/2)) (mul_nonneg hB (tsum_nonneg (fun _ => exp_nonneg _))) (by positivity)
  · exact (flatFourier_smooth hs ha).mono (fun y hy => by
      have h := hball hy
      change x 0/2<y 0 at h
      change 0<y 0
      linarith)
  · intro n y hy
    exact flatFourier_factorial_bound hs ha (by linarith : 0<x 0/2) n (hball hy).le

lemma torusRealContinuation_analytic {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : TorusL2) : AnalyticOnNhd ℝ (torusRealContinuation s f) {x | 0<x 0} := by
  have hre (h) : |(mFourierCoeff f h).re|≤‖f‖ :=
    (Complex.abs_re_le_norm _).trans (torusFourierCoeff_bound f h)
  have him (h) : |(mFourierCoeff f h).im|≤‖f‖ :=
    (Complex.abs_im_le_norm _).trans (torusFourierCoeff_bound f h)
  intro x hx
  apply ((flatFourier_analytic hs hre x hx).add (flatFourier_analytic hs him x hx)).congr
  filter_upwards [(axial_halfspace_open 0).mem_nhds hx] with y hy
  exact (torusRealContinuation_eq hs f hy).symm

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma pairCLM_surjective_of_minor (D : Coord3 →L[ℝ] (Fin 2 → ℝ)) (p q : Coord3)
    (hn : D p 0*D q 1-D p 1*D q 0≠0) : Function.Surjective D := by
  intro y
  refine ⟨((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0)) • p+
    ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0)) • q,?_⟩
  ext j
  fin_cases j <;> simp only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 0+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 0=y 0
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring
  · change ((y 0*D q 1-y 1*D q 0)/(D p 0*D q 1-D p 1*D q 0))*D p 1+
      ((D p 0*y 1-D p 1*y 0)/(D p 0*D q 1-D p 1*D q 0))*D q 1=y 1
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,←add_div,div_eq_iff hn]
    ring

lemma potential_component_fderivAt {u : Coord3 → Fin 2 → ℝ} {x : Coord3}
    (hu : DifferentiableAt ℝ u x) (j : Fin 2) (v : Coord3) :
    fderiv ℝ (fun y => u y j) x v=fderiv ℝ u x v j := by
  rw [(hasFDerivAt_pi'.mp hu.hasFDerivAt j).fderiv]
  rfl

theorem analyticPair_regular_of_patch {u : Coord3 → Fin 2 → ℝ}
    {A : Coord3 → Symmetric3} {U O : Set Coord3}
    (hU : IsOpen U) (hc : IsPreconnected U)
    (hu : ∀ j,AnalyticOnNhd ℝ (fun x => u x j) U)
    (hA : ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => (A x).val) U)
    (hO : IsOpen O) (hOU : O⊆U) (hne : O.Nonempty)
    (hr : TwoFieldRankRegular u O) :
    ∀ᵐ x : Coord3,x∈U → x∈regularRegion u A U := by
  have hus : ContDiffOn ℝ (↑(⊤:ℕ∞)) u U :=
    (AnalyticOnNhd.pi hu).contDiffOn_of_completeSpace
  have hud (x) (hx : x∈U) :=
    (hus.differentiableOn (by simp) x hx).differentiableAt (hU.mem_nhds hx)
  obtain ⟨a,ha⟩ := hne
  rcases hr with hr|hr|⟨κ,hκ⟩
  · have hs := gradientColumns_surjective _ (hr a ha)
    obtain ⟨p,hp⟩ := hs ![1,0]
    obtain ⟨q,hq⟩ := hs ![0,1]
    let M : Coord3 → ℝ := fun x =>
      fderiv ℝ (fun y => u y 0) x p*fderiv ℝ (fun y => u y 1) x q-
      fderiv ℝ (fun y => u y 0) x q*fderiv ℝ (fun y => u y 1) x p
    have hM : AnalyticOnNhd ℝ M U := analytic_gradient_minor (hu 0) (hu 1) p q
    have hMa : M a≠0 := by
      dsimp only [M]
      simp only [potential_component_fderivAt (hud a (hOU ha)),hp,hq]
      norm_num
    have hz := analyticNull_fin 3 U M hU hc hM ⟨a,hOU ha,hMa⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : M x≠0 := by simpa [hxu] using hx
    have hh := Filter.inter_mem (hU.mem_nhds hxu) ((hM x hxu).continuousAt.eventually_ne hn)
    obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hh
    have hVU : V⊆U := fun y hy => (hVsub hy).1
    refine mem_regularRegion_iff.mpr ⟨V,hVU,⟨hV,hus.mono hVU,hA.mono hVU,Or.inl ?_⟩,hxV⟩
    intro y hy
    apply gradientColumns_rank
    apply pairCLM_surjective_of_minor _ p q
    have hn := (hVsub hy).2
    change M y≠0 at hn
    dsimp only [M] at hn
    simpa only [potential_component_fderivAt (hud y (hVU hy)),mul_comm] using hn
  · obtain ⟨v,l,κ,hv,hl,hd,he⟩ := hr
    obtain ⟨j,hj⟩ := hl
    let l' : Fin 2 → ℝ := fun k => l k/l j
    let κ' : Fin 2 → ℝ := fun k => κ k-(l k/l j)*κ j
    have heg (k : Fin 2) : EqOn (fun x => u x k)
        (fun x => l' k*u x j+κ' k) U := by
      apply (hu k).eqOn_of_preconnected_of_eventuallyEq
        ((analyticOnNhd_const.mul (hu j)).add analyticOnNhd_const) hc (hOU ha)
      filter_upwards [hO.mem_nhds ha] with x hx
      change u x k = l' k*u x j+κ' k
      dsimp only [l',κ']
      rw [he x hx k,he x hx j]
      field_simp [hj]
      ring
    have hev : (fun x => u x j)=ᶠ[𝓝 a] (fun x => l j*v x+κ j) :=
      Filter.Eventually.mono (hO.mem_nhds ha) (fun x hx => he x hx j)
    have hvd := (hv.differentiableOn (by simp) a ha).differentiableAt (hO.mem_nhds ha)
    have hf : fderiv ℝ (fun x => u x j) a=l j • fderiv ℝ v a := by
      rw [hev.fderiv_eq,((hvd.hasFDerivAt.const_mul (l j)).add_const (κ j)).fderiv]
    have hfn : fderiv ℝ (fun x => u x j) a≠0 := by
      rw [hf]
      exact smul_ne_zero hj (hd a ha)
    obtain ⟨w,hw⟩ : ∃ w : Coord3,fderiv ℝ (fun x => u x j) a w≠0 := by
      by_contra! h
      exact hfn (ContinuousLinearMap.ext h)
    have hD := analytic_directional_fderiv (hu j) w
    have hz := analyticNull_fin 3 U (fun x => fderiv ℝ (fun y => u y j) x w)
      hU hc hD ⟨a,hOU ha,hw⟩
    filter_upwards [compl_mem_ae_iff.mpr hz] with x hx hxu
    have hn : fderiv ℝ (fun y => u y j) x w≠0 := by simpa [hxu] using hx
    have hh := Filter.inter_mem (hU.mem_nhds hxu) ((hD x hxu).continuousAt.eventually_ne hn)
    obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hh
    have hVU : V⊆U := fun y hy => (hVsub hy).1
    refine mem_regularRegion_iff.mpr ⟨V,hVU,⟨hV,hus.mono hVU,hA.mono hVU,
      Or.inr (Or.inl ⟨fun y => u y j,l',κ',(hu j).contDiffOn_of_completeSpace.mono hVU,
        ⟨j,?_⟩,?_,fun y hy k => heg k (hVU hy)⟩)⟩,hxV⟩
    · simp [l',hj]
    · intro y hy hyz
      exact (hVsub hy).2 (by rw [hyz]; rfl)
  · have heg (k : Fin 2) : EqOn (fun x => u x k) (fun _ => κ k) U := by
      apply (hu k).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hc (hOU ha)
      filter_upwards [hO.mem_nhds ha] with x hx
      exact congrFun (hκ x hx) k
    exact ae_of_all _ (fun x hx => mem_regularRegion_iff.mpr
      ⟨U,Subset.rfl,⟨hU,hus,hA,Or.inr (Or.inr ⟨κ,fun y hy => funext (fun k => heg k hy)⟩)⟩,hx⟩)

end ScalarConductivity

end
end

end OAI
