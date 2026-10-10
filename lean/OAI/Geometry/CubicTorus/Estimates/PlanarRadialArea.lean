import Mathlib
import OAI.Geometry.CubicTorus.Regularity.NormalMeasureCoordinatePermutation

namespace OAI

section

noncomputable section
open Set
namespace CubicTorus

lemma square_below_nonnegative_chord {q c e y : ℝ}
    (hl0 : 0≤q) (hl1 : q≤1) (hc : 0≤c) (he : 0≤e) (hy : 0≤y)
    (hch : y≤(1-q)*c+q*e) : y^2≤(1-q)*c^2+q*e^2 := by
  have hl : 0≤1-q := by linarith
  have hh := (sq_le_sq₀ hy (add_nonneg (mul_nonneg hl hc) (mul_nonneg hl0 he))).mpr hch
  have hv := mul_nonneg (mul_nonneg hl0 hl) (sq_nonneg (c-e))
  nlinarith only [hh,hv]

lemma firstCorner_chord_endpoint_bound {d : ℝ} (hd0 : 0≤d) (hd1 : d≤1) :
    (2/9 : ℝ)*d+(4/81)*(1-d^2)^2+
      ((2/9)*(1-d^2)+d*(1-d^2)/(1+(1-d^2)))^2≤3/10 := by
  let b := 1-d^2
  have hb : 0≤b := by dsimp [b]; nlinarith
  have hden : 0<1+b := by linarith
  have hp := firstCornerPolynomial1_nonneg hd0 hd1
  change 0≤(3/10-(2/9)*d-(4/81)*b^2)*(1+b)^2-b^2*((2/9)*(1+b)+d)^2 at hp
  change (2/9)*d+(4/81)*b^2+((2/9)*b+d*b/(1+b))^2≤3/10
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hden)).mp
  have he : ((2/9)*d+(4/81)*b^2+((2/9)*b+d*b/(1+b))^2)*(1+b)^2=
      ((2/9)*d+(4/81)*b^2)*(1+b)^2+b^2*((2/9)*(1+b)+d)^2 := by
    field_simp
  rw [he]
  nlinarith only [hp]

theorem firstCorner_dimensionless_bound {t d : ℝ} (ht0 : 0≤t) (ht1 : t<1)
    (hd0 : 0≤d) (htd : t+d^2≤1) :
    (2/9 : ℝ)*d+(4/81)*t^2+
      ((2/9)*t+d*(1-t-d^2)/(1-t^2))^2≤3/10 := by
  have hd1 : d≤1 := by nlinarith
  let b := 1-d^2
  have hb : 0≤b := by dsimp [b]; nlinarith
  have htb : t≤b := by dsimp [b]; linarith
  have hb1 : b≤1 := by dsimp [b]; nlinarith [sq_nonneg d]
  have htden : 0<1+t := by linarith
  have hbden : 0<1+b := by linarith
  have htden2 : 0<1-t^2 := by nlinarith
  by_cases hbz : b=0
  · have htz : t=0 := by linarith
    have hdz : d=1 := by dsimp [b] at hbz; nlinarith
    rw [htz,hdz]
    norm_num
  have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hbz)
  let c := d*b
  let e := (2/9 : ℝ)*b+c/(1+b)
  let q := t/b
  let y := (2/9 : ℝ)*t+d*(b-t)/(1-t^2)
  have hc : 0≤c := mul_nonneg hd0 hb
  have he : 0≤e := by dsimp [e]; positivity
  have hy : 0≤y := by dsimp [y]; positivity
  have hl0 : 0≤q := div_nonneg ht0 hb
  have hl1 : q≤1 := (div_le_one hbpos).mpr htb
  have hlt : q*b=t := div_mul_cancel₀ _ hbz
  have hch : y≤(1-q)*c+q*e := by
    have h1 : d*(b-t)/(1-t^2)≤c/(1+t) := by
      dsimp only [c]
      apply (div_le_div_iff₀ htden2 htden).mpr
      have hh := mul_nonneg (mul_nonneg hd0 ht0) (sub_nonneg.mpr hb1)
      have hh' := mul_nonneg hh htden.le
      nlinarith only [hh']
    have h2 : (2/9 : ℝ)*t+c/(1+t)≤(1-q)*c+q*e := by
      have hid : (1-q)*c+q*e-((2/9 : ℝ)*t+c/(1+t))=
          c*t*(b-t)/((1+b)*(1+t)) := by
        dsimp only [q,e]
        field_simp
        ring
      have hh : 0≤c*t*(b-t)/((1+b)*(1+t)) := by positivity
      rw [← hid] at hh
      linarith
    exact le_trans (add_le_add le_rfl h1) h2
  have hysq := square_below_nonnegative_chord hl0 hl1 hc he hy hch
  have htsq : t^2≤q*b^2 := by
    rw [← hlt]
    have hl2 := mul_nonneg hl0 (sub_nonneg.mpr hl1)
    have hh := mul_nonneg hl2 (sq_nonneg b)
    nlinarith only [hh]
  have h0 := firstCornerPolynomial0_nonneg hd0 hd1
  have h1 := firstCorner_chord_endpoint_bound hd0 hd1
  have h0' : (2/9 : ℝ)*d+c^2≤3/10 := by dsimp [c,b]; nlinarith only [h0]
  have h1' : (2/9 : ℝ)*d+(4/81)*b^2+e^2≤3/10 := h1
  have hK0 := mul_le_mul_of_nonneg_left h0' (sub_nonneg.mpr hl1)
  have hK1 := mul_le_mul_of_nonneg_left h1' hl0
  have hydef : ((2/9 : ℝ)*t+d*(1-t-d^2)/(1-t^2))=y := by
    dsimp [y,b]; congr 1; congr 1; ring
  rw [hydef]
  nlinarith only [hysq,htsq,hK0,hK1]

theorem firstCorner_scaled_strict_bound {t d x : ℝ} (ht0 : 0≤t) (ht1 : t<1)
    (hd0 : 0≤d) (htd : t+d^2≤1)
    (hx : x=Real.pi*(1-t-d^2)/(1-t^2)) :
    (2*Real.pi/9)*d+
      ((2*Real.pi/9)^2*t^2+((2*Real.pi/9)*t+x*d)^2)/Real.pi<1 := by
  have hh := firstCorner_dimensionless_bound ht0 ht1 hd0 htd
  have hp := mul_le_mul_of_nonneg_left hh Real.pi_pos.le
  have he : (2*Real.pi/9)*d+
      ((2*Real.pi/9)^2*t^2+((2*Real.pi/9)*t+x*d)^2)/Real.pi=
      Real.pi*((2/9)*d+(4/81)*t^2+((2/9)*t+d*(1-t-d^2)/(1-t^2))^2) := by
    rw [hx]
    field_simp
    ring
  rw [he]
  nlinarith only [hp,Real.pi_lt_d2]

end CubicTorus

end
end

section

noncomputable section
open Set
namespace CubicTorus

theorem firstCorner_endpoint_contradiction {A h b r s : ℝ}
    (hA0 : 0<A) (hA : A≤2*Real.pi/9) (hh : 0≤h)
    (hb0 : 0≤b) (hb1 : b<1) (hr0 : 0≤r) (hr1 : r≤4*Real.pi/81)
    (hs1 : s≤1)
    (htop : Real.sqrt (Real.pi*r)≤A*b-h*(4*Real.pi/81-r))
    (hbottom : Real.sqrt (Real.pi*(1-s))≤A*b+h*(s-4*Real.pi/81))
    (hdrop : s-r≤A*Real.sqrt (1-b)) : False := by
  let a := 2*Real.pi/9
  let x := h*A
  let d := Real.sqrt (1-b)
  let w := Real.sqrt (Real.pi*r)/a
  have ha : 0<a := by dsimp [a]; positivity
  have hp : Real.pi≠0 := Real.pi_pos.ne'
  have hva : 4*Real.pi/81=a^2/Real.pi := by dsimp [a]; field_simp; ring
  have haA : A≤a := hA
  have hx0 : 0≤x := mul_nonneg hh hA0.le
  have hd0 : 0≤d := Real.sqrt_nonneg _
  have hd2 : d^2=1-b := Real.sq_sqrt (by linarith)
  have hw0 : 0≤w := div_nonneg (Real.sqrt_nonneg _) ha.le
  have haw : a*w=Real.sqrt (Real.pi*r) := by dsimp only [w]; field_simp
  have hrw : r=a^2*w^2/Real.pi := by
    have hz := Real.sq_sqrt (mul_nonneg Real.pi_pos.le hr0)
    rw [← haw,mul_pow] at hz
    apply (eq_div_iff hp).mpr
    nlinarith only [hz]
  have hw1 : w≤1 := by
    rw [hva,hrw] at hr1
    have hz := (div_le_div_iff_of_pos_right Real.pi_pos).mp hr1
    have ha2 := sq_pos_of_pos ha
    have hw2' : w^2≤1 := (mul_le_mul_iff_right₀ ha2).mp (by simpa only [mul_one] using hz)
    nlinarith only [hw2',hw0]
  have hw2 : 0≤1-w^2 := by nlinarith
  have hxn : x≤h*a := mul_le_mul_of_nonneg_left haA hh
  have hnorm : w+x/Real.pi*(1-w^2)≤b := by
    have hleft := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hxn Real.pi_pos.le) hw2
    have hleft' := mul_le_mul_of_nonneg_left (add_le_add (le_refl w) hleft) ha.le
    have ht : a*(w+h*a/Real.pi*(1-w^2))≤A*b := by
      have hid : a*(w+h*a/Real.pi*(1-w^2))=a*w+h*(4*Real.pi/81-r) := by
        rw [hva,hrw]
        ring
      rw [hid,haw]
      linarith only [htop]
    have hright := mul_le_mul_of_nonneg_right haA hb0
    exact (mul_le_mul_iff_right₀ ha).mp (hleft'.trans (ht.trans hright))
  let f : ℝ → ℝ := fun t => t+x/Real.pi*(1-t^2)
  have hf : Continuous f := by fun_prop
  have hf1 : f 1=1 := by dsimp [f]; ring
  obtain ⟨t,ht,hft⟩ := intermediate_value_Icc hw1 hf.continuousOn
    (show b∈Icc (f w) (f 1) from ⟨hnorm,by rw [hf1]; exact hb1.le⟩)
  have ht0 : 0≤t := hw0.trans ht.1
  have ht1 : t<1 := by
    by_contra hn
    have he : t=1 := le_antisymm ht.2 (le_of_not_gt hn)
    rw [he,hf1] at hft
    linarith
  have htden : 0<1-t^2 := by nlinarith
  have hroot : t+x/Real.pi*(1-t^2)=b := hft
  have hxterm : 0≤x/Real.pi*(1-t^2) := by positivity
  have htd : t+d^2≤1 := by linarith only [hroot,hxterm,hd2]
  have hxroot : x=Real.pi*(1-t-d^2)/(1-t^2) := by
    apply (eq_div_iff htden.ne').mpr
    have he := congrArg (fun y : ℝ => y*Real.pi) hroot
    field_simp at he
    rw [show 1-t-d^2=b-t by linarith only [hd2]]
    nlinarith only [he]
  have hwtsq : w^2≤t^2 := (sq_le_sq₀ hw0 ht0).mpr ht.1
  have hrbound : r≤a^2*t^2/Real.pi := by
    rw [hrw]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwtsq (sq_nonneg a)) Real.pi_pos.le
  have hEt : A*b-h*(4*Real.pi/81-a^2*t^2/Real.pi)≤a*t := by
    have he : A*b-h*(4*Real.pi/81-a^2*t^2/Real.pi)=
        A*t+(h/Real.pi)*(A^2-a^2)*(1-t^2) := by
      rw [hva,← hroot]
      dsimp only [x]
      ring
    have hA2 : A^2≤a^2 := (sq_le_sq₀ hA0.le ha.le).mpr haA
    have hcorr : (h/Real.pi)*(A^2-a^2)*(1-t^2)≤0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (div_nonneg hh Real.pi_pos.le) (sub_nonpos.mpr hA2)) htden.le
    rw [he]
    have hat := mul_le_mul_of_nonneg_right haA ht0
    linarith only [hcorr,hat]
  have hsb : s≤a^2*t^2/Real.pi+a*d := by
    have hAd := mul_le_mul_of_nonneg_right haA hd0
    linarith only [hdrop,hrbound,hAd]
  have hbottom' : Real.sqrt (Real.pi*(1-s))≤a*t+x*d := by
    have hdiff := mul_le_mul_of_nonneg_left hdrop hh
    have hrr := mul_le_mul_of_nonneg_left hrbound hh
    have hxd : h*(A*d)=x*d := by dsimp [x]; ring
    rw [hxd] at hdiff
    linarith only [hbottom,hdiff,hrr,hEt]
  have hbsq : Real.pi*(1-s)≤(a*t+x*d)^2 := by
    have hy : 0≤a*t+x*d := by positivity
    have hh' := (sq_le_sq₀ (Real.sqrt_nonneg (Real.pi*(1-s))) hy).mpr hbottom'
    rwa [Real.sq_sqrt (mul_nonneg Real.pi_pos.le (by linarith : 0≤1-s))] at hh'
  have hnec : 1≤a*d+(a^2*t^2+(a*t+x*d)^2)/Real.pi := by
    have hh' := mul_le_mul_of_nonneg_left hsb Real.pi_pos.le
    have hcancel : Real.pi*(a^2*t^2/Real.pi+a*d)=a^2*t^2+Real.pi*a*d := by field_simp
    rw [hcancel] at hh'
    have hh2 : 1≤((a*d)*Real.pi+(a^2*t^2+(a*t+x*d)^2))/Real.pi :=
      (le_div_iff₀ Real.pi_pos).mpr (by nlinarith only [hh',hbsq])
    simpa only [add_div,mul_div_cancel_right₀ _ hp] using hh2
  exact (not_lt_of_ge hnec) (firstCorner_scaled_strict_bound ht0 ht1 hd0 htd hxroot)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_boundary_curve_tangent {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {γ : ℝ → Cover} {v : Cover} {a : ℝ} (hd : HasDerivAt γ v a)
    (hb : ∀ᶠ b in 𝓝 a,quotientMap (γ b)∈frontier (openRepresentative E)) :
    ⟪N (γ a),v⟫=0 := by
  let x := γ a
  have hx : quotientMap x∈frontier (openRepresentative E) := hb.self_of_nhds
  obtain ⟨n,g,σ,hn,hg,hg0,hσ,hmatch,hcover⟩ :=
    isMinimizerAt_normal_graph_chart hV hE hm hμ hN hp ha x hx
  have hc : N x=σ • graphSlopeNormal n (gradient g 0) := by
    simpa only [normalGraph_zero hg0,add_zero] using hmatch.self_of_nhds.1
  let δ : ℝ → Cover := fun b => γ b-x
  let F : ℝ → ℝ := fun b => g (normalPlaneCoordinates n (δ b))-⟪n,δ b⟫
  have hδ0 : δ a=0 := sub_self _
  have hδd : HasDerivAt δ v a := by simpa only [sub_zero] using hd.sub_const x
  have ht : Tendsto δ (𝓝 a) (𝓝 (0 : Cover)) := by
    have ht := hδd.continuousAt.tendsto
    rwa [hδ0] at ht
  have hz : F =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [hb,ht.eventually hcover] with b hb' hcov
    have he : x+δ b=γ b := by dsimp [δ]; abel
    rw [he] at hcov
    have hgph := (normalGraph_coordinates_eq_iff hn _ _).mp (hcov.mp hb')
    change g (normalPlaneCoordinates n (δ b))-⟪n,δ b⟫=0
    exact sub_eq_zero.mpr hgph
  have hcd := (normalPlaneCoordinates n).hasFDerivAt.comp_hasDerivAt a hδd
  have hgd := (hg.differentiable (by simp) (0 : Plane)).hasFDerivAt.comp_hasDerivAt_of_eq
    a hcd (by simp [hδ0])
  have hnd := (innerSL ℝ n).hasFDerivAt.comp_hasDerivAt a hδd
  have hFd : HasDerivAt F (⟪gradient g 0,normalPlaneCoordinates n v⟫-⟪n,v⟫) a := by
    rw [inner_gradient_left]
    exact hgd.sub hnd
  have he : ⟪gradient g 0,normalPlaneCoordinates n v⟫-⟪n,v⟫=0 :=
    hFd.unique ((hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq hz)
  change ⟪N x,v⟫=0
  rw [hc,graphSlopeNormal_weight hn,real_inner_smul_left,real_inner_smul_left,inner_sub_left,
    normalPlaneEmbedding_inner_coordinates hn,sub_eq_zero.mp he]
  ring

lemma coordinateSectionPoint_hasDerivAt {c : Cover} {t a : ℝ} {γ : ℝ → ℂ} {v : ℂ}
    (hγ : HasDerivAt γ v a) :
    HasDerivAt (fun b => coordinateSectionPoint c t (γ b)) (coordinatePlaneLift v) a := by
  convert! (coordinatePlaneLift.hasFDerivAt.comp_hasDerivAt a hγ).const_add
      (c+(t-c 0) • EuclideanSpace.single 0 1) using 1

theorem isMinimizerAt_radial_curve_tangent {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {c : Cover} {t : ℝ} {r dr : ℝ → ℝ} (hr : ∀ a,HasDerivAt r (dr a) a)
    (hb : ∀ a,quotientMap (coordinateSectionPoint c t (radialCurve r a))∈frontier (openRepresentative E))
    (a : ℝ) :
    ⟪N (coordinateSectionPoint c t (radialCurve r a)),coordinatePlaneLift (radialVelocity r dr a)⟫=0 := by
  exact isMinimizerAt_boundary_curve_tangent hV hE hm hμ hN hp ha
    (coordinateSectionPoint_hasDerivAt (radialCurve_deriv hr a)) (Eventually.of_forall hb)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped ENNReal Real
namespace CubicTorus

def planarRadialRegion (r : ℝ → ℝ) : Set ℂ :=
  {z | ‖z‖<r (z.arg/(2*Real.pi))}

lemma measurableSet_planarRadialRegion {r : ℝ → ℝ} (hr : Measurable r) :
    MeasurableSet (planarRadialRegion r) :=
  measurableSet_lt measurable_norm (hr.comp (Complex.measurable_arg.div_const _))

lemma mem_planarRadialRegion_polar {r : ℝ → ℝ} {p : ℝ × ℝ}
    (hp : p∈Complex.polarCoord.target) :
    Complex.polarCoord.symm p∈planarRadialRegion r ↔ p.1<r (p.2/(2*Real.pi)) := by
  have he := congrArg Prod.snd (Complex.polarCoord.right_inv hp)
  rw [Complex.polarCoord_apply] at he
  change (Complex.polarCoord.symm p).arg=p.2 at he
  change ‖Complex.polarCoord.symm p‖<r _ ↔ _
  rw [Complex.norm_polarCoord_symm,abs_of_pos hp.1,he]

lemma lintegral_radial_coordinate {R : ℝ} (hR : 0≤R) :
    (∫⁻ x in Ioi (0 : ℝ),if x<R then ENNReal.ofReal x else 0)=ENNReal.ofReal (R^2/2) := by
  have he : (fun x : ℝ => if x<R then ENNReal.ofReal x else 0)=
      (Iio R).indicator ENNReal.ofReal := by rfl
  rw [he,lintegral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  rw [inter_comm,Ioi_inter_Iio,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hi : IntegrableOn (fun x : ℝ => x) (Ioc 0 R) :=
    (continuous_id.intervalIntegrable 0 R).1.mono_set (by rfl)
  have hn : 0≤ᵐ[volume.restrict (Ioc 0 R)] (fun x : ℝ => x) :=
    (ae_restrict_mem measurableSet_Ioc).mono fun x hx => hx.1.le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,← intervalIntegral.integral_of_le hR,integral_id]
  simp

theorem volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t) :
    volume (planarRadialRegion r)=
      ENNReal.ofReal (Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2)) := by
  let f : ℂ → ℝ≥0∞ := (planarRadialRegion r).indicator (fun _ => 1)
  have hfm : Measurable f := measurable_const.indicator (measurableSet_planarRadialRegion hr.measurable)
  have hvol : (∫⁻ z,f z)=volume (planarRadialRegion r) := by
    simp [f,lintegral_indicator,measurableSet_planarRadialRegion hr.measurable]
  rw [← hvol,← Complex.lintegral_comp_polarCoord_symm]
  let g : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1<r (p.2/(2*Real.pi)) then ENNReal.ofReal p.1 else 0
  have hgm : Measurable g := by
    exact Measurable.ite (measurableSet_lt measurable_fst
      (hr.measurable.comp (measurable_snd.div_const _)))
      measurable_fst.ennreal_ofReal measurable_const
  have hg : (∫⁻ p in polarCoord.target,ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p))=
      ∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,g p := by
    apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp'
    have hmem := mem_planarRadialRegion_polar (r := r) hp'
    by_cases hh : p.1<r (p.2/(2*Real.pi))
    · simp only [f,g,indicator_of_mem (hmem.mpr hh),ite_eq_left hh,smul_eq_mul,mul_one]
    · simp only [f,g,indicator_of_notMem (not_imp_not.mpr hmem.mp hh),ite_eq_right hh,smul_eq_mul,mul_zero]
  rw [hg,Measure.volume_eq_prod,setLIntegral_prod _ hgm.aemeasurable]
  rw [lintegral_lintegral_swap hgm.aemeasurable]
  have hb : (∫⁻ t in Ioo (-Real.pi) Real.pi,∫⁻ x in Ioi (0 : ℝ),g (x,t))=
      ∫⁻ t in Ioo (-Real.pi) Real.pi,ENNReal.ofReal ((r (t/(2*Real.pi)))^2/2) := by
    apply lintegral_congr
    intro t
    exact lintegral_radial_coordinate (R := r (t/(2*Real.pi))) (hpos _).le
  rw [hb,Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  have hrc : Continuous (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) :=
    ((hr.comp (continuous_id.div_const _)).pow 2).div_const _
  have hpi : -Real.pi≤Real.pi := by linarith [Real.pi_pos]
  have hi : IntegrableOn (fun t : ℝ => (r (t/(2*Real.pi)))^2/2) (Ioc (-Real.pi) Real.pi) := by
    exact (hrc.intervalIntegrable (-Real.pi) Real.pi).1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun x => by positivity)),
    ← intervalIntegral.integral_of_le hpi]
  congr 1
  rw [intervalIntegral.integral_div,intervalIntegral.integral_comp_div (fun t => (r t)^2) (by positivity : 2*Real.pi≠0)]
  have hlo : -Real.pi/(2*Real.pi)= -(1/2 : ℝ) := by field_simp
  have hhi : Real.pi/(2*Real.pi)=(1/2 : ℝ) := by field_simp
  rw [hlo,hhi]
  have hper : Function.Periodic (fun t => (r t)^2) 1 := fun t => congrArg (fun a : ℝ => a^2) (hp t)
  have hs := hper.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  norm_num only [neg_add_cancel_left,zero_add] at hs
  have hs' : (∫ t in (-(1/2) : ℝ)..(1/2),(r t)^2)=∫ t in (0 : ℝ)..1,(r t)^2 := by
    exact hs
  rw [hs']
  simp only [smul_eq_mul]
  ring

lemma real_volume_planarRadialRegion {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t) :
    volume.real (planarRadialRegion r)=Real.pi*(∫ t in (0 : ℝ)..1,(r t)^2) := by
  rw [Measure.real,volume_planarRadialRegion hr hp hpos,ENNReal.toReal_ofReal]
  exact mul_nonneg Real.pi_pos.le
    (intervalIntegral.integral_nonneg (by norm_num) (fun t _ => sq_nonneg (r t)))

theorem planar_radial_area_length {r dr : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (dr t) t) (hdc : Continuous dr)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t) :
    4*Real.pi*volume.real (planarRadialRegion r) ≤
      (∫ t in (0 : ℝ)..1,Real.sqrt ((dr t)^2+(2*Real.pi*r t)^2))^2 := by
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  rw [real_volume_planarRadialRegion hrc hp hpos]
  convert radial_curve_isoperimetric hr hdc hp hpos using 1; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped Real
namespace CubicTorus

lemma unit_square_integral_swap {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    (∫ t in (0 : ℝ)..1,∫ s in (0 : ℝ)..1,f (t,s))=
      ∫ s in (0 : ℝ)..1,∫ t in (0 : ℝ)..1,f (t,s) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]
  apply integral_integral_swap
  rw [Measure.prod_restrict,← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

theorem periodic_parametric_green {A B As Bt : ℝ × ℝ → ℝ}
    (hAs : Continuous As) (hBt : Continuous Bt)
    (hdA : ∀ t s,HasDerivAt (fun u => A (t,u)) (As (t,s)) s)
    (hdB : ∀ t s,HasDerivAt (fun u => B (u,s)) (Bt (t,s)) t)
    (hA0 : ∀ t,A (t,0)=0) (hBp : ∀ s,B (1,s)=B (0,s)) :
    (∫ t in (0 : ℝ)..1,∫ s in (0 : ℝ)..1,As (t,s)-Bt (t,s))=
      ∫ t in (0 : ℝ)..1,A (t,1) := by
  have hiA := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) (f := fun t s => As (t,s)) hAs 0 1
  have hiB := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) (f := fun t s => Bt (t,s)) hBt 0 1
  have hsub (t : ℝ) : (∫ s in (0 : ℝ)..1,As (t,s)-Bt (t,s))=
      (∫ s in (0 : ℝ)..1,As (t,s))-(∫ s in (0 : ℝ)..1,Bt (t,s)) := by
    exact intervalIntegral.integral_sub
      ((hAs.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hBt.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  simp_rw [hsub]
  rw [intervalIntegral.integral_sub (hiA.intervalIntegrable _ _) (hiB.intervalIntegrable _ _),
    unit_square_integral_swap hBt]
  have hB (s : ℝ) : (∫ t in (0 : ℝ)..1,Bt (t,s))=0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hdB t s)
      ((hBt.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _),hBp,sub_self]
  have hA (t : ℝ) : (∫ s in (0 : ℝ)..1,As (t,s))=A (t,1) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hdA t s)
      ((hAs.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _),hA0,sub_zero]
  simp_rw [hB,hA]
  simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
open scoped Real
namespace CubicTorus

def complexDet (z w : ℂ) : ℝ := z.re*w.im-z.im*w.re

def complexRealDiv (F : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ F z 1).re+(fderiv ℝ F z Complex.I).im

lemma complexDet_continuous {X : Type*} [TopologicalSpace X] {f g : X → ℂ}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => complexDet (f x) (g x)) :=
  ((Complex.continuous_re.comp hf).mul (Complex.continuous_im.comp hg)).sub
    ((Complex.continuous_im.comp hf).mul (Complex.continuous_re.comp hg))

lemma complexDet_smul_left (r : ℝ) (z w : ℂ) : complexDet (r • z) w=r*complexDet z w := by
  simp only [complexDet,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

lemma complexDet_smul_right (r : ℝ) (z w : ℂ) : complexDet z (r • w)=r*complexDet z w := by
  simp only [complexDet,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

lemma complexDet_deriv {f g : ℝ → ℂ} {df dg : ℂ} {t : ℝ}
    (hf : HasDerivAt f df t) (hg : HasDerivAt g dg t) :
    HasDerivAt (fun u => complexDet (f u) (g u))
      (complexDet df (g t)+complexDet (f t) dg) t := by
  have hfr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hfi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
  have hgr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hg
  have hgi := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hg
  convert! (hfr.mul hgi).sub (hfi.mul hgr) using 1; first | rfl | (dsimp [complexDet]; ring)

lemma complexDet_trace_identity (L : ℂ →L[ℝ] ℂ) (z w : ℂ) :
    complexDet (L z) w-complexDet (L w) z=((L 1).re+(L Complex.I).im)*complexDet z w := by
  have he (v : ℂ) : L v=v.re • L 1+v.im • L Complex.I := by
    calc
      L v=L (v.re • (1 : ℂ)+v.im • Complex.I) := congrArg L (by apply Complex.ext <;> simp)
      _=v.re • L 1+v.im • L Complex.I := by rw [map_add,map_smul,map_smul]
  rw [he z,he w]
  simp only [complexDet,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem complex_green_homotopy {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    {γ dγ : ℝ → ℂ} (hγ : ∀ t,HasDerivAt γ (dγ t) t) (hdγ : Continuous dγ)
    (hclose : γ 1=γ 0) :
    (∫ t in (0 : ℝ)..1,∫ s in (0 : ℝ)..1,
      s*complexDet (γ t) (dγ t)*complexRealDiv F (s • γ t))=
      ∫ t in (0 : ℝ)..1,complexDet (F (γ t)) (dγ t) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  let Φ : ℝ × ℝ → ℂ := fun p => p.2 • γ p.1
  let L : ℝ × ℝ → ℂ →L[ℝ] ℂ := fun p => fderiv ℝ F (Φ p)
  let A : ℝ × ℝ → ℝ := fun p => p.2*complexDet (F (Φ p)) (dγ p.1)
  let B : ℝ × ℝ → ℝ := fun p => complexDet (F (Φ p)) (γ p.1)
  let As : ℝ × ℝ → ℝ := fun p => complexDet (F (Φ p)) (dγ p.1)+
    p.2*complexDet (L p (γ p.1)) (dγ p.1)
  let Bt : ℝ × ℝ → ℝ := fun p => complexDet (L p (p.2 • dγ p.1)) (γ p.1)+
    complexDet (F (Φ p)) (dγ p.1)
  have hΦ : Continuous Φ := continuous_snd.smul (hγc.comp continuous_fst)
  have hL : Continuous L := (hF.continuous_fderiv (by norm_num)).comp hΦ
  have hAs : Continuous As :=
    (complexDet_continuous (hF.continuous.comp hΦ) (hdγ.comp continuous_fst)).add
      (continuous_snd.mul (complexDet_continuous (hL.clm_apply (hγc.comp continuous_fst))
        (hdγ.comp continuous_fst)))
  have hBt : Continuous Bt :=
    (complexDet_continuous (hL.clm_apply (continuous_snd.smul (hdγ.comp continuous_fst)))
      (hγc.comp continuous_fst)).add
      (complexDet_continuous (hF.continuous.comp hΦ) (hdγ.comp continuous_fst))
  have hdA (t s : ℝ) : HasDerivAt (fun u => A (t,u)) (As (t,s)) s := by
    have hΦd : HasDerivAt (fun u : ℝ => Φ (t,u)) (γ t) s := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id s).smul_const (γ t)
    have hFd := (hF.differentiable (by norm_num) (Φ (t,s))).hasFDerivAt.comp_hasDerivAt s hΦd
    have hdet := complexDet_deriv hFd (hasDerivAt_const s (dγ t))
    convert! (hasDerivAt_id s).mul hdet using 1; first | rfl | (dsimp [A,As,L,complexDet]; ring)
  have hdB (t s : ℝ) : HasDerivAt (fun u => B (u,s)) (Bt (t,s)) t := by
    have hΦd : HasDerivAt (fun u : ℝ => Φ (u,s)) (s • dγ t) t := (hγ t).const_smul s
    have hFd := (hF.differentiable (by norm_num) (Φ (t,s))).hasFDerivAt.comp_hasDerivAt t hΦd
    exact complexDet_deriv hFd (hγ t)
  have hz (t : ℝ) : A (t,0)=0 := by simp [A]
  have hp (s : ℝ) : B (1,s)=B (0,s) := by simp only [B,Φ,hclose]
  have heq (t s : ℝ) : As (t,s)-Bt (t,s)=
      s*complexDet (γ t) (dγ t)*complexRealDiv F (s • γ t) := by
    dsimp only [As,Bt]
    rw [map_smul,complexDet_smul_left]
    calc
      _=s*(complexDet (L (t,s) (γ t)) (dγ t)-complexDet (L (t,s) (dγ t)) (γ t)) := by ring
      _=_ := by rw [complexDet_trace_identity]; dsimp [L,Φ,complexRealDiv]; ring
  have hh := periodic_parametric_green hAs hBt hdA hdB hz hp
  simp_rw [heq] at hh
  simpa only [A,Φ,one_smul,one_mul] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped Real
namespace CubicTorus

lemma polarCoord_symm_unitAngle (x t : ℝ) :
    Complex.polarCoord.symm (x,t)=x • unitAngle (t/(2*Real.pi)) := by
  rw [Complex.polarCoord_symm_apply,unitAngle]
  have he : 2*Real.pi*(t/(2*Real.pi))=t := by field_simp
  rw [he,Complex.exp_mul_I,Complex.real_smul]
  simp

lemma continuous_polarSymm : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  simp only [Complex.polarCoord_symm_apply]
  fun_prop

lemma integral_radial_coordinate {D : ℂ → ℝ} {R t : ℝ} (hR : 0≤R) :
    (∫ x in Ioi (0 : ℝ),if x<R then x*D (Complex.polarCoord.symm (x,t)) else 0)=
      ∫ x in (0 : ℝ)..R,x*D (x • unitAngle (t/(2*Real.pi))) := by
  change (∫ x in Ioi (0 : ℝ),(Iio R).indicator
    (fun x => x*D (Complex.polarCoord.symm (x,t))) x)=_
  rw [integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio,
    inter_comm,Ioi_inter_Iio,Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le hR]
  congr 1
  funext x
  rw [polarCoord_symm_unitAngle]

theorem integral_planarRadialRegion_polar {r : ℝ → ℝ} (hr : Continuous r)
    (hpos : ∀ t,0<r t) {D : ℂ → ℝ} (hD : Continuous D) :
    (∫ z in planarRadialRegion r,D z)=
      ∫ t in (-Real.pi)..Real.pi,∫ x in (0 : ℝ)..r (t/(2*Real.pi)),
        x*D (x • unitAngle (t/(2*Real.pi))) := by
  let T : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
  let K : Set (ℝ × ℝ) := {p | p.1<r (p.2/(2*Real.pi))}
  let k : ℝ × ℝ → ℝ := fun p => p.1*D (Complex.polarCoord.symm p)
  let g : ℝ × ℝ → ℝ := K.indicator k
  have hKm : MeasurableSet K := measurableSet_lt measurable_fst
    (hr.measurable.comp (measurable_snd.div_const _))
  have hkc : Continuous k := continuous_fst.mul (hD.comp continuous_polarSymm)
  have hb := (isCompact_Icc (a := -Real.pi) (b := Real.pi)).bddAbove_image (hr.comp (continuous_id.div_const (2*Real.pi))).continuousOn
  obtain ⟨R,hR⟩ := hb
  let B : Set (ℝ × ℝ) := Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi
  have hBc : IsCompact B := isCompact_Icc.prod isCompact_Icc
  have hgm : IntegrableOn g T := by
    have hi : Integrable (B.indicator k) volume :=
      (hkc.continuousOn.integrableOn_compact hBc).integrable_indicator hBc.measurableSet
    have hi' := hi.indicator hKm
    apply hi'.integrableOn.congr_fun _ (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    by_cases hk : p∈K
    · have hpB : p∈B := by
        refine ⟨⟨hp.1.le,?_⟩,hp.2.1.le,hp.2.2.le⟩
        exact (show p.1<r (p.2/(2*Real.pi)) from hk).le.trans
          (hR (mem_image_of_mem _ ⟨hp.2.1.le,hp.2.2.le⟩))
      simp only [g,indicator_of_mem hk,indicator_of_mem hpB]
    · simp only [g,indicator_of_notMem hk]
  rw [← integral_indicator (measurableSet_planarRadialRegion hr.measurable),
    ← Complex.integral_comp_polarCoord_symm]
  have he : (∫ p in polarCoord.target,p.1 • (planarRadialRegion r).indicator D (Complex.polarCoord.symm p))=
      ∫ p in T,g p := by
    apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
    intro p hp
    have hm := mem_planarRadialRegion_polar (r := r) hp
    by_cases hpr : p.1<r (p.2/(2*Real.pi))
    · simp only [g,indicator_of_mem (show p∈K from hpr),indicator_of_mem (hm.mpr hpr),smul_eq_mul,k]
    · simp only [g,indicator_of_notMem (show p∉K from hpr),
        indicator_of_notMem (not_imp_not.mpr hm.mp hpr),smul_eq_mul,k,mul_zero]
  rw [he]
  dsimp only [T]
  rw [Measure.volume_eq_prod,setIntegral_prod _ (by rwa [← Measure.volume_eq_prod])]
  have hswap : Integrable (Function.uncurry (fun x t => g (x,t)))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact hgm
  rw [integral_integral_swap hswap]
  have hinner : (fun t => ∫ x in Ioi (0 : ℝ),g (x,t))=
      fun t => ∫ x in (0 : ℝ)..r (t/(2*Real.pi)),x*D (x • unitAngle (t/(2*Real.pi))) := by
    funext t
    simpa only [g,K,k,indicator_apply,mem_ofPred_eq] using
      (integral_radial_coordinate (D := D) (t := t) (hpos (t/(2*Real.pi))).le)
  rw [hinner,Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi≤Real.pi)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Complex
open scoped Real
namespace CubicTorus

lemma integral_radial_coordinate_scale {D : ℂ → ℝ} {R : ℝ} (hR : 0<R) (u : ℂ) :
    (∫ x in (0 : ℝ)..R,x*D (x • u))=
      ∫ s in (0 : ℝ)..1,s*R^2*D (s • (R • u)) := by
  have hh := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (c := R) (fun x : ℝ => x*D (x • u)) hR.ne'
  simp only [mul_zero,mul_one,smul_eq_mul] at hh
  calc
    _ = R*(∫ s in (0 : ℝ)..1,(R*s)*D ((R*s) • u)) := by rw [hh]; field_simp
    _ = _ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro s hs
      dsimp only
      rw [smul_smul,show s*R=R*s by ring]
      ring

theorem integral_planarRadialRegion_homotopy {r : ℝ → ℝ} (hr : Continuous r)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t)
    {D : ℂ → ℝ} (hD : Continuous D) :
    (∫ z in planarRadialRegion r,D z)=
      ∫ t in (0 : ℝ)..1,∫ s in (0 : ℝ)..1,
        s*(2*Real.pi*(r t)^2)*D (s • radialCurve r t) := by
  rw [integral_planarRadialRegion_polar hr hpos hD]
  simp_rw [integral_radial_coordinate_scale (hpos _)]
  let f : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..1,s*(r t)^2*D (s • radialCurve r t)
  have he (t : ℝ) : (r t) • unitAngle t=radialCurve r t := by
    rw [radialCurve,Complex.real_smul]
  simp_rw [he]
  change (∫ t in (-Real.pi)..Real.pi,f (t/(2*Real.pi)))=_
  rw [intervalIntegral.integral_comp_div f (by positivity : 2*Real.pi≠0)]
  have hlo : -Real.pi/(2*Real.pi)= -(1/2 : ℝ) := by field_simp
  have hhi : Real.pi/(2*Real.pi)=(1/2 : ℝ) := by field_simp
  rw [hlo,hhi]
  have hfper : Function.Periodic f 1 := by
    intro t
    simp only [f,radialCurve,hp t,unitAngle_periodic t]
  have hs := hfper.intervalIntegral_add_eq (-(1/2 : ℝ)) 0
  have hs' : (∫ t in (-(1/2) : ℝ)..(1/2),f t)=∫ t in (0 : ℝ)..1,f t := by
    convert hs using 1 <;> norm_num
  rw [hs']
  simp only [smul_eq_mul]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only [f]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s hs
  ring

lemma complexRealDiv_continuous {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    Continuous (complexRealDiv F) := by
  exact (Complex.continuous_re.comp ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const)).add
    (Complex.continuous_im.comp ((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const))

lemma complexDet_eq_im (z w : ℂ) : complexDet z w=(star z*w).im := by
  simp [complexDet,Complex.mul_im,sub_eq_add_neg]

theorem green_planarRadialRegion {r dr : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (dr t) t) (hdc : Continuous dr)
    (hp : Function.Periodic r 1) (hpos : ∀ t,0<r t)
    {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    (∫ z in planarRadialRegion r,complexRealDiv F z)=
      ∫ t in (0 : ℝ)..1,complexDet (F (radialCurve r t)) (radialVelocity r dr t) := by
  have hrc : Continuous r := continuous_iff_continuousAt.mpr fun t => (hr t).continuousAt
  have hvc : Continuous (radialVelocity r dr) := by
    exact ((Complex.continuous_ofReal.comp hdc).add
      ((Complex.continuous_ofReal.comp (continuous_const.mul hrc)).mul continuous_const)).mul unitAngle_continuous
  have hclose : radialCurve r 1=radialCurve r 0 := by
    have h1 := hp 0
    have hu := unitAngle_periodic 0
    simp only [zero_add] at h1 hu
    simp only [radialCurve,h1,hu]
  rw [integral_planarRadialRegion_homotopy hrc hp hpos (complexRealDiv_continuous hF)]
  have hh := complex_green_homotopy hF (radialCurve_deriv hr) hvc hclose
  simpa only [complexDet_eq_im,radialCurve_area_integrand] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def coordinatePlaneProjection : Cover →L[ℝ] ℂ :=
  (EuclideanSpace.proj (1 : Fin 3)).smulRight (1 : ℂ)+
    (EuclideanSpace.proj (2 : Fin 3)).smulRight Complex.I

@[simp] lemma coordinatePlaneProjection_re (u : Cover) : (coordinatePlaneProjection u).re=u 1 := by
  simp [coordinatePlaneProjection]
@[simp] lemma coordinatePlaneProjection_im (u : Cover) : (coordinatePlaneProjection u).im=u 2 := by
  simp [coordinatePlaneProjection]

lemma coordinatePlaneProjection_inner (u : Cover) (z : ℂ) :
    ⟪u,coordinatePlaneLift z⟫=(coordinatePlaneProjection u).re*z.re+(coordinatePlaneProjection u).im*z.im := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply,conj_trivial,Fin.sum_univ_three,coordinatePlaneLift_apply,
    Fin.reduceEq,ite_true,ite_false,zero_mul,zero_add,coordinatePlaneProjection_re,coordinatePlaneProjection_im]
  ring

lemma coordinatePlaneProjection_norm_sq (u : Cover) :
    ‖coordinatePlaneProjection u‖^2=‖u‖^2-(u 0)^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply,coordinatePlaneProjection_re,coordinatePlaneProjection_im]
  rw [← real_inner_self_eq_norm_sq,PiLp.inner_apply]
  simp only [Fin.sum_univ_three,RCLike.inner_apply,conj_trivial]
  ring

lemma coordinatePlaneProjection_unit {u : Cover} (hu : ‖u‖=1) (ha : u 0=0) :
    ‖coordinatePlaneProjection u‖=1 := by
  have hh := coordinatePlaneProjection_norm_sq u
  rw [hu,ha] at hh
  nlinarith [norm_nonneg (coordinatePlaneProjection u)]

lemma complexDet_four_square (u v : ℂ) :
    (complexDet u v)^2+(u.re*v.re+u.im*v.im)^2=‖u‖^2*‖v‖^2 := by
  simp only [complexDet,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma complexDet_unit_positive {m z w : ℂ} (hm : ‖m‖=1)
    (hperp : m.re*w.re+m.im*w.im=0) (hz : 0 < m.re*z.re+m.im*z.im)
    (hw : 0<complexDet z w) : complexDet m w=‖w‖ := by
  have hs := complexDet_four_square m w
  rw [hm,hperp] at hs
  have hu : m.re^2+m.im^2=1 := by
    have hh : ‖m‖^2=1 := by rw [hm]; norm_num
    rw [Complex.sq_norm,Complex.normSq_apply] at hh
    nlinarith [hh]
  have he : complexDet m w*(m.re*z.re+m.im*z.im)=complexDet z w := by
    have hid : complexDet m w*(m.re*z.re+m.im*z.im)-
        complexDet m z*(m.re*w.re+m.im*w.im)=
        complexDet z w*(m.re^2+m.im^2) := by
      dsimp [complexDet]
      ring
    rw [hperp,hu,mul_zero,sub_zero,mul_one] at hid
    exact hid
  have hp : 0<complexDet m w := (mul_pos_iff_of_pos_right hz).mp (he.symm ▸ hw)
  nlinarith [norm_nonneg w]

def coordinatePlaneField (F : Cover → Cover) (c : Cover) (t : ℝ) : ℂ → ℂ :=
  fun z => coordinatePlaneProjection (F (coordinateSectionPoint c t z))

lemma coordinatePlaneField_contDiff {F : Cover → Cover}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (c : Cover) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinatePlaneField F c t) :=
  coordinatePlaneProjection.contDiff.comp (hF.comp (coordinateSectionPoint_contDiff c t))

lemma coordinatePlaneField_divergence {F : Cover → Cover}
    (hF : Differentiable ℝ F) (ha : ∀ x,F x 0=0) (c : Cover) (t : ℝ) (z : ℂ) :
    complexRealDiv (coordinatePlaneField F c t) z=divergence F (coordinateSectionPoint c t z) := by
  let x := coordinateSectionPoint c t z
  have hd : HasFDerivAt (coordinateSectionPoint c t) coordinatePlaneLift z := by
    convert! coordinatePlaneLift.hasFDerivAt.const_add
      (c+(t-c 0) • EuclideanSpace.single 0 1) using 1
  have hfd : HasFDerivAt (coordinatePlaneField F c t)
      (coordinatePlaneProjection.comp ((fderiv ℝ F x).comp coordinatePlaneLift)) z :=
    coordinatePlaneProjection.hasFDerivAt.comp z ((hF x).hasFDerivAt.comp z hd)
  have he1 : coordinatePlaneLift 1=EuclideanSpace.single 1 1 := by ext i; fin_cases i <;> simp
  have heI : coordinatePlaneLift Complex.I=EuclideanSpace.single 2 1 := by ext i; fin_cases i <;> simp
  have hz0 : (EuclideanSpace.proj (0 : Fin 3)).comp (fderiv ℝ F x)=0 := by
    have hh := (EuclideanSpace.proj (0 : Fin 3)).hasFDerivAt.comp x (hF x).hasFDerivAt
    have heq : (fun a => F a 0)=(fun _ => (0 : ℝ)) := funext ha
    have hh' : HasFDerivAt (fun a => F a 0) ((EuclideanSpace.proj (0 : Fin 3)).comp (fderiv ℝ F x)) x := hh
    rw [heq] at hh'
    exact hh'.unique (hasFDerivAt_const (0 : ℝ) x)
  have hz0' : (fderiv ℝ F x (EuclideanSpace.single 0 1)) 0=0 := by
    have hh := congrArg (fun L : Cover →L[ℝ] ℝ => L (EuclideanSpace.single 0 1)) hz0
    exact hh
  change (fderiv ℝ (coordinatePlaneField F c t) z 1).re+
      (fderiv ℝ (coordinatePlaneField F c t) z Complex.I).im=divergence F x
  rw [hfd.fderiv]
  simp only [ContinuousLinearMap.comp_apply,he1,heI,coordinatePlaneProjection_re,coordinatePlaneProjection_im,
    divergence,Fin.sum_univ_three,hz0',zero_add]

end CubicTorus

end
end

end OAI
