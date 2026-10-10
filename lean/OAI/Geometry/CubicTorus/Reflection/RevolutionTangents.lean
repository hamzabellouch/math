import Mathlib
import OAI.Geometry.CubicTorus.Profiles.FlatTranslation

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem first_transition_nonstandard_revolution
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (G : Set Torus) (b : Fin 3 → Bool) (r : ℝ × ℝ → ℝ),
      MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
      ¬SmallStandardRegion (4*Real.pi/81) G ∧
      TrueRadialTube G (chamberCorner b) r ∧
      (∀ i : Fin 3, coordinateReflection i ⁻¹' G =ᵐ[torusVolume] G) ∧
      ∀ t a, r (t,a)=r (t,0) := by
  have hV : 4*Real.pi/81 ∈ Ioo (0 : ℝ) 1 :=
    ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,i,hF,he,hm,_,hμ,ha,hs,hsg,_,_,hv⟩ :=
    isMinimizerAt_first_transition_nonstandard_two_vertices hmE hnstd
  obtain ⟨e,r,hr⟩ := isMinimizerAt_two_vertices_smooth_tube hV hF hm hμ hN hp ha hs hsg i hv
  let G := torusCoordinatePermute e ⁻¹' F
  have hG : MeasurableSet G := (torusCoordinatePermute e).continuous.measurable hF
  have hmG : IsMinimizerAt (4*Real.pi/81) G := isMinimizerAt_coordinatePermute hm e
  have hsG := reflection_invariant_coordinatePermute hs e
  obtain ⟨ν,M,hM,hMp,hν,haM,hrot⟩ := hr.exists_rotation_zero hV hG hmG _ (hsG 1) (hsG 2)
  refine ⟨G,c ∘ e.symm,r,hG,hmG,?_,hr,hsG,?_⟩
  · intro h
    exact hnstd (smallStandardRegion_of_translated he (smallStandardRegion_of_coordinatePermute e h))
  · exact hr.radial_independent_angle hV hG hmG hν hM hMp haM hrot

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def revolutionPoint (c : Cover) (r : ℝ → ℝ) (t a : ℝ) : Cover :=
  coordinateSectionPoint c t (r t • unitAngle a)

@[simp] lemma unitAngle_zero : unitAngle 0=1 := by simp [unitAngle]

lemma revolutionPoint_meridian_deriv {c : Cover} {r : ℝ → ℝ} {p t a : ℝ}
    (hr : HasDerivAt r p t) :
    HasDerivAt (fun u => revolutionPoint c r u a)
      (EuclideanSpace.single 0 1+p • coordinatePlaneLift (unitAngle a)) t :=
  coordinateSectionPoint_axial_hasDerivAt hr

lemma revolutionPoint_angle_deriv {c : Cover} {r : ℝ → ℝ} (t a : ℝ) :
    HasDerivAt (revolutionPoint c r t)
      ((2*Real.pi*r t) • coordinatePlaneLift (Complex.I*unitAngle a)) a := by
  have hd := coordinateSectionPoint_hasDerivAt (c := c) (t := t)
    ((unitAngle_deriv a).const_smul (r t))
  convert! hd using 1
  rw [← map_smul]
  congr 1
  simp only [Complex.real_smul,Complex.ofReal_mul]
  ring

lemma revolutionPoint_zero_meridian_deriv {c : Cover} {r : ℝ → ℝ} {p t : ℝ}
    (hr : HasDerivAt r p t) :
    HasDerivAt (fun u => revolutionPoint c r u 0)
      (EuclideanSpace.single 0 1+p • EuclideanSpace.single 1 1) t := by
  have he : coordinatePlaneLift (unitAngle 0)=EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp
  simpa only [he] using revolutionPoint_meridian_deriv (c := c) (a := 0) hr

lemma revolutionPoint_zero_angle_deriv {c : Cover} {r : ℝ → ℝ} (t : ℝ) :
    HasDerivAt (revolutionPoint c r t)
      ((2*Real.pi*r t) • EuclideanSpace.single 2 1) 0 := by
  have he : coordinatePlaneLift (Complex.I*unitAngle 0)=EuclideanSpace.single 2 1 := by
    ext i; fin_cases i <;> simp
  simpa only [he] using revolutionPoint_angle_deriv (c := c) (r := r) t 0

theorem isMinimizerAt_revolution_tangents {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {c : Cover} {r p : ℝ → ℝ} (hr : ∀ t,HasDerivAt r (p t) t)
    (hpos : ∀ t,0<r t)
    (hb : ∀ t a,quotientMap (revolutionPoint c r t a)∈frontier (openRepresentative E))
    (t a : ℝ) :
    N (revolutionPoint c r t a) 0+p t*⟪N (revolutionPoint c r t a),coordinatePlaneLift (unitAngle a)⟫=0 ∧
    (unitAngle a).re*N (revolutionPoint c r t a) 2-
      (unitAngle a).im*N (revolutionPoint c r t a) 1=0 := by
  have h₁ := isMinimizerAt_boundary_curve_tangent hV hE hm hμ hN hp ha
    (revolutionPoint_meridian_deriv (c := c) (a := a) (hr t))
    (Eventually.of_forall (fun u => hb u a))
  have h₂ := isMinimizerAt_boundary_curve_tangent hV hE hm hμ hN hp ha
    (revolutionPoint_angle_deriv (c := c) (r := r) t a)
    (Eventually.of_forall (hb t))
  refine ⟨?_,?_⟩
  · simpa only [inner_add_right,real_inner_smul_right,EuclideanSpace.inner_single_right,
      conj_trivial,one_mul] using h₁
  · rw [real_inner_smul_right,coordinatePlaneLift_quarter_inner] at h₂
    exact (mul_eq_zero.mp h₂).resolve_left (mul_pos (mul_pos (by norm_num) Real.pi_pos) (hpos t)).ne'

theorem isMinimizerAt_revolution_meridian_normal {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {c : Cover} {r p : ℝ → ℝ} (hr : ∀ t,HasDerivAt r (p t) t)
    (hpos : ∀ t,0<r t)
    (hb : ∀ t a,quotientMap (revolutionPoint c r t a)∈frontier (openRepresentative E))
    (t : ℝ) :
    let n := N (revolutionPoint c r t 0)
    n 2=0 ∧ n 0= -(p t)*n 1 ∧ (n 1)^2*(1+p t^2)=1 ∧ n 1≠0 := by
  let n := N (revolutionPoint c r t 0)
  obtain ⟨h₁,h₂⟩ := isMinimizerAt_revolution_tangents hV hE hm hμ hN hp ha hr hpos hb t 0
  have he : coordinatePlaneLift (unitAngle 0)=EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp
  simp only [he,EuclideanSpace.inner_single_right,conj_trivial,one_mul] at h₁
  simp only [unitAngle_zero,Complex.one_re,Complex.one_im,one_mul,zero_mul,sub_zero] at h₂
  change n 0+p t*n 1=0 at h₁
  change n 2=0 at h₂
  have hn := isMinimizerAt_normal_unit_boundary hV hE hm hμ hN.continuous hp ha _ (hb t 0)
  change ‖n‖=1 at hn
  have hn' := congrArg (fun z : ℝ => z^2) hn
  rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three,h₂] at hn'
  have h0 : n 0= -(p t)*n 1 := by linarith only [h₁]
  have hsq : (n 1)^2*(1+p t^2)=1 := by rw [h0] at hn'; nlinarith only [hn']
  exact ⟨h₂,h0,hsq,fun hz => by rw [hz] at hsq; norm_num at hsq⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

@[simp] lemma unitSquareScale_zero : unitSquareScale 0=1/2 := by
  norm_num [unitSquareScale,unitAngle_zero,complexSquareGauge]

lemma coverCoordinateReflection_section_zero (c : Cover) (t : ℝ) (z : ℂ) :
    coverCoordinateReflection 0 (coordinateSectionPoint c t z)=coordinateSectionPoint c (-t) z := by
  ext i
  fin_cases i <;> simp [coverCoordinateReflection_apply]

lemma TrueRadialTube.radius_eq_of_boundary {E : Set Torus} {c : Cover} {r : ℝ × ℝ → ℝ}
    (hr : TrueRadialTube E c r) {p : ℝ × ℝ} {u : ℝ}
    (hu : 0≤u) (hu' : u≤unitSquareScale p.2)
    (hb : quotientMap (coordinateSectionPoint c p.1 (u • unitAngle p.2))∈frontier (openRepresentative E)) :
    u=r p := by
  have hcl := hr.2.2.2.2.2.2.1 p u hu hu'
  have hop := hr.2.2.2.2.2.1 p u hu hu'
  have hc : u≤r p := hcl.mp (frontier_subset_closure hb)
  have hn : r p≤u := le_of_not_gt (fun h => (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (isOpen_openRepresentative E))) hb (hop.mpr h))
  exact le_antisymm hc hn

theorem TrueRadialTube.axial_even {E : Set Torus} (hE : MeasurableSet E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hs : coordinateReflection 0 ⁻¹' E =ᵐ[torusVolume] E) (t a : ℝ) :
    r (-t,a)=r (t,a) := by
  have hb := hr.2.2.2.2.1 (t,a)
  have hbr : coordinateReflection 0 (quotientMap (coordinateSectionPoint c t (r (t,a) • unitAngle a)))∈
      frontier (openRepresentative E) := by
    change quotientMap (coordinateSectionPoint c t (r (t,a) • unitAngle a))∈
      coordinateReflection 0 ⁻¹' frontier (openRepresentative E)
    rw [frontier_reflection_invariant hE 0 hs]
    exact hb
  rw [← quotientMap_coordinateReflection,coverCoordinateReflection_section_zero] at hbr
  exact (hr.radius_eq_of_boundary (p := (-t,a)) (hr.2.2.2.1 (t,a)).1.le (hr.2.2.2.1 (t,a)).2.le hbr).symm

theorem TrueRadialTube.deriv_negative_chamber {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (ha : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover))
    {b : Fin 3 → Bool} {r : ℝ × ℝ → ℝ} (htube : TrueRadialTube E (chamberCorner b) r)
    (hangle : ∀ t a,r (t,a)=r (t,0))
    (hsg : ∀ (x : Cover) (i : Fin 3),quotientMap x∈frontier (openRepresentative E)∩
      coordinateHalf i (if b i then 0 else 1/2) →0<N x i) :
    ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),deriv (fun s => r (s,0)) t<0 := by
  let R := fun t => r (t,0)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := htube.1.comp (contDiff_id.prodMk contDiff_const)
  have hd (t) : HasDerivAt R (deriv R t) t := (hR.differentiable (by simp) t).hasDerivAt
  have hpos (t) : 0<R t := (htube.2.2.2.1 (t,0)).1
  have hb (t a) : quotientMap (revolutionPoint (chamberCorner b) R t a)∈frontier (openRepresentative E) := by
    have h := htube.2.2.2.2.1 (t,a)
    simpa only [hangle t a,revolutionPoint,R] using h
  intro t ht
  let x := revolutionPoint (chamberCorner b) R t 0
  have hx0 : chamberCorner b 0<x 0 ∧ x 0<chamberCorner b 0+1/2 := by
    simpa only [x,revolutionPoint,coordinateSectionPoint_apply,ite_true,Set.mem_Ioo] using ht
  have hx1 : chamberCorner b 1<x 1 ∧ x 1<chamberCorner b 1+1/2 := by
    have hR1 : R t<1/2 := by simpa only [unitSquareScale_zero] using (htube.2.2.2.1 (t,0)).2
    simp only [x,revolutionPoint,coordinateSectionPoint_apply,show (1 : Fin 3)≠0 by decide,
      ite_false,ite_true,unitAngle_zero,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one]
    exact ⟨lt_add_of_pos_right _ (hpos t),add_lt_add_right hR1 _⟩
  have hn0 := hsg x 0 ⟨hb t 0,mem_coordinateHalf_of_chamber_interval b x 0 hx0⟩
  have hn1 := hsg x 1 ⟨hb t 0,mem_coordinateHalf_of_chamber_interval b x 1 hx1⟩
  have htan := (isMinimizerAt_revolution_tangents hV hE hm hμ hN hp ha hd hpos hb t 0).1
  have he : coordinatePlaneLift (unitAngle 0)=EuclideanSpace.single 1 1 := by
    ext i; fin_cases i <;> simp
  simp only [he,EuclideanSpace.inner_single_right,conj_trivial,one_mul] at htan
  change N x 0+deriv R t*N x 1=0 at htan
  change deriv R t<0
  by_contra hh
  have hf := mul_nonneg (le_of_not_gt hh) hn1.le
  linarith only [hn0,htan,hf]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem first_transition_nonstandard_monotone_revolution
    {E : Set Torus} (hmE : IsMinimizerAt (4*Real.pi/81) E)
    (hnstd : ¬SmallStandardRegion (4*Real.pi/81) E) :
    ∃ (G : Set Torus) (b : Fin 3 → Bool) (r : ℝ × ℝ → ℝ),
      MeasurableSet G ∧ IsMinimizerAt (4*Real.pi/81) G ∧
      ¬SmallStandardRegion (4*Real.pi/81) G ∧
      TrueRadialTube G (chamberCorner b) r ∧
      (∀ i : Fin 3, coordinateReflection i ⁻¹' G =ᵐ[torusVolume] G) ∧
      (∀ t a,r (t,a)=r (t,0)) ∧
      (∀ t a,r (-t,a)=r (t,a)) ∧
      ∀ t∈Ioo (chamberCorner b 0) (chamberCorner b 0+1/2),
        deriv (fun s => r (s,0)) t<0 := by
  have hV : 4*Real.pi/81 ∈ Ioo (0 : ℝ) 1 :=
    ⟨firstTransition_mem_Ioo_half.1,by linarith [firstTransition_mem_Ioo_half.2]⟩
  obtain ⟨v,F,μ,N,hN,hp,c,H,i,hF,he,hm,_,hμ,ha,hs,hsg,_,_,hv⟩ :=
    isMinimizerAt_first_transition_nonstandard_two_vertices hmE hnstd
  obtain ⟨e,r,hr⟩ := isMinimizerAt_two_vertices_smooth_tube hV hF hm hμ hN hp ha hs hsg i hv
  let G := torusCoordinatePermute e ⁻¹' F
  have hG : MeasurableSet G := (torusCoordinatePermute e).continuous.measurable hF
  have hmG : IsMinimizerAt (4*Real.pi/81) G := isMinimizerAt_coordinatePermute hm e
  have hsG := reflection_invariant_coordinatePermute hs e
  obtain ⟨ν,M,hM,hMp,hν,haM,hrot⟩ := hr.exists_rotation_zero hV hG hmG _ (hsG 1) (hsG 2)
  have hangle := hr.radial_independent_angle hV hG hmG hν hM hMp haM hrot
  refine ⟨G,c ∘ e.symm,r,hG,hmG,?_,hr,hsG,hangle,hr.axial_even hG (hsG 0),?_⟩
  · intro h
    exact hnstd (smallStandardRegion_of_translated he (smallStandardRegion_of_coordinatePermute e h))
  · exact hr.deriv_negative_chamber hV hG hmG (isNormalMeasure_coordinatePermute hF hμ e)
      (coordinatePermutedField_contDiff e hN) (coordinatePermutedField_periodic e hp)
      (permuted_normal_ae hN.continuous hp ha e) hangle (chamberSign_coordinatePermute hF hsg e)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma revolution_normal_divergence {c : Cover} {r p q : ℝ → ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : ∀ t,HasDerivAt p (q t) t)
    (hpos : ∀ t,0<r t) {N : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (htan : ∀ t a,
      N (revolutionPoint c r t a) 0+p t*⟪N (revolutionPoint c r t a),coordinatePlaneLift (unitAngle a)⟫=0 ∧
      (unitAngle a).re*N (revolutionPoint c r t a) 2-
        (unitAngle a).im*N (revolutionPoint c r t a) 1=0)
    (hunit : ∀ t,∀ᶠ y in 𝓝 (revolutionPoint c r t 0),‖N y‖=1)
    (hnormal : ∀ t,let n := N (revolutionPoint c r t 0)
      n 2=0 ∧ n 0= -(p t)*n 1 ∧ (n 1)^2*(1+p t^2)=1 ∧ n 1≠0)
    (t : ℝ) :
    divergence N (revolutionPoint c r t 0)=N (revolutionPoint c r t 0) 1*
      (1/r t-q t/(1+p t^2)) := by
  let x := revolutionPoint c r t 0
  let n := N x
  let D := fderiv ℝ N x
  have hs : 0<1+p t^2 := by positivity
  obtain ⟨hn2,hn0,_,hn1⟩ := hnormal t
  change n 2=0 at hn2
  change n 0= -(p t)*n 1 at hn0
  change n 1≠0 at hn1
  have hD (w : Cover) : ⟪n,D w⟫=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left]
    have he := smooth_unit_normal_derivative (hN.differentiable (by simp) x) (hunit t)
    change D.adjoint n=0 at he
    rw [he,inner_zero_left]
  have hD1 (w : Cover) : D w 1=p t*D w 0 := by
    have he := hD w
    simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,Fin.sum_univ_three,
      hn0,hn2] at he
    have hh : n 1*(D w 1-p t*D w 0)=0 := by nlinarith only [he]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn1)
  have hda := (hN.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt 0
    (revolutionPoint_zero_angle_deriv (c := c) (r := r) t)
  have hda' (i : Fin 3) : HasDerivAt (fun a => N (revolutionPoint c r t a) i)
      ((2*Real.pi*r t)*D (EuclideanSpace.single 2 1) i) 0 := by
    convert! (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hda using 1
    simp only [map_smul,smul_eq_mul]
    rfl
  have hre : HasDerivAt (fun a => (unitAngle a).re) 0 0 := by
    convert! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (unitAngle_deriv 0) using 1
    simp
  have him : HasDerivAt (fun a => (unitAngle a).im) (2*Real.pi) 0 := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (unitAngle_deriv 0) using 1
    simp
  have hzeroA : (fun a => (unitAngle a).re*N (revolutionPoint c r t a) 2-
      (unitAngle a).im*N (revolutionPoint c r t a) 1)=fun _ => 0 := by
    funext a; exact (htan t a).2
  have hA := ((hre.mul (hda' 2)).sub (him.mul (hda' 1))).unique
    ((hasDerivAt_const 0 (0 : ℝ)).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hzeroA))
  simp only [unitAngle_zero,Complex.one_re,Complex.one_im,zero_mul,one_mul,add_zero,zero_add] at hA
  change 2*Real.pi*r t*D (EuclideanSpace.single 2 1) 2-2*Real.pi*n 1=0 at hA
  have h22 : D (EuclideanSpace.single 2 1) 2=n 1/r t := by
    apply (eq_div_iff (hpos t).ne').2
    have he : (2*Real.pi)*(r t*D (EuclideanSpace.single 2 1) 2-n 1)=0 := by linarith only [hA]
    have hh := (mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    linarith only [hh]
  have hdt := (hN.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt t
    (revolutionPoint_zero_meridian_deriv (c := c) (hr t))
  have hdt' (i : Fin 3) : HasDerivAt (fun u => N (revolutionPoint c r u 0) i)
      (D (EuclideanSpace.single 0 1) i+p t*D (EuclideanSpace.single 1 1) i) t := by
    convert! (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hdt using 1
    simp only [map_add,map_smul,smul_eq_mul]
    rfl
  have hzeroT : (fun u => N (revolutionPoint c r u 0) 0+p u*N (revolutionPoint c r u 0) 1)=fun _ => 0 := by
    funext u
    have he : coordinatePlaneLift (unitAngle 0)=EuclideanSpace.single 1 1 := by
      ext i; fin_cases i <;> simp
    simpa only [he,EuclideanSpace.inner_single_right,conj_trivial,one_mul] using (htan u 0).1
  have hT := ((hdt' 0).add ((hp t).mul (hdt' 1))).unique
    ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hzeroT))
  change D (EuclideanSpace.single 0 1) 0+p t*D (EuclideanSpace.single 1 1) 0+
    (q t*n 1+p t*(D (EuclideanSpace.single 0 1) 1+p t*D (EuclideanSpace.single 1 1) 1))=0 at hT
  have htrace : D (EuclideanSpace.single 0 1) 0+D (EuclideanSpace.single 1 1) 1=
      -(q t*n 1)/(1+p t^2) := by
    apply (eq_div_iff hs.ne').2
    rw [hD1 (EuclideanSpace.single 0 1),hD1 (EuclideanSpace.single 1 1)] at hT
    rw [hD1 (EuclideanSpace.single 1 1)]
    linear_combination hT
  change divergence N x=n 1*(1/r t-q t/(1+p t^2))
  rw [divergence_eq_coverTrace]
  change coverTrace D=_
  rw [coverTrace,Fin.sum_univ_three,htrace,h22]
  ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
namespace CubicTorus

lemma hasDerivAt_delaunay_first_integral {r p q : ℝ → ℝ} {H t : ℝ}
    (hr : HasDerivAt r (p t) t) (hp : HasDerivAt p (q t) t)
    (hCMC : H=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3)
    (hr0 : 0<r t) :
    HasDerivAt (fun s => r s/Real.sqrt (1+p s^2)-H/2*r s^2) 0 t := by
  have hs0 : 0<Real.sqrt (1+p t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
  have hd := ((hasDerivAt_const t (1 : ℝ)).add (hp.pow 2)).sqrt (by positivity : 1+p t^2≠0)
  have he := (hr.div hd hs0.ne').sub ((hr.pow 2).const_mul (H/2))
  convert! he using 1
  simp only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,zero_add,Nat.cast_ofNat,pow_one]
  field_simp
  have hcmc : H*(r t*(Real.sqrt (1+p t^2))^3)=
      (Real.sqrt (1+p t^2))^2-r t*q t := by
    field_simp at hCMC ⊢
    nlinarith only [hCMC]
  linear_combination p t * hcmc

theorem delaunay_first_integral {r p q : ℝ → ℝ} {H : ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : ∀ t,HasDerivAt p (q t) t)
    (hpos : ∀ t,0<r t)
    (hCMC : ∀ t,H=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3) :
    ∃ α : ℝ,∀ t,r t/Real.sqrt (1+p t^2)=α+H/2*r t^2 := by
  let f := fun t => r t/Real.sqrt (1+p t^2)-H/2*r t^2
  have hd (t) : HasDerivAt f 0 t := hasDerivAt_delaunay_first_integral (hr t) (hp t) (hCMC t) (hpos t)
  refine ⟨f 0,?_⟩
  intro t
  have he := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  change r t/Real.sqrt (1+p t^2)-H/2*r t^2=f 0 at he
  linarith only [he]

lemma delaunay_first_integral_endpoints {a b α β : ℝ} (ha : 0<a) (hab : a<b)
    (h₁ : a=α+β*a^2) (h₂ : b=α+β*b^2) :
    β=1/(a+b) ∧ α=a*b/(a+b) := by
  have hs : a+b≠0 := (show 0<a+b by linarith).ne'
  have he : (b-a)*(β*(a+b)-1)=0 := by nlinarith only [h₁,h₂]
  have hβ := (mul_eq_zero.mp he).resolve_left (sub_pos.mpr hab).ne'
  have hβ' : β=1/(a+b) := (eq_div_iff hs).2 (by linarith only [hβ])
  refine ⟨hβ',?_⟩
  rw [hβ'] at h₁
  apply (eq_div_iff hs).2
  field_simp at h₁
  nlinarith only [h₁]

lemma delaunay_slope_product {r p β k : ℝ} (hr : 0<r) (hβ : 0<β) (hk : 0<k)
    (hf : r/Real.sqrt (1+p^2)=β*(r^2+k)) :
    p*(p/Real.sqrt (1+p^2))=r/(β*(r^2+k))-β*(r^2+k)/r := by
  have hs : 0<Real.sqrt (1+p^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p^2 by positivity)
  have hu : 0<r^2+k := add_pos_of_nonneg_of_pos (sq_nonneg _) hk
  have he : r=β*(r^2+k)*Real.sqrt (1+p^2) := (div_eq_iff hs.ne').mp hf
  have he₁ : r/(β*(r^2+k))=Real.sqrt (1+p^2) := (div_eq_iff (mul_pos hβ hu).ne').2 (by linarith only [he])
  have he₂ : β*(r^2+k)/r=1/Real.sqrt (1+p^2) := by
    rw [eq_div_iff hs.ne',div_mul_eq_mul_div,div_eq_one_iff_eq hr.ne']
    exact he.symm
  rw [he₁,he₂]
  field_simp
  nlinarith only [hs2]

lemma hasDerivAt_delaunay_slope {r p q : ℝ → ℝ} {β k t : ℝ}
    (hp : HasDerivAt p (q t) t) (hr : 0<r t)
    (hf : r t/Real.sqrt (1+p t^2)=β*(r t^2+k))
    (hCMC : 2*β=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3) :
    HasDerivAt (fun s => p s/Real.sqrt (1+p s^2)) (β*(k/r t^2-1)) t := by
  have hs0 : 0<Real.sqrt (1+p t^2) := Real.sqrt_pos.mpr (by positivity)
  have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
  have hd := ((hasDerivAt_const t (1 : ℝ)).add (hp.pow 2)).sqrt (by positivity : 1+p t^2≠0)
  have he := hp.div hd hs0.ne'
  convert! he using 1
  simp only [Pi.add_apply,Pi.pow_apply,Nat.reduceSub,zero_add,Nat.cast_ofNat,pow_one]
  have hsimp : (q t*Real.sqrt (1+p t^2)-p t*(2*p t*q t/(2*Real.sqrt (1+p t^2)))) /
      (Real.sqrt (1+p t^2))^2 = q t/(Real.sqrt (1+p t^2))^3 := by
    field_simp
    nlinarith only [congrArg (fun z : ℝ => q t*z) hs2]
  rw [hsimp]
  have hu : 1/(r t*Real.sqrt (1+p t^2))=β*(r t^2+k)/r t^2 := by
    rw [← hf]
    field_simp
  have ht : β*(k/r t^2-1)=1/(r t*Real.sqrt (1+p t^2))-2*β := by
    rw [hu]
    field_simp
    ring
  linarith only [ht,hCMC]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_const_of_sq_eq_one {f : ℝ → ℝ} (hc : Continuous f)
    (hf : ∀ t,f t^2=1) : ∀ t,f t=f 0 := by
  have hnot (a b : ℝ) (ha : f a = -1) (hb : f b=1) : False := by
    obtain ⟨z,hz⟩ := intermediate_value_univ a b hc
      (show (0 : ℝ)∈Icc (f a) (f b) by rw [ha,hb]; constructor <;> norm_num)
    have h := hf z
    rw [hz] at h
    norm_num at h
  intro t
  rcases sq_eq_one_iff.mp (hf t) with ht|ht <;>
    rcases sq_eq_one_iff.mp (hf 0) with h0|h0
  · exact ht.trans h0.symm
  · exact (hnot 0 t h0 ht).elim
  · exact (hnot t 0 ht h0).elim
  · exact ht.trans h0.symm

theorem revolution_classical_CMC {c : Cover} {r p q : ℝ → ℝ} {H : ℝ}
    (hr : ∀ t,HasDerivAt r (p t) t) (hp : ∀ t,HasDerivAt p (q t) t)
    (hpos : ∀ t,0<r t) {N : Cover → Cover} (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (htan : ∀ t a,
      N (revolutionPoint c r t a) 0+p t*⟪N (revolutionPoint c r t a),coordinatePlaneLift (unitAngle a)⟫=0 ∧
      (unitAngle a).re*N (revolutionPoint c r t a) 2-
        (unitAngle a).im*N (revolutionPoint c r t a) 1=0)
    (hunit : ∀ t,∀ᶠ y in 𝓝 (revolutionPoint c r t 0),‖N y‖=1)
    (hnormal : ∀ t,let n := N (revolutionPoint c r t 0)
      n 2=0 ∧ n 0= -(p t)*n 1 ∧ (n 1)^2*(1+p t^2)=1 ∧ n 1≠0)
    (hCMC : ∀ t,divergence N (revolutionPoint c r t 0)=H) :
    ∃ σ : ℝ,σ^2=1 ∧
      (∀ t,N (revolutionPoint c r t 0) 1=σ/Real.sqrt (1+p t^2)) ∧
      ∀ t,H/σ=1/(r t*Real.sqrt (1+p t^2))-q t/(Real.sqrt (1+p t^2))^3 := by
  let f := fun t => N (revolutionPoint c r t 0) 1*Real.sqrt (1+p t^2)
  have hpc : Continuous p := continuous_iff_continuousAt.mpr fun t => (hp t).continuousAt
  have hrc : Continuous (fun t => revolutionPoint c r t 0) :=
    continuous_iff_continuousAt.mpr fun t => (revolutionPoint_zero_meridian_deriv (hr t)).continuousAt
  have hfc : Continuous f :=
    ((EuclideanSpace.proj 1 : Cover →L[ℝ] ℝ).continuous.comp (hN.continuous.comp hrc)).mul
      ((continuous_const.add (hpc.pow 2)).sqrt)
  have hf (t : ℝ) : f t^2=1 := by
    dsimp [f]
    rw [mul_pow,Real.sq_sqrt (by positivity)]
    exact (hnormal t).2.2.1
  have he := continuous_const_of_sq_eq_one hfc hf
  have hs0 (t : ℝ) : 0<Real.sqrt (1+p t^2) := Real.sqrt_pos.mpr (by positivity)
  have hn (t : ℝ) : N (revolutionPoint c r t 0) 1=f 0/Real.sqrt (1+p t^2) :=
    (eq_div_iff (hs0 t).ne').2 (he t)
  refine ⟨f 0,hf 0,hn,?_⟩
  intro t
  have hσ : f 0≠0 := by intro hz; have hh := hf 0; rw [hz] at hh; norm_num at hh
  have hdiv := revolution_normal_divergence hr hp hpos hN htan hunit hnormal t
  rw [hCMC t,hn t] at hdiv
  rw [hdiv]
  have hs2 := Real.sq_sqrt (show 0≤1+p t^2 by positivity)
  field_simp [hσ,(hpos t).ne',(hs0 t).ne',show 1+p t^2≠0 by positivity]
  nlinarith only [congrArg (fun x : ℝ => q t*r t*x) hs2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem TrueRadialTube.exists_revolution_CMC {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (htube : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    let R := fun t => r (t,0)
    ∃ (μ : FiniteMeasure NormalBundle) (H σ : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (_hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0 ≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      σ^2=1 ∧
      (∀ t,N (revolutionPoint c R t 0) 1=σ/Real.sqrt (1+(deriv R t)^2)) ∧
      (∀ t,H/σ=1/(R t*Real.sqrt (1+(deriv R t)^2))-
        deriv (deriv R) t/(Real.sqrt (1+(deriv R t)^2))^3) ∧
      ∃ α : ℝ,∀ t,R t/Real.sqrt (1+(deriv R t)^2)=α+(H/σ)/2*R t^2 := by
  dsimp only
  let R := fun t => r (t,0)
  have hR : ContDiff ℝ (⊤ : ℕ∞) R := htube.1.comp (contDiff_id.prodMk contDiff_const)
  have hP : ContDiff ℝ (⊤ : ℕ∞) (deriv R) := (contDiff_infty_iff_deriv.mp hR).2
  have hd (t) : HasDerivAt R (deriv R t) t := (hR.differentiable (by simp) t).hasDerivAt
  have hd' (t) : HasDerivAt (deriv R) (deriv (deriv R) t) t :=
    (hP.differentiable (by simp) t).hasDerivAt
  have hpos (t) : 0<R t := (htube.2.2.2.1 (t,0)).1
  have hb (t a) : quotientMap (revolutionPoint c R t a)∈frontier (openRepresentative E) := by
    have h := htube.2.2.2.2.1 (t,a)
    simpa only [hangle t a,revolutionPoint,R] using h
  obtain ⟨μ,H,N,hN,hp,hμ,ha,hu,hcmc,hstab,hj⟩ := Periodic.isMinimizerAt_full_jacobi_system hV hE hm
  have htan := isMinimizerAt_revolution_tangents hV hE hm hμ hN hp ha hd hpos hb
  have hn := isMinimizerAt_revolution_meridian_normal hV hE hm hμ hN hp ha hd hpos hb
  obtain ⟨σ,hσ,hsign,hode⟩ := revolution_classical_CMC hd hd' hpos hN htan
    (fun t => (hu _ (hb t 0)).1) hn (fun t => (hu _ (hb t 0)).2)
  exact ⟨μ,H,σ,N,hN,hp,hμ,ha,hu,hstab,hσ,hsign,hode,delaunay_first_integral hd hd' hpos hode⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

def axisRadialField (c : Cover) (α β g : ℝ → ℝ) (x : Cover) : Cover :=
  α (x 0) • EuclideanSpace.single 0 1+
    (β (x 0)*g (x 1-c 1)) • EuclideanSpace.single 1 1+
    (β (x 0)*g (x 2-c 2)) • EuclideanSpace.single 2 1

lemma axisRadialField_contDiff (c : Cover) {α β g : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (axisRadialField c α β g) := by
  have hx (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x : Cover => x i) :=
    (EuclideanSpace.proj i : Cover →L[ℝ] ℝ).contDiff
  exact (((hα.comp (hx 0)).smul contDiff_const).add
    (((hβ.comp (hx 0)).mul (hg.comp ((hx 1).sub contDiff_const))).smul contDiff_const)).add
    (((hβ.comp (hx 0)).mul (hg.comp ((hx 2).sub contDiff_const))).smul contDiff_const)

lemma axisRadialField_periodic (c : Cover) {α β g : ℝ → ℝ}
    (hα : Function.Periodic α 1) (hβ : Function.Periodic β 1)
    (hg : Function.Periodic g 1) :
    ∀ m x,axisRadialField c α β g (x+latticeVector m)=axisRadialField c α β g x := by
  intro m x
  have ha : α (x 0+(m 0 : ℝ))=α (x 0) := by simpa using hα.int_mul (m 0) (x 0)
  have hb : β (x 0+(m 0 : ℝ))=β (x 0) := by simpa using hβ.int_mul (m 0) (x 0)
  have he (i : Fin 3) : g (x i+(m i : ℝ)-c i)=g (x i-c i) := by
    convert hg.int_mul (m i) (x i-c i) using 1; congr 1; ring
  simp only [axisRadialField,PiLp.add_apply,latticeVector,ha,hb,he]

lemma divergence_axisRadialField (c x : Cover) {α β g : ℝ → ℝ}
    (hα : Differentiable ℝ α) (hβ : Differentiable ℝ β) (hg : Differentiable ℝ g) :
    divergence (axisRadialField c α β g) x=
      deriv α (x 0)+β (x 0)*(deriv g (x 1-c 1)+deriv g (x 2-c 2)) := by
  have hd (f : ℝ → ℝ) (hf : Differentiable ℝ f) (i : Fin 3) (d : ℝ) :
      HasFDerivAt (fun y : Cover => f (y i-d))
        ((deriv f (x i-d)) • (EuclideanSpace.proj i : Cover →L[ℝ] ℝ)) x := by
    convert! (hf (x i-d)).hasDerivAt.hasFDerivAt.comp x
      (((EuclideanSpace.proj i : Cover →L[ℝ] ℝ).hasFDerivAt).sub_const d) using 1
    ext y
    simp [mul_comm]
  have ha := hd α hα 0 0
  have hb := hd β hβ 0 0
  simp only [sub_zero] at ha hb
  have h₁ := hb.mul (hd g hg 1 (c 1))
  have h₂ := hb.mul (hd g hg 2 (c 2))
  have htot := ((ha.smul_const (EuclideanSpace.single 0 1 : Cover)).add
    (h₁.smul_const (EuclideanSpace.single 1 1 : Cover))).add
      (h₂.smul_const (EuclideanSpace.single 2 1 : Cover))
  change HasFDerivAt (axisRadialField c α β g) _ x at htot
  unfold divergence
  rw [htot.fderiv]
  simp [Fin.sum_univ_succ,EuclideanSpace.proj]
  ring

@[simp] lemma axisRadialField_zero (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 0=α (x 0) := by simp [axisRadialField]
@[simp] lemma axisRadialField_one (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 1=β (x 0)*g (x 1-c 1) := by simp [axisRadialField]
@[simp] lemma axisRadialField_two (c x : Cover) (α β g : ℝ → ℝ) :
    axisRadialField c α β g x 2=β (x 0)*g (x 2-c 2) := by simp [axisRadialField]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.revolution_section {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) (t : ℝ) :
    centeredPlaneSection (openRepresentative E) c t={z : ℂ | ‖z‖<r (t,0)} := by
  have he := planarRadialRegion_eq_actual_section
    (fun a => (hr.2.2.2.1 (t,a)).1) (fun a => (hr.2.2.2.1 (t,a)).2)
    (fun a u hu hub => hr.2.2.2.2.2.1 (t,a) u hu hub)
  rw [← he]
  ext z
  simp only [planarRadialRegion,mem_ofPred_eq,hangle]

lemma TrueRadialTube.revolution_section_volume {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) (t : ℝ) :
    volume.real (centeredPlaneSection (openRepresentative E) c t)=Real.pi*r (t,0)^2 := by
  have he := planarRadialRegion_eq_actual_section
    (fun a => (hr.2.2.2.1 (t,a)).1) (fun a => (hr.2.2.2.1 (t,a)).2)
    (fun a u hu hub => hr.2.2.2.2.2.1 (t,a) u hu hub)
  rw [← he,real_volume_planarRadialRegion
    (show Continuous (fun a => r (t,a)) from hr.1.continuous.comp (continuous_const.prodMk continuous_id)) (hr.2.2.1 t)
      (fun a => (hr.2.2.2.1 (t,a)).1)]
  simp only [hangle,intervalIntegral.integral_const,sub_zero,one_smul]

lemma TrueRadialTube.revolution_radius_bound {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (_hangle : ∀ t a,r (t,a)=r (t,0)) :
    ∃ R : ℝ,0≤R ∧ R<1/2 ∧ ∀ t,r (t,0)≤R := by
  obtain ⟨R,hR,hRb,hb⟩ := hr.uniform_square_gap
  refine ⟨R,hR,hRb,fun t => ?_⟩
  have h := hb (t,0)
  have hp := (hr.2.2.2.1 (t,0)).1
  exact (by simpa [unitAngle_zero,complexSquareGauge,abs_of_pos hp] using h : r (t,0)≤R ∧ 0≤R).1

theorem TrueRadialTube.revolution_volume {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {c : Cover} {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) :
    V=Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)^2) := by
  have hU := (isOpen_openRepresentative E).measurableSet
  have hs (t) : axialSectionArea (openRepresentative E) 0 t=Real.pi*r (t,0)^2 := by
    rw [← centeredPlaneSection_real_volume hU c t]
    exact hr.revolution_section_volume hangle t
  have hInt := integral_axialSectionArea hU 0
  simp_rw [hs] at hInt
  rw [integral_const_mul] at hInt
  have hv : torusVolume.real (openRepresentative E)=V := by
    rw [Measure.real,measure_congr (isMinimizerAt_openRepresentative_ae hV hE hm),hm.2.1,
      ENNReal.toReal_ofReal hV.1.le]
  rw [hv] at hInt
  rw [integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)] at hInt
  exact hInt.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_boundary_flux_le {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hm : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    {F : Cover → Cover} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hp : ∀ m x,F (x+latticeVector m)=F x)
    (hb : ∀ x,quotientMap x∈frontier (openRepresentative E) → ‖F x‖≤1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' E,divergence F x)≤(perimeter E).toReal := by
  obtain ⟨C,hC0,hC⟩ := periodic_bounded hF.continuous hp
  rw [← normalMeasure_flux hμ hF hp (show 0<C+1 by linarith)
    (fun x => (hC x).trans (by linarith : C≤C+1))]
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hm).symm)
  calc
    _ ≤ ∫ _z : NormalBundle,(1 : ℝ) ∂(μ : Measure NormalBundle) := by
      apply integral_mono_ae
        ((normalTest F hF.continuous).continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) (integrable_const _)
      filter_upwards [hbd] with z hz
      calc
        _ ≤ ‖(z.2 : Cover)‖*‖F z.1‖ := real_inner_le_norm _ _
        _ ≤ 1 := by simpa only [z.2.property,one_mul] using hb z.1 hz
    _ = (perimeter E).toReal := by
      rw [integral_const,smul_eq_mul,mul_one,Measure.real,← FiniteMeasure.ennreal_mass,ENNReal.coe_toReal,hμ.1]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma TrueRadialTube.axisRadialField_boundary_bound {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) {α β g : ℝ → ℝ}
    (hα : Function.Periodic α 1) (hβ : Function.Periodic β 1)
    (hg : Function.Periodic g 1)
    (he : ∀ t a,g (r (t,0)*(unitAngle a).re)=r (t,0)*(unitAngle a).re ∧
      g (r (t,0)*(unitAngle a).im)=r (t,0)*(unitAngle a).im)
    (hb : ∀ t,α t^2+(β t*r (t,0))^2≤1) :
    ∀ x,quotientMap x∈frontier (openRepresentative E) →
      ‖axisRadialField c α β g x‖≤1 := by
  intro x hx
  rw [← hr.boundary_range] at hx
  obtain ⟨p,hpx⟩ := hx
  obtain ⟨m,hm⟩ := same_quotient_lattice hpx.symm
  rw [hm,axisRadialField_periodic c hα hβ hg]
  have hn := congrArg (fun z : ℝ => z^2) (unitAngle_norm p.2)
  rw [Complex.sq_norm] at hn
  simp only [Complex.normSq_apply,one_pow] at hn
  have hsq : ‖axisRadialField c α β g
      (coordinateSectionPoint c p.1 (r p • unitAngle p.2))‖^2≤1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_three]
    simp only [axisRadialField_zero,axisRadialField_one,axisRadialField_two,
      coordinateSectionPoint_apply]
    simp only [reduceIte,Fin.isValue,show (1 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false,
      Complex.smul_re,Complex.smul_im,smul_eq_mul,add_sub_cancel_left]
    rw [show r p=r (p.1,0) from hangle p.1 p.2,(he p.1 p.2).1,(he p.1 p.2).2]
    have hid : (β p.1*(r (p.1,0)*(unitAngle p.2).re))^2+
        (β p.1*(r (p.1,0)*(unitAngle p.2).im))^2=
        (β p.1*r (p.1,0))^2*((unitAngle p.2).re*(unitAngle p.2).re+
          (unitAngle p.2).im*(unitAngle p.2).im) := by ring
    rw [hn,mul_one] at hid
    linarith only [hb p.1,hid]
  nlinarith only [hsq,norm_nonneg (axisRadialField c α β g
    (coordinateSectionPoint c p.1 (r p • unitAngle p.2)))]

theorem TrueRadialTube.axisRadialField_flux {E : Set Torus} {c : Cover}
    {r : ℝ × ℝ → ℝ} (hr : TrueRadialTube E c r)
    (hangle : ∀ t a,r (t,a)=r (t,0)) {α β g : ℝ → ℝ}
    (hα : ContDiff ℝ (⊤ : ℕ∞) α) (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpα : Function.Periodic α 1) (hpβ : Function.Periodic β 1)
    (hpg : Function.Periodic g 1)
    (he : ∀ t y,|y|<r (t,0) → deriv g y=1) :
    (∫ x in fundamentalCube∩quotientMap ⁻¹' openRepresentative E,
      divergence (axisRadialField c α β g) x)=
      Real.pi*(∫ t in (0 : ℝ)..1,r (t,0)^2*(deriv α t+2*β t)) := by
  have hF := axisRadialField_contDiff c hα hβ hg
  have hFp := axisRadialField_periodic c hpα hpβ hpg
  have hU := (isOpen_openRepresentative E).measurableSet
  rw [axial_weighted_section_fubini hU 0 (continuous_divergence hF) (divergence_periodic hFp)]
  have hh (t : ℝ) : axialSectionIntegral (openRepresentative E) 0
      (divergence (axisRadialField c α β g)) t=
      Real.pi*(r (t,0)^2*(deriv α t+2*β t)) := by
    rw [← centeredPlaneSection_integral hU (continuous_divergence hF) (divergence_periodic hFp) c]
    have hs : (∫ z in centeredPlaneSection (openRepresentative E) c t,
        divergence (axisRadialField c α β g) (coordinateSectionPoint c t z))=
        ∫ _z in centeredPlaneSection (openRepresentative E) c t,(deriv α t+2*β t) := by
      apply setIntegral_congr_fun (show MeasurableSet (centeredPlaneSection (openRepresentative E) c t) from by
        rw [hr.revolution_section hangle]
        exact (isOpen_lt continuous_norm continuous_const).measurableSet)
      intro z hz
      rw [hr.revolution_section hangle] at hz
      have hz' : ‖z‖<r (t,0) := hz
      change divergence (axisRadialField c α β g) (coordinateSectionPoint c t z)=_
      rw [divergence_axisRadialField c _ (hα.differentiable (by simp))
        (hβ.differentiable (by simp)) (hg.differentiable (by simp))]
      simp only [coordinateSectionPoint_apply]
      simp only [reduceIte,Fin.isValue,show (1 : Fin 3)≠0 by decide,
      show (2 : Fin 3)≠0 by decide,show (2 : Fin 3)≠1 by decide,ite_false,add_sub_cancel_left]
      rw [he t z.re ((Complex.abs_re_le_norm z).trans_lt hz'),
        he t z.im ((Complex.abs_im_le_norm z).trans_lt hz')]
      ring
    rw [hs,integral_const,smul_eq_mul]
    simp only [Measure.real,Measure.restrict_apply_univ]
    rw [← Measure.real_def,hr.revolution_section_volume hangle]
    ring
  simp_rw [hh]
  rw [integral_const_mul,integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ)≤1)]

end CubicTorus

end
end

end OAI
