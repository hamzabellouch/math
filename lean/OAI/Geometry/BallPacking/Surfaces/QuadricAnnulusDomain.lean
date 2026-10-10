import Mathlib
import OAI.Geometry.BallPacking.Surfaces.QuadricCurveManifold

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Topology
open Set Function Filter
open scoped Manifold
open Manifold
variable (m : ℕ)

theorem plus_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ plus s :=
  (contDiffAt_id.add (contDiffAt_id.inv hs)).div_const 2

theorem minus_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ minus s :=
  (contDiffAt_id.sub (contDiffAt_id.inv hs)).div_const 2

theorem baseSquare_contDiffAt {s : ℂ} (hs : s≠0) : ContDiffAt ℂ ∞ baseSquare s :=
  contDiffAt_const.add ((plus_contDiffAt hs).pow 2)

theorem annulusDomain_isOpen : IsOpen (annulusDomain m) := by
  rw [isOpen_iff_mem_nhds]
  intro s hs
  have hc := (baseSquare_contDiffAt hs.1).continuousAt
  have hz : ∀ᶠ t in 𝓝 s,t≠0 := isOpen_compl_singleton.mem_nhds hs.1
  have hb : ∀ᶠ t in 𝓝 s,0<(baseSquare t).re :=
    (Complex.continuous_re.continuousAt.comp hc).eventually (Ioi_mem_nhds hs.2.1)
  have hj : ∀ j : Fin (m+2),∀ᶠ t in 𝓝 s,1<j.val → 0<(parameters m j-baseSquare t).re := by
    intro j
    by_cases h : 1<j.val
    · exact ((Complex.continuous_re.continuousAt.comp (continuousAt_const.sub hc)).eventually
        (Ioi_mem_nhds (hs.2.2 j h))).mono (fun _ ht _ => ht)
    · exact Filter.Eventually.of_forall (fun _ ht => (h ht).elim)
  filter_upwards [hz,hb,Filter.eventually_all.mpr hj] with t ht0 htb htj
  exact ⟨ht0,htb,htj⟩

theorem unitCircle_subset_domain {s : ℂ} (hs : ‖s‖=1) : s∈annulusDomain m := by
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hp : plus s=(s.re : ℂ) := by
    rw [plus,Complex.inv_eq_conj hs,Complex.add_conj]
    push_cast
    ring
  have hb : (baseSquare s).re=1+s.re^2 := by simp [baseSquare,hp,← Complex.ofReal_pow]
  have hn : s.re^2≤1 := by
    have he := Complex.normSq_eq_norm_sq s
    rw [hs,one_pow] at he
    simp only [Complex.normSq_apply] at he
    nlinarith [sq_nonneg s.im]
  refine ⟨hs0,?_,?_⟩
  · rw [hb]; positivity
  · intro j hj
    have hj' : (2 : ℝ)≤j.val := by exact_mod_cast hj
    simp only [parameters,Complex.sub_re,Complex.add_re,Complex.natCast_re,Complex.one_re,hb]
    linarith

theorem annulusPoint_contDiffAt {s : ℂ} (hs : s∈annulusDomain m) :
    ContDiffAt ℂ ∞ (annulusPoint m) s := by
  apply ContDiffAt.prodMk
  · exact (sqrt_contDiffAt hs.2.1).comp s (baseSquare_contDiffAt hs.1)
  · apply contDiffAt_pi.mpr
    intro j
    by_cases hj0 : j=0
    · subst j
      simpa using plus_contDiffAt hs.1
    by_cases hj1 : j=1
    · subst j
      have hn : (1 : Fin (m+2))≠0 := by simp
      simpa only [ite_eq_right hn,ite_true] using minus_contDiffAt hs.1
    · have hj : 1<j.val := by
        have h0 : j.val≠0 := fun h => hj0 (Fin.ext h)
        have h1 : j.val≠1 := fun h => hj1 (Fin.ext (by simpa using h))
        omega
      have hb : ContDiffAt ℂ ∞ (fun t : ℂ => parameters m j-baseSquare t) s :=
        contDiffAt_const.sub (baseSquare_contDiffAt hs.1)
      have hr := (sqrt_contDiffAt (hs.2.2 j hj)).comp s hb
      have hh : ContDiffAt ℂ ∞ (fun t => Complex.I*Complex.sqrt (parameters m j-baseSquare t)) s :=
        contDiffAt_const.mul hr
      simpa only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1] using hh

def annulusCoordinate : Affine (m+2) →L[ℂ] ℂ :=
  ((ContinuousLinearMap.proj 0).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))+
  ((ContinuousLinearMap.proj 1).comp (ContinuousLinearMap.snd ℂ ℂ (Fin (m+2) → ℂ)))

@[simp] theorem annulusCoordinate_apply (x : Affine (m+2)) : annulusCoordinate m x=x.2 0+x.2 1 := rfl

@[simp] theorem annulusCoordinate_point (s : ℂ) : annulusCoordinate m (annulusPoint m s)=s := by
  simp

theorem annulusCoordinate_mul {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    annulusCoordinate m x*(x.2 0-x.2 1)=1 := by
  have h0 := mem_locus.mp hx 0
  have h1 := mem_locus.mp hx 1
  simp only [parameters_zero,parameters_one] at h0 h1
  change (x.2 0+x.2 1)*(x.2 0-x.2 1)=1
  linear_combination h0-h1

theorem annulusCoordinate_ne_zero {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    annulusCoordinate m x≠0 := by
  intro h
  have he := annulusCoordinate_mul m hx
  rw [h,zero_mul] at he
  exact zero_ne_one he

theorem inverse_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    (annulusCoordinate m x)⁻¹=x.2 0-x.2 1 := by
  apply mul_left_cancel₀ (annulusCoordinate_ne_zero m hx)
  rw [mul_inv_cancel₀ (annulusCoordinate_ne_zero m hx),annulusCoordinate_mul m hx]

theorem plus_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    plus (annulusCoordinate m x)=x.2 0 := by
  rw [plus,inverse_coordinate m hx,annulusCoordinate_apply]
  ring

theorem minus_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    minus (annulusCoordinate m x)=x.2 1 := by
  rw [minus,inverse_coordinate m hx,annulusCoordinate_apply]
  ring

theorem baseSquare_coordinate {x : Affine (m+2)} (hx : x∈locus (parameters m)) :
    baseSquare (annulusCoordinate m x)=x.1^2 := by
  have h0 := mem_locus.mp hx 0
  rw [baseSquare,plus_coordinate m hx]
  simp only [parameters_zero] at h0
  linear_combination h0

abbrev Surface := locus (parameters m)

def annulusBranch : Set (Surface m) := {x | annulusCoordinate m x.val∈annulusDomain m ∧
  0<x.val.1.re ∧ ∀ j : Fin (m+2),1<j.val → 0<(x.val.2 j).im}

theorem annulusPoint_positive {s : ℂ} (hs : s∈annulusDomain m) :
    0<(annulusPoint m s).1.re ∧
    ∀ j : Fin (m+2),1<j.val → 0<((annulusPoint m s).2 j).im := by
  refine ⟨sqrt_re_pos hs.2.1,?_⟩
  intro j hj
  have hj0 : j≠0 := by intro h; subst j; simp at hj
  have hj1 : j≠1 := by intro h; subst j; simp at hj
  simpa only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,Complex.mul_im,
    Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add] using sqrt_re_pos (hs.2.2 j hj)

theorem annulusPoint_coordinate {x : Surface m} (hx : x∈annulusBranch m) :
    annulusPoint m (annulusCoordinate m x.val)=x.val := by
  apply Prod.ext
  · change Complex.sqrt (baseSquare (annulusCoordinate m x.val))=x.val.1
    rw [baseSquare_coordinate m x.property]
    exact sqrt_of_sq_pos hx.2.1
  · funext j
    by_cases hj0 : j=0
    · subst j
      exact (annulusPoint_zero m _).trans (plus_coordinate m x.property)
    by_cases hj1 : j=1
    · subst j
      exact (annulusPoint_one m _).trans (minus_coordinate m x.property)
    · have hj : 1<j.val := by
        have h0 : j.val≠0 := fun h => hj0 (Fin.ext h)
        have h1 : j.val≠1 := fun h => hj1 (Fin.ext (by simpa using h))
        omega
      have hp : 0<(-Complex.I*x.val.2 j).re := by
        simpa only [Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,
          Complex.I_im,neg_zero,zero_mul,neg_mul,one_mul,zero_sub,neg_neg] using hx.2.2 j hj
      have he : parameters m j-baseSquare (annulusCoordinate m x.val)=(-Complex.I*x.val.2 j)^2 := by
        rw [baseSquare_coordinate m x.property,mul_pow,neg_pow,Complex.I_sq]
        have hjx := mem_locus.mp x.property j
        linear_combination hjx
      simp only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,he,sqrt_of_sq_pos hp]
      rw [← mul_assoc]
      simp

def annulusBasepoint : Surface m := ⟨annulusPoint m 1,annulusPoint_mem m one_ne_zero⟩

def annulusInverse (s : ℂ) : Surface m := by
  classical
  exact if h : s≠0 then ⟨annulusPoint m s,annulusPoint_mem m h⟩ else annulusBasepoint m

@[simp] theorem annulusInverse_val {s : ℂ} (hs : s≠0) :
    (annulusInverse m s).val=annulusPoint m s := by
  simp only [annulusInverse,dite_eq_left hs]

theorem annulusBranch_isOpen : IsOpen (annulusBranch m) := by
  have hc : Continuous (fun x : Surface m => annulusCoordinate m x.val) :=
    (annulusCoordinate m).continuous.comp continuous_subtype_val
  have ht : Continuous (fun x : Surface m => x.val.1.re) :=
    Complex.continuous_re.comp (continuous_fst.comp continuous_subtype_val)
  have hw : ∀ j : Fin (m+2),Continuous (fun x : Surface m => (x.val.2 j).im) :=
    fun j => Complex.continuous_im.comp
      ((continuous_apply j).comp (continuous_snd.comp continuous_subtype_val))
  change IsOpen ((fun x : Surface m => annulusCoordinate m x.val) ⁻¹' annulusDomain m ∩
    ({x : Surface m | 0<x.val.1.re} ∩ {x : Surface m | ∀ j,1<j.val → 0<(x.val.2 j).im}))
  refine ((annulusDomain_isOpen m).preimage hc).inter ((isOpen_lt continuous_const ht).inter ?_)
  simp only [ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (hw j)

def annulusChart : OpenPartialHomeomorph (Surface m) ℂ where
  toFun x := annulusCoordinate m x.val
  invFun := annulusInverse m
  source := annulusBranch m
  target := annulusDomain m
  map_source' _ hx := hx.1
  map_target' s hs := by
    refine ⟨?_,?_⟩
    · rw [annulusInverse_val m hs.1,annulusCoordinate_point]
      exact hs
    · rw [annulusInverse_val m hs.1]
      exact annulusPoint_positive m hs
  left_inv' x hx := by
    apply Subtype.ext
    rw [annulusInverse_val m hx.1.1]
    exact annulusPoint_coordinate m hx
  right_inv' s hs := by
    rw [annulusInverse_val m hs.1,annulusCoordinate_point]
  open_source := annulusBranch_isOpen m
  open_target := annulusDomain_isOpen m
  continuousOn_toFun := ((annulusCoordinate m).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc : ContinuousOn (annulusPoint m) (annulusDomain m) :=
      fun s hs => (annulusPoint_contDiffAt m hs).continuousAt.continuousWithinAt
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr fun s => (annulusInverse_val m s.property.1).symm

@[simp] theorem annulusChart_apply (x : Surface m) : annulusChart m x=annulusCoordinate m x.val := rfl
@[simp] theorem annulusChart_source : (annulusChart m).source=annulusBranch m := rfl
@[simp] theorem annulusChart_target : (annulusChart m).target=annulusDomain m := rfl

end PackingSufficiencySupport.DiagonalQuadrics.Explicit

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit

abbrev PlaneBase := ℂ × ℂ
abbrev BaseCurve := Surface 0

 def polynomial (z : PlaneBase) : ℂ := z.1*z.2*(z.1-z.2)+z.2-2*z.1
 def homogeneous (u v w : ℂ) : ℂ := v*w*(v-w)+u^2*(w-2*v)
 def projection (z : Affine 2) : PlaneBase := (z.2 0-z.1,z.2 1-z.1)
 def inclusion (x : BaseCurve) : PlaneBase := projection x.val

 theorem polynomial_contDiff : ContDiff ℂ ∞ polynomial := by
  unfold polynomial
  fun_prop

 theorem projection_contDiff : ContDiff ℂ ∞ projection := by
  exact (((contDiff_apply ℂ ℂ 0).comp contDiff_snd).sub contDiff_fst).prodMk
    (((contDiff_apply ℂ ℂ 1).comp contDiff_snd).sub contDiff_fst)

 theorem source_equation_zero (x : BaseCurve) : (x.val.2 0)^2=x.val.1^2-1 := by
  simpa only [parameters_zero] using (mem_locus.mp x.property) 0
 theorem source_equation_one (x : BaseCurve) : (x.val.2 1)^2=x.val.1^2-2 := by
  simpa only [parameters_one] using (mem_locus.mp x.property) 1

 theorem inclusion_polynomial (x : BaseCurve) : polynomial (inclusion x)=0 := by
  have h0 := source_equation_zero x
  have h1 := source_equation_one x
  dsimp [polynomial,inclusion,projection]
  linear_combination (x.val.2 1-x.val.1)*h0-(x.val.2 0-x.val.1)*h1

 theorem inclusion_fst_ne_zero (x : BaseCurve) : (inclusion x).1≠0 := by
  intro h
  have he : x.val.2 0=x.val.1 := sub_eq_zero.mp h
  have h0 := source_equation_zero x
  rw [he] at h0
  have hh : (1:ℂ)=0 := by linear_combination h0
  exact one_ne_zero hh

 theorem inclusion_snd_ne_zero (x : BaseCurve) : (inclusion x).2≠0 := by
  intro h
  have he : x.val.2 1=x.val.1 := sub_eq_zero.mp h
  have h1 := source_equation_one x
  rw [he] at h1
  have hh : (1:ℂ)=0 := by linear_combination h1 / 2
  exact one_ne_zero hh

 def recovery (z : PlaneBase) : Affine 2 :=
  let t := -(z.1^2+1)/(2*z.1)
  (t,![t+z.1,t+z.2])

 theorem recovery_inclusion (x : BaseCurve) : recovery (inclusion x)=x.val := by
  have hv := inclusion_fst_ne_zero x
  have h0 := source_equation_zero x
  have ht : -((inclusion x).1^2+1)/(2*(inclusion x).1)=x.val.1 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hv)).mpr
    dsimp [inclusion,projection]
    linear_combination -h0
  apply Prod.ext
  · exact ht
  · funext j
    change ![-((inclusion x).1^2+1)/(2*(inclusion x).1)+(inclusion x).1,
      -((inclusion x).1^2+1)/(2*(inclusion x).1)+(inclusion x).2] j=x.val.2 j
    rw [ht]
    fin_cases j <;> simp [inclusion,projection]

 theorem inclusion_contMDiff : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,PlaneBase) ∞ inclusion :=
  projection_contDiff.contMDiff.comp (curve_inclusion_contMDiff (parameters 0))

 theorem recovery_contDiffOn : ContDiffOn ℂ ∞ recovery {z | z.1≠0} := by
  intro z hz
  have ht : ContDiffAt ℂ ∞ (fun z : PlaneBase => -(z.1^2+1)/(2*z.1)) z :=
    ((contDiffAt_fst.pow 2).add contDiffAt_const).neg.div
      (contDiffAt_const.mul contDiffAt_fst) (mul_ne_zero (by norm_num) hz)
  apply ContDiffAt.contDiffWithinAt
  apply ht.prodMk
  apply contDiffAt_pi.mpr
  intro j
  fin_cases j
  · exact ht.add contDiffAt_fst
  · exact ht.add contDiffAt_snd

 theorem inclusion_isEmbedding : Topology.IsEmbedding inclusion := by
  let f : BaseCurve → {z : PlaneBase // z.1≠0} := fun x => ⟨inclusion x,inclusion_fst_ne_zero x⟩
  have hf : Continuous f := inclusion_contMDiff.continuous.subtype_mk _
  have hR : Continuous (fun z : {z : PlaneBase // z.1≠0} => recovery z.val) :=
    recovery_contDiffOn.continuousOn.domRestrict
  have hcomp : (fun z : {z : PlaneBase // z.1≠0} => recovery z.val) ∘ f=
      (Subtype.val : BaseCurve → Affine 2) := funext recovery_inclusion
  have he := Topology.IsEmbedding.of_comp hf hR (hcomp ▸ Topology.IsEmbedding.subtypeVal)
  exact Topology.IsEmbedding.subtypeVal.comp he

 def gradV (z : PlaneBase) : ℂ := 2*z.1*z.2-z.2^2-2
 def gradW (z : PlaneBase) : ℂ := z.1^2-2*z.1*z.2+1
 def jacobian (z : PlaneBase) : PlaneBase →L[ℂ] ℂ :=
  gradV z • ContinuousLinearMap.fst ℂ ℂ ℂ+gradW z • ContinuousLinearMap.snd ℂ ℂ ℂ

 theorem polynomial_hasFDerivAt (z : PlaneBase) : HasFDerivAt polynomial (jacobian z) z := by
  have hv := hasFDerivAt_fst (𝕜 := ℂ) (p := z)
  have hw := hasFDerivAt_snd (𝕜 := ℂ) (p := z)
  have h := (((hv.mul hw).mul (hv.sub hw)).add hw).sub (hv.const_mul 2)
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  symm
  change (2*z.1*z.2-z.2^2-2)*v.1+(z.1^2-2*z.1*z.2+1)*v.2=
    z.1*z.2*(v.1-v.2)+(z.1-z.2)*(z.1*v.2+z.2*v.1)+v.2-2*v.1
  ring

 theorem gradient_nonzero {z : PlaneBase} (hz : polynomial z=0) : gradV z≠0 ∨ gradW z≠0 := by
  by_contra h
  push Not at h
  obtain ⟨hv,hw⟩ := h
  have he : z.2=2*z.1 := by
    dsimp [polynomial] at hz
    dsimp [gradV] at hv
    dsimp [gradW] at hw
    linear_combination (3*hz-z.1*hv-z.2*hw)/2
  have hv' : gradV z= -2 := by rw [gradV,he]; ring
  rw [hv'] at hv
  norm_num at hv

 theorem jacobian_surjective {z : PlaneBase} (hz : polynomial z=0) : Surjective (jacobian z) := by
  rcases gradient_nonzero hz with hv | hw
  · intro w
    refine ⟨(w/gradV z,0),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hv]
  · intro w
    refine ⟨(0,w/gradW z),?_⟩
    simp [jacobian,mul_div_cancel₀ _ hw]

 theorem marked_points : homogeneous 0 1 0=0 ∧ homogeneous 0 0 1=0 := by
  norm_num [homogeneous]

 theorem homogeneous_affine (v w : ℂ) : homogeneous 1 v w=polynomial (v,w) := by
  simp only [homogeneous,polynomial,one_pow,one_mul]
  ring

end PackingSufficiencySupport.CubicModel
end

end OAI
