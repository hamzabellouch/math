import Mathlib
import OAI.Geometry.Cannon.Model
import OAI.Geometry.Cannon.Conformal.AnalyticFixInftyAffine

namespace OAI

section
section
section
section
section
noncomputable section
namespace CannonH3
open CannonRelease Set Topology

abbrev Height := {t : ℝ // 0 < t}
abbrev Half := ℂ × Height

def coords : HyperbolicThree ≃ₜ Half where
  toFun x := ⟨⟨x.val 0,x.val 1⟩,⟨x.val 2,x.property⟩⟩
  invFun p := ⟨![p.1.re,p.1.im,p.2.val],p.2.property⟩
  left_inv x := by apply Subtype.ext; funext i; fin_cases i <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · have hc : Continuous (fun x : HyperbolicThree => (x.val 0:ℂ)+(x.val 1:ℂ)*Complex.I) :=
        (Complex.continuous_ofReal.comp ((continuous_apply 0).comp continuous_subtype_val)).add
          ((Complex.continuous_ofReal.comp ((continuous_apply 1).comp continuous_subtype_val)).mul continuous_const)
      convert hc using 1
      funext x
      exact (Complex.re_add_im _).symm
    · exact ((continuous_apply 2).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re.comp continuous_fst
    · exact Complex.continuous_im.comp continuous_fst
    · exact continuous_subtype_val.comp continuous_snd

def distArg (x y : Half) : ℝ :=
  1+(‖x.1-y.1‖^2+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)

lemma dist_coords (x y : HyperbolicThree) :
    hyperbolicDist x y=Real.arcosh (distArg (coords x) (coords y)) := by
  unfold hyperbolicDist distArg
  congr 1
  have he : ‖(coords x).1-(coords y).1‖^2=(x.val 0-y.val 0)^2+(x.val 1-y.val 1)^2 := by
    rw [Complex.sq_norm]
    change (x.val 0-y.val 0)*(x.val 0-y.val 0)+(x.val 1-y.val 1)*(x.val 1-y.val 1)=_
    ring
  rw [he]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  change 1+((x.val 0-y.val 0)^2+((x.val 1-y.val 1)^2+(x.val 2-y.val 2)^2))/(2*x.val 2*y.val 2)=
    1+(((x.val 0-y.val 0)^2+(x.val 1-y.val 1)^2)+(x.val 2-y.val 2)^2)/(2*x.val 2*y.val 2)
  ring

def lift (f : Half ≃ₜ Half) (hf : ∀ x y, distArg (f x) (f y)=distArg x y) : H3Isom :=
  ⟨(coords.trans f).trans coords.symm,by
    intro x y
    rw [dist_coords,dist_coords]
    simpa only [Homeomorph.trans_apply,Homeomorph.apply_symm_apply] using congrArg Real.arcosh (hf (coords x) (coords y))⟩

def heightScale (s : ℝ) (hs : 0 < s) : Height ≃ₜ Height where
  toFun t := ⟨s*t.val,mul_pos hs t.property⟩
  invFun t := ⟨t.val/s,div_pos t.property hs⟩
  left_inv t := by ext; exact mul_div_cancel_left₀ t.val hs.ne'
  right_inv t := by ext; exact mul_div_cancel₀ t.val hs.ne'
  continuous_toFun := (continuous_const.mul continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.div_const s).subtype_mk _

def complexAffine (a b : ℂ) (ha : a ≠ 0) : ℂ ≃ₜ ℂ where
  toFun z := a*z+b
  invFun z := (z-b)/a
  left_inv z := by simp [ha]
  right_inv z := by field_simp; ring
  continuous_toFun := (continuous_const.mul continuous_id).add continuous_const
  continuous_invFun := (continuous_id.sub continuous_const).div_const a

def affine (a b : ℂ) (ha : a ≠ 0) : Half ≃ₜ Half :=
  (complexAffine a b ha).prodCongr (heightScale ‖a‖ (norm_pos_iff.mpr ha))

lemma affine_preserves (a b : ℂ) (ha : a ≠ 0) (x y : Half) :
    distArg (affine a b ha x) (affine a b ha y)=distArg x y := by
  have he : a*x.1+b-(a*y.1+b)=a*(x.1-y.1) := by ring
  change 1+(‖a*x.1+b-(a*y.1+b)‖^2+(‖a‖*x.2.val-‖a‖*y.2.val)^2)/
    (2*(‖a‖*x.2.val)*(‖a‖*y.2.val))=distArg x y
  rw [he,norm_mul]
  unfold distArg
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  field_simp

def affineIsom (a b : ℂ) (ha : a ≠ 0) : H3Isom := lift (affine a b ha) (affine_preserves a b ha)

def q (x : Half) : ℝ := ‖x.1‖^2+x.2.val^2
lemma q_pos (x : Half) : 0 < q x := by
  have hh := x.2.property
  unfold q
  nlinarith [sq_nonneg ‖x.1‖]

def inversionFun (x : Half) : Half :=
  ⟨star x.1 / (q x:ℂ),⟨x.2.val/q x,div_pos x.2.property (q_pos x)⟩⟩

lemma inversion_q (x : Half) : q (inversionFun x)=(q x)⁻¹ := by
  change ‖star x.1/(q x:ℂ)‖^2+(x.2.val/q x)^2=(q x)⁻¹
  rw [norm_div,norm_star,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (q_pos x)]
  unfold q
  have hq := (q_pos x).ne'
  change ‖x.1‖^2+x.2.val^2 ≠ 0 at hq
  field_simp

lemma inversion_involutive : Function.Involutive inversionFun := by
  intro x
  apply Prod.ext
  · change star (star x.1/(q x:ℂ))/((q (inversionFun x)):ℂ)=x.1
    rw [inversion_q]
    simp [Complex.conj_ofReal,Complex.ofReal_inv,(q_pos x).ne']
  · apply Subtype.ext
    change (x.2.val/q x)/q (inversionFun x)=x.2.val
    rw [inversion_q]
    field_simp [(q_pos x).ne']

lemma continuous_q : Continuous q := by
  unfold q
  fun_prop

lemma continuous_inversion : Continuous inversionFun := by
  apply Continuous.prodMk
  · exact (continuous_star.comp continuous_fst).div
      (Complex.continuous_ofReal.comp continuous_q) (fun x => by exact_mod_cast (q_pos x).ne')
  · exact ((continuous_subtype_val.comp continuous_snd).div continuous_q (fun x => (q_pos x).ne')).subtype_mk _

def inversion : Half ≃ₜ Half where
  toFun := inversionFun
  invFun := inversionFun
  left_inv := inversion_involutive
  right_inv := inversion_involutive
  continuous_toFun := continuous_inversion
  continuous_invFun := continuous_inversion
end CannonH3

namespace CannonH3
lemma inversion_preserves (x y : Half) :
    distArg (inversion x) (inversion y)=distArg x y := by
  have hxq : q x ≠ 0 := (q_pos x).ne'
  have hyq : q y ≠ 0 := (q_pos y).ne'
  have hxt : x.2.val ≠ 0 := x.2.property.ne'
  have hyt : y.2.val ≠ 0 := y.2.property.ne'
  have heq : ‖(inversion x).1-(inversion y).1‖^2 =
    (x.1.re/q x-y.1.re/q y)^2+(-x.1.im/q x-(-y.1.im)/q y)^2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
    change ((star x.1/(q x:ℂ)).re-(star y.1/(q y:ℂ)).re)*
      ((star x.1/(q x:ℂ)).re-(star y.1/(q y:ℂ)).re)+
      ((star x.1/(q x:ℂ)).im-(star y.1/(q y:ℂ)).im)*
      ((star x.1/(q x:ℂ)).im-(star y.1/(q y:ℂ)).im)=_
    simp only [Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.star_def,Complex.conj_re,Complex.conj_im]
    ring
  unfold distArg
  rw [heq,Complex.sq_norm]
  change 1+(_+(x.2.val/q x-y.2.val/q y)^2)/(2*(x.2.val/q x)*(y.2.val/q y))=
    1+(Complex.normSq (x.1-y.1)+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)
  apply congrArg (fun t : ℝ => 1+t)
  apply (div_eq_div_iff (by positivity : 2*(x.2.val/q x)*(y.2.val/q y) ≠ 0)
    (by positivity : 2*x.2.val*y.2.val ≠ 0)).mpr
  field_simp
  unfold q
  rw [Complex.sq_norm,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  ring

def inversionIsom : CannonRelease.H3Isom := lift inversion inversion_preserves
end CannonH3

noncomputable section
open Set Filter Topology
open scoped OnePoint

namespace CannonH3
open Set Topology
open scoped OnePoint

abbrev Boundary := OnePoint ℂ

def potential (x : Half) (p : Boundary) : ℝ :=
  p.elim (1/x.2.val) (fun z => (‖x.1-z‖^2+x.2.val^2)/(x.2.val*(1+‖z‖^2)))

@[simp] lemma potential_infty (x : Half) : potential x ∞=1/x.2.val := rfl
@[simp] lemma potential_coe (x : Half) (z : ℂ) :
  potential x (z:Boundary)=(‖x.1-z‖^2+x.2.val^2)/(x.2.val*(1+‖z‖^2)) := rfl

lemma potential_pos (x : Half) (p : Boundary) : 0 < potential x p := by
  induction p using OnePoint.rec with
  | infty => exact one_div_pos.mpr x.2.property
  | coe z =>
    apply div_pos
    · nlinarith [sq_nonneg ‖x.1-z‖,x.2.property]
    · exact mul_pos x.2.property (by nlinarith [sq_nonneg ‖z‖])

def Compatible (f : Boundary ≃ₜ Boundary) (F : Half ≃ₜ Half) : Prop :=
  ∀ x y p, potential (F x) (f p)*potential y p=
    potential x p*potential (F y) (f p)

def quadratic (x : Half) (p : ℂ) : ℝ := ‖x.1-p‖^2+x.2.val^2
lemma quadratic_pos (x : Half) (p : ℂ) : 0 < quadratic x p := by
  unfold quadratic
  nlinarith [sq_nonneg ‖x.1-p‖,x.2.property]

lemma height_relation {F : Half ≃ₜ Half} (hF : Compatible 1 F) (x y : Half) :
    (F x).2.val*y.2.val=x.2.val*(F y).2.val := by
  have he := hF x y ∞
  change (1/(F x).2.val)*(1/y.2.val)=(1/x.2.val)*(1/(F y).2.val) at he
  have hxt := x.2.property.ne'
  have hyt := y.2.property.ne'
  have hfxt := (F x).2.property.ne'
  have hfyt := (F y).2.property.ne'
  field_simp at he
  nlinarith [he]

lemma quadratic_relation {F : Half ≃ₜ Half} (hF : Compatible 1 F) (x y : Half) (p : ℂ) :
    quadratic (F x) p*quadratic y p=quadratic x p*quadratic (F y) p := by
  have he := hF x y (p:Boundary)
  change (quadratic (F x) p/((F x).2.val*(1+‖p‖^2)))*
      (quadratic y p/(y.2.val*(1+‖p‖^2)))=
    (quadratic x p/(x.2.val*(1+‖p‖^2)))*
      (quadratic (F y) p/((F y).2.val*(1+‖p‖^2))) at he
  rw [div_mul_div_comm,div_mul_div_comm] at he
  have hd : (F x).2.val*(1+‖p‖^2)*(y.2.val*(1+‖p‖^2))=
      x.2.val*(1+‖p‖^2)*((F y).2.val*(1+‖p‖^2)) := by
    calc
      _ = ((F x).2.val*y.2.val)*(1+‖p‖^2)^2 := by ring
      _ = (x.2.val*(F y).2.val)*(1+‖p‖^2)^2 := by rw [height_relation hF x y]
      _ = _ := by ring
  rw [hd] at he
  exact (div_left_inj' (mul_ne_zero
    (mul_ne_zero x.2.property.ne' (by nlinarith [sq_nonneg ‖p‖]))
    (mul_ne_zero (F y).2.property.ne' (by nlinarith [sq_nonneg ‖p‖])))).mp he

lemma quadratic_re (x : Half) (r : ℝ) :
    quadratic x (r:ℂ)=r^2-2*x.1.re*r+q x := by
  unfold quadratic q
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  ring

lemma quadratic_im (x : Half) (r : ℝ) :
    quadratic x ((r:ℂ)*Complex.I)=r^2-2*x.1.im*r+q x := by
  unfold quadratic q
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,add_zero,sub_zero]
  ring

lemma product_quadratic_coefficients (a A b B c C : ℝ)
    (h : ∀ r : ℝ, (r^2-2*a*r+A)*(r^2+1)=
      (r^2-2*b*r+B)*(r^2-2*c*r+C)) :
    A=B*C ∧ a=b+c ∧ A+1=B+C+4*b*c ∧ a=b*C+c*B := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  have hm2 := h (-2)
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero,sub_zero,zero_add] at h0
  norm_num at h0
  refine ⟨h0,?_,?_,?_⟩
  · nlinarith [h1,hm1,h2,hm2]
  · nlinarith [h0,h1,hm1]
  · nlinarith [h1,hm1,h2,hm2]

def basepoint : Half := ⟨0,⟨1,by norm_num⟩⟩

lemma basepoint_fixed {F : Half ≃ₜ Half} (hF : Compatible 1 F) : F basepoint=basepoint := by
  let xr : Half := ⟨1,⟨1,by norm_num⟩⟩
  let xi : Half := ⟨Complex.I,⟨1,by norm_num⟩⟩
  have hr : ∀ r : ℝ, (r^2-2*(F xr).1.re*r+q (F xr))*(r^2+1)=
      (r^2-2*1*r+2)*(r^2-2*(F basepoint).1.re*r+q (F basepoint)) := by
    intro r
    have he := quadratic_relation hF xr basepoint (r:ℂ)
    rw [quadratic_re,quadratic_re,quadratic_re,quadratic_re] at he
    simpa [xr,basepoint,q,show (1:ℝ)+1=2 by norm_num] using he
  obtain ⟨hA,ha,hB,hb⟩ := product_quadratic_coefficients _ _ _ _ _ _ hr
  have hre : (F basepoint).1.re=0 := by nlinarith
  have hq : q (F basepoint)=1 := by nlinarith
  have hi : ∀ r : ℝ, (r^2-2*(F xi).1.im*r+q (F xi))*(r^2+1)=
      (r^2-2*1*r+2)*(r^2-2*(F basepoint).1.im*r+q (F basepoint)) := by
    intro r
    have he := quadratic_relation hF xi basepoint ((r:ℂ)*Complex.I)
    rw [quadratic_im,quadratic_im,quadratic_im,quadratic_im] at he
    simpa [xi,basepoint,q,show (1:ℝ)+1=2 by norm_num] using he
  obtain ⟨hA',ha',hB',hb'⟩ := product_quadratic_coefficients _ _ _ _ _ _ hi
  have him : (F basepoint).1.im=0 := by nlinarith
  have hz : (F basepoint).1=0 := Complex.ext hre him
  apply Prod.ext hz
  apply Subtype.ext
  change (F basepoint).2.val=1
  unfold q at hq
  rw [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_add] at hq
  nlinarith [(F basepoint).2.property]

lemma compatible_identity_unique {F : Half ≃ₜ Half} (hF : Compatible 1 F) : F=1 := by
  have h0 := basepoint_fixed hF
  apply Homeomorph.ext
  intro x
  have hquad (p : ℂ) : quadratic (F x) p=quadratic x p := by
    have he := quadratic_relation hF x basepoint p
    rw [h0] at he
    exact mul_right_cancel₀ (quadratic_pos basepoint p).ne' he
  have hq : q (F x)=q x := by simpa [quadratic,q] using hquad 0
  have hre : (F x).1.re=x.1.re := by
    have he := hquad 1
    have e1 := quadratic_re (F x) 1
    have e2 := quadratic_re x 1
    norm_num at e1 e2
    rw [e1,e2] at he
    linarith
  have him : (F x).1.im=x.1.im := by
    have he := hquad Complex.I
    have e1 := quadratic_im (F x) 1
    have e2 := quadratic_im x 1
    norm_num at e1 e2
    rw [e1,e2] at he
    linarith
  have hz : (F x).1=x.1 := Complex.ext hre him
  apply Prod.ext hz
  apply Subtype.ext
  change (F x).2.val=x.2.val
  unfold q at hq
  rw [hz] at hq
  nlinarith [(F x).2.property,x.2.property]
end CannonH3

namespace CannonH3
open Set

lemma compatible_one : Compatible 1 1 := by intro x y p; rfl
lemma compatible_mul {f g : Boundary ≃ₜ Boundary} {F G : Half ≃ₜ Half}
    (hf : Compatible f F) (hg : Compatible g G) : Compatible (f*g) (F*G) := by
  intro x y p
  change potential (F (G x)) (f (g p))*potential y p=
    potential x p*potential (F (G y)) (f (g p))
  apply mul_right_cancel₀ (potential_pos (G y) (g p)).ne'
  have h1 := hf (G x) (G y) (g p)
  have h2 := hg x y p
  linear_combination potential y p*h1+potential (F (G y)) (f (g p))*h2

lemma compatible_inv {f : Boundary ≃ₜ Boundary} {F : Half ≃ₜ Half}
    (hf : Compatible f F) : Compatible f⁻¹ F⁻¹ := by
  intro x y p
  simpa only [Homeomorph.inv_apply,Homeomorph.apply_symm_apply] using
    (hf (F.symm x) (F.symm y) (f.symm p)).symm

def paired : Subgroup ((Boundary ≃ₜ Boundary) × (Half ≃ₜ Half)) where
  carrier := {u | Compatible u.1 u.2 ∧ ∀ x y, distArg (u.2 x) (u.2 y)=distArg x y}
  one_mem' := ⟨compatible_one,by intro x y; rfl⟩
  mul_mem' := by
    rintro ⟨f,F⟩ ⟨g,G⟩ ⟨hf,hF⟩ ⟨hg,hG⟩
    refine ⟨compatible_mul hf hg,?_⟩
    intro x y
    exact (hF (G x) (G y)).trans (hG x y)
  inv_mem' := by
    rintro ⟨f,F⟩ ⟨hf,hF⟩
    refine ⟨compatible_inv hf,?_⟩
    intro x y
    change distArg (F.symm x) (F.symm y)=distArg x y
    simpa only [Homeomorph.apply_symm_apply] using (hF (F.symm x) (F.symm y)).symm

def boundaryProjection : paired →* (Boundary ≃ₜ Boundary) where
  toFun u := u.val.1
  map_one' := rfl
  map_mul' _ _ := rfl

lemma boundaryProjection_injective : Function.Injective boundaryProjection := by
  apply (injective_iff_map_eq_one boundaryProjection).mpr
  intro u hu
  apply Subtype.ext
  apply Prod.ext hu
  apply compatible_identity_unique
  have hh := u.property.1
  change u.val.1=1 at hu
  rwa [hu] at hh

def boundaryGroup : Subgroup (Boundary ≃ₜ Boundary) := boundaryProjection.range

def pairedH3 : paired →* CannonRelease.H3Isom where
  toFun u := lift u.val.2 u.property.2
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    change coords.symm (coords x)=x
    exact coords.symm_apply_apply x
  map_mul' u v := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    change coords.symm (u.val.2 (v.val.2 (coords x)))=
      coords.symm (u.val.2 (coords (coords.symm (v.val.2 (coords x)))))
    rw [coords.apply_symm_apply]

def extensionHom : boundaryGroup →* CannonRelease.H3Isom :=
  pairedH3.comp (MonoidHom.ofInjective boundaryProjection_injective).symm.toMonoidHom

lemma extensionHom_compatible (f : boundaryGroup) :
    Compatible f.val ((coords.symm.trans (extensionHom f).val).trans coords) := by
  let p : paired := (MonoidHom.ofInjective boundaryProjection_injective).symm f
  have he : boundaryProjection p=f.val := by
    have hh := (MonoidHom.ofInjective boundaryProjection_injective).apply_symm_apply f
    exact congrArg Subtype.val hh
  intro x y z
  have hh := p.property.1 x y z
  rw [show p.val.1=f.val from he] at hh
  change potential (coords (coords.symm (p.val.2 (coords (coords.symm x))))) (f.val z)*potential y z=
    potential x z*potential (coords (coords.symm (p.val.2 (coords (coords.symm y))))) (f.val z)
  simpa only [coords.apply_symm_apply] using hh
end CannonH3

namespace CannonH3
open Set
open scoped OnePoint

def boundaryAffine (a b : ℂ) (ha : a ≠ 0) : Boundary ≃ₜ Boundary :=
  (complexAffine a b ha).onePointCongr

lemma affine_potential (a b : ℂ) (ha : a ≠ 0) (x : Half) (p : ℂ) :
    potential (affine a b ha x) (boundaryAffine a b ha p)=
      (‖a‖*(1+‖p‖^2)/(1+‖a*p+b‖^2))*potential x p := by
  change (‖a*x.1+b-(a*p+b)‖^2+(‖a‖*x.2.val)^2)/
    ((‖a‖*x.2.val)*(1+‖a*p+b‖^2))=_
  have he : a*x.1+b-(a*p+b)=a*(x.1-p) := by ring
  rw [he,norm_mul,potential_coe]
  have ha' : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hp : 1+‖p‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖p‖]
  have hap : 1+‖a*p+b‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖a*p+b‖]
  field_simp

lemma affine_compatible (a b : ℂ) (ha : a ≠ 0) :
    Compatible (boundaryAffine a b ha) (affine a b ha) := by
  intro x y p
  induction p using OnePoint.rec with
  | infty =>
    change (1/(‖a‖*x.2.val))*(1/y.2.val)=(1/x.2.val)*(1/(‖a‖*y.2.val))
    ring
  | coe p => rw [affine_potential,affine_potential]; ring

lemma inversion_potential (x : Half) (p : Boundary) :
    potential (inversion x) (CannonMobius.inversion p)=potential x p := by
  have hq : q x ≠ 0 := (q_pos x).ne'
  have ht : x.2.val ≠ 0 := x.2.property.ne'
  induction p using OnePoint.rec with
  | infty =>
    change potential (inversion x) ((0:ℂ):Boundary)=potential x ∞
    rw [potential_coe,potential_infty,sub_zero]
    change q (inversionFun x)/((x.2.val/q x)*(1+‖(0:ℂ)‖^2))=1/x.2.val
    rw [inversion_q]
    simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,mul_one]
    field_simp
  | coe p =>
    by_cases hp : p=0
    · subst p
      change potential (inversion x) (CannonMobius.inv ((0:ℂ):Boundary))=potential x ((0:ℂ):Boundary)
      rw [CannonMobius.inv_zero,potential_infty,potential_coe]
      change 1/(x.2.val/q x)=(‖x.1-0‖^2+x.2.val^2)/(x.2.val*(1+‖(0:ℂ)‖^2))
      simp only [sub_zero,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero,mul_one]
      unfold q
      field_simp
    · have hp' : ‖p‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hp)
      change potential (inversion x) (CannonMobius.inv (p:Boundary))=potential x p
      rw [CannonMobius.inv_coe hp,potential_coe,potential_coe]
      have he : ‖(inversion x).1-p⁻¹‖^2=
        (‖x.1-p‖^2+x.2.val^2)/(q x*‖p‖^2)-(x.2.val/q x)^2 := by
        change ‖star x.1/(q x:ℂ)-p⁻¹‖^2=_
        simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
          Complex.div_ofReal_re,Complex.div_ofReal_im,Complex.star_def,Complex.conj_re,
          Complex.conj_im,Complex.inv_re,Complex.inv_im]
        have hn : Complex.normSq p ≠ 0 := (Complex.normSq_pos.mpr hp).ne'
        have hn' : p.re*p.re+p.im*p.im ≠ 0 := hn
        unfold q
        rw [Complex.sq_norm]
        simp only [Complex.normSq_apply]
        simp only [sq]
        have hn2 : p.re^2+p.im^2 ≠ 0 := by simpa only [sq] using hn'
        field_simp [hn', hn2, Complex.normSq_apply]
        ring_nf
      rw [he,norm_inv]
      change (_+(x.2.val/q x)^2)/((x.2.val/q x)*(1+(‖p‖⁻¹)^2))=_
      have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
      have hs : 1+‖p‖^2 ≠ 0 := by nlinarith [sq_nonneg ‖p‖]
      field_simp
      ring

lemma inversion_compatible : Compatible CannonMobius.inversion inversion := by
  intro x y p
  rw [inversion_potential,inversion_potential]

end CannonH3

noncomputable section
open Set Filter Topology

namespace CannonH3
open scoped OnePoint

lemma affine_mem_boundaryGroup (a b : ℂ) (ha : a ≠ 0) :
    CannonMobius.affine a b ha ∈ boundaryGroup := by
  have he : boundaryAffine a b ha=CannonMobius.affine a b ha := by
    apply Homeomorph.ext
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  refine ⟨⟨(boundaryAffine a b ha,affine a b ha),affine_compatible a b ha,
    affine_preserves a b ha⟩,he⟩

lemma inversion_mem_boundaryGroup : CannonMobius.inversion ∈ boundaryGroup :=
  ⟨⟨(CannonMobius.inversion,inversion),inversion_compatible,inversion_preserves⟩,rfl⟩

lemma biholomorphic_mem_boundaryGroup {f : Boundary ≃ₜ Boundary}
    (hf : f ∈ CannonMobius.biholomorphic) : f ∈ boundaryGroup :=
  CannonMobius.biholomorphic_mem_of_generators boundaryGroup
    affine_mem_boundaryGroup inversion_mem_boundaryGroup hf

def reflection : Half ≃ₜ Half :=
  Complex.conjCLE.toHomeomorph.prodCongr (Homeomorph.refl Height)
def boundaryReflection : Boundary ≃ₜ Boundary := Complex.conjCLE.toHomeomorph.onePointCongr

lemma reflection_potential (x : Half) (p : Boundary) :
    potential (reflection x) (boundaryReflection p)=potential x p := by
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p =>
    change (‖star x.1-star p‖^2+x.2.val^2)/(x.2.val*(1+‖star p‖^2))=_
    rw [← star_sub,norm_star,norm_star]
    rfl
lemma reflection_compatible : Compatible boundaryReflection reflection := by
  intro x y p
  rw [reflection_potential,reflection_potential]
lemma reflection_distArg (x y : Half) : distArg (reflection x) (reflection y)=distArg x y := by
  change 1+(‖star x.1-star y.1‖^2+(x.2.val-y.2.val)^2)/(2*x.2.val*y.2.val)=_
  rw [← star_sub,norm_star]
  rfl
lemma reflection_mem_boundaryGroup : boundaryReflection ∈ boundaryGroup :=
  ⟨⟨(boundaryReflection,reflection),reflection_compatible,reflection_distArg⟩,rfl⟩

lemma boundaryReflection_sq : boundaryReflection*boundaryReflection=1 := by
  apply Homeomorph.ext
  intro p
  induction p using OnePoint.rec with
  | infty => rfl
  | coe p => exact congrArg (fun z : ℂ => (z:Boundary)) (star_star p)

theorem conformal_or_anticonformal_mem {f : Boundary ≃ₜ Boundary}
    (hf : f ∈ CannonMobius.biholomorphic ∨ boundaryReflection*f ∈ CannonMobius.biholomorphic) :
    f ∈ boundaryGroup := by
  rcases hf with hf|hf
  · exact biholomorphic_mem_boundaryGroup hf
  · have h := boundaryGroup.mul_mem reflection_mem_boundaryGroup
      (biholomorphic_mem_boundaryGroup hf)
    simpa only [← mul_assoc,boundaryReflection_sq,one_mul] using h

def conformalActionExtension {G : Type*} [Group G]
    (σ : G →* (Boundary ≃ₜ Boundary))
    (hσ : ∀ g, σ g ∈ CannonMobius.biholomorphic ∨
      boundaryReflection*σ g ∈ CannonMobius.biholomorphic) : G →* CannonRelease.H3Isom :=
  extensionHom.comp (σ.codRestrict boundaryGroup (fun g => conformal_or_anticonformal_mem (hσ g)))

lemma conformalActionExtension_compatible {G : Type*} [Group G]
    (σ : G →* (Boundary ≃ₜ Boundary))
    (hσ : ∀ g, σ g ∈ CannonMobius.biholomorphic ∨
      boundaryReflection*σ g ∈ CannonMobius.biholomorphic) (g : G) :
    Compatible (σ g) ((coords.symm.trans (conformalActionExtension σ hσ g).val).trans coords) :=
  extensionHom_compatible ⟨σ g,conformal_or_anticonformal_mem (hσ g)⟩
end CannonH3

namespace CannonH3
lemma compatible_unique {f : Boundary ≃ₜ Boundary} {F G : Half ≃ₜ Half}
    (hF : Compatible f F) (hG : Compatible f G) : F=G := by
  have hh := compatible_mul hF (compatible_inv hG)
  rw [mul_inv_cancel] at hh
  exact mul_inv_eq_one.mp (compatible_identity_unique hh)

def interior (f : boundaryGroup) : Half ≃ₜ Half :=
  (coords.symm.trans (extensionHom f).val).trans coords
lemma interior_compatible (f : boundaryGroup) : Compatible f.val (interior f) :=
  extensionHom_compatible f
lemma interior_one : interior 1=1 := compatible_unique (interior_compatible 1) compatible_one
lemma interior_mul (f g : boundaryGroup) : interior (f*g)=interior f*interior g :=
  compatible_unique (interior_compatible (f*g)) (compatible_mul (interior_compatible f) (interior_compatible g))
lemma interior_affine (a b : ℂ) (ha : a ≠ 0) :
    interior ⟨CannonMobius.affine a b ha,affine_mem_boundaryGroup a b ha⟩=affine a b ha := by
  apply compatible_unique (interior_compatible _)
  have he : CannonMobius.affine a b ha=boundaryAffine a b ha := by
    apply Homeomorph.ext
    intro p
    induction p using OnePoint.rec with
    | infty => rfl
    | coe z => rfl
  change Compatible (CannonMobius.affine a b ha) (affine a b ha)
  rw [he]
  exact affine_compatible a b ha
lemma interior_inversion : interior ⟨CannonMobius.inversion,inversion_mem_boundaryGroup⟩=inversion :=
  compatible_unique (interior_compatible _) inversion_compatible
lemma interior_reflection : interior ⟨boundaryReflection,reflection_mem_boundaryGroup⟩=reflection :=
  compatible_unique (interior_compatible _) reflection_compatible
end CannonH3

end
end
end
end
end
end
end
end

end OAI
