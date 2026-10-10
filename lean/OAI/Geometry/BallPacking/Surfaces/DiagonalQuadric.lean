import Mathlib

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Topology
open Set Function

variable {m : ℕ}
abbrev Affine (m : ℕ) := ℂ × (Fin m → ℂ)

def equations (a : Fin m → ℂ) (z : Affine m) : Fin m → ℂ :=
  fun j => z.2 j ^ 2 - z.1 ^ 2 + a j

def locus (a : Fin m → ℂ) : Set (Affine m) := equations a ⁻¹' {0}

def jacobian (z : Affine m) : Affine m →L[ℂ] (Fin m → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (2*z.2 j) • ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))) -
    (2*z.1) • ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)

@[simp] theorem jacobian_apply (z v : Affine m) (j : Fin m) :
    jacobian z v j = 2*z.2 j*v.2 j-2*z.1*v.1 := rfl

theorem equations_contDiff (a : Fin m → ℂ) : ContDiff ℂ ∞ (equations a) := by
  apply contDiff_pi.mpr
  intro j
  exact (((contDiff_apply ℂ ℂ j).comp contDiff_snd).pow 2).sub
    (contDiff_fst.pow 2) |>.add contDiff_const

theorem equations_hasFDerivAt (a : Fin m → ℂ) (z : Affine m) :
    HasFDerivAt (equations a) (jacobian z) z := by
  apply hasFDerivAt_pi.mpr
  intro j
  convert! ((((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))).hasFDerivAt.pow 2).sub
    ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).hasFDerivAt.pow 2)).add_const (a j) using 1
  simp

@[simp] theorem mem_locus {a : Fin m → ℂ} {z : Affine m} :
    z∈locus a ↔ ∀ j,z.2 j^2=z.1^2-a j := by
  simp only [locus,mem_preimage,mem_singleton_iff,funext_iff,equations,Pi.zero_apply]
  constructor <;> intro h j <;> have := h j <;> linear_combination this

theorem locus_isClosed (a : Fin m → ℂ) : IsClosed (locus a) :=
  isClosed_singleton.preimage (equations_contDiff a).continuous

theorem at_most_one_zero {a : Fin m → ℂ} (ha : Injective a) {z : Affine m}
    (hz : z∈locus a) {i j : Fin m} (hi : z.2 i=0) (hj : z.2 j=0) : i=j := by
  apply ha
  have hzi := (mem_locus.mp hz) i
  have hzj := (mem_locus.mp hz) j
  rw [hi,zero_pow (by decide)] at hzi
  rw [hj,zero_pow (by decide)] at hzj
  linear_combination hzi-hzj

theorem base_ne_zero_at_branch {a : Fin m → ℂ} (ha : ∀ j,a j≠0) {z : Affine m}
    (hz : z∈locus a) {i : Fin m} (hi : z.2 i=0) : z.1≠0 := by
  intro ht
  have hzi := (mem_locus.mp hz) i
  apply ha i
  simpa only [hi,ht,zero_pow (by decide : (2:ℕ)≠0),zero_sub,eq_neg_iff_add_eq_zero,zero_add] using hzi

theorem jacobian_surjective {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {z : Affine m} (hz : z∈locus a) : Surjective (jacobian z) := by
  classical
  by_cases hw : ∀ j,z.2 j≠0
  · intro y
    refine ⟨(0,fun j => y j/(2*z.2 j)),?_⟩
    ext j
    simp only [jacobian_apply,mul_zero,sub_zero]
    exact mul_div_cancel₀ (y j) (mul_ne_zero (by norm_num) (hw j))
  · push Not at hw
    obtain ⟨i,hi⟩ := hw
    have ht := base_ne_zero_at_branch ha0 hz hi
    intro y
    let v : ℂ := -y i/(2*z.1)
    refine ⟨(v,fun j => if j=i then 0 else (y j+2*z.1*v)/(2*z.2 j)),?_⟩
    have hv : 2*z.1*v= -y i := mul_div_cancel₀ (-y i) (mul_ne_zero (by norm_num) ht)
    ext j
    simp only [jacobian_apply]
    by_cases hji : j=i
    · subst j
      simp only [hi,mul_zero,zero_mul,zero_sub,hv,neg_neg]
    · have hj : z.2 j≠0 := fun hj => hji (at_most_one_zero ha hz hj hi)
      rw [ite_eq_right hji,mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hj),add_sub_cancel_right]

theorem ordinary_augmented_bijective {z : Affine m} (hw : ∀ j,z.2 j≠0) :
    Bijective ((ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)).prod (jacobian z)) := by
  constructor
  · intro v w h
    have ht : v.1=w.1 := by
      have ht := congrArg (fun x : Affine m => x.1) h
      exact ht
    apply Prod.ext ht
    funext j
    have he := congrArg (fun x : Affine m => x.2 j) h
    change 2*z.2 j*v.2 j-2*z.1*v.1=2*z.2 j*w.2 j-2*z.1*w.1 at he
    rw [ht] at he
    have hm : (2*z.2 j)*v.2 j=(2*z.2 j)*w.2 j := by linear_combination he
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) (hw j)) hm
  · rintro ⟨t,y⟩
    refine ⟨(t,fun j => (y j+2*z.1*t)/(2*z.2 j)),?_⟩
    apply Prod.ext
    · rfl
    · funext j
      change 2*z.2 j*((y j+2*z.1*t)/(2*z.2 j))-2*z.1*t=y j
      rw [mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (hw j)),add_sub_cancel_right]

theorem branch_augmented_bijective {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {z : Affine m} (hz : z∈locus a) {i : Fin m} (hi : z.2 i=0) :
    Bijective (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))).prod
      (jacobian z)) := by
  classical
  have ht := base_ne_zero_at_branch ha0 hz hi
  constructor
  · intro v w h
    have hwi : v.2 i=w.2 i := congrArg Prod.fst h
    have he j := congrArg (fun x : Affine m => x.2 j) h
    have hti := he i
    simp only [ContinuousLinearMap.prod_apply,jacobian_apply,hi,mul_zero,zero_mul,zero_sub,
      neg_inj] at hti
    have htv : v.1=w.1 := mul_left_cancel₀ (mul_ne_zero (by norm_num) ht) hti
    apply Prod.ext htv
    funext j
    by_cases hji : j=i
    · subst j
      exact hwi
    · have hj : z.2 j≠0 := fun hj => hji (at_most_one_zero ha hz hj hi)
      have hej := he j
      change 2*z.2 j*v.2 j-2*z.1*v.1=2*z.2 j*w.2 j-2*z.1*w.1 at hej
      rw [htv] at hej
      have hm : (2*z.2 j)*v.2 j=(2*z.2 j)*w.2 j := by linear_combination hej
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) hj) hm
  · rintro ⟨t,y⟩
    let v : ℂ := -y i/(2*z.1)
    refine ⟨(v,fun j => if j=i then t else (y j+2*z.1*v)/(2*z.2 j)),?_⟩
    apply Prod.ext
    · change (if i=i then t else (y i+2*z.1*v)/(2*z.2 i))=t
      simp only [ite_true]
    · have hv : 2*z.1*v= -y i := mul_div_cancel₀ (-y i) (mul_ne_zero (by norm_num) ht)
      funext j
      change 2*z.2 j*(if j=i then t else (y j+2*z.1*v)/(2*z.2 j))-2*z.1*v=y j
      by_cases hji : j=i
      · subst j
        simp only [hi,mul_zero,zero_mul,zero_sub,hv,neg_neg]
      · have hj : z.2 j≠0 := fun hj => hji (at_most_one_zero ha hz hj hi)
        rw [ite_eq_right hji,mul_div_cancel₀ _ (mul_ne_zero (by norm_num) hj),add_sub_cancel_right]

@[simp] theorem sqrt_sq_complex (z : ℂ) : Complex.sqrt z ^ 2=z := by
  exact Complex.cpow_nat_inv_pow z (by decide : (2:ℕ)≠0)

theorem sqrt_of_sq_pos {z : ℂ} (hz : 0<z.re) : Complex.sqrt (z^2)=z :=
  Complex.sq_cpow_two_inv hz

theorem sqrt_re_pos {z : ℂ} (hz : 0<z.re) : 0<(Complex.sqrt z).re := by
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  positivity

theorem sqrt_contDiffAt {z : ℂ} (hz : 0<z.re) : ContDiffAt ℂ ∞ Complex.sqrt z :=
  ((Complex.differentiableOn_sqrt.contDiffOn Complex.isOpen_slitPlane) z (Or.inl hz)).contDiffAt
    (Complex.isOpen_slitPlane.mem_nhds (Or.inl hz))

namespace Explicit
variable (m : ℕ)

def parameters (j : Fin (m+2)) : ℂ := (j.val : ℂ)+1

instance parameters_injective : Fact (Injective (parameters m)) := ⟨by
  intro i j h
  apply Fin.ext
  have he : (i.val : ℂ)=(j.val : ℂ) := add_right_cancel h
  exact_mod_cast he⟩

instance parameters_nonzero : Fact (∀ j,parameters m j≠0) := ⟨by
  intro j
  have hp : 0<(j.val : ℝ)+1 := by positivity
  intro h
  have he := congrArg Complex.re h
  simp only [parameters,Complex.add_re,Complex.natCast_re,Complex.one_re,Complex.zero_re] at he
  linarith⟩

@[simp] theorem parameters_zero : parameters m 0=1 := by simp [parameters]
@[simp] theorem parameters_one : parameters m 1=2 := by norm_num [parameters]

def plus (s : ℂ) : ℂ := (s+s⁻¹)/2
def minus (s : ℂ) : ℂ := (s-s⁻¹)/2
def baseSquare (s : ℂ) : ℂ := 1+plus s^2

@[simp] theorem plus_add_minus (s : ℂ) : plus s+minus s=s := by unfold plus minus; ring

theorem plus_sq_sub_minus_sq {s : ℂ} (hs : s≠0) : plus s^2-minus s^2=1 := by
  unfold plus minus
  field_simp
  ring

def annulusPoint (s : ℂ) : Affine (m+2) :=
  (Complex.sqrt (baseSquare s),fun j =>
    if j=0 then plus s else if j=1 then minus s
    else Complex.I*Complex.sqrt (parameters m j-baseSquare s))

@[simp] theorem annulusPoint_zero (s : ℂ) : (annulusPoint m s).2 0=plus s := by simp [annulusPoint]
@[simp] theorem annulusPoint_one (s : ℂ) : (annulusPoint m s).2 1=minus s := by
  have hn : (1 : Fin (m+2))≠0 := by simp
  simp [annulusPoint,hn]

theorem annulusPoint_mem {s : ℂ} (hs : s≠0) : annulusPoint m s∈locus (parameters m) := by
  rw [mem_locus]
  intro j
  change (annulusPoint m s).2 j^2=Complex.sqrt (baseSquare s)^2-parameters m j
  rw [sqrt_sq_complex]
  by_cases hj0 : j=0
  · subst j
    simp [baseSquare]
  by_cases hj1 : j=1
  · subst j
    have he := plus_sq_sub_minus_sq hs
    simp only [annulusPoint_one,parameters_one,baseSquare]
    linear_combination -he
  · simp only [annulusPoint,ite_eq_right hj0,ite_eq_right hj1,mul_pow,Complex.I_sq,sqrt_sq_complex]
    ring

def annulusDomain : Set ℂ := {s | s≠0 ∧ 0<(baseSquare s).re ∧
  ∀ j : Fin (m+2),1<j.val → 0<(parameters m j-baseSquare s).re}

end Explicit

def endSign (b : Bool) : ℂ := if b then -1 else 1
@[simp] theorem endSign_sq (b : Bool) : endSign b^2=1 := by cases b <;> norm_num [endSign]
@[simp] theorem endSign_mul_self (b : Bool) : endSign b*endSign b=1 := by
  simpa only [pow_two] using endSign_sq b
@[simp] theorem endSign_re (b : Bool) : (endSign b).re=if b then -1 else 1 := by
  cases b <;> rfl
@[simp] theorem endSign_im (b : Bool) : (endSign b).im=0 := by cases b <;> simp [endSign]
 theorem endSign_ne_zero (b : Bool) : endSign b≠0 := by cases b <;> norm_num [endSign]

 def infinityRoot (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) (j : Fin m) : ℂ :=
  endSign (ε j)*Complex.sqrt (1-a j*s^2)
 def infinityPoint (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) : Affine m :=
  (s⁻¹,fun j => s⁻¹*infinityRoot a ε s j)
 def infinityRegion (a : Fin m → ℂ) : Set ℂ := {s | ∀ j,0<(1-a j*s^2).re}
 def infinityDomain (a : Fin m → ℂ) : Set ℂ := {s | s≠0 ∧ s∈infinityRegion a}

@[simp] theorem infinityRoot_sq (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) (j : Fin m) :
    infinityRoot a ε s j^2=1-a j*s^2 := by
  simp only [infinityRoot,mul_pow,endSign_sq,sqrt_sq_complex,one_mul]

 theorem infinityPoint_mem (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ} (hs : s≠0) :
    infinityPoint a ε s∈locus a := by
  apply mem_locus.mpr
  intro j
  change (s⁻¹*infinityRoot a ε s j)^2=(s⁻¹)^2-a j
  rw [mul_pow,infinityRoot_sq]
  field_simp

@[simp] theorem infinityPoint_coordinate (a : Fin m → ℂ) (ε : Fin m → Bool) (s : ℂ) :
    (infinityPoint a ε s).1⁻¹=s := inv_inv s

 theorem infinityRoot_positive (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityRegion a) (j : Fin m) : 0<(endSign (ε j)*infinityRoot a ε s j).re := by
  rw [infinityRoot,← mul_assoc,endSign_mul_self,one_mul]
  exact sqrt_re_pos (hs j)

 theorem infinityRegion_open (a : Fin m → ℂ) : IsOpen (infinityRegion a) := by
  change IsOpen {s : ℂ | ∀ j,0<(1-a j*s^2).re}
  simp only [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro j
  apply isOpen_lt continuous_const
  fun_prop

 theorem infinityDomain_open (a : Fin m → ℂ) : IsOpen (infinityDomain a) :=
  isOpen_ne_fun continuous_id continuous_const |>.inter (infinityRegion_open a)

@[simp] theorem zero_mem_infinityRegion (a : Fin m → ℂ) : (0 : ℂ)∈infinityRegion a := by
  intro j
  norm_num

 theorem infinityRoot_contDiffAt (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityRegion a) : ContDiffAt ℂ ∞ (infinityRoot a ε) s := by
  apply contDiffAt_pi.mpr
  intro j
  exact contDiffAt_const.mul ((sqrt_contDiffAt (hs j)).comp s
    (contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_id.pow 2))))

 theorem infinityPoint_contDiffAt (a : Fin m → ℂ) (ε : Fin m → Bool) {s : ℂ}
    (hs : s∈infinityDomain a) : ContDiffAt ℂ ∞ (infinityPoint a ε) s := by
  apply (contDiffAt_id.inv hs.1).prodMk
  apply contDiffAt_pi.mpr
  intro j
  exact (contDiffAt_id.inv hs.1).mul (contDiffAt_pi.mp (infinityRoot_contDiffAt a ε hs.2) j)

 theorem infinityRegion_contains_ball (a : Fin m → ℂ) :
    ∃ r : ℝ,0<r ∧ Metric.ball 0 r⊆infinityRegion a :=
  Metric.isOpen_iff.mp (infinityRegion_open a) 0 (zero_mem_infinityRegion a)

theorem branch_augmented_regular_bijective {z : Affine m} (ht : z.1≠0)
    (i : Fin m) (hw : ∀ j,j≠i → z.2 j≠0) :
    Bijective (((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))).prod
      (jacobian z)) := by
  classical
  constructor
  · intro v w h
    have hwi : v.2 i=w.2 i := congrArg (fun x : Affine m => x.1) h
    have he j := congrArg (fun x : Affine m => x.2 j) h
    have hti := he i
    change 2*z.2 i*v.2 i-2*z.1*v.1=2*z.2 i*w.2 i-2*z.1*w.1 at hti
    have hm : 2*z.1*v.1=2*z.1*w.1 := by rw [hwi] at hti; linear_combination -hti
    have htv : v.1=w.1 := mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) ht) hm
    apply Prod.ext htv
    funext j
    by_cases hji : j=i
    · subst j; exact hwi
    · have hej := he j
      change 2*z.2 j*v.2 j-2*z.1*v.1=2*z.2 j*w.2 j-2*z.1*w.1 at hej
      rw [htv] at hej
      have hm : (2*z.2 j)*v.2 j=(2*z.2 j)*w.2 j := by linear_combination hej
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:ℂ)≠0) (hw j hji)) hm
  · rintro ⟨t,y⟩
    let v : ℂ := (2*z.2 i*t-y i)/(2*z.1)
    have hv : 2*z.1*v=2*z.2 i*t-y i :=
      mul_div_cancel₀ _ (mul_ne_zero (by norm_num : (2:ℂ)≠0) ht)
    refine ⟨(v,fun j => if j=i then t else (y j+2*z.1*v)/(2*z.2 j)),?_⟩
    apply Prod.ext
    · change (if i=i then t else (y i+2*z.1*v)/(2*z.2 i))=t
      simp only [ite_true]
    · funext j
      change 2*z.2 j*(if j=i then t else (y j+2*z.1*v)/(2*z.2 j))-2*z.1*v=y j
      by_cases hji : j=i
      · subst j
        rw [ite_eq_left rfl,hv]
        ring
      · rw [ite_eq_right hji,mul_div_cancel₀ _ (mul_ne_zero (by norm_num) (hw j hji)),add_sub_cancel_right]

def curveCoordinate : Option (Fin m) → Affine m →L[ℂ] ℂ
  | none => ContinuousLinearMap.fst ℂ ℂ (Fin m → ℂ)
  | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin m → ℂ))

def regularCoordinate : Option (Fin m) → Set (Affine m)
  | none => {z | ∀ j,z.2 j≠0}
  | some i => {z | z.1≠0 ∧ ∀ j,j≠i → z.2 j≠0}

theorem regularCoordinate_isOpen (c : Option (Fin m)) : IsOpen (regularCoordinate c) := by
  cases c with
  | none =>
    simp only [regularCoordinate,ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_ne_fun (by fun_prop) continuous_const
  | some i =>
    change IsOpen ({z : Affine m | z.1≠0} ∩ {z | ∀ j,j≠i → z.2 j≠0})
    apply IsOpen.inter (isOpen_ne_fun continuous_fst continuous_const)
    simp only [ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
      isOpen_ne_fun (by fun_prop) continuous_const

theorem regularCoordinate_bijective (c : Option (Fin m)) {z : Affine m}
    (hz : z∈regularCoordinate c) : Bijective ((curveCoordinate c).prod (jacobian z)) := by
  cases c with
  | none => exact ordinary_augmented_bijective hz
  | some i => exact branch_augmented_regular_bijective hz.1 i hz.2

theorem exists_regularCoordinate {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    {z : Affine m} (hz : z∈locus a) : ∃ c,z∈regularCoordinate c := by
  by_cases hw : ∀ j,z.2 j≠0
  · exact ⟨none,hw⟩
  · push Not at hw
    obtain ⟨i,hi⟩ := hw
    exact ⟨some i,base_ne_zero_at_branch ha0 hz hi,
      fun j hji hj => hji (at_most_one_zero ha hz hj hi)⟩

def normalCoordinates (a : Fin m → ℂ) (c : Option (Fin m)) (z : Affine m) : Affine m :=
  (curveCoordinate c z,equations a z)

theorem normalCoordinates_contDiff (a : Fin m → ℂ) (c : Option (Fin m)) :
    ContDiff ℂ ∞ (normalCoordinates a c) :=
  (curveCoordinate c).contDiff.prodMk (equations_contDiff a)

theorem normalCoordinates_hasFDerivAt (a : Fin m → ℂ) (c : Option (Fin m)) (z : Affine m) :
    HasFDerivAt (normalCoordinates a c) ((curveCoordinate c).prod (jacobian z)) z :=
  (curveCoordinate c).hasFDerivAt.prodMk (equations_hasFDerivAt a z)

theorem exists_normal_straightening (a : Fin m → ℂ) (c : Option (Fin m))
    {z : Affine m} (hz : z∈regularCoordinate c) :
    ∃ e : OpenPartialHomeomorph (Affine m) (Affine m),
      z∈e.source ∧ e.source⊆regularCoordinate c ∧
      (e : Affine m → Affine m)=normalCoordinates a c ∧
      ContDiff ℂ ∞ (e : Affine m → Affine m) ∧
      ContDiffOn ℂ ∞ (e.symm : Affine m → Affine m) e.target := by
  let A := (curveCoordinate c).prod (jacobian z)
  have hb := regularCoordinate_bijective c hz
  let L : Affine m ≃L[ℂ] Affine m := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)
  have hd : HasFDerivAt (normalCoordinates a c) (L : Affine m →L[ℂ] Affine m) z :=
    normalCoordinates_hasFDerivAt a c z
  let e₀ := (normalCoordinates_contDiff a c).contDiffAt.toOpenPartialHomeomorph
    (normalCoordinates a c) hd (by simp)
  let e := e₀.restrOpen (regularCoordinate c) (regularCoordinate_isOpen c)
  have he : (e : Affine m → Affine m)=normalCoordinates a c := rfl
  have heSub : e.source⊆regularCoordinate c := inter_subset_right
  refine ⟨e,⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ hd (by simp),hz⟩,
    heSub,he,normalCoordinates_contDiff a c,?_⟩
  intro y hy
  have hreg := heSub (e.map_target hy)
  have hb' := regularCoordinate_bijective c hreg
  let B := (curveCoordinate c).prod (jacobian (e.symm y))
  let K : Affine m ≃L[ℂ] Affine m := ContinuousLinearEquiv.ofBijective B
    (LinearMap.ker_eq_bot.mpr hb'.1) (LinearMap.range_eq_top.mpr hb'.2)
  exact (e.contDiffAt_symm (𝕜 := ℂ) (f₀' := K) hy
    (normalCoordinates_hasFDerivAt a c (e.symm y))
      (normalCoordinates_contDiff a c).contDiffAt).contDiffWithinAt

structure NormalChart (a : Fin m → ℂ) where
  coordinate : Option (Fin m)
  ambient : OpenPartialHomeomorph (Affine m) (Affine m)
  coe_eq : (ambient : Affine m → Affine m)=normalCoordinates a coordinate
  smooth_inverse : ContDiffOn ℂ ∞ (ambient.symm : Affine m → Affine m) ambient.target

theorem exists_normalChart_at {a : Fin m → ℂ} (ha : Injective a) (ha0 : ∀ j,a j≠0)
    (x : locus a) : ∃ e : NormalChart a,(x : Affine m)∈e.ambient.source := by
  obtain ⟨c,hc⟩ := exists_regularCoordinate ha ha0 x.property
  obtain ⟨e,he,_hreg,heq,_hf,hg⟩ := exists_normal_straightening a c hc
  exact ⟨⟨c,e,heq,hg⟩,he⟩

namespace NormalChart
variable {a : Fin m → ℂ} (e : NormalChart a)

@[simp] theorem ambient_apply (x : Affine m) :
    e.ambient x=(curveCoordinate e.coordinate x,equations a x) := by
  rw [e.coe_eq]
  rfl

theorem inverse_on_slice {t : ℂ} (ht : (t,0)∈e.ambient.target) :
    e.ambient.symm (t,0)∈locus a := by
  have h := congrArg Prod.snd (e.ambient.right_inv ht)
  rw [e.ambient_apply] at h
  exact h

def sliceInverse (x : locus a) (t : ℂ) : locus a := by
  classical
  exact if h : (t,0)∈e.ambient.target then ⟨e.ambient.symm (t,0),e.inverse_on_slice h⟩ else x

theorem sliceInverse_eq (x : locus a) {t : ℂ} (ht : (t,0)∈e.ambient.target) :
    (e.sliceInverse x t : Affine m)=e.ambient.symm (t,0) := by
  simp only [sliceInverse,dite_eq_left ht]

def sliceChart (x : locus a) : OpenPartialHomeomorph (locus a) ℂ where
  toFun y := curveCoordinate e.coordinate y.val
  invFun := e.sliceInverse x
  source := Subtype.val ⁻¹' e.ambient.source
  target := (fun t : ℂ => (t,(0 : Fin m → ℂ))) ⁻¹' e.ambient.target
  map_source' := by
    intro y hy
    have he := e.ambient.map_source hy
    rw [e.ambient_apply] at he
    have hy0 : equations a y.val=0 := y.property
    change (curveCoordinate e.coordinate y.val,(0 : Fin m → ℂ))∈e.ambient.target
    simpa only [hy0] using he
  map_target' := by
    intro t ht
    change (e.sliceInverse x t : Affine m)∈e.ambient.source
    rw [e.sliceInverse_eq x ht]
    exact e.ambient.map_target ht
  left_inv' := by
    intro y hy
    have hy0 : equations a y.val=0 := y.property
    have hyt : (curveCoordinate e.coordinate y.val,0)∈e.ambient.target := by
      simpa only [e.ambient_apply,hy0] using e.ambient.map_source hy
    apply Subtype.ext
    rw [e.sliceInverse_eq x hyt]
    have he : (curveCoordinate e.coordinate y.val,0)=e.ambient y.val := by
      rw [e.ambient_apply,hy0]
    rw [he]
    exact e.ambient.left_inv hy
  right_inv' := by
    intro t ht
    rw [e.sliceInverse_eq x ht]
    simpa only [e.ambient_apply] using congrArg Prod.fst (e.ambient.right_inv ht)
  open_source := e.ambient.open_source.preimage continuous_subtype_val
  open_target := e.ambient.open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun := ((curveCoordinate e.coordinate).continuous.comp continuous_subtype_val).continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply continuous_induced_rng.mpr
    have hc := e.ambient.continuousOn_symm.comp
      (show Continuous (fun t : ℂ => (t,(0 : Fin m → ℂ))) from
        continuous_id.prodMk continuous_const).continuousOn (mapsTo_preimage _ _)
    rw [continuousOn_iff_continuous_domRestrict] at hc
    exact hc.congr (fun t => (e.sliceInverse_eq x t.property).symm)

@[simp] theorem sliceChart_apply (x y : locus a) :
    e.sliceChart x y=curveCoordinate e.coordinate y.val := rfl

@[simp] theorem sliceChart_source (x : locus a) :
    (e.sliceChart x).source=Subtype.val ⁻¹' e.ambient.source := rfl

@[simp] theorem sliceChart_target (x : locus a) :
    (e.sliceChart x).target=(fun t : ℂ => (t,(0 : Fin m → ℂ))) ⁻¹' e.ambient.target := rfl

theorem sliceChart_symm_eq (x : locus a) {t : ℂ} (ht : t∈(e.sliceChart x).target) :
    ((e.sliceChart x).symm t : Affine m)=e.ambient.symm (t,0) := e.sliceInverse_eq x ht

theorem sliceChart_inverse_smooth (x : locus a) :
    ContDiffOn ℂ ∞ (fun t => ((e.sliceChart x).symm t : Affine m)) (e.sliceChart x).target := by
  have hs : ContDiff ℂ ∞ (fun t : ℂ => (t,(0 : Fin m → ℂ))) :=
    contDiff_id.prodMk contDiff_const
  have hc := e.smooth_inverse.comp hs.contDiffOn (mapsTo_preimage _ _)
  exact hc.congr (fun t ht => e.sliceChart_symm_eq x ht)

theorem transition_smooth (x : locus a) (f : NormalChart a) (y : locus a) :
    ContDiffOn ℂ ∞ ((e.sliceChart x).symm.trans (f.sliceChart y))
      ((e.sliceChart x).symm.trans (f.sliceChart y)).source := by
  have hc := (curveCoordinate f.coordinate).contDiff.comp_contDiffOn (e.sliceChart_inverse_smooth x)
  exact hc.mono inter_subset_left

end NormalChart

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
