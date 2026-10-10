import OAI.MathematicalPhysics.CriticalSK.HeatBath
import OAI.MathematicalPhysics.CriticalSK.SphereGeometry

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

namespace CriticalSK

section

open Set Filter MeasureTheory

variable {n : ℕ}

def flipSite (i : Fin n) (x : Spin n) : Spin n := Function.update x i (!(x i))

@[simp] lemma flipSite_apply_self (i : Fin n) (x : Spin n) : flipSite i x i = !(x i) := by simp [flipSite]

@[simp] lemma flipSite_apply_ne (i : Fin n) (x : Spin n) {j : Fin n} (h : j ≠ i) : flipSite i x j = x j := by simp [flipSite,h]

@[simp] lemma flipSite_involutive (i : Fin n) (x : Spin n) : flipSite i (flipSite i x) = x := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj]

lemma flipSite_ne (i : Fin n) (x : Spin n) : flipSite i x ≠ x := by
  intro hh
  have he := congrFun hh i
  simp only [flipSite_apply_self] at he
  cases h : x i <;> simp_all

def flipSiteEquiv (i : Fin n) : Spin n ≃ Spin n where
  toFun := flipSite i
  invFun := flipSite i
  left_inv := flipSite_involutive i
  right_inv := flipSite_involutive i

lemma sameExcept_flipSite (i : Fin n) (x : Spin n) : sameExcept i x (flipSite i x) := by
  intro j hj
  exact flipSite_apply_ne i x hj

lemma sameExcept_two (i : Fin n) (x y : Spin n) :
    sameExcept i x y ↔ y=x ∨ y=flipSite i x := by
  constructor
  · intro h
    by_cases he : y i=x i
    · left
      funext j
      by_cases hj : j=i
      · simpa only [hj] using he
      · exact h j hj
    · right
      funext j
      by_cases hj : j=i
      · subst j
        simp only [flipSite_apply_self]
        cases hx : x i <;> cases hy : y i <;> simp_all
      · rw [flipSite_apply_ne i x hj]
        exact h j hj
  · rintro (h|h)
    · subst y; exact sameExcept_refl i x
    · subst y; exact sameExcept_flipSite i x

lemma sum_sameExcept (i : Fin n) (x : Spin n) (f : Spin n → ℝ) :
    (∑ y : Spin n, if sameExcept i x y then f y else 0) = f x+f (flipSite i x) := by
  classical
  have he (y : Spin n) : (if sameExcept i x y then f y else 0) =
      (if y=x then f x else 0)+(if y=flipSite i x then f (flipSite i x) else 0) := by
    simp only [sameExcept_two]
    have hne := flipSite_ne i x
    split_ifs <;> simp_all
  simp_rw [he]
  simp [Finset.sum_add_distrib]

def incidentCoeff (i : Fin n) (x : Spin n) (e : Edge n) : ℝ :=
  if e.val.1=i then spinValue (x e.val.2) else if e.val.2=i then spinValue (x e.val.1) else 0

def localField (W : Disorder n) (i : Fin n) (x : Spin n) : ℝ :=
  ∑ e : Edge n, W e*incidentCoeff i x e

def deleteDisorder (W : Disorder n) (i : Fin n) : Disorder n :=
  fun e => if e.val.1=i ∨ e.val.2=i then 0 else W e

lemma incidentCoeff_fiber {i : Fin n} {x y : Spin n} (h : sameExcept i x y) (e : Edge n) :
    incidentCoeff i y e = incidentCoeff i x e := by
  unfold incidentCoeff
  have hne : e.val.1 ≠ e.val.2 := ne_of_lt e.property
  split_ifs with h1 h2
  · rw [h e.val.2 (by grind)]
  · rw [h e.val.1 h1]
  · rfl

lemma localField_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    localField W i y = localField W i x := by
  simp_rw [localField,incidentCoeff_fiber h]

lemma delete_hamiltonian_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    hamiltonian (deleteDisorder W i) y = hamiltonian (deleteDisorder W i) x := by
  unfold hamiltonian deleteDisorder
  apply Finset.sum_congr rfl
  intro e _
  split_ifs with he
  · simp
  · rw [h e.val.1 (fun hh => he (Or.inl hh)), h e.val.2 (fun hh => he (Or.inr hh))]

lemma hamiltonian_cavity (W : Disorder n) (i : Fin n) (x : Spin n) :
    hamiltonian W x = hamiltonian (deleteDisorder W i) x+spinValue (x i)*localField W i x := by
  simp only [hamiltonian,localField,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  unfold deleteDisorder incidentCoeff
  by_cases h1 : e.val.1=i
  · simp [h1]; ring
  · by_cases h2 : e.val.2=i
    · simp [h1,h2]; ring
    · simp [h1,h2]

lemma gibbs_delete_fiber (W : Disorder n) {i : Fin n} {x y : Spin n} (h : sameExcept i x y) :
    gibbs (deleteDisorder W i) y = gibbs (deleteDisorder W i) x := by
  simp only [gibbs,delete_hamiltonian_fiber W h]

lemma cavity_exp_pair (W : Disorder n) (i : Fin n) (x : Spin n) :
    (Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/2 =
      Real.exp (hamiltonian (deleteDisorder W i) x)*Real.cosh (localField W i x) := by
  rw [hamiltonian_cavity W i x,hamiltonian_cavity W i (flipSite i x),
    localField_fiber W (sameExcept_flipSite i x),delete_hamiltonian_fiber W (sameExcept_flipSite i x)]
  simp only [Real.exp_add,flipSite_apply_self,spinValue_not,Real.cosh_eq]
  cases x i <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,neg_neg] <;> ring

def cavityNormalization (W : Disorder n) (i : Fin n) : ℝ :=
  mean (deleteDisorder W i) (fun x => Real.cosh (localField W i x))

lemma cavityNormalization_ge_one (W : Disorder n) (i : Fin n) : 1 ≤ cavityNormalization W i := by
  rw [cavityNormalization,← mean_const (deleteDisorder W i) 1]
  exact mean_mono _ (fun _ => Real.one_le_cosh _)

lemma partition_cavity (W : Disorder n) (i : Fin n) :
    partition W = partition (deleteDisorder W i)*cavityNormalization W i := by
  have hh : ∑ x : Spin n, Real.exp (hamiltonian W (flipSite i x)) = partition W :=
    (flipSiteEquiv i).sum_comp (fun x => Real.exp (hamiltonian W x))
  have hs := congrArg (fun f : Spin n → ℝ => ∑ x, f x) (funext (cavity_exp_pair W i))
  rw [← Finset.sum_div,Finset.sum_add_distrib,hh] at hs
  change (partition W+partition W)/2 = _ at hs
  unfold cavityNormalization mean gibbs
  simp only [Finset.mul_sum]
  rw [show (fun x : Spin n => partition (deleteDisorder W i)*(Real.exp (hamiltonian (deleteDisorder W i) x)/partition (deleteDisorder W i)*Real.cosh (localField W i x))) =
    (fun x => Real.exp (hamiltonian (deleteDisorder W i) x)*Real.cosh (localField W i x)) by
      funext x
      field_simp [ne_of_gt (partition_pos (deleteDisorder W i))]]
  linarith

lemma gibbs_cavity (W : Disorder n) (i : Fin n) (x : Spin n) :
    gibbs W x = gibbs (deleteDisorder W i) x*Real.exp (spinValue (x i)*localField W i x)/cavityNormalization W i := by
  simp only [gibbs,partition_cavity W i,hamiltonian_cavity W i x,Real.exp_add]
  ring

lemma gibbs_cavity_pair (W : Disorder n) (i : Fin n) (x : Spin n) :
    (gibbs W x+gibbs W (flipSite i x))/2 =
      gibbs (deleteDisorder W i) x*Real.cosh (localField W i x)/cavityNormalization W i := by
  unfold gibbs
  rw [← add_div]
  rw [show (Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/partition W/2 =
    ((Real.exp (hamiltonian W x)+Real.exp (hamiltonian W (flipSite i x)))/2)/partition W by ring]
  rw [cavity_exp_pair,partition_cavity W i]
  ring

lemma mean_cavity_even (W : Disorder n) (i : Fin n) (f : Spin n → ℝ)
    (hf : ∀ x, f (flipSite i x)=f x) :
    mean W f = mean (deleteDisorder W i) (fun x => Real.cosh (localField W i x)*f x)/cavityNormalization W i := by
  have hh : ∑ x : Spin n, gibbs W (flipSite i x)*f (flipSite i x) = mean W f :=
    (flipSiteEquiv i).sum_comp (fun x => gibbs W x*f x)
  simp_rw [hf] at hh
  have hs := congrArg (fun g : Spin n → ℝ => ∑ x, g x) (funext (fun x => congrArg (fun a : ℝ => a*f x) (gibbs_cavity_pair W i x)))
  simp only [add_div,add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib,← Finset.sum_div,hh] at hs
  unfold mean at *
  simp only [mul_assoc] at hs
  linarith

lemma siteAverage_two (W : Disorder n) (i : Fin n) (f : Spin n → ℝ) (x : Spin n) :
    siteAverage W i f x = (gibbs W x*f x+gibbs W (flipSite i x)*f (flipSite i x))/(gibbs W x+gibbs W (flipSite i x)) := by
  rw [siteAverage_eq]
  simp only [siteKernel]
  have he (y : Spin n) : (if sameExcept i x y then gibbs W y/(∑ z, if sameExcept i x z then gibbs W z else 0) else 0)*f y =
      (if sameExcept i x y then gibbs W y*f y else 0)/(∑ z, if sameExcept i x z then gibbs W z else 0) := by
    split_ifs <;> ring
  simp_rw [he]
  rw [← Finset.sum_div,sum_sameExcept,sum_sameExcept]

lemma siteAverage_spin (W : Disorder n) (i : Fin n) (x : Spin n) :
    siteAverage W i (fun y => spinValue (y i)) x = Real.sinh (localField W i x)/Real.cosh (localField W i x) := by
  rw [siteAverage_two,gibbs_cavity W i x,gibbs_cavity W i (flipSite i x),
    gibbs_delete_fiber W (sameExcept_flipSite i x),localField_fiber W (sameExcept_flipSite i x)]
  have hg := ne_of_gt (gibbs_pos (deleteDisorder W i) x)
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  rw [Real.sinh_eq,Real.cosh_eq]
  simp only [flipSite_apply_self,spinValue_not]
  cases x i <;> simp only [spinValue,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,neg_neg] <;>
    field_simp [hg,hZ] <;> ring

def alphaSite (W : Disorder n) (i : Fin n) : ℝ := mean W (fun x => (Real.cosh (localField W i x))⁻¹^2)

lemma alphaSite_pos (W : Disorder n) (i : Fin n) : 0 < alphaSite W i := by
  unfold alphaSite mean
  exact Finset.sum_pos (fun _ _ => mul_pos (gibbs_pos W _) (sq_pos_of_pos (inv_pos.mpr (Real.cosh_pos _)))) Finset.univ_nonempty

end

section

open Set Filter MeasureTheory

variable {n : ℕ} (W : Disorder n)

lemma mean_mul_mean_inv {f : Spin n → ℝ} (hf : ∀ x, 0 < f x) :
    1 ≤ mean W f*mean W (fun x => (f x)⁻¹) := by
  have hh := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := gibbs W) (f := fun x => gibbs W x*f x) (g := fun x => gibbs W x*(f x)⁻¹)
    (fun x _ => mul_nonneg (gibbs_nonneg W x) (hf x).le)
    (fun x _ => mul_nonneg (gibbs_nonneg W x) (inv_nonneg.mpr (hf x).le))
    (fun x _ => by apply le_of_eq; field_simp [ne_of_gt (hf x)])
  simpa only [gibbs_sum,one_pow,mean] using hh

lemma alphaSite_cavity (i : Fin n) :
    alphaSite W i = mean (deleteDisorder W i) (fun x => (Real.cosh (localField W i x))⁻¹)/cavityNormalization W i := by
  rw [alphaSite,mean_cavity_even W i _ (fun x => by rw [localField_fiber W (sameExcept_flipSite i x)])]
  congr 1
  congr 1
  funext x
  field_simp

lemma alphaSite_normalization (i : Fin n) : 1 ≤ alphaSite W i*cavityNormalization W i^2 := by
  have hh := mean_mul_mean_inv (deleteDisorder W i) (fun x => Real.cosh_pos (localField W i x))
  rw [alphaSite_cavity]
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  convert hh using 1
  dsimp only [cavityNormalization] at *
  field_simp

lemma one_sub_tanh_sq (z : ℝ) : 1-(Real.sinh z/Real.cosh z)^2 = (Real.cosh z)⁻¹^2 := by
  have hh := Real.cosh_sq_sub_sinh_sq z
  have hc := ne_of_gt (Real.cosh_pos z)
  field_simp
  nlinarith

lemma site_spin_variance (i : Fin n) :
    mean W (fun x => (spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x)^2) = alphaSite W i := by
  rw [siteAverage_form_identity]
  have he : (fun x : Spin n => spinValue (x i)*(spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x)) =
      (fun x => 1-spinValue (x i)*siteAverage W i (fun y => spinValue (y i)) x) := by
    funext x
    have hh := spinValue_sq (x i)
    nlinarith
  rw [he,mean_sub,siteAverage_self_square,← mean_sub]
  simp_rw [siteAverage_spin,one_sub_tanh_sq]
  rfl

lemma siteAverage_const_mul (i : Fin n) (c : ℝ) (f : Spin n → ℝ) :
    siteAverage W i (fun x => c*f x) = fun x => c*siteAverage W i f x := by
  funext x
  simp only [siteAverage_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma siteAverage_linear_residual (i : Fin n) (a : Fin n → ℝ) (x : Spin n) :
    linearObservable a x-siteAverage W i (linearObservable a) x =
      a i*(spinValue (x i)-siteAverage W i (fun y => spinValue (y i)) x) := by
  have he : linearObservable a = fun y => a i*spinValue (y i)+linearRest a i y :=
    funext (linearObservable_split a i)
  rw [he,siteAverage_add,siteAverage_const_mul,
    siteAverage_of_fiber_constant W i _ (linearRest_fiber_constant a i)]
  ring

lemma dirichlet_linear_eq (a : Fin n → ℝ) :
    dirichlet W (linearObservable a) = ∑ i, alphaSite W i*a i^2 := by
  unfold dirichlet
  simp_rw [← siteAverage_eq,siteAverage_linear_residual,mul_pow,mean_const_mul,site_spin_variance]
  congr 1
  funext i
  ring

lemma dirichlet_linear_pos {a : Fin n → ℝ} (ha : a ≠ 0) :
    0 < dirichlet W (linearObservable a) := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp ha
  rw [dirichlet_linear_eq]
  apply Finset.sum_pos' (fun j _ => mul_nonneg (alphaSite_pos W j).le (sq_nonneg _))
  exact ⟨i,Finset.mem_univ i,mul_pos (alphaSite_pos W i) (sq_pos_of_ne_zero hi)⟩

lemma mean_delete_le (i : Fin n) (f : Spin n → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hflip : ∀ x, f (flipSite i x)=f x) :
    mean (deleteDisorder W i) f ≤ cavityNormalization W i*mean W f := by
  rw [mean_cavity_even W i f hflip]
  have hZ : cavityNormalization W i ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (cavityNormalization_ge_one W i))
  rw [mul_div_cancel₀ _ hZ]
  exact mean_mono _ (fun x => le_mul_of_one_le_left (hf x) (Real.one_le_cosh _))

def cavityOverlapCoord (i : Fin n) (x y : Spin n) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, spinValue (x j)*spinValue (y j))/(n:ℝ)

def cavityOverlap (i : Fin n) : ℝ :=
  mean (deleteDisorder W i) (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2))

lemma cavityOverlapCoord_eq (i : Fin n) (x y : Spin n) :
    cavityOverlapCoord i x y = cubeOverlap x y-spinValue (x i)*spinValue (y i)/(n:ℝ) := by
  rw [cubeOverlap_signMean]
  unfold signMean cavityOverlapCoord
  simp only [spinProduct,spinValue_beq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

lemma cavityOverlapCoord_fiber_left {i : Fin n} {x x' : Spin n} (h : sameExcept i x x') (y : Spin n) :
    cavityOverlapCoord i x' y = cavityOverlapCoord i x y := by
  unfold cavityOverlapCoord
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.ne_of_mem_erase hj)]

lemma cavityOverlapCoord_comm (i : Fin n) (x y : Spin n) : cavityOverlapCoord i x y = cavityOverlapCoord i y x := by
  unfold cavityOverlapCoord
  simp only [mul_comm]

lemma cavityOverlap_nonneg (i : Fin n) : 0 ≤ cavityOverlap W i :=
  mean_nonneg _ (fun _ => mean_nonneg _ (fun _ => sq_nonneg _))

lemma cavityOverlap_compare (i : Fin n) :
    cavityOverlap W i ≤ 2*cavityNormalization W i^2*(gibbsOverlap W+(n:ℝ)⁻¹^2) := by
  have hZ := (cavityNormalization_ge_one W i).trans' zero_le_one
  have hfirst := mean_delete_le W i (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2))
    (fun _ => mean_nonneg _ (fun _ => sq_nonneg _))
    (fun x => by simp_rw [cavityOverlapCoord_fiber_left (sameExcept_flipSite i x)])
  have hsecond (x : Spin n) := mean_delete_le W i (fun y => cavityOverlapCoord i x y^2)
    (fun _ => sq_nonneg _) (fun y => by rw [cavityOverlapCoord_comm i x (flipSite i y),
      cavityOverlapCoord_fiber_left (sameExcept_flipSite i y),cavityOverlapCoord_comm])
  have hpoint (x y : Spin n) : cavityOverlapCoord i x y^2 ≤ 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2 := by
    rw [cavityOverlapCoord_eq]
    have hh : (spinValue (x i)*spinValue (y i)/(n:ℝ))^2 = (n:ℝ)⁻¹^2 := by
      rw [div_pow,mul_pow,spinValue_sq,spinValue_sq,one_mul,one_div,inv_pow]
    nlinarith [sq_nonneg (cubeOverlap x y+spinValue (x i)*spinValue (y i)/(n:ℝ))]
  have hQ : mean W (fun x => mean W (fun y => 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2)) =
      2*gibbsOverlap W+2*(n:ℝ)⁻¹^2 := by
    simp_rw [mean_add,mean_const_mul,mean_const]
    unfold mean gibbsOverlap
    simp only [Finset.mul_sum,mul_assoc]
  calc
    cavityOverlap W i ≤ cavityNormalization W i*mean W (fun x => mean (deleteDisorder W i) (fun y => cavityOverlapCoord i x y^2)) := hfirst
    _ ≤ cavityNormalization W i*mean W (fun x => cavityNormalization W i*mean W (fun y => cavityOverlapCoord i x y^2)) :=
      mul_le_mul_of_nonneg_left (mean_mono W hsecond) hZ
    _ = cavityNormalization W i^2*mean W (fun x => mean W (fun y => cavityOverlapCoord i x y^2)) := by rw [mean_const_mul]; ring
    _ ≤ cavityNormalization W i^2*mean W (fun x => mean W (fun y => 2*(cubeOverlap x y)^2+2*(n:ℝ)⁻¹^2)) :=
      mul_le_mul_of_nonneg_left (mean_mono W (fun x => mean_mono W (hpoint x))) (sq_nonneg _)
    _ = _ := by rw [hQ]; ring

end

open Set Filter MeasureTheory ProbabilityTheory

variable {n : ℕ}

def touches (i : Fin n) (e : Edge n) : Prop := e.val.1=i ∨ e.val.2=i

instance (i : Fin n) : DecidablePred (touches i) := fun _ => Classical.propDecidable _

abbrev Incident (i : Fin n) := {e : Edge n // touches i e}

abbrev Nonincident (i : Fin n) := {e : Edge n // ¬touches i e}

def edgeOfOther (i j : Fin n) (h : j ≠ i) : Edge n :=
  if hij : i < j then ⟨(i,j),hij⟩ else ⟨(j,i),lt_of_le_of_ne (le_of_not_gt hij) h⟩

lemma edgeOfOther_touches (i j : Fin n) (h : j ≠ i) : touches i (edgeOfOther i j h) := by
  unfold edgeOfOther touches
  split_ifs <;> simp

def otherEnd (i : Fin n) (e : Incident i) : Fin n :=
  if e.val.val.1=i then e.val.val.2 else e.val.val.1

lemma otherEnd_ne (i : Fin n) (e : Incident i) : otherEnd i e ≠ i := by
  unfold otherEnd
  have hlt := e.val.property
  split_ifs <;> grind

def incidentOtherEquiv (i : Fin n) : Incident i ≃ {j : Fin n // j ≠ i} where
  toFun e := ⟨otherEnd i e,otherEnd_ne i e⟩
  invFun j := ⟨edgeOfOther i j.val j.property,edgeOfOther_touches i j.val j.property⟩
  left_inv e := by
    apply Subtype.ext
    apply Subtype.ext
    have he := e.property
    have hlt := e.val.property
    dsimp only [touches] at he
    dsimp only [otherEnd,edgeOfOther]
    split_ifs <;> ext <;> grind
  right_inv j := by
    apply Subtype.ext
    dsimp only [otherEnd,edgeOfOther]
    split_ifs <;> grind

lemma incidentCoeff_other (i : Fin n) (x : Spin n) (e : Incident i) :
    incidentCoeff i x e.val = spinValue (x ((incidentOtherEquiv i) e).val) := by
  change incidentCoeff i x e.val = spinValue (x (otherEnd i e))
  unfold incidentCoeff otherEnd
  have he := e.property
  dsimp only [touches] at he
  split_ifs <;> grind

lemma sum_incident_other (i : Fin n) (f : Fin n → ℝ) :
    (∑ e : Incident i, f (otherEnd i e)) = ∑ j ∈ Finset.univ.erase i, f j := by
  calc
    _ = ∑ j : {j : Fin n // j ≠ i}, f j := (incidentOtherEquiv i).sum_comp _
    _ = _ := (Finset.sum_subtype (Finset.univ.erase i) (by intro j; simp [ne_comm]) f).symm

lemma incident_coeff_square (i : Fin n) (x : Spin n) :
    (∑ e : Incident i, incidentCoeff i x e.val^2) = (n:ℝ)-1 := by
  simp_rw [incidentCoeff_other]
  change (∑ e : Incident i, (spinValue (x (otherEnd i e)))^2) = _
  rw [sum_incident_other i (fun j => spinValue (x j)^2)]
  simp only [spinValue_sq,Finset.sum_const, nsmul_eq_mul,mul_one]
  rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,Nat.cast_sub (by have := i.isLt; omega),Nat.cast_one]

lemma incident_coeff_product (i : Fin n) (x y : Spin n) :
    (∑ e : Incident i, incidentCoeff i x e.val*incidentCoeff i y e.val) =
      (n:ℝ)*cavityOverlapCoord i x y := by
  simp_rw [incidentCoeff_other]
  change (∑ e : Incident i, spinValue (x (otherEnd i e))*spinValue (y (otherEnd i e))) = _
  rw [sum_incident_other i (fun j => spinValue (x j)*spinValue (y j)),cavityOverlapCoord,mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt (Nat.zero_lt_of_lt i.isLt)))]

def cavitySplit (i : Fin n) : Disorder n ≃ᵐ ((Incident i → ℝ) × (Nonincident i → ℝ)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Edge n => ℝ) (touches i)

def incidentLaw (i : Fin n) : Measure (Incident i → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (n:ℝ≥0)⁻¹

def nonincidentLaw (i : Fin n) : Measure (Nonincident i → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 (n:ℝ≥0)⁻¹

instance (i : Fin n) : IsProbabilityMeasure (incidentLaw i) := by unfold incidentLaw; infer_instance

instance (i : Fin n) : IsProbabilityMeasure (nonincidentLaw i) := by unfold nonincidentLaw; infer_instance

lemma cavitySplit_preserving (i : Fin n) :
    MeasurePreserving (cavitySplit i) (disorderLaw n) ((incidentLaw i).prod (nonincidentLaw i)) :=
  measurePreserving_piEquivPiSubtypeProd _ _

lemma cavityJoin_apply_incident (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (e : Incident i) :
    (cavitySplit i).symm (u,v) e.val = u e := by
  simp [cavitySplit,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,e.property]

lemma cavityJoin_apply_nonincident (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (e : Nonincident i) :
    (cavitySplit i).symm (u,v) e.val = v e := by
  simp [cavitySplit,MeasurableEquiv.piEquivPiSubtypeProd,Equiv.piEquivPiSubtypeProd,e.property]

lemma delete_cavityJoin (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) :
    deleteDisorder ((cavitySplit i).symm (u,v)) i = (cavitySplit i).symm (0,v) := by
  funext e
  by_cases he : touches i e
  · rw [show e = (⟨e,he⟩ : Incident i).val from rfl,cavityJoin_apply_incident]
    simp only [deleteDisorder,ite_eq_left (show e.val.1=i ∨ e.val.2=i from he)]
    rfl
  · rw [show e = (⟨e,he⟩ : Nonincident i).val from rfl,cavityJoin_apply_nonincident]
    simp only [deleteDisorder,ite_eq_right (show ¬(e.val.1=i ∨ e.val.2=i) from he)]
    exact cavityJoin_apply_nonincident i u v ⟨e,he⟩

lemma localField_cavityJoin (i : Fin n) (u : Incident i → ℝ) (v : Nonincident i → ℝ) (x : Spin n) :
    localField ((cavitySplit i).symm (u,v)) i x = ∑ e : Incident i, incidentCoeff i x e.val*u e := by
  unfold localField
  rw [← Fintype.sum_subtype_add_sum_subtype (touches i)]
  have hz : (∑ e : Nonincident i, (cavitySplit i).symm (u,v) e.val*incidentCoeff i x e.val) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have he := e.property
    simp only [touches,not_or] at he
    simp [incidentCoeff,he.1,he.2]
  rw [hz,add_zero]
  simp_rw [cavityJoin_apply_incident,mul_comm]

end CriticalSK

end

end OAI
