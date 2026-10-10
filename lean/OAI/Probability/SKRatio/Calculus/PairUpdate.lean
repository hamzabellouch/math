import Mathlib
import OAI.Probability.SKRatio.Calculus.Expectation

namespace OAI

section
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace SKRatio.Fields
open Real Matrix TwoSpin
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

lemma tanh_pair_mean (α J : ℝ) (y : Bool) :
    tanh (α+J*spinValue y)=TwoSpin.pairConditionalMean (tanh α) (tanh J) y := by
  have hh : tanh (J*spinValue y)=tanh J*spinValue y := by
    cases y <;> simp only [spinValue_false,spinValue_true,mul_one,mul_neg_one,tanh_neg]
  rw [tanh_add_real,hh]
  simp only [TwoSpin.pairConditionalMean,mul_comm,mul_assoc]

lemma pairBoltzmann_cubic_bound (α γ J : ℝ) (F : Bool → Bool → ℝ)
    (hJ : |tanh J| ≤ 1/1000) :
    let g₁ := fun y => (F true y-F false y)/2;
    let g₂ := fun x => (F x true-F x false)/2;
    let m₁ := fun y => tanh (α+J*spinValue y);
    let m₂ := fun x => tanh (γ+J*spinValue x);
    let v₁ := fun y => 1-m₁ y^2;
    let v₂ := fun x => 1-m₂ x^2;
    -pairBoltzmannMean α γ J (fun x y =>
      (tanh J+2*(tanh J)^2*m₁ y*m₂ x)*v₁ y*v₂ x*g₁ y*g₂ x) -
      1920000*|tanh J|^3*pairBoltzmannMean α γ J (fun x y =>
        v₁ y*(g₁ y)^2+v₂ x*(g₂ x)^2) ≤
    pairBoltzmannMean α γ J (fun x y =>
      (spinValue x-m₁ y)*g₁ y*((spinValue y-m₂ x)*g₂ x)) := by
  dsimp only
  obtain ⟨p,s,r,hg₁,hg₂⟩ := pair_gradients_representation F (tanh α) (tanh γ)
  simp_rw [pairBoltzmannMean_eq,tanh_pair_residual,tanh_pair_variance,
    tanh_pair_mean,hg₁,hg₂]
  exact pair_cubic_signed_bound (abs_tanh_lt_one α).le (abs_tanh_lt_one γ).le hJ

lemma update_true_false (i : Fin n) (x : Spin n) :
    (Function.update x i true=x ∧ Function.update x i false=flip i x) ∨
      (Function.update x i true=flip i x ∧ Function.update x i false=x) := by
  cases hx : x i
  · right
    constructor
    · simp [flip,hx]
    · simpa only [hx] using Function.update_eq_self i x
  · left
    constructor
    · simpa only [hx] using Function.update_eq_self i x
    · simp [flip,hx]

lemma conditionalExpectation_updates (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (∑ b : Bool,weight g h (Function.update x i b)*f (Function.update x i b))/
      (∑ b : Bool,weight g h (Function.update x i b)) := by
  simp only [Fintype.sum_bool]
  rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]
  · rfl
  · unfold conditionalExpectation
    rw [add_comm (weight g h (flip i x)*f (flip i x)),add_comm (weight g h (flip i x))]

lemma weight_update_factor (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) (b : Bool) :
    weight g h (Function.update x i b)=exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
      exp (localField g h i x*spinValue b) := by
  unfold weight
  rw [hamiltonian_update,← exp_add]
  congr 1;ring

lemma conditionalExpectation_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i f x=
      (f (Function.update x i true)+f (Function.update x i false))/2+
        tanh (localField g h i x)*spinGradient i f x := by
  rw [conditionalExpectation_updates]
  simp_rw [weight_update_factor,exp_spin]
  simp only [Fintype.sum_bool,spinValue_true,spinValue_false,mul_one,mul_neg_one]
  unfold spinGradient
  have h₁ := (exp_pos (hamiltonian g h x-spinValue (x i)*localField g h i x)).ne'
  have h₂ := (cosh_pos (localField g h i x)).ne'
  have he : exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+tanh (localField g h i x)))+
      exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*
        (cosh (localField g h i x)*(1+-tanh (localField g h i x)))=
      2*exp (hamiltonian g h x-spinValue (x i)*localField g h i x)*cosh (localField g h i x) := by ring
  rw [he]
  field_simp [h₁,h₂]
  ring

lemma spin_affine (i : Fin n) (f : Spin n→ℝ) (x : Spin n) :
    f x=(f (Function.update x i true)+f (Function.update x i false))/2+
      spinValue (x i)*spinGradient i f x := by
  unfold spinGradient
  cases hx : x i
  · have hf : Function.update x i false=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_false,hf];ring
  · have ht : Function.update x i true=x := by simpa only [hx] using Function.update_eq_self i x
    rw [spinValue_true,ht];ring

lemma conditionalDifference_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) (x : Spin n) :
    f x-conditionalExpectation g h i f x=
      (spinValue (x i)-tanh (localField g h i x))*spinGradient i f x := by
  rw [conditionalExpectation_local]
  have he := spin_affine i f x
  linarith only [he]

lemma spinGradient_update (i : Fin n) (f : Spin n→ℝ) (x : Spin n) (b : Bool) :
    spinGradient i f (Function.update x i b)=spinGradient i f x := by
  simp only [spinGradient,Function.update_idem]

lemma conditionalSiteEnergy_local (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f : Spin n→ℝ) :
    expectation g h (fun x=>(f x-conditionalExpectation g h i f x)^2)=
      expectation g h (fun x=>(1-tanh (localField g h i x)^2)*spinGradient i f x^2) := by
  rw [← expectation_conditionalExpectation g h i]
  congr 1
  funext x
  rw [conditionalExpectation_local]
  simp_rw [conditionalDifference_local,localField_update_self,spinGradient_update]
  simp only [Function.update_self,spinValue_true,spinValue_false,spinGradient]
  simp_rw [Function.update_idem,localField_update_self]
  ring

def pairUpdate (i j : Fin n) (x : Spin n) (a b : Bool) : Spin n :=
  Function.update (Function.update x i a) j b

lemma pairUpdate_overwrite (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b c d : Bool) :
    pairUpdate i j (pairUpdate i j x a b) c d=pairUpdate i j x c d := by
  funext k
  by_cases hj : k=j
  · subst k;simp [pairUpdate]
  · by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · simp [pairUpdate,hj,hi]

lemma pairUpdate_left (i j : Fin n) (hij : i ≠ j) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b i=a := by simp [pairUpdate,hij]
lemma pairUpdate_right (i j : Fin n) (x : Spin n) (a b : Bool) :
    pairUpdate i j x a b j=b := by simp [pairUpdate]

lemma sum_spin_update (i : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ b : Bool,F (Function.update x i b))=2*∑ x,F x := by
  have he (x : Spin n) : (∑ b : Bool,F (Function.update x i b))=F x+F (flip i x) := by
    simp only [Fintype.sum_bool]
    rcases update_true_false i x with ⟨ht,hf⟩|⟨ht,hf⟩ <;> rw [ht,hf]; ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,sum_flip]
  ring

lemma sum_pairUpdate (i j : Fin n) (F : Spin n→ℝ) :
    (∑ x,∑ a : Bool,∑ b : Bool,F (pairUpdate i j x a b))=4*∑ x,F x := by
  unfold pairUpdate
  rw [sum_spin_update i (fun x=>∑ b : Bool,F (Function.update x j b)),sum_spin_update]
  ring

def pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (F : Spin n→ℝ) (x : Spin n) : ℝ :=
  (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b)*F (pairUpdate i j x a b))/
    (∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b))

lemma pairConditionalMean_update (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) (a b : Bool) :
    pairConditionalMean g h i j F (pairUpdate i j x a b)=pairConditionalMean g h i j F x := by
  simp only [pairConditionalMean,pairUpdate_overwrite i j hij]

lemma pairConditional_partition_pos (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (x : Spin n) :
    0 < ∑ a : Bool,∑ b : Bool,weight g h (pairUpdate i j x a b) := by
  simp only [Fintype.sum_bool]
  exact add_pos (add_pos (weight_pos _ _ _) (weight_pos _ _ _))
    (add_pos (weight_pos _ _ _) (weight_pos _ _ _))

lemma expectation_pairConditionalMean (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) : expectation g h (pairConditionalMean g h i j F)=expectation g h F := by
  have h₁ := sum_pairUpdate i j (fun x=>mass g h x*pairConditionalMean g h i j F x)
  have h₂ := sum_pairUpdate i j (fun x=>mass g h x*F x)
  have he : (∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*
      pairConditionalMean g h i j F (pairUpdate i j x a b))=
      ∑ x,∑ a : Bool,∑ b : Bool,mass g h (pairUpdate i j x a b)*F (pairUpdate i j x a b) := by
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [pairConditionalMean_update g h i j hij,mass,div_mul_eq_mul_div]
    simp only [← Finset.sum_div,← Finset.sum_mul]
    unfold pairConditionalMean
    rw [mul_div_cancel₀ _ (pairConditional_partition_pos g h i j x).ne']
  unfold expectation
  linarith only [h₁,h₂,he]

lemma pairUpdate_hamiltonian (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (x : Spin n) (a b : Bool) :
    let α := localField g h i x-coupling g i j*spinValue (x j);
    let γ := localField g h j x-coupling g i j*spinValue (x i);
    hamiltonian g h (pairUpdate i j x a b)=
      (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
        coupling g i j*spinValue (x i)*spinValue (x j))+
      (α*spinValue a+γ*spinValue b+coupling g i j*spinValue a*spinValue b) := by
  dsimp only
  unfold pairUpdate
  rw [hamiltonian_update,hamiltonian_update,localField_update,
    Function.update_of_ne (Ne.symm hij),coupling_symm g j i]
  ring

lemma pairUpdate_localField₁ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h i (pairUpdate i j x a b)=
      (localField g h i x-coupling g i j*spinValue (x j))+coupling g i j*spinValue b := by
  unfold pairUpdate
  rw [localField_update,localField_update_self]
  by_cases hij : i=j
  · subst j;simp
  · rw [Function.update_of_ne (Ne.symm hij)]
    ring

lemma pairUpdate_localField₂ (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n)
    (x : Spin n) (a b : Bool) :
    localField g h j (pairUpdate i j x a b)=
      (localField g h j x-coupling g i j*spinValue (x i))+coupling g i j*spinValue a := by
  unfold pairUpdate
  rw [localField_update_self,localField_update,coupling_symm g j i]
  ring

lemma pairUpdate_gradient₁ (i j : Fin n) (hij : i ≠ j) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient i F (pairUpdate i j x a b)=
      (F (pairUpdate i j x true b)-F (pairUpdate i j x false b))/2 := by
  have he (c : Bool) : Function.update (pairUpdate i j x a b) i c=pairUpdate i j x c b := by
    funext k
    by_cases hi : k=i
    · subst k;simp [pairUpdate,hij]
    · by_cases hj : k=j
      · subst k;simp [pairUpdate,hij.symm]
      · simp [pairUpdate,hj,hi]
  simp only [spinGradient,he]
lemma pairUpdate_gradient₂ (i j : Fin n) (F : Spin n→ℝ)
    (x : Spin n) (a b : Bool) :
    spinGradient j F (pairUpdate i j x a b)=
      (F (pairUpdate i j x a true)-F (pairUpdate i j x a false))/2 := by
  simp only [spinGradient,pairUpdate,Function.update_idem]

lemma pairConditionalMean_boltzmann (g : Disorder n) (h : Fin n→ℝ) (i j : Fin n) (hij : i ≠ j)
    (F : Spin n→ℝ) (x : Spin n) :
    pairConditionalMean g h i j F x=
      pairBoltzmannMean (localField g h i x-coupling g i j*spinValue (x j))
        (localField g h j x-coupling g i j*spinValue (x i)) (coupling g i j)
        (fun a b=>F (pairUpdate i j x a b)) := by
  let α := localField g h i x-coupling g i j*spinValue (x j)
  let γ := localField g h j x-coupling g i j*spinValue (x i)
  let C := exp (hamiltonian g h x-α*spinValue (x i)-γ*spinValue (x j)-
    coupling g i j*spinValue (x i)*spinValue (x j))
  have hC : C ≠ 0 := (exp_pos _).ne'
  have hw (a b : Bool) : weight g h (pairUpdate i j x a b)=C*pairBoltzmannWeight α γ (coupling g i j) a b := by
    unfold weight
    rw [pairUpdate_hamiltonian g h i j hij,exp_add]
    rfl
  unfold pairConditionalMean
  simp_rw [hw,mul_assoc,← Finset.mul_sum]
  rw [mul_div_mul_left _ _ hC]
  rfl

def siteVariance (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) : ℝ :=
  1-tanh (localField g h i x)^2

def weightedGradient (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (f : Spin n→ℝ) (x : Spin n) : ℝ :=
  siteVariance g h i x*spinGradient i f x

lemma expectation_mono (g : Disorder n) (h : Fin n→ℝ) {F G : Spin n→ℝ}
    (hFG : ∀ x,F x ≤ G x) : expectation g h F ≤ expectation g h G := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (hFG x) (mass_nonneg g h x)

lemma pairConditional_cubic_bound (g : Disorder n) (h : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (f : Spin n → ℝ) (x : Spin n)
    (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -pairConditionalMean g h i j (fun y =>
      (tanh (coupling g i j)+2*(tanh (coupling g i j))^2*
        tanh (localField g h i y)*tanh (localField g h j y))*
          siteVariance g h i y*siteVariance g h j y*spinGradient i f y*spinGradient j f y) x -
    1920000*|tanh (coupling g i j)|^3*pairConditionalMean g h i j
      (fun y => siteVariance g h i y*spinGradient i f y^2+
        siteVariance g h j y*spinGradient j f y^2) x ≤
    pairConditionalMean g h i j (fun y => (f y-conditionalExpectation g h i f y)*
      (f y-conditionalExpectation g h j f y)) x := by
  simp_rw [pairConditionalMean_boltzmann g h i j hij,siteVariance,
    conditionalDifference_local,pairUpdate_localField₁,pairUpdate_localField₂,
    pairUpdate_gradient₁ i j hij,pairUpdate_gradient₂,pairUpdate_left i j hij,pairUpdate_right]
  exact pairBoltzmann_cubic_bound
    (localField g h i x-coupling g i j*spinValue (x j))
    (localField g h j x-coupling g i j*spinValue (x i))
    (coupling g i j) (fun a b => f (pairUpdate i j x a b)) hc

lemma gibbs_pair_cubic_bound (g : Disorder n) (h : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (f : Spin n → ℝ)
    (hc : |tanh (coupling g i j)| ≤ 1/1000) :
    -expectation g h (fun y =>
      (tanh (coupling g i j)+2*(tanh (coupling g i j))^2*
        tanh (localField g h i y)*tanh (localField g h j y))*
          siteVariance g h i y*siteVariance g h j y*spinGradient i f y*spinGradient j f y) -
    1920000*|tanh (coupling g i j)|^3*(expectation g h
      (fun y => siteVariance g h i y*spinGradient i f y^2)+expectation g h
      (fun y => siteVariance g h j y*spinGradient j f y^2)) ≤
    expectation g h (fun y => (f y-conditionalExpectation g h i f y)*
      (f y-conditionalExpectation g h j f y)) := by
  have hh := expectation_mono g h (fun x => pairConditional_cubic_bound g h i j hij f x hc)
  have eneg (F : Spin n → ℝ) : expectation g h (fun x => -F x) = -expectation g h F := by
    simp [expectation]
  simpa only [expectation_sub,expectation_const_mul,expectation_pairConditionalMean g h i j hij,
    expectation_add,eneg] using hh

lemma siteVariance_pos (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    0 < siteVariance g h i x := by
  unfold siteVariance
  have ht := abs_tanh_lt_one (localField g h i x)
  have hs := (sq_lt_sq₀ (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).mpr ht
  simp only [sq_abs,one_pow] at hs
  linarith only [hs]
lemma siteVariance_le_one (g : Disorder n) (h : Fin n→ℝ) (i : Fin n) (x : Spin n) :
    siteVariance g h i x ≤ 1 := sub_le_self _ (sq_nonneg _)

lemma dirichlet_weighted (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    dirichlet g h f=∑ i,expectation g h (fun x=>siteVariance g h i x*spinGradient i f x^2) := by
  unfold dirichlet siteVariance
  simp_rw [conditionalSiteEnergy_local]

lemma heatBathGenerator_square (g : Disorder n) (h : Fin n→ℝ) (f : Spin n→ℝ) :
    expectation g h (fun x=>heatBathGenerator g h f x^2)=
      ∑ i,∑ j,expectation g h (fun x=>(f x-conditionalExpectation g h i f x)*
        (f x-conditionalExpectation g h j f x)) := by
  simp only [heatBathGenerator,sq,Finset.sum_mul,Finset.mul_sum,expectation_sum]
  rw [Finset.sum_comm]

lemma positive_form_cauchy {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫) (u v : E) :
    ⟪u,H v⟫^2 ≤ ⟪u,H u⟫*⟪v,H v⟫ := by
  have hh : ∀ t : ℝ,0 ≤ ⟪v,H v⟫*(t*t)+(2*⟪u,H v⟫)*t+⟪u,H u⟫ := by
    intro t
    have hp := hpos (u+t • v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right] at hp
    have he : ⟪v,H u⟫=⟪u,H v⟫ := (real_inner_comm (H u) v).trans (hH u v)
    rw [he] at hp
    nlinarith only [hp]
  have hd := discrim_le_zero hh
  unfold discrim at hd
  nlinarith only [hd]

lemma curvature_poincare_on_kernel_orthogonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric) (hpos : ∀ v,0 ≤ ⟪v,H v⟫)
    {ρ : ℝ} (hρ : 0 < ρ) (hcurv : ∀ v,ρ*⟪v,H v⟫ ≤ ⟪H v,H v⟫)
    (f : E) (hf : f ∈ (LinearMap.ker H)ᗮ) :
    ρ*⟪f,f⟫ ≤ ⟪f,H f⟫ := by
  have hrange : f ∈ LinearMap.range H := by
    rwa [← hH.orthogonal_range,Submodule.orthogonal_orthogonal] at hf
  obtain ⟨g,rfl⟩ := hrange
  have hc := positive_form_cauchy H hH hpos (H g) g
  have hg := hcurv g
  have hp := hpos (H g)
  have hn : 0 ≤ ⟪H g,H g⟫ := real_inner_self_nonneg
  have hh : ρ*⟪H g,H g⟫^2 ≤ ⟪H g,H (H g)⟫*⟪H g,H g⟫ := by
    calc
      _ ≤ ρ*(⟪H g,H (H g)⟫*⟪g,H g⟫) := mul_le_mul_of_nonneg_left hc hρ.le
      _ = ⟪H g,H (H g)⟫*(ρ*⟪g,H g⟫) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hg hp
  by_cases hz : ⟪H g,H g⟫=0
  · rw [hz,mul_zero];exact hp
  · have hpos' : 0 < ⟪H g,H g⟫ := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith only [hh,hpos']

lemma conditionalExpectation_add (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (f k : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (f+k) x=conditionalExpectation g h i f x+conditionalExpectation g h i k x := by
  unfold conditionalExpectation
  simp only [Pi.add_apply]
  ring
lemma conditionalExpectation_smul (g : Disorder n) (h : Fin n→ℝ) (i : Fin n)
    (c : ℝ) (f : Spin n→ℝ) (x : Spin n) :
    conditionalExpectation g h i (c • f) x=c*conditionalExpectation g h i f x := by
  unfold conditionalExpectation
  simp only [Pi.smul_apply,smul_eq_mul]
  ring

def heatBathLinear (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) →ₗ[ℝ] (Spin n→ℝ) where
  toFun := heatBathGenerator g h
  map_add' f k := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_add,Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _;ring
  map_smul' c f := by
    funext x
    simp only [heatBathGenerator,conditionalExpectation_smul,Pi.smul_apply,smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _;ring

def gibbsScale (g : Disorder n) (h : Fin n→ℝ) : (Spin n→ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Spin n) where
  toFun f := WithLp.toLp 2 (fun x=>sqrt (mass g h x)*f x)
  invFun v := fun x=>v x/sqrt (mass g h x)
  left_inv f := by
    funext x
    change sqrt (mass g h x)*f x/sqrt (mass g h x)=f x
    exact mul_div_cancel_left₀ (f x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  right_inv v := by
    ext x
    exact mul_div_cancel₀ (v x) (sqrt_pos.mpr (mass_pos g h x)).ne'
  map_add' f k := by ext x;simp [mul_add]
  map_smul' c f := by ext x;simp [mul_left_comm]

lemma gibbsScale_inner (g : Disorder n) (h : Fin n→ℝ) (f k : Spin n→ℝ) :
    ⟪gibbsScale g h f,gibbsScale g h k⟫=expectation g h (fun x=>f x*k x) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
  unfold dotProduct expectation
  apply Finset.sum_congr rfl
  intro x _
  change sqrt (mass g h x)*k x*(sqrt (mass g h x)*f x)=mass g h x*(f x*k x)
  calc
    _ = sqrt (mass g h x)^2*(f x*k x) := by ring
    _ = _ := by rw [sq_sqrt (mass_nonneg g h x)]

lemma heatBathLinear_const (g : Disorder n) (h : Fin n→ℝ) (c : ℝ) :
    heatBathLinear g h (fun _=>c)=0 := by
  funext x
  simp only [heatBathLinear,heatBathGenerator,LinearMap.coe_mk,AddHom.coe_mk,
    conditionalExpectation_const,sub_self,Finset.sum_const_zero,Pi.zero_apply]

end SKRatio.Fields
end
end

end OAI
