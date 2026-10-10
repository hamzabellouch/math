import OAI.MathematicalPhysics.Elasticity.Transport

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
lemma leadingP_neg (θ : Fin 3 → ℂ) (m f : A) : leadingP D θ m (-f)=-leadingP D θ m f := by
  simp only [leadingP,direction,map_neg,smul_neg,Finset.sum_neg_distrib]
  ring
lemma normal_sub (θ : Fin 3 → ℂ) (u v : Fin 3 → A) : normal θ (u-v)=normal θ u-normal θ v := by
  simp only [normal,Pi.sub_apply,smul_sub,Finset.sum_sub_distrib]
lemma normal_neg (θ : Fin 3 → ℂ) (u : Fin 3 → A) : normal θ (-u)=-normal θ u := by
  simp only [normal,Pi.neg_apply,smul_neg,Finset.sum_neg_distrib]

lemma normal_particular (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) (q : A) :
    normal θ (fun i => -(n i • q))=-q := by
  simp only [normal,smul_neg,smul_smul,Finset.sum_neg_distrib]
  rw [← Finset.sum_smul,hn,one_smul]
lemma exists_normalizing_vector (θ : Fin 3 → ℂ) (hθ : θ≠0) : ∃ n : Fin 3 → ℂ,∑ i,θ i*n i=1 := by
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hθ
  change θ i≠0 at hi
  refine ⟨Pi.single i (θ i)⁻¹,?_⟩
  simp [Pi.single_apply,hi]

lemma residual_source_tangent (θ n : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hn : ∑ i,θ i*n i=1)
    (lam m : A) (u : Fin 3 → A) (b : A)
    (hc : normal θ (R D lam m u b)=leadingP D θ m (div D u-b)) :
    normal θ (-R D lam m u b-leadingR D θ lam m (fun i => -(n i • (div D u-b))) 0)=0 := by
  rw [normal_sub,normal_neg,leading_normal D θ hθ,normal_particular θ n hn,leadingP_neg,hc]
  exact sub_self _
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityFrame
open ElasticityAugmented

def tangentProjection (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) : Amp →ₗ[ℂ] Fiber θ :=
  (LinearMap.id-(normal θ).smulRight (n,0)).codRestrict (fiber θ) (by
    intro v
    change normal θ (v-normal θ v • (n,0))=0
    rw [map_sub,map_smul]
    have he : normal θ (n,0)=1 := hn
    rw [he,smul_eq_mul,mul_one,sub_self])
lemma tangentProjection_apply (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1) (v : Amp) :
    ((tangentProjection θ n hn v : Fiber θ) : Amp)=v-normal θ v • (n,0) := rfl
lemma tangentProjection_of_normal (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1)
    (v : Amp) (hv : normal θ v=0) :
    ((tangentProjection θ n hn v : Fiber θ) : Amp)=v := by
  rw [tangentProjection_apply,hv,zero_smul,sub_zero]
lemma tangentProjection_smooth (θ n : Fin 3 → ℂ) (hn : ∑ i,θ i*n i=1)
    (p : Fin 3 → Smooth) (s : Smooth) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => tangentProjection θ n hn
      ((fun i => (p i : X → ℂ) x),(s : X → ℂ) x)) := by
  exact ((tangentProjection θ n hn).toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
    (((contDiff_pi.mpr (fun i => smooth_coe (p i))).prodMk (smooth_coe s)))

lemma smooth_vector_forced (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (f : Fiber θ) (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)+f) :
    ∀ i,(direction (A := Smooth) coord θ (vectorSmooth θ u hu i) : X → ℂ) x=
      θ i*(scalarSmooth θ u hu : X → ℂ) x+(f : Amp).1 i := by
  intro i
  rw [vectorSmooth,projection_direction,he,map_add]
  exact congrArg (fun z : ℂ => z+(f : Amp).1 i)
    (connection_vector θ hθ ((t : X → ℂ) x) (fun j => (qq j : X → ℂ) x) (u x) i)
lemma smooth_scalar_forced (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0)
    (u : X → Fiber θ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (t : Smooth) (qq : Fin 3 → Smooth)
    (f : Fiber θ) (x : X)
    (he : fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ 1)+
        Complex.I • fderiv ℝ u x (ElasticityParameter.characteristicPlane ElasticityParameter.basis θ Complex.I)=
        connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)+f) :
    (direction (A := Smooth) coord θ (scalarSmooth θ u hu) : X → ℂ) x=
      ((t*scalarSmooth θ u hu+∑ i,qq i*vectorSmooth θ u hu i : Smooth) : X → ℂ) x+(f : Amp).2 := by
  rw [scalarSmooth,projection_direction,he,map_add]
  apply congrArg (fun z : ℂ => z+(f : Amp).2)
  have h := connection_scalar θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x)
  simp only [Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_mul,Pi.add_apply,Pi.mul_apply]
  change ((connection θ hθ ((t : X → ℂ) x) (fun i => (qq i : X → ℂ) x) (u x) : Fiber θ) : Amp).2=
    (t : X → ℂ) x*((u x : Fiber θ) : Amp).2+
      ((qq 0 : X → ℂ) x*((u x : Fiber θ) : Amp).1 0+
      (qq 1 : X → ℂ) x*((u x : Fiber θ) : Amp).1 1+
      (qq 2 : X → ℂ) x*((u x : Fiber θ) : Amp).1 2)
  simpa only [Fin.sum_univ_three] using h
end ElasticityFrame

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma transformed_scalar_exact (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0) :
    leadingS coord θ (k-r*r) (r*r) a b=
      2*((k+r*r)*direction (A := Smooth) coord θ b+direction (A := Smooth) coord θ k*b+
        r*(2*thetaGamma θ r hr*changeS k r hr a b+
          ∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)) := by
  have ht : (∑ i, (2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i) : Smooth)=
      r*(2*thetaGamma θ r hr*changeS k r hr a b+
        ∑ i, direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
    simp_rw [transformed_gradient θ r hr a,normal_form_top θ k r hr a b hR]
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    congr 2
    simp only [thetaGamma,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Algebra.smul_def]
    ring
  rw [← ht]
  simp only [leadingS,sub_add_cancel,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  ring

lemma scalar_residual_algebra (r k R K b db H J s : ℂ) (hr : r≠0) (hk : k≠0)
    (hl : k+r*r≠0) (hB : 2*r*s+k*b+r*H=0) :
    -(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+(2*R/r)*s)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J))=
      (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J)) := by
  calc
    _ = (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J))+
        (R/(2*r^2)-r*K/(2*k*(k+r*r)))*(2*r*s+k*b+r*H) := by
      have hp : k+r^2≠0 := by simpa only [pow_two] using hl
      field_simp [hr,hk,hl,hp]
      ring
    _ = _ := by rw [hB]; ring

lemma normal_form_bottom_residual (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (hR : leadingR coord θ (k-r*r) (r*r) a b=0) :
    direction (A := Smooth) coord θ (changeS k r hr a b)-
      (transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i)=
      -(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*leadingS coord θ (k-r*r) (r*r) a b) := by
  rw [changeS_derivative θ k r hr a b hR,transportT_eq θ k r hr hk hl,
    transportQ_contract,transformed_scalar_exact θ k r hr a b hR]
  apply Subtype.ext
  funext x
  let R := (r : X → ℂ) x
  let K := (k : X → ℂ) x
  let DR := (direction (A := Smooth) coord θ r : X → ℂ) x
  let DK := (direction (A := Smooth) coord θ k : X → ℂ) x
  let B := (b : X → ℂ) x
  let DB := (direction (A := Smooth) coord θ b : X → ℂ) x
  let H := ((∑ i,logarithmicGrad r hr i*changeP r a i : Smooth) : X → ℂ) x
  let J := ((∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i : Smooth) : X → ℂ) x
  let S := (changeS k r hr a b : X → ℂ) x
  have he : S=-(1/2 : ℂ)*(K*R⁻¹*B+H) := rfl
  have hB : 2*R*S+K*B+R*H=0 := by
    rw [he]
    have hn : R≠0 := hr x
    field_simp [hn]
    ring
  have hgamma : (thetaGamma θ r hr : X → ℂ) x=2*DR/R := by
    rw [thetaGamma_eq]
    change 2*R⁻¹*DR=2*DR/R
    ring
  have ha := scalar_residual_algebra R K DR DK B DB H J S (hr x) (hk x)
    (show K+R*R≠0 from hl x) hB
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_pow,
    Subalgebra.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,hgamma]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  change -(1/2 : ℂ)*((DK*R⁻¹-K*(R⁻¹)^2*DR)*B+K*R⁻¹*DB+J+(2*DR/R)*S)-
    (R*R*(K+R*R)⁻¹*(K⁻¹*DK-2*DR/R)*S+
      (1/2 : ℂ)*((R*R*(K+R*R)⁻¹*K⁻¹*DK-(1/2 : ℂ)*(2*DR/R))*H-R*R*(K+R*R)⁻¹*J))=
    -(1/4 : ℂ)*(K*R⁻¹*(K+R*R)⁻¹*(2*((K+R*R)*DB+DK*B+R*(2*(2*DR/R)*S+J))))
  convert ha using 1 <;> simp only [div_eq_mul_inv,inv_pow,mul_inv_rev] <;> ring

/-- Both directions of the actual physical leading transport equivalence. -/
theorem leading_equations_iff (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    (leadingR coord θ (k-r*r) (r*r) a b=0 ∧ leadingS coord θ (k-r*r) (r*r) a b=0) ↔
      (∀ i,direction (A := Smooth) coord θ (changeP r a i)=θ i • changeS k r hr a b) ∧
      direction (A := Smooth) coord θ (changeS k r hr a b)=
        transportT θ k r hk hl*changeS k r hr a b+
          ∑ i,transportQ θ k r hr hk hl i*changeP r a i := by
  constructor
  · rintro ⟨hR,hS⟩
    exact ⟨normal_form_top θ k r hr a b hR,normal_form_bottom θ k r hr hk hl a b hR hS⟩
  · rintro ⟨hP,hT⟩
    have hR := (leadingR_iff θ k r hr a b).mpr hP
    refine ⟨hR,?_⟩
    have hh := normal_form_bottom_residual θ k r hr hk hl a b hR
    rw [hT,sub_self] at hh
    apply Subtype.ext
    funext x
    have he := congrArg (fun f : Smooth => (f : X → ℂ) x) hh
    simp only [Subalgebra.coe_smul,Subalgebra.coe_mul,Subalgebra.coe_zero,Pi.zero_apply,Pi.mul_apply,
      Pi.smul_apply,smul_eq_mul,smoothInv_apply] at he
    rw [← mul_assoc] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (by
      apply mul_ne_zero
      · norm_num
      · exact mul_ne_zero (mul_ne_zero (hk x) (inv_ne_zero (hr x))) (inv_ne_zero (hl x)))
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma changeS_derivative_raw (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    direction (A := Smooth) coord θ (changeS k r hr a b)=
      -(1/2 : ℂ) • ((direction (A := Smooth) coord θ k*smoothInv r hr-
        k*(smoothInv r hr)^2*direction (A := Smooth) coord θ r)*b+
        k*smoothInv r hr*direction (A := Smooth) coord θ b+
        (∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)+
          ∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i)) := by
  conv_lhs => rw [changeS,direction_smul,direction_add]
  simp only [direction_sum,direction_mul,direction_inv,Finset.sum_add_distrib]
  congr 1
  ring

lemma transformed_scalar_raw (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    leadingS coord θ (k-r*r) (r*r) a b=
      2*((k+r*r)*direction (A := Smooth) coord θ b+direction (A := Smooth) coord θ k*b+
        r*(2*(∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))+
          ∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)) := by
  have ht : (∑ i, (2*coord i (r*r)*direction (A := Smooth) coord θ (a i)+
      direction (A := Smooth) coord θ (coord i (r*r))*a i) : Smooth)=
      r*(2*(∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))+
        ∑ i, direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i) := by
    simp_rw [transformed_gradient θ r hr a]
    rw [← Finset.mul_sum,Finset.sum_add_distrib]
    simp only [Finset.mul_sum,mul_assoc]
  rw [← ht]
  simp only [leadingS,sub_add_cancel,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  ring

lemma contraction_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hP : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) :
    ((∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i) : Smooth) : X → ℂ) x=
      (thetaGamma θ r hr : X → ℂ) x*(changeS k r hr a b : X → ℂ) x := by
  simp only [thetaGamma,Fin.sum_univ_three,Subalgebra.coe_add,Subalgebra.coe_mul,
    Subalgebra.coe_smul,Pi.add_apply,Pi.mul_apply,Pi.smul_apply,smul_eq_mul,hP]
  ring

lemma changeS_derivative_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hP : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) :
    (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((-(1/2 : ℂ) • ((direction (A := Smooth) coord θ k*smoothInv r hr-
        k*(smoothInv r hr)^2*direction (A := Smooth) coord θ r)*b+
        k*smoothInv r hr*direction (A := Smooth) coord θ b+
        (∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)+
          thetaGamma θ r hr*changeS k r hr a b) : Smooth) : X → ℂ) x := by
  rw [changeS_derivative_raw]
  simp only [Subalgebra.coe_smul,Subalgebra.coe_add,Subalgebra.coe_mul,Pi.smul_apply,Pi.add_apply,Pi.mul_apply]
  rw [contraction_at θ k r hr a b x hP]

lemma transformed_scalar_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hP : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) :
    ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=
      ((2*((k+r*r)*direction (A := Smooth) coord θ b+direction (A := Smooth) coord θ k*b+
        r*(2*thetaGamma θ r hr*changeS k r hr a b+
          ∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i)) : Smooth) : X → ℂ) x := by
  rw [transformed_scalar_raw θ k r hr a b]
  simp only [Subalgebra.coe_add,Subalgebra.coe_mul,Pi.add_apply,Pi.mul_apply]
  rw [contraction_at θ k r hr a b x hP]
  ring

lemma normal_form_bottom_residual_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth)
    (x : X) (hP : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) :
    ((direction (A := Smooth) coord θ (changeS k r hr a b)-
      (transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i) : Smooth) : X → ℂ) x=
      ((-(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*leadingS coord θ (k-r*r) (r*r) a b) : Smooth) : X → ℂ) x := by
  rw [transportT_eq θ k r hr hk hl,transportQ_contract]
  simp only [Subalgebra.coe_sub,Subalgebra.coe_smul,Subalgebra.coe_mul,Pi.sub_apply,
    Pi.smul_apply,Pi.mul_apply]
  rw [changeS_derivative_at θ k r hr a b x hP,transformed_scalar_at θ k r hr a b x hP]
  let R := (r : X → ℂ) x
  let K := (k : X → ℂ) x
  let DR := (direction (A := Smooth) coord θ r : X → ℂ) x
  let DK := (direction (A := Smooth) coord θ k : X → ℂ) x
  let B := (b : X → ℂ) x
  let DB := (direction (A := Smooth) coord θ b : X → ℂ) x
  let H := ((∑ i,logarithmicGrad r hr i*changeP r a i : Smooth) : X → ℂ) x
  let J := ((∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i : Smooth) : X → ℂ) x
  let S := (changeS k r hr a b : X → ℂ) x
  have he : S=-(1/2 : ℂ)*(K*R⁻¹*B+H) := rfl
  have hB : 2*R*S+K*B+R*H=0 := by
    rw [he]
    have hn : R≠0 := hr x
    field_simp [hn]
    ring
  have hgamma : (thetaGamma θ r hr : X → ℂ) x=2*DR/R := by
    rw [thetaGamma_eq]
    change 2*R⁻¹*DR=2*DR/R
    ring
  have ha := scalar_residual_algebra R K DR DK B DB H J S (hr x) (hk x)
    (show K+R*R≠0 from hl x) hB
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_pow,
    Subalgebra.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,hgamma]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  change -(1/2 : ℂ)*((DK*R⁻¹-K*(R⁻¹)^2*DR)*B+K*R⁻¹*DB+J+(2*DR/R)*S)-
    (R*R*(K+R*R)⁻¹*(K⁻¹*DK-2*DR/R)*S+
      (1/2 : ℂ)*((R*R*(K+R*R)⁻¹*K⁻¹*DK-(1/2 : ℂ)*(2*DR/R))*H-R*R*(K+R*R)⁻¹*J))=
    -(1/4 : ℂ)*(K*R⁻¹*(K+R*R)⁻¹*(2*((K+R*R)*DB+DK*B+R*(2*(2*DR/R)*S+J))))
  convert ha using 1 <;> simp only [div_eq_mul_inv,inv_pow,mul_inv_rev] <;> ring

end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma leadingR_contract (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    (∑ i,logarithmicGrad r hr i*leadingR coord θ (k-r*r) (r*r) a b i)=
      2*r*((∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i))-
        thetaGamma θ r hr*changeS k r hr a b) := by
  simp_rw [leadingR_change θ k r hr a b]
  simp only [thetaGamma,mul_sub,Finset.mul_sum,Finset.sum_mul,Finset.sum_sub_distrib,
    Algebra.smul_def]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma scalar_forced_residual (r k R K b db H J G s : ℂ) (hr : r≠0) (hk : k≠0)
    (hl : k+r*r≠0) (hB : 2*r*s+k*b+r*H=0) :
    -(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+G)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J))=
      (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*G+J))+
        ((k-r*r)/(2*(k+r*r)))*(G-(2*R/r)*s) := by
  have ha := scalar_residual_algebra r k R K b db H J s hr hk hl hB
  calc
    _ = (-(1/2 : ℂ)*((K/r-k*R/r^2)*b+k/r*db+J+(2*R/r)*s)-
      ((r*r/(k+r*r))*(K/k-2*R/r)*s+
        (1/2 : ℂ)*(((r*r/(k+r*r))*(K/k)-(2*R/r)/2)*H-(r*r/(k+r*r))*J)))-
        (1/2 : ℂ)*(G-(2*R/r)*s) := by ring
    _ = (-k/(2*r*(k+r*r)))*((k+r*r)*db+K*b+r*(2*(2*R/r)*s+J))-
        (1/2 : ℂ)*(G-(2*R/r)*s) := by rw [ha]
    _ = _ := by
      have hp : k+r^2≠0 := by simpa only [pow_two] using hl
      field_simp [hr,hl,hp]
      ring

/-- Exact forced transport intertwining, with no homogeneous leading-equation
premise. This is the source term needed for the physical compatible recursion. -/
lemma normal_form_forced_residual (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) :
    direction (A := Smooth) coord θ (changeS k r hr a b)-
      (transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i)=
      -(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*leadingS coord θ (k-r*r) (r*r) a b)+
      (1/4 : ℂ) • ((k-r*r)*smoothInv r hr*smoothInv (k+r*r) hl*
        ∑ i,logarithmicGrad r hr i*leadingR coord θ (k-r*r) (r*r) a b i) := by
  rw [changeS_derivative_raw θ k r hr a b,transportT_eq θ k r hr hk hl,
    transportQ_contract,transformed_scalar_raw θ k r hr a b,leadingR_contract]
  apply Subtype.ext
  funext x
  let R := (r : X → ℂ) x
  let K := (k : X → ℂ) x
  let DR := (direction (A := Smooth) coord θ r : X → ℂ) x
  let DK := (direction (A := Smooth) coord θ k : X → ℂ) x
  let B := (b : X → ℂ) x
  let DB := (direction (A := Smooth) coord θ b : X → ℂ) x
  let H := ((∑ i,logarithmicGrad r hr i*changeP r a i : Smooth) : X → ℂ) x
  let J := ((∑ i,direction (A := Smooth) coord θ (logarithmicGrad r hr i)*changeP r a i : Smooth) : X → ℂ) x
  let G := ((∑ i,logarithmicGrad r hr i*direction (A := Smooth) coord θ (changeP r a i) : Smooth) : X → ℂ) x
  let S := (changeS k r hr a b : X → ℂ) x
  have he : S=-(1/2 : ℂ)*(K*R⁻¹*B+H) := rfl
  have hB : 2*R*S+K*B+R*H=0 := by
    rw [he]
    have hn : R≠0 := hr x
    field_simp [hn]
    ring
  have hgamma : (thetaGamma θ r hr : X → ℂ) x=2*DR/R := by
    rw [thetaGamma_eq]
    change 2*R⁻¹*DR=2*DR/R
    ring
  have ha := scalar_forced_residual R K DR DK B DB H J G S (hr x) (hk x)
    (show K+R*R≠0 from hl x) hB
  simp only [Subalgebra.coe_add,Subalgebra.coe_sub,Subalgebra.coe_mul,Subalgebra.coe_pow,
    Subalgebra.coe_smul,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,hgamma]
  have h2 : ((2 : Smooth) : X → ℂ) x=(2 : ℂ) := rfl
  rw [h2]
  change -(1/2 : ℂ)*((DK*R⁻¹-K*(R⁻¹)^2*DR)*B+K*R⁻¹*DB+J+G)-
    (R*R*(K+R*R)⁻¹*(K⁻¹*DK-2*DR/R)*S+
      (1/2 : ℂ)*((R*R*(K+R*R)⁻¹*K⁻¹*DK-(1/2 : ℂ)*(2*DR/R))*H-R*R*(K+R*R)⁻¹*J))=
    -(1/4 : ℂ)*(K*R⁻¹*(K+R*R)⁻¹*(2*((K+R*R)*DB+DK*B+R*(2*G+J))))+
    (1/4 : ℂ)*((K-R*R)*R⁻¹*(K+R*R)⁻¹*(2*R*(G-(2*DR/R)*S)))
  have hR : R≠0 := hr x
  have hL : K+R^2≠0 := by
    simpa only [pow_two] using (show K+R*R≠0 from hl x)
  convert ha using 1 <;> simp only [div_eq_mul_inv,inv_pow,mul_inv_rev] <;>
    field_simp [hR,hL]
  all_goals norm_num
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

def topSource (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (H : Fin 3 → Smooth) : Fin 3 → Smooth :=
  fun i => (1/2 : ℂ) • (smoothInv r hr*H i)
def scalarSource (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (H : Fin 3 → Smooth) (K : Smooth) : Smooth :=
  -(1/4 : ℂ) • (k*smoothInv r hr*smoothInv (k+r*r) hl*K)+
    (1/4 : ℂ) • ((k-r*r)*smoothInv r hr*smoothInv (k+r*r) hl*
      ∑ i,logarithmicGrad r hr i*H i)

lemma forced_equations_at (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) (K : Smooth) (a : Fin 3 → Smooth) (b : Smooth) (x : X)
    (hp : ∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x+(topSource r hr H i : X → ℂ) x)
    (hs : (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x+
          (scalarSource k r hr hl H K : X → ℂ) x) :
    (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
      ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x := by
  have hR (i) : ((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x := by
    have h := congrArg (fun f : Smooth => (f : X → ℂ) x) (leadingR_change θ k r hr a b i)
    change ((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=
      2*(r : X → ℂ) x*((direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x-
        θ i*(changeS k r hr a b : X → ℂ) x) at h
    rw [h,hp i]
    change 2*(r : X → ℂ) x*(θ i*(changeS k r hr a b : X → ℂ) x+
      (1/2 : ℂ)*(((r : X → ℂ) x)⁻¹*(H i : X → ℂ) x)-θ i*(changeS k r hr a b : X → ℂ) x)=_
    field_simp [hr x]
    ring
  refine ⟨hR,?_⟩
  have h := congrArg (fun f : Smooth => (f : X → ℂ) x)
    (normal_form_forced_residual θ k r hr hk hl a b)
  change (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x-
    ((transportT θ k r hk hl*changeS k r hr a b+
      ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x=_ at h
  rw [hs,add_sub_cancel_left] at h
  simp only [scalarSource,Subalgebra.coe_add,Subalgebra.coe_mul,Subalgebra.coe_sub,
    Subalgebra.coe_smul,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,smoothInv_apply,Fin.sum_univ_three,hR] at h
  have hc : -(1/4 : ℂ)*(k : X → ℂ) x*((r : X → ℂ) x)⁻¹*
      (((k : X → ℂ) x+(r : X → ℂ) x*(r : X → ℂ) x)⁻¹)≠0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hk x)) (inv_ne_zero (hr x)))
      (inv_ne_zero (hl x))
  apply (mul_left_cancel₀ hc)
  linear_combination -h
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

theorem leading_equations_at_iff (θ : Fin 3 → ℂ) (k r : Smooth)
    (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0) (a : Fin 3 → Smooth) (b : Smooth) (x : X) :
    ((∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=0) ∧
      ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=0) ↔
    (∀ i,(direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
      θ i*(changeS k r hr a b : X → ℂ) x) ∧
    (direction (A := Smooth) coord θ (changeS k r hr a b) : X → ℂ) x=
      ((transportT θ k r hk hl*changeS k r hr a b+
        ∑ i,transportQ θ k r hr hk hl i*changeP r a i : Smooth) : X → ℂ) x := by
  have hR (i) := congrArg (fun f : Smooth => (f : X → ℂ) x) (leadingR_change θ k r hr a b i)
  change ∀ i, ((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=
    2*(r : X → ℂ) x*((direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x-
      θ i*(changeS k r hr a b : X → ℂ) x) at hR
  have hn : (2 : ℂ)*(r : X → ℂ) x≠0 := mul_ne_zero (by norm_num) (hr x)
  constructor
  · rintro ⟨hp,hs⟩
    have hP (i) : (direction (A := Smooth) coord θ (changeP r a i) : X → ℂ) x=
        θ i*(changeS k r hr a b : X → ℂ) x := by
      have hh := (hR i).symm.trans (hp i)
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hn)
    refine ⟨hP,?_⟩
    have hh := normal_form_bottom_residual_at θ k r hr hk hl a b x hP
    simp only [Subalgebra.coe_sub,Pi.sub_apply,Subalgebra.coe_smul,Subalgebra.coe_mul,
      Pi.smul_apply,Pi.mul_apply,smul_eq_mul,hs,mul_zero] at hh
    exact sub_eq_zero.mp hh
  · rintro ⟨hP,hS⟩
    refine ⟨fun i => ?_,?_⟩
    · rw [hR i,hP i,sub_self,mul_zero]
    · have hh := normal_form_bottom_residual_at θ k r hr hk hl a b x hP
      simp only [Subalgebra.coe_sub,Pi.sub_apply,hS,sub_self,Subalgebra.coe_smul,
        Subalgebra.coe_mul,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,smoothInv_apply] at hh
      rw [← mul_assoc] at hh
      exact (mul_eq_zero.mp hh.symm).resolve_left (by
        apply mul_ne_zero
        · norm_num
        · exact mul_ne_zero (mul_ne_zero (hk x) (inv_ne_zero (hr x))) (inv_ne_zero (hl x)))
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma normal_inverseP (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (p : Fin 3 → Smooth) : normal θ (inverseP r hr p)=smoothInv r hr*normal θ p := by
  simp only [normal,inverseP,Finset.mul_sum,Algebra.smul_def]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Actual physical leading amplitudes, with three independent transformed
columns and both augmented leading equations on any prescribed compact region.
The equations are local: no global transport equation is assumed. -/
theorem exists_physical_leading_frame (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    {C : Set X} (hC : IsCompact C) :
    ∃ a : Fin 3 → Fin 3 → Smooth, ∃ b : Fin 3 → Smooth,
    ∃ B : X → Module.Basis (Fin 3) ℂ (ElasticityFrame.Fiber θ),
      (∀ ν,normal θ (a ν)=0) ∧
      (∀ ν x, x∈C →
        (∀ i,((leadingR coord θ (k-r*r) (r*r) (a ν) (b ν) i : Smooth) : X → ℂ) x=0) ∧
        ((leadingS coord θ (k-r*r) (r*r) (a ν) (b ν) : Smooth) : X → ℂ) x=0) ∧
      ∀ ν x, ((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (changeP r (a ν) i : X → ℂ) x),(changeS k r hr (a ν) (b ν) : X → ℂ) x) := by
  let t := transportT θ k r hk hl
  let q := transportQ θ k r hr hk hl
  obtain ⟨B,hB,he⟩ := ElasticityFrame.exists_constraint_columns θ hθ hne
    (t : X → ℂ) (fun i => (q i : X → ℂ)) (smooth_coe t) (fun i => smooth_coe (q i)) hC
  let p (ν : Fin 3) := ElasticityFrame.vectorSmooth θ (fun x => B x ν) (hB ν)
  let s (ν : Fin 3) := ElasticityFrame.scalarSmooth θ (fun x => B x ν) (hB ν)
  let a (ν : Fin 3) := inverseP r hr (p ν)
  let b (ν : Fin 3) := inverseS k r hr hk (p ν) (s ν)
  refine ⟨a,b,B,?_,?_,?_⟩
  · intro ν
    rw [show a ν=inverseP r hr (p ν) from rfl,normal_inverseP,
      ElasticityFrame.smooth_normal θ (fun x => B x ν) (hB ν),mul_zero]
  · intro ν x hx
    apply (leading_equations_at_iff θ k r hr hk hl (a ν) (b ν) x).mpr
    have hp := ElasticityFrame.smooth_vector_equation θ hθ (fun x => B x ν) (hB ν) t q x (he ν x hx)
    have hs := ElasticityFrame.smooth_scalar_equation θ hθ (fun x => B x ν) (hB ν) t q x (he ν x hx)
    change (∀ i,(direction (A := Smooth) coord θ
      (changeP r (inverseP r hr (p ν)) i) : X → ℂ) x=
        θ i*(changeS k r hr (inverseP r hr (p ν)) (inverseS k r hr hk (p ν) (s ν)) : X → ℂ) x) ∧ _
    rw [change_inverseP,change_inverseS]
    exact ⟨hp,hs⟩
  · intro ν x
    change ((B x ν : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
      ((fun i => (changeP r (inverseP r hr (p ν)) i : X → ℂ) x),
        (changeS k r hr (inverseP r hr (p ν)) (inverseS k r hr hk (p ν) (s ν)) : X → ℂ) x)
    rw [change_inverseP,change_inverseS]
    rfl
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

lemma normal_topSource (θ : Fin 3 → ℂ) (r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) : normal θ (topSource r hr H)=(1/2 : ℂ) • (smoothInv r hr*normal θ H) := by
  simp only [normal,topSource,Algebra.smul_def,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

/-- Smooth physical leading equations with arbitrary tangent vector forcing.
Solvability is proved from actual planar transport, not assumed. Forcing need
only be tangent on the compact region on which the equations are requested. -/
theorem exists_physical_forced_transport (θ : Fin 3 → ℂ) (hθ : ∑ i,θ i*θ i=0) (hne : θ≠0)
    (k r : Smooth) (hr : ∀ x,(r : X → ℂ) x≠0) (hk : ∀ x,(k : X → ℂ) x≠0)
    (hl : ∀ x,((k+r*r : Smooth) : X → ℂ) x≠0)
    (H : Fin 3 → Smooth) (K : Smooth) {C : Set X} (hC : IsCompact C)
    (hH : ∀ x∈C,((normal θ H : Smooth) : X → ℂ) x=0) :
    ∃ a : Fin 3 → Smooth, ∃ b : Smooth, normal θ a=0 ∧
      ∀ x∈C, (∀ i,((leadingR coord θ (k-r*r) (r*r) a b i : Smooth) : X → ℂ) x=(H i : X → ℂ) x) ∧
        ((leadingS coord θ (k-r*r) (r*r) a b : Smooth) : X → ℂ) x=(K : X → ℂ) x := by
  obtain ⟨n,hn⟩ := exists_normalizing_vector θ hne
  let Fp := topSource r hr H
  let Fs := scalarSource k r hr hl H K
  let f : X → ElasticityFrame.Fiber θ := fun x => ElasticityFrame.tangentProjection θ n hn
    ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := ElasticityFrame.tangentProjection_smooth θ n hn Fp Fs
  let t := transportT θ k r hk hl
  let q := transportQ θ k r hr hk hl
  obtain ⟨u,hu,he⟩ := ElasticityFrame.exists_constraint_transport θ hθ hne
    (t : X → ℂ) (fun i => (q i : X → ℂ)) (smooth_coe t) (fun i => smooth_coe (q i)) f hf hC
  let p := ElasticityFrame.vectorSmooth θ u hu
  let s := ElasticityFrame.scalarSmooth θ u hu
  let a := inverseP r hr p
  let b := inverseS k r hr hk p s
  refine ⟨a,b,?_,?_⟩
  · rw [show a=inverseP r hr p from rfl,normal_inverseP,
      ElasticityFrame.smooth_normal θ u hu,mul_zero]
  · intro x hx
    have hF : ((f x : ElasticityFrame.Fiber θ) : ElasticityFrame.Amp)=
        ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x) := by
      apply ElasticityFrame.tangentProjection_of_normal θ n hn
      have h := congrArg (fun v : Smooth => (v : X → ℂ) x) (normal_topSource θ r hr H)
      change ElasticityFrame.normal θ ((fun i => (Fp i : X → ℂ) x),(Fs : X → ℂ) x)=
        (1/2 : ℂ)*(((r : X → ℂ) x)⁻¹*((normal θ H : Smooth) : X → ℂ) x) at h
      rw [h,hH x hx,mul_zero,mul_zero]
    have hp := ElasticityFrame.smooth_vector_forced θ hθ u hu t q (f x) x (he x hx)
    have hs := ElasticityFrame.smooth_scalar_forced θ hθ u hu t q (f x) x (he x hx)
    rw [hF] at hp hs
    apply forced_equations_at θ k r hr hk hl H K a b x
    · change ∀ i,(direction (A := Smooth) coord θ (changeP r (inverseP r hr p) i) : X → ℂ) x=
        θ i*(changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s) : X → ℂ) x+_
      rw [change_inverseP,change_inverseS]
      exact hp
    · change (direction (A := Smooth) coord θ
        (changeS k r hr (inverseP r hr p) (inverseS k r hr hk p s)) : X → ℂ) x=_
      rw [change_inverseS,change_inverseP]
      exact hs
end ElasticityAugmented

end
end

end OAI
