import Mathlib
import OAI.Algebra.FiniteTensor.ArtinSteps

namespace OAI

/-! Algebraic kernel relations, localization descent and polynomial parameter algebraicity. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
noncomputable section

 

theorem algebraic_kernel_annihilator {F B L : Type*} [Field F] [CommRing B]
    [CommRing L] [IsDomain L] [Algebra F B] [Algebra F L]
    (φ : B →ₐ[F] L) (r : B) (hr : IsAlgebraic F r) (hz : φ r=0) :
    ∃ (n : ℕ) (h : B),0<n ∧ φ h≠0 ∧ h*r^n=0 := by
  obtain ⟨P,hP,hPr⟩ := hr
  obtain ⟨n,q,hq,hq0⟩ := polynomial_remove_X_factor P hP
  let h := Polynomial.aeval r q
  have hh : φ h=algebraMap F L (q.coeff 0) := by
    dsimp [h]
    rw [←Polynomial.aeval_algHom_apply, hz]
    simp [Polynomial.aeval_def,Polynomial.eval₂_at_zero]
  have hh0 : φ h≠0 := by
    rw [hh]
    exact (map_ne_zero (algebraMap F L)).mpr hq0
  have hprod : h*r^n=0 := by
    rw [hq,map_mul,map_pow,Polynomial.aeval_X] at hPr
    simpa only [mul_comm] using hPr
  have hn : 0<n := by
    by_contra hn
    have he : n=0 := by omega
    rw [he,pow_zero,mul_one] at hprod
    exact hh0 (by rw [hprod,map_zero])
  exact ⟨n,h,hn,hh0,hprod⟩

 
theorem quotient_kernel_power_mem {F R L : Type*} [Field F] [CommRing R]
    [CommRing L] [IsDomain L] [Algebra F R] [Algebra F L]
    (I : Ideal R) (φ : R →ₐ[F] L) (hI : ∀ x∈I,φ x=0)
    (g : R) (hg : φ g=0)
    (halg : IsAlgebraic F (Ideal.Quotient.mk I g)) :
    ∃ (n : ℕ) (H : R),0<n ∧ φ H≠0 ∧ H*g^n∈I := by
  let ψ := Ideal.Quotient.liftₐ I φ hI
  have hψ (r : R) : ψ (Ideal.Quotient.mk I r)=φ r := rfl
  obtain ⟨n,h,hn,hh,hprod⟩ := algebraic_kernel_annihilator ψ
    (Ideal.Quotient.mk I g) halg (by rw [hψ,hg])
  obtain ⟨H,rfl⟩ := Ideal.Quotient.mk_surjective h
  refine ⟨n,H,hn,hh,?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [map_mul,map_pow] using hprod

 

theorem quotient_mvpolynomial_isIntegral {F σ : Type*} [Field F]
    (I : Ideal (MvPolynomial σ F))
    (hX : ∀ i : σ,IsIntegral F (Ideal.Quotient.mk I (MvPolynomial.X i)))
    (g : MvPolynomial σ F) : IsIntegral F (Ideal.Quotient.mk I g) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
    change IsIntegral F (algebraMap F (MvPolynomial σ F ⧸ I) c)
    exact isIntegral_algebraMap
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp => simpa only [map_mul] using hp.mul (hX i)

 

theorem diagonal_kernel_power_mem {F σ L : Type*} [Field F]
    [CommRing L] [IsDomain L] [Algebra F L]
    (a : σ → L) (P : σ → Polynomial F)
    (hP : ∀ i,(P i).Monic) (hroot : ∀ i,Polynomial.aeval (a i) (P i)=0)
    (g : MvPolynomial σ F) (hg : MvPolynomial.aeval a g=0) :
    ∃ (n : ℕ) (H : MvPolynomial σ F),0<n ∧ MvPolynomial.aeval a H≠0 ∧
      H*g^n∈Ideal.span (Set.range (fun i=>Polynomial.aeval (MvPolynomial.X i) (P i))) := by
  let I : Ideal (MvPolynomial σ F) := Ideal.span
    (Set.range (fun i=>Polynomial.aeval (MvPolynomial.X i) (P i)))
  have hI : ∀ x∈I,MvPolynomial.aeval a x=0 := by
    intro x hx
    have he : I≤RingHom.ker (MvPolynomial.aeval a).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change MvPolynomial.aeval a (Polynomial.aeval (MvPolynomial.X i) (P i))=0
      rw [←Polynomial.aeval_algHom_apply]
      simpa using hroot i
    exact he hx
  have hX (i : σ) : IsIntegral F (Ideal.Quotient.mk I (MvPolynomial.X i)) := by
    refine ⟨P i,hP i,?_⟩
    have hi : Polynomial.aeval (MvPolynomial.X i) (P i)∈I :=
      Ideal.subset_span (Set.mem_range_self i)
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hi
    change (Ideal.Quotient.mkₐ F I) (Polynomial.aeval (MvPolynomial.X i) (P i))=0 at he
    rwa [←Polynomial.aeval_algHom_apply] at he
  exact quotient_kernel_power_mem I (MvPolynomial.aeval a) hI g hg
    (quotient_mvpolynomial_isIntegral I hX g).isAlgebraic

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section

 

theorem localization_kernel_power_descent {R S L : Type*} [CommRing R]
    [CommRing S] [CommRing L] [IsDomain L] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S]
    (φ : R →+* L) (ψ : S →+* L)
    (hcomp : ψ.comp (algebraMap R S)=φ)
    (hM : ∀ m∈M,φ m≠0)
    (I : Ideal R) (g : R) (n : ℕ) (H : S)
    (hH : ψ H≠0) (hmem : H*(algebraMap R S g)^n∈I.map (algebraMap R S)) :
    ∃ H₀ : R,φ H₀≠0 ∧ H₀*g^n∈I := by
  obtain ⟨d,H₀,hH₀⟩ := IsLocalization.exists_integer_multiple' M H
  have hc (r : R) : ψ (algebraMap R S r)=φ r := RingHom.congr_fun hcomp r
  have hH₀' : φ H₀≠0 := by
    rw [←hc H₀,hH₀,map_mul,hc]
    exact mul_ne_zero hH (hM d d.property)
  have hmem' : algebraMap R S (H₀*g^n)∈I.map (algebraMap R S) := by
    rw [map_mul,map_pow,hH₀]
    convert (I.map (algebraMap R S)).mul_mem_left (algebraMap R S d) hmem using 1
    ring
  obtain ⟨c,hcM,hcI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff M S I _).mp hmem'
  refine ⟨c*H₀,by rw [map_mul]; exact mul_ne_zero (hM c hcM) hH₀',?_⟩
  simpa only [mul_assoc] using hcI

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

 

theorem nonmonic_diagonal_kernel_power_mem {R L σ : Type*} [CommRing R]
    [IsDomain R] [Field L] [Algebra R L] [FaithfulSMul R L]
    (a : σ → L) (P : σ → Polynomial R) (hP : ∀ i,P i≠0)
    (hroot : ∀ i,Polynomial.aeval (a i) (P i)=0)
    (g : MvPolynomial σ R) (hg : MvPolynomial.aeval a g=0) :
    ∃ (n : ℕ) (H : MvPolynomial σ R),0<n ∧ MvPolynomial.aeval a H≠0 ∧
      H*g^n∈Ideal.span (Set.range (fun i=>Polynomial.aeval (MvPolynomial.X i) (P i))) := by
  let F := FractionRing R
  let : Algebra F L := FractionRing.liftAlgebra R L
  let : IsScalarTower R F L := FractionRing.isScalarTower_liftAlgebra R L
  let I : Ideal (MvPolynomial σ R) := Ideal.span
    (Set.range (fun i=>Polynomial.aeval (MvPolynomial.X i) (P i)))
  let J := I.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ F))
  let φ : MvPolynomial σ R →ₐ[R] L := MvPolynomial.aeval a
  let ψ : MvPolynomial σ F →ₐ[F] L := MvPolynomial.aeval a
  have hcomp : ψ.toRingHom.comp (algebraMap (MvPolynomial σ R) (MvPolynomial σ F))=
      φ.toRingHom := by
    apply RingHom.ext
    intro p
    change MvPolynomial.aeval a (algebraMap (MvPolynomial σ R) (MvPolynomial σ F) p)=
      MvPolynomial.aeval a p
    rw [MvPolynomial.algebraMap_def,MvPolynomial.aeval_map_algebraMap]
  have heI : ∀ x∈I,φ x=0 := by
    intro x hx
    have he : I≤RingHom.ker φ.toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change MvPolynomial.aeval a (Polynomial.aeval (MvPolynomial.X i) (P i))=0
      rw [←Polynomial.aeval_algHom_apply]
      simpa using hroot i
    exact he hx
  have heJ : ∀ x∈J,ψ x=0 := by
    intro x hx
    have he : J≤RingHom.ker ψ.toRingHom := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro y hy
      change ψ (algebraMap (MvPolynomial σ R) (MvPolynomial σ F) y)=0
      exact (RingHom.congr_fun hcomp y).trans (heI y hy)
    exact he hx
  have hX (i : σ) : IsIntegral F (Ideal.Quotient.mk J (MvPolynomial.X i)) := by
    apply IsAlgebraic.isIntegral
    refine ⟨(P i).map (algebraMap R F),
      (Polynomial.map_ne_zero_iff (IsFractionRing.injective R F)).mpr (hP i),?_⟩
    have hi : Polynomial.aeval (MvPolynomial.X i) (P i)∈I :=
      Ideal.subset_span (Set.mem_range_self i)
    have hj : algebraMap (MvPolynomial σ R) (MvPolynomial σ F)
        (Polynomial.aeval (MvPolynomial.X i) (P i))∈J := Ideal.mem_map_of_mem _ hi
    have hr : algebraMap (MvPolynomial σ R) (MvPolynomial σ F)
        (Polynomial.aeval (MvPolynomial.X i) (P i))=
        Polynomial.aeval (MvPolynomial.X i) ((P i).map (algebraMap R F)) := by
      rw [MvPolynomial.algebraMap_def]
      induction P i using Polynomial.induction_on' with
      | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
      | monomial n r => simp [Polynomial.aeval_monomial]
    rw [hr] at hj
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr hj
    change (Ideal.Quotient.mkₐ F J) (Polynomial.aeval (MvPolynomial.X i)
      ((P i).map (algebraMap R F)))=0 at hq
    rwa [←Polynomial.aeval_algHom_apply] at hq
  let g' := algebraMap (MvPolynomial σ R) (MvPolynomial σ F) g
  have hg' : ψ g'=0 := (RingHom.congr_fun hcomp g).trans hg
  obtain ⟨n,H,hn,hH,hHI⟩ := quotient_kernel_power_mem J ψ heJ g' hg'
    (quotient_mvpolynomial_isIntegral J hX g').isAlgebraic
  let M : Submonoid (MvPolynomial σ R) := (nonZeroDivisors R).map MvPolynomial.C
  have hM : ∀ m∈M,φ m≠0 := by
    rintro _ ⟨r,hr,rfl⟩
    change MvPolynomial.aeval a (C r)≠0
    rw [MvPolynomial.aeval_C]
    exact fun hz=>(mem_nonZeroDivisors_iff_ne_zero.mp hr)
      (FaithfulSMul.algebraMap_injective R L (by simpa only [map_zero] using hz))
  obtain ⟨H₀,hH₀,hH₀I⟩ := localization_kernel_power_descent M φ.toRingHom
    ψ.toRingHom hcomp hM I g n H hH hHI
  exact ⟨n,H₀,hn,hH₀,hH₀I⟩

 

theorem diagonal_relation_det_ne_zero {R L σ : Type*} [CommRing R]
    [CommRing L] [IsDomain L] [Algebra R L] [Fintype σ] [DecidableEq σ]
    (a : σ → L) (P : σ → Polynomial R)
    (hder : ∀ i,Polynomial.aeval (a i) (P i).derivative≠0) :
    Matrix.det (fun k i=>MvPolynomial.aeval (R:=R) a
      (MvPolynomial.pderiv i (Polynomial.aeval (MvPolynomial.X k) (P k))))≠0 := by
  have he : (fun k i=>MvPolynomial.aeval (R:=R) a
      (MvPolynomial.pderiv i (Polynomial.aeval (MvPolynomial.X k) (P k))))=
      Matrix.diagonal (fun k=>Polynomial.aeval (a k) (P k).derivative) := by
    funext k i
    rw [Derivation.map_aeval]
    simp only [smul_eq_mul,map_mul,←Polynomial.aeval_algHom_apply,MvPolynomial.aeval_X]
    by_cases h : k=i
    · subst i
      simp
    · simp [MvPolynomial.pderiv_X,h]
  rw [he,Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _=>hder i

end
end PD4Tensor.Spreading

 

noncomputable section

namespace PD4Tensor.Spreading

 

theorem exists_relation_derivative_ne_zero {R S : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [CommRing S] [Algebra R S] (hi : Function.Injective (algebraMap R S))
    (f : S) (hf : IsAlgebraic R f) :
    ∃ P : Polynomial R, P≠0 ∧ Polynomial.aeval f P=0 ∧
      Polynomial.aeval f P.derivative≠0 := by
  classical
  obtain ⟨P,hP,hPf⟩ := hf
  have hex : ∃ n : ℕ, ∃ P : Polynomial R, P≠0 ∧ Polynomial.aeval f P=0 ∧ P.natDegree=n :=
    ⟨P.natDegree,P,hP,hPf,rfl⟩
  obtain ⟨Q,hQ,hQf,hQn⟩ := Nat.find_spec hex
  refine ⟨Q,hQ,hQf,?_⟩
  intro hd
  have hQd : Q.natDegree≠0 := by
    intro h
    have heq := Polynomial.eq_C_of_natDegree_eq_zero h
    rw [heq,Polynomial.aeval_C] at hQf
    have hz : Q.coeff 0=0 := hi (by simpa only [map_zero] using hQf)
    apply hQ
    simpa only [hz,Polynomial.C_0] using heq
  have hder : Q.derivative≠0 := Polynomial.derivative_ne_zero.mpr hQd
  have hlt : Q.derivative.natDegree<Nat.find hex := by
    rw [←hQn]
    exact Polynomial.natDegree_derivative_lt hQd
  exact Nat.find_min hex hlt ⟨Q.derivative,hder,hd,rfl⟩

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

 

theorem polynomial_parameter_algebraicity {R L ι : Type*} [CommRing R]
    [IsDomain R] [Field L] [Algebra R L] [FaithfulSMul R L]
    (x : ι → L) (a : L) :
    letI : Algebra (FractionRing R) L := FractionRing.liftAlgebra R L
    AlgebraicIndependent (FractionRing R) x →
    IsAlgebraic (Algebra.adjoin (FractionRing R) (Set.range x)) a →
    ∃ P : Polynomial (MvPolynomial ι R),P≠0 ∧
      P.eval₂ (MvPolynomial.aeval x).toRingHom a=0 := by
  let K := FractionRing R
  let : Algebra K L := FractionRing.liftAlgebra R L
  let : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  intro hx ha
  let B := MvPolynomial ι R
  let C := MvPolynomial ι K
  let : Algebra B L := (MvPolynomial.aeval (R:=R) x).toRingHom.toAlgebra
  let : Algebra C L := (MvPolynomial.aeval (R:=K) x).toRingHom.toAlgebra
  let : IsScalarTower B C L := IsScalarTower.of_algebraMap_eq fun p=>by
    change MvPolynomial.aeval (R:=R) x p=MvPolynomial.aeval (R:=K) x
      (algebraMap B C p)
    rw [MvPolynomial.algebraMap_def,MvPolynomial.aeval_map_algebraMap]
  let M : Submonoid B := (nonZeroDivisors R).map MvPolynomial.C
  let : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  have hc : IsAlgebraic C a := by
    apply ha.of_ringHom_of_comp_eq hx.aevalEquiv.toRingHom (RingHom.id L)
      hx.aevalEquiv.surjective Function.injective_id
    apply RingHom.ext
    intro p
    exact hx.algebraMap_aevalEquiv p
  obtain ⟨P,hP,hPa⟩ := hc.restrictScalars B
  exact ⟨P,hP,hPa⟩

end
end PD4Tensor.Spreading
end

end

end OAI
