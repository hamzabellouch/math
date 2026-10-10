import Mathlib
import OAI.Algebra.FiniteTensor.TensorResidues

namespace OAI

/-! Coordinate equivalences induced by invertible tangent matrices. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
noncomputable section
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

 

theorem coordinate_error_raises (J : Ideal A) (f : A →ₐ[K] A)
    (h₀ : ∀ a, a-f a∈J) (h₁ : ∀ a∈J, a-f a∈J^2) :
    ∀ n a, a∈J^n → a-f a∈J^(n+1) := by
  intro n
  induction n with
  | zero => intro a _; simpa using h₀ a
  | succ n ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on (R:=A) (C:=fun a => a-f a∈J^(n+1+1)) ha ?_ ?_
    · intro x hx y hy
      have hfy : f y∈J := by
        have hey : y-f y∈J := (Ideal.pow_le_self (by decide : 2 ≠ 0)) (h₁ y hy)
        simpa using J.sub_mem hy hey
      have hxy := Ideal.mul_mem_mul hx (h₁ y hy)
      have hxy' : (x-f x)*f y∈J^(n+1)*J^1 :=
        Ideal.mul_mem_mul (ih x hx) (by simpa using hfy)
      rw [← pow_add] at hxy
      rw [← pow_add] at hxy'
      have h := (J^(n+1+1)).add_mem (by simpa [Nat.add_assoc] using hxy) hxy'
      convert h using 1; simp only [map_mul]; ring
    · intro x y hx hy
      simpa only [map_add, add_sub_add_comm] using (J^(n+1+1)).add_mem hx hy

 

theorem coordinate_error_on_span {ι : Type*} (z : ι → A) (f : A →ₐ[K] A)
    (h₀ : ∀ a, a-f a∈Ideal.span (Set.range z))
    (hz : ∀ i, z i-f (z i)∈Ideal.span (Set.range z)^2) :
    ∀ a∈Ideal.span (Set.range z), a-f a∈Ideal.span (Set.range z)^2 := by
  intro a ha
  let J : Ideal A := Ideal.span (Set.range z)
  change a-f a∈J^2
  refine Submodule.span_induction (p:=fun a _ => a-f a∈J^2) ?_ ?_ ?_ ?_ ha
  · rintro a ⟨i,rfl⟩
    exact hz i
  · simp
  · intro a b ha hb hea heb
    simpa only [map_add,add_sub_add_comm] using (J^2).add_mem hea heb
  · intro r a ha hea
    change r*a-f (r*a)∈J^2
    have hfa : f a∈J := by
      have he : a-f a∈J := (Ideal.pow_le_self (by decide : 2≠0)) hea
      simpa using J.sub_mem ha he
    have hprod : (r-f r)*f a∈J^2 := by
      simpa only [pow_two] using Ideal.mul_mem_mul (h₀ r) hfa
    have h := (J^2).add_mem (Ideal.mul_mem_left _ r hea) hprod
    convert h using 1; simp only [map_mul]; ring

 

theorem bijective_of_identity_tangent (J : Ideal A) (f : A →ₐ[K] A)
    (h₀ : ∀ a, a-f a∈J) (h₁ : ∀ a∈J, a-f a∈J^2)
    (N : ℕ) (hN : J^N=⊥) : Function.Bijective f := by
  let e : Module.End K A := 1-f.toLinearMap
  have he (a : A) : e a=a-f a := rfl
  have hen : ∀ n a, (e^n) a∈J^n := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ' e,Module.End.mul_apply,he]
      exact coordinate_error_raises J f h₀ h₁ n _ (ih a)
  have hn : IsNilpotent e := by
    refine ⟨N,?_⟩
    ext a
    have ha := hen N a
    rw [hN,Ideal.mem_bot] at ha
    exact ha
  have hf : IsUnit f.toLinearMap := by
    have h := hn.isUnit_one_sub
    simpa only [e,sub_sub_cancel] using h
  exact (Module.End.isUnit_iff _).mp hf

 
def coordinatesEquiv (J : Ideal A) (f : A →ₐ[K] A)
    (h₀ : ∀ a, a-f a∈J) (h₁ : ∀ a∈J, a-f a∈J^2)
    (N : ℕ) (hN : J^N=⊥) : A ≃ₐ[K] A :=
  AlgEquiv.ofBijective f (bijective_of_identity_tangent J f h₀ h₁ N hN)

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K σ : Type*) [CommRing K] [Fintype σ] [DecidableEq σ] (e : σ → ℕ)

 
def ideal : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range (fun i : σ => (MvPolynomial.X i : MvPolynomial σ K)^e i))
abbrev Ring := MvPolynomial σ K ⧸ ideal K σ e

def coord (i : σ) : Ring K σ e :=
  Ideal.Quotient.mk (ideal K σ e) (MvPolynomial.X i)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem coord_pow (i : σ) : coord K σ e i ^ e i=0 := by
  rw [coord,←map_pow,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

variable {K σ e} {B : Type*} [CommRing B] [Algebra K B]
def evaluate (v : σ → B) (hv : ∀ i, v i^e i=0) : Ring K σ e →ₐ[K] B :=
  Ideal.Quotient.liftₐ (ideal K σ e) (MvPolynomial.aeval v) (by
    have h : ideal K σ e ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      simpa using hv i
    exact fun a ha => h ha)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem evaluate_coord (v : σ → B) (hv : ∀ i, v i^e i=0) (i : σ) :
    evaluate v hv (coord K σ e i)=v i := by
  change (MvPolynomial.aeval v) (MvPolynomial.X i)=v i
  exact MvPolynomial.aeval_X v i

omit [Fintype σ] [DecidableEq σ] in
@[ext] theorem hom_ext {f g : Ring K σ e →ₐ[K] B}
    (h : ∀ i, f (coord K σ e i)=g (coord K σ e i)) : f=g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

variable (K σ e)
def augmentationIdeal : Ideal (Ring K σ e) := Ideal.span (Set.range (coord K σ e))

 
omit [DecidableEq σ] in
theorem augmentation_nilpotent : IsNilpotent (augmentationIdeal K σ e) := by
  have hfg : (augmentationIdeal K σ e).FG :=
    Submodule.fg_span (Set.finite_range (coord K σ e))
  apply hfg.isNilpotent_iff_le_nilradical.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact mem_nilradical.mpr ⟨e i,coord_pow K σ e i⟩

variable {K σ e}
 
omit [Fintype σ] [DecidableEq σ] in
theorem error_mem (J : Ideal (Ring K σ e)) (f : Ring K σ e →ₐ[K] Ring K σ e)
    (hz : ∀ i, coord K σ e i-f (coord K σ e i)∈J) (a : Ring K σ e) :
    a-f a∈J := by
  refine Quotient.inductionOn' a ?_
  intro q
  change Ideal.Quotient.mk (ideal K σ e) q-f (Ideal.Quotient.mk (ideal K σ e) q)∈J
  induction q using MvPolynomial.induction_on with
  | C c =>
    change algebraMap K (Ring K σ e) c-f (algebraMap K (Ring K σ e) c)∈J
    simp
  | add q r hq hr =>
    simpa only [map_add,add_sub_add_comm] using J.add_mem hq hr
  | mul_X q i hq =>
    change Ideal.Quotient.mk _ q * coord K σ e i-
      f (Ideal.Quotient.mk _ q * coord K σ e i)∈J
    have h := J.add_mem (Ideal.mul_mem_left J (Ideal.Quotient.mk (ideal K σ e) q) (hz i))
      (Ideal.mul_mem_right (f (coord K σ e i)) J hq)
    convert h using 1; simp only [map_mul]; ring

 

omit [DecidableEq σ] in
theorem bijective_of_tangent_identity (f : Ring K σ e →ₐ[K] Ring K σ e)
    (hz : ∀ i, coord K σ e i-f (coord K σ e i)∈augmentationIdeal K σ e^2) :
    Function.Bijective f := by
  have h₀ : ∀ a, a-f a∈augmentationIdeal K σ e :=
    error_mem _ f (fun i => (Ideal.pow_le_self (by decide : 2≠0)) (hz i))
  have h₁ := coordinate_error_on_span (coord K σ e) f h₀ hz
  obtain ⟨N,hN⟩ := augmentation_nilpotent K σ e
  exact bijective_of_identity_tangent _ f h₀ h₁ N hN

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
open scoped BigOperators
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)
  [CharP K p] [Fact p.Prime]

@[simp] theorem linearSubst_one : linearSubst K σ p (1 : Matrix σ σ K)=AlgHom.id K _ := by
  apply FiniteCoordinates.hom_ext (e:=fun _ => p)
  intro i
  change linearSubst K σ p 1 (coord K σ p i)=coord K σ p i
  simp [linearSubst_coord,Matrix.one_apply]

 

def linearEquiv (M : Matrix σ σ K) (hM : M.det≠0) : Ring K σ p ≃ₐ[K] Ring K σ p := by
  let f := linearSubst K σ p M
  let g := linearSubst K σ p M⁻¹
  have hfg : f.comp g=AlgHom.id K _ := by
    rw [←linearSubst_mul,Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),linearSubst_one]
  have hgf : g.comp f=AlgHom.id K _ := by
    rw [←linearSubst_mul,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),linearSubst_one]
  exact AlgEquiv.ofBijective f ⟨(fun a b h => by
    have ha := DFunLike.congr_fun hgf a
    have hb := DFunLike.congr_fun hgf b
    change g (f a)=a at ha
    change g (f b)=b at hb
    rw [←ha,←hb,h]),fun a => ⟨g a,DFunLike.congr_fun hfg a⟩⟩

def polynomialSubst (c : σ → MvPolynomial σ K)
    (hc : ∀ i, MvPolynomial.constantCoeff (c i)=0) : Ring K σ p →ₐ[K] Ring K σ p :=
  FiniteCoordinates.evaluate (fun i => Ideal.Quotient.mk (ideal K σ p) (c i)) (by
    intro i
    rw [frobenius_mk,hc]
    simp [zero_pow (Fact.out : p.Prime).ne_zero])

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem polynomialSubst_coord (c : σ → MvPolynomial σ K)
    (hc : ∀ i, MvPolynomial.constantCoeff (c i)=0) (i : σ) :
    polynomialSubst K σ p c hc (coord K σ p i)=Ideal.Quotient.mk (ideal K σ p) (c i) := by
  change (MvPolynomial.aeval _) (MvPolynomial.X i)=_
  exact MvPolynomial.aeval_X _ i

 

omit [Fintype σ] [DecidableEq σ] [CharP K p] [Fact p.Prime] in
theorem map_idealOfVars :
    (MvPolynomial.idealOfVars σ K).map (Ideal.Quotient.mk (ideal K σ p))=
      FiniteCoordinates.augmentationIdeal K σ (fun _ => p) := by
  rw [MvPolynomial.idealOfVars,Ideal.map_span]
  congr 1
  exact Set.range_comp (Ideal.Quotient.mk (ideal K σ p)) MvPolynomial.X |>.symm

 

theorem polynomialSubst_bijective (c : σ → MvPolynomial σ K)
    (hc : ∀ i, MvPolynomial.constantCoeff (c i)=0)
    (hM : (tangentMatrix K σ c).det≠0) :
    Function.Bijective (polynomialSubst K σ p c hc) := by
  let M := tangentMatrix K σ c
  let J : Ideal (Ring K σ p) := FiniteCoordinates.augmentationIdeal K σ (fun _ => p)
  have herr (i : σ) : Ideal.Quotient.mk (ideal K σ p) (c i)-
      ∑ j : σ, M i j • coord K σ p j∈J^2 := by
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (ideal K σ p))
      (sub_linearPart_mem K σ (c i) (hc i))
    rw [Ideal.map_pow,map_idealOfVars,map_sub] at h
    have he : Ideal.Quotient.mk (ideal K σ p) (linearPart K σ (c i))=
        ∑ j : σ, M i j • coord K σ p j := by
      simp only [linearPart,map_sum,map_mul,M,tangentMatrix]
      apply Finset.sum_congr rfl
      intro j hj
      exact (Algebra.smul_def ((c i).coeff (Finsupp.single j 1)) (coord K σ p j)).symm
    rw [he] at h
    exact h
  let f := (polynomialSubst K σ p c hc).comp (linearSubst K σ p M⁻¹)
  have hf : Function.Bijective f := by
    apply FiniteCoordinates.bijective_of_tangent_identity
    intro i
    change coord K σ p i-f (coord K σ p i)∈J^2
    have hsum : (∑ j : σ, M⁻¹ i j • (Ideal.Quotient.mk (ideal K σ p) (c j)-
        ∑ k : σ, M j k • coord K σ p k))∈J^2 := by
      exact (J^2).sum_mem (fun j _ => ((J^2).restrictScalars K).smul_mem (M⁻¹ i j) (herr j))
    have he : (∑ j : σ, M⁻¹ i j • ∑ k : σ, M j k • coord K σ p k)=coord K σ p i := by
      simp only [Finset.smul_sum,smul_smul]
      rw [Finset.sum_comm]
      simp only [←Finset.sum_smul,←Matrix.mul_apply,
        Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),Matrix.one_apply]
      simp
    simp only [smul_sub,Finset.sum_sub_distrib,he] at hsum
    have hneg : -(∑ j : σ, M⁻¹ i j • Ideal.Quotient.mk (ideal K σ p) (c j)-coord K σ p i) ∈ (J^2 : Ideal (Ring K σ p)) := (J^2).neg_mem hsum
    have hn : -(∑ j : σ, M⁻¹ i j • Ideal.Quotient.mk (ideal K σ p) (c j)-coord K σ p i)=
        coord K σ p i-∑ j : σ, M⁻¹ i j • Ideal.Quotient.mk (ideal K σ p) (c j) := by ring
    rw [hn] at hneg
    simp only [f,AlgHom.comp_apply,linearSubst_coord,map_sum,map_smul,
      polynomialSubst_coord]
    convert hneg using 1
    rfl
  have hlin : Function.Bijective (linearSubst K σ p M⁻¹) := by
    apply (linearEquiv K σ p M⁻¹ ?_).bijective
    rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    exact inv_ne_zero hM
  exact (Function.Bijective.of_comp_iff _ hlin).mp hf

end
end PD4Tensor.FrobeniusTruncation
end

end OAI
