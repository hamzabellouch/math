import Mathlib
import OAI.Algebra.FiniteTensor.FiniteCharts
import OAI.Algebra.FiniteTensor.FormalEvaluation

namespace OAI

/-! Frobenius specialization, moving substitutions and split coordinate restrictions. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor
open MvPowerSeries.WithPiTopology
noncomputable section
variable {R S A B σ : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra S B] [Finite σ]

 

theorem nilEval_coefficients (f : R →+* S) (F : A →+* B)
    (hF : ∀ r, F (algebraMap R A r)=algebraMap S B (f r))
    (v : σ → A) (hv : ∀ i, IsNilpotent (v i)) (q : MvPowerSeries σ R) :
    F (nilEval R v hv q)=nilEval S (fun i => F (v i)) (fun i => (hv i).map F)
      (MvPowerSeries.map f q) := by
  let : UniformSpace R := ⊥
  let : UniformSpace S := ⊥
  let : UniformSpace A := ⊥
  let : UniformSpace B := ⊥
  let : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  let : ContinuousSMul S B := ⟨continuous_of_discreteTopology⟩
  have hcm : Continuous (MvPowerSeries.map (σ:=σ) f) := by
    apply continuous_pi
    intro d
    change Continuous (fun q : MvPowerSeries σ R => f (MvPowerSeries.coeff d q))
    exact (continuous_of_discreteTopology : Continuous f).comp (continuous_coeff R d)
  have hcA : Continuous (nilEval R v hv : MvPowerSeries σ R → A) := MvPowerSeries.continuous_aeval _
  have hcB : Continuous (nilEval S (fun i => F (v i)) (fun i => (hv i).map F) :
      MvPowerSeries σ S → B) := MvPowerSeries.continuous_aeval _
  have h := Continuous.ext_on (denseRange_toMvPowerSeries (σ:=σ) (R:=R))
    ((continuous_of_discreteTopology : Continuous F).comp hcA)
    (hcB.comp hcm) (by
      rintro _ ⟨r,rfl⟩
      have hm : MvPowerSeries.map f (r : MvPowerSeries σ R)=
          (MvPolynomial.map f r : MvPowerSeries σ S) := by
        ext d
        simp only [MvPowerSeries.coeff_map,MvPolynomial.coeff_coe,MvPolynomial.coeff_map]
      change F (nilEval R v hv (r : MvPowerSeries σ R))=
        nilEval S (fun i => F (v i)) (fun i => (hv i).map F) (MvPowerSeries.map f (r : MvPowerSeries σ R))
      rw [hm,nilEval_coe,nilEval_coe]
      clear hm
      induction r using MvPolynomial.induction_on with
      | C c => simpa only [MvPolynomial.aeval_C,MvPolynomial.map_C] using hF c
      | add r s hr hs => simp only [map_add,hr,hs]
      | mul_X r i hr => simp only [map_mul,MvPolynomial.aeval_X,MvPolynomial.map_X,hr])
  exact congr_fun h q

end
end PD4Tensor

namespace PD4Tensor
open MvPowerSeries.WithPiTopology
noncomputable section
variable {R A σ : Type*} [CommRing R] [CommRing A] [Algebra R A] [Finite σ]
  (p : ℕ) [Fact p.Prime] [CharP R p]

 

theorem nilEval_frobenius (v : σ → A) (hv : ∀ i, v i ^ p=0)
    (q : MvPowerSeries σ R) :
    nilEval R v (fun i => ⟨p,hv i⟩) q ^ p=
      algebraMap R A (MvPowerSeries.constantCoeff q ^ p) := by
  let : UniformSpace R := ⊥
  let : UniformSpace A := ⊥
  let : ContinuousSMul R A := ⟨continuous_of_discreteTopology⟩
  have hc : Continuous (nilEval R v (fun i => ⟨p,hv i⟩) : MvPowerSeries σ R → A) :=
    MvPowerSeries.continuous_aeval _
  have h := Continuous.ext_on (denseRange_toMvPowerSeries (σ:=σ) (R:=R))
    (hc.pow p) ((continuous_of_discreteTopology : Continuous (algebraMap R A)).comp
      ((continuous_constantCoeff R).pow p)) (by
      rintro _ ⟨r,rfl⟩
      change nilEval R v _ (r : MvPowerSeries σ R) ^ p=
        algebraMap R A (MvPolynomial.constantCoeff r ^ p)
      rw [show nilEval R v _ (r : MvPowerSeries σ R)=MvPolynomial.aeval v r from
        nilEval_coe R v (fun i => ⟨p,hv i⟩) r]
      induction r using MvPolynomial.induction_on with
      | C c => simp
      | add r s hr hs =>
        rw [←map_pow,add_pow_char,map_add,map_pow,map_pow,hr,hs]
        simp only [map_add,add_pow_char]
      | mul_X r i hr =>
        simp only [map_mul,MvPolynomial.aeval_X,mul_pow,hv,mul_zero,
          MvPolynomial.constantCoeff_X,mul_zero,zero_pow (Fact.out : p.Prime).ne_zero,map_zero])
  exact congr_fun h q

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K σ : Type*) [CommRing K] [Fintype σ] [DecidableEq σ] (e : σ → ℕ)

def constantMap (he : ∀ i, 0<e i) : Ring K σ e →ₐ[K] K :=
  evaluate (fun _ => 0) (fun i => zero_pow (Nat.ne_of_gt (he i)))

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem constantMap_coord (he : ∀ i, 0<e i) (i : σ) :
    constantMap K σ e he (coord K σ e i)=0 := evaluate_coord _ _ i

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem constantMap_mk (he : ∀ i, 0<e i) (r : MvPolynomial σ K) :
    constantMap K σ e he (Ideal.Quotient.mk (ideal K σ e) r)=MvPolynomial.constantCoeff r := by
  change MvPolynomial.aeval (fun _ : σ => (0 : K)) r=MvPolynomial.constantCoeff r
  simp

omit [Fintype σ] [DecidableEq σ] in
theorem constantMap_surjective (he : ∀ i, 0<e i) :
    Function.Surjective (constantMap K σ e he) := by
  intro a
  exact ⟨algebraMap K (Ring K σ e) a,(constantMap K σ e he).commutes a⟩

variable (τ : Type*) [Fintype τ] [DecidableEq τ] (f : τ → ℕ)

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem coefficientSpecialization_scalar (he : ∀ i, 0<e i) (a : Ring K σ e) :
    coefficientSpecialization K σ τ e f he (algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) a)=
      algebraMap K (Ring K τ f) (constantMap K σ e he a) := by
  have hh : (coefficientSpecialization K σ τ e f he).comp
      (IsScalarTower.toAlgHom K (Ring K σ e) (Ring (Ring K σ e) τ f))=
      (Algebra.ofId K (Ring K τ f)).comp (constantMap K σ e he) := by
    apply hom_ext
    intro i
    change coefficientSpecialization K σ τ e f he
      (algebraMap (Ring K σ e) (Ring (Ring K σ e) τ f) (coord K σ e i))=
      algebraMap K (Ring K τ f) (constantMap K σ e he (coord K σ e i))
    rw [coefficientSpecialization_parameter,constantMap_coord,map_zero]
  exact AlgHom.congr_fun hh a

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K σ : Type*) [CommRing K] [Fintype σ] [DecidableEq σ] (e : σ → ℕ)
  (p : ℕ) [Fact p.Prime] [CharP K p]

 

omit [Fintype σ] [DecidableEq σ] in
theorem pow_eq_constantMap (he : ∀ i, 0<e i) (hep : ∀ i, e i≤p) (a : Ring K σ e) :
    a^p=algebraMap K (Ring K σ e) ((constantMap K σ e he a)^p) := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [constantMap_mk]
  induction r using MvPolynomial.induction_on with
  | C c =>
    rw [MvPolynomial.constantCoeff_C]
    change algebraMap K (Ring K σ e) c ^ p=_
    exact (map_pow _ _ _).symm
  | add r s hr hs =>
    rw [←map_pow,add_pow_char,map_add,map_pow,map_pow,hr,hs]
    simp only [map_add,add_pow_char]
  | mul_X r i hr =>
    rw [map_mul,mul_pow]
    change _ * coord K σ e i ^ p=_
    rw [pow_eq_zero_of_le (hep i) (coord_pow K σ e i),mul_zero]
    simp [zero_pow (Fact.out : p.Prime).ne_zero]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K ι σ : Type*) [Field K] [Fintype ι] [DecidableEq ι]
  [Fintype σ] [DecidableEq σ] (e : ι → ℕ) (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Fintype ι] [DecidableEq ι] [Fact p.Prime] in
private theorem parameter_charP (he : ∀ i, 0<e i) : CharP (Ring K ι e) p := by
  apply ((algebraMap K (Ring K ι e)).charP_iff ?_ p).mp inferInstance
  intro a b hab
  have hh := congrArg (constantMap K ι e he) hab
  simpa using hh

 

def movingSubst (he : ∀ i, 0<e i) (hep : ∀ i, e i≤p)
    (c : σ → MvPowerSeries σ (Ring K ι e))
    (hc : ∀ j, constantMap K ι e he (MvPowerSeries.constantCoeff (c j))=0) :
    Ring (Ring K ι e) σ (fun _ => p) →ₐ[Ring K ι e] Ring (Ring K ι e) σ (fun _ => p) := by
  letI : CharP (Ring K ι e) p := parameter_charP K ι e p he
  exact evaluate (fun j => nilEval (Ring K ι e) (coord (Ring K ι e) σ (fun _ => p))
    (fun i => ⟨p,coord_pow _ _ _ i⟩) (c j)) (by
      intro j
      rw [nilEval_frobenius p _ (fun i => coord_pow _ _ _ i),
        pow_eq_constantMap K ι e p he hep,hc]
      simp [zero_pow (Fact.out : p.Prime).ne_zero])

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem movingSubst_coord (he : ∀ i, 0<e i) (hep : ∀ i, e i≤p)
    (c : σ → MvPowerSeries σ (Ring K ι e))
    (hc : ∀ j, constantMap K ι e he (MvPowerSeries.constantCoeff (c j))=0) (j : σ) :
    movingSubst K ι σ e p he hep c hc (coord (Ring K ι e) σ (fun _ => p) j)=
      nilEval (Ring K ι e) (coord (Ring K ι e) σ (fun _ => p))
        (fun i => ⟨p,coord_pow _ _ _ i⟩) (c j) := evaluate_coord _ _ j

 

omit [Fintype ι] [DecidableEq ι] [DecidableEq σ] in
theorem movingSubst_central (he : ∀ i, 0<e i) (hep : ∀ i, e i≤p)
    (c : σ → MvPowerSeries σ (Ring K ι e))
    (hc : ∀ j, constantMap K ι e he (MvPowerSeries.constantCoeff (c j))=0) (j : σ) :
    coefficientSpecialization K ι σ e (fun _ => p) he
      (movingSubst K ι σ e p he hep c hc (coord (Ring K ι e) σ (fun _ => p) j))=
      FrobeniusTruncation.formalEval K σ p
        (MvPowerSeries.map (constantMap K ι e he).toRingHom (c j)) := by
  rw [movingSubst_coord]
  have hh := nilEval_coefficients (constantMap K ι e he).toRingHom
    (coefficientSpecialization K ι σ e (fun _ => p) he).toRingHom
    (coefficientSpecialization_scalar K ι e σ (fun _ => p) he)
    (coord (Ring K ι e) σ (fun _ => p)) (fun i => ⟨p,coord_pow _ _ _ i⟩) (c j)
  simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,coefficientSpecialization_coord] at hh
  convert hh using 1; rfl

 

omit [DecidableEq ι] in
theorem movingSubst_bijective (he : ∀ i, 0<e i) (hep : ∀ i, e i≤p)
    (c : σ → MvPowerSeries σ (Ring K ι e))
    (hc : ∀ j, constantMap K ι e he (MvPowerSeries.constantCoeff (c j))=0)
    (hM : Matrix.det (fun i j => constantMap K ι e he
      (MvPowerSeries.coeff (Finsupp.single j 1) (c i)))≠0) :
    Function.Bijective (movingSubst K ι σ e p he hep c hc) := by
  let c₀ (j : σ) := MvPowerSeries.map (constantMap K ι e he).toRingHom (c j)
  have hc₀ (j : σ) : MvPowerSeries.constantCoeff (c₀ j)=0 := by
    change (constantMap K ι e he).toRingHom (MvPowerSeries.constantCoeff (c j))=0
    exact hc j
  have hM₀ : Matrix.det (fun i j => MvPowerSeries.coeff (Finsupp.single j 1) (c₀ i))≠0 := by
    change Matrix.det (fun i j => (constantMap K ι e he).toRingHom
      (MvPowerSeries.coeff (Finsupp.single j 1) (c i)))≠0
    exact hM
  let C := AlgEquiv.ofBijective (FrobeniusTruncation.formalSubst K σ p c₀ hc₀)
    (FrobeniusTruncation.formalSubst_bijective K σ p c₀ hc₀ hM₀)
  apply bijective_of_central_equiv K ι σ e (fun _ => p) he C
  intro j
  change _=FrobeniusTruncation.formalSubst K σ p c₀ hc₀ (FrobeniusTruncation.coord K σ p j)
  rw [FrobeniusTruncation.formalSubst_coord]
  exact movingSubst_central K ι σ e p he hep c hc j

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
  (p : ℕ) [CharP K p] [Fact p.Prime]

abbrev constant : Ring K σ p →ₐ[K] K :=
  FiniteCoordinates.constantMap K σ (fun _ => p) (fun _ => (Fact.out : p.Prime).pos)

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
@[simp] theorem constant_coord (i : σ) : constant K σ p (coord K σ p i)=0 :=
  FiniteCoordinates.constantMap_coord _ _ _ _ i

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
@[simp] theorem constant_mk (f : MvPolynomial σ K) :
    constant K σ p (Ideal.Quotient.mk (ideal K σ p) f)=MvPolynomial.constantCoeff f :=
  FiniteCoordinates.constantMap_mk _ _ _ _ f

 

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
@[simp] theorem constant_hom (q : Ring K σ p →ₐ[K] Ring K σ p) (a : Ring K σ p) :
    constant K σ p (q a)=constant K σ p a := by
  have h : (constant K σ p).comp q=constant K σ p := by
    apply FiniteCoordinates.hom_ext
    intro i
    change constant K σ p (q (coord K σ p i))=constant K σ p (coord K σ p i)
    rw [constant_coord]
    apply (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp
    rw [←map_pow,←map_pow,variable_pow,map_zero,map_zero]
  exact AlgHom.congr_fun h a

def tangentCoeff (j : σ) : Ring K σ p →ₗ[K] K :=
  (constant K σ p).toLinearMap.comp (derivative K σ p j)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem tangentCoeff_mk (j : σ) (f : MvPolynomial σ K) :
    tangentCoeff K σ p j (Ideal.Quotient.mk (ideal K σ p) f)=
      f.coeff (Finsupp.single j 1) := by
  change constant K σ p (derivative K σ p j (Ideal.Quotient.mk (ideal K σ p) f))=_
  rw [derivative_mk,constant_mk,MvPolynomial.constantCoeff_eq,MvPolynomial.coeff_pderiv]
  simp

omit [Fintype σ] in
@[simp] theorem tangentCoeff_coord (j i : σ) :
    tangentCoeff K σ p j (coord K σ p i)=if i=j then 1 else 0 := by
  rw [coord,tangentCoeff_mk]
  by_cases h : i=j
  · subst i; simp
  · simp [MvPolynomial.coeff_X,Finsupp.single_eq_single_iff,h]

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem tangentCoeff_scalar (j : σ) (a : K) :
    tangentCoeff K σ p j (algebraMap K (Ring K σ p) a)=0 := by
  change constant K σ p (derivative K σ p j
    (Ideal.Quotient.mk (ideal K σ p) (MvPolynomial.C a)))=0
  rw [derivative_mk,MvPolynomial.pderiv_C,map_zero,map_zero]

omit [Fintype σ] [DecidableEq σ] in
theorem tangentCoeff_mul (j : σ) (a b : Ring K σ p) :
    tangentCoeff K σ p j (a*b)=
      tangentCoeff K σ p j a * constant K σ p b +
      constant K σ p a * tangentCoeff K σ p j b := by
  change constant K σ p (derivative K σ p j (a*b))=_
  rw [derivative_mul,map_add,map_mul,map_mul]
  rfl

 
theorem tangentCoeff_hom (q : Ring K σ p →ₐ[K] Ring K σ p)
    (j : σ) (a : Ring K σ p) :
    tangentCoeff K σ p j (q a)=
      ∑ i, tangentCoeff K σ p i a * tangentCoeff K σ p j (q (coord K σ p i)) := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective a
  induction f using MvPolynomial.induction_on with
  | C a =>
    change tangentCoeff K σ p j (q (algebraMap K (Ring K σ p) a))=
      ∑ i, tangentCoeff K σ p i (algebraMap K (Ring K σ p) a) * _
    simp only [q.commutes,tangentCoeff_scalar,zero_mul,Finset.sum_const_zero]
  | add f g hf hg =>
    simp only [map_add,hf,hg,add_mul,Finset.sum_add_distrib]
  | mul_X f i hf =>
    simp only [map_mul,show Ideal.Quotient.mk (ideal K σ p)
      (MvPolynomial.X i)=coord K σ p i from rfl,tangentCoeff_mul,constant_hom,
      constant_coord,mul_zero,zero_add,tangentCoeff_coord]
    simp

def tangentHom (q : Ring K σ p →ₐ[K] Ring K σ p) : Matrix σ σ K :=
  fun i j => tangentCoeff K σ p j (q (coord K σ p i))

omit [Fintype σ] in
@[simp] theorem tangentHom_id : tangentHom K σ p (AlgHom.id K (Ring K σ p))=1 := by
  ext i j
  simp [tangentHom,Matrix.one_apply]

theorem tangentHom_comp (q r : Ring K σ p →ₐ[K] Ring K σ p) :
    tangentHom K σ p (q.comp r)=tangentHom K σ p r * tangentHom K σ p q := by
  ext i j
  exact tangentCoeff_hom K σ p q j (r (coord K σ p i))

 

theorem tangentHom_det_ne_zero (q : Ring K σ p ≃ₐ[K] Ring K σ p) :
    Matrix.det (tangentHom K σ p q.toAlgHom)≠0 := by
  have hc : q.toAlgHom.comp q.symm.toAlgHom=AlgHom.id K (Ring K σ p) := by
    apply AlgHom.ext
    intro a
    exact q.apply_symm_apply a
  have h := congrArg Matrix.det (tangentHom_comp K σ p q.toAlgHom q.symm.toAlgHom)
  rw [hc,tangentHom_id,Matrix.det_one,Matrix.det_mul] at h
  intro hz
  rw [hz,mul_zero] at h
  exact one_ne_zero h

 

theorem inverse_representatives (q : Ring K σ p ≃ₐ[K] Ring K σ p)
    (f : σ → MvPolynomial σ K)
    (hf : ∀ i, Ideal.Quotient.mk (ideal K σ p) (f i)=q (coord K σ p i)) :
    (∀ i, MvPolynomial.constantCoeff (f i)=0) ∧ (tangentMatrix K σ f).det≠0 := by
  constructor
  · intro i
    rw [←constant_mk K σ p,hf]
    change constant K σ p (q.toAlgHom (coord K σ p i))=0
    rw [constant_hom,constant_coord]
  · have h : tangentMatrix K σ f=tangentHom K σ p q.toAlgHom := by
      ext i j
      change (f i).coeff (Finsupp.single j 1)=
        tangentCoeff K σ p j (q (coord K σ p i))
      rw [←hf,tangentCoeff_mk]
    rw [h]
    exact tangentHom_det_ne_zero K σ p q

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (R σ τ : Type*) [CommRing R] [Fintype σ] [DecidableEq σ]
  [Fintype τ] [DecidableEq τ] (p : ℕ)

def renameHom (e : σ → τ) : Ring R σ (fun _ => p) →ₐ[R] Ring R τ (fun _ => p) :=
  evaluate (fun i => coord R τ (fun _ => p) (e i)) (fun _ => coord_pow _ _ _ _)

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem renameHom_coord (e : σ → τ) (i : σ) :
    renameHom R σ τ p e (coord R σ (fun _ => p) i)=coord R τ (fun _ => p) (e i) :=
  evaluate_coord _ _ _

def reindexEquiv (e : σ ≃ τ) : Ring R σ (fun _ => p) ≃ₐ[R] Ring R τ (fun _ => p) :=
  AlgEquiv.ofAlgHom (renameHom R σ τ p e) (renameHom R τ σ p e.symm)
    (by apply hom_ext; intro i; simp only [AlgHom.comp_apply,renameHom_coord,
        Equiv.apply_symm_apply,AlgHom.id_apply])
    (by apply hom_ext; intro i; simp only [AlgHom.comp_apply,renameHom_coord,
        Equiv.symm_apply_apply,AlgHom.id_apply])

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem reindexEquiv_coord (e : σ ≃ τ) (i : σ) :
    reindexEquiv R σ τ p e (coord R σ (fun _ => p) i)=coord R τ (fun _ => p) (e i) :=
  renameHom_coord R σ τ p e i

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem reindexEquiv_symm_coord (e : σ ≃ τ) (i : τ) :
    (reindexEquiv R σ τ p e).symm (coord R τ (fun _ => p) i)=
      coord R σ (fun _ => p) (e.symm i) := renameHom_coord R τ σ p e.symm i

def uniformLeft (hp : 0<p) : Ring R (σ ⊕ τ) (fun _ => p) →ₐ[R] Ring R σ (fun _ => p) :=
  evaluate (Sum.elim (coord R σ (fun _ => p)) (fun _ => 0)) (by
    intro i
    cases i with
    | inl i => exact coord_pow _ _ _ i
    | inr i => exact zero_pow (Nat.ne_of_gt hp))

def uniformInclude : Ring R σ (fun _ => p) →ₐ[R] Ring R (σ ⊕ τ) (fun _ => p) :=
  renameHom R σ (σ ⊕ τ) p Sum.inl

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem uniformLeft_coord (hp : 0<p) (i : σ ⊕ τ) :
    uniformLeft R σ τ p hp (coord R (σ ⊕ τ) (fun _ => p) i)=
      Sum.elim (coord R σ (fun _ => p)) (fun _ => 0) i := evaluate_coord _ _ _

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
@[simp] theorem uniformLeft_include (hp : 0<p) (a : Ring R σ (fun _ => p)) :
    uniformLeft R σ τ p hp (uniformInclude R σ τ p a)=a := by
  have h : (uniformLeft R σ τ p hp).comp (uniformInclude R σ τ p)=AlgHom.id R _ := by
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply,uniformInclude,renameHom_coord,uniformLeft_coord,
      Sum.elim_inl,AlgHom.id_apply]
  exact AlgHom.congr_fun h a

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
theorem uniformLeft_surjective (hp : 0<p) : Function.Surjective (uniformLeft R σ τ p hp) :=
  fun a => ⟨uniformInclude R σ τ p a,uniformLeft_include R σ τ p hp a⟩

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
theorem uniformLeft_ker (hp : 0<p) : RingHom.ker (uniformLeft R σ τ p hp).toRingHom=
    Ideal.span (Set.range (fun j => coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j))) := by
  let J := Ideal.span (Set.range (fun j => coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))
  apply le_antisymm
  · intro a ha
    change uniformLeft R σ τ p hp a=0 at ha
    have h := error_mem J ((uniformInclude R σ τ p).comp (uniformLeft R σ τ p hp)) (by
      intro i
      cases i with
      | inl i =>
        simp only [AlgHom.comp_apply,uniformLeft_coord,Sum.elim_inl,uniformInclude,
          renameHom_coord,sub_self,Ideal.zero_mem]
      | inr j =>
        simp only [AlgHom.comp_apply,uniformLeft_coord,Sum.elim_inr,map_zero,sub_zero]
        exact Ideal.subset_span (Set.mem_range_self j)) a
    simpa only [AlgHom.comp_apply,ha,map_zero,sub_zero] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    change uniformLeft R σ τ p hp (coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j))=0
    simp only [uniformLeft_coord,Sum.elim_inr]

variable {R σ τ p}
 
def splitRestriction {υ : Type*} [Fintype υ] [DecidableEq υ]
    (hp : 0<p) (e : υ ≃ σ ⊕ τ)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    Ring R υ (fun _ => p) →ₐ[R] Ring R σ (fun _ => p) :=
  (uniformLeft R σ τ p hp).comp
    ((reindexEquiv R υ (σ ⊕ τ) p e).toAlgHom.comp q.toAlgHom)

omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
theorem splitRestriction_surjective {υ : Type*} [Fintype υ] [DecidableEq υ]
    (hp : 0<p) (e : υ ≃ σ ⊕ τ)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    Function.Surjective (splitRestriction hp e q) :=
  (uniformLeft_surjective R σ τ p hp).comp
    ((reindexEquiv R υ (σ ⊕ τ) p e).surjective.comp q.surjective)

 
omit [Fintype σ] [DecidableEq σ] [Fintype τ] [DecidableEq τ] in
theorem splitRestriction_ker {υ : Type*} [Fintype υ] [DecidableEq υ]
    (hp : 0<p) (e : υ ≃ σ ⊕ τ)
    (q : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p)) :
    RingHom.ker (splitRestriction hp e q).toRingHom=
      Ideal.span (Set.range (fun j => q.symm (coord R υ (fun _ => p) (e.symm (Sum.inr j))))) := by
  let E := reindexEquiv R υ (σ ⊕ τ) p e
  let Q := q.trans E
  have h : RingHom.ker (splitRestriction hp e q).toRingHom=
      Ideal.comap Q.toRingHom (Ideal.span (Set.range (fun j => coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))) := by
    rw [←uniformLeft_ker R σ τ p hp]
    rfl
  rw [h]
  have hm : Ideal.comap Q.toRingHom (Ideal.span (Set.range (fun j => coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j))))=
      (Ideal.span (Set.range (fun j => coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))).map Q.symm.toRingHom := by
    ext a
    rw [Ideal.mem_map_iff_of_surjective Q.symm.toRingHom Q.symm.surjective]
    constructor
    · intro ha
      exact ⟨Q a,ha,Q.symm_apply_apply a⟩
    · rintro ⟨b,hb,rfl⟩
      change Q (Q.symm b)∈Ideal.span (Set.range (fun j =>
        coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))
      rwa [Q.apply_symm_apply]
  rw [hm,Ideal.map_span]
  congr 1
  ext a
  simp only [Set.mem_image,Set.mem_range]
  constructor
  · rintro ⟨b,⟨j,rfl⟩,rfl⟩
    refine ⟨j,?_⟩
    change q.symm (coord R υ (fun _ => p) (e.symm (Sum.inr j)))=
      q.symm (E.symm (coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))
    rw [reindexEquiv_symm_coord]
  · rintro ⟨j,rfl⟩
    refine ⟨coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j),⟨j,rfl⟩,?_⟩
    change q.symm (E.symm (coord R (σ ⊕ τ) (fun _ => p) (Sum.inr j)))=_
    rw [reindexEquiv_symm_coord]

end
end PD4Tensor.FiniteCoordinates
end

end OAI
