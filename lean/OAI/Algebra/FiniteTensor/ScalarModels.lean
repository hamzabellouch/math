import Mathlib
import OAI.Algebra.FiniteTensor.ComplementaryGraphs

namespace OAI

/-! Squarefree scalar tensor models, primitives and complementary dimensions. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.Spreading
variable (A : Type*) [CommRing A] (m : ℕ)

def squareIdeal : Ideal (MvPolynomial (Fin m) A) :=
  Ideal.span (Set.range (fun i : Fin m => (MvPolynomial.X i : MvPolynomial (Fin m) A)^2))

abbrev Parameters := MvPolynomial (Fin m) A ⧸ squareIdeal A m

def parameter (i : Fin m) : Parameters A m :=
  Ideal.Quotient.mk (squareIdeal A m) (MvPolynomial.X i)

def augmentation : Parameters A m →+* A :=
  Ideal.Quotient.lift (squareIdeal A m)
    (MvPolynomial.eval₂Hom (RingHom.id A) (fun _ => 0)) (by
      have h : squareIdeal A m ≤
          RingHom.ker (MvPolynomial.eval₂Hom (RingHom.id A) (fun _ : Fin m => 0)) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        simp
      exact fun a ha => h ha)

def parameterIdeal : Ideal (Parameters A m) := Ideal.span (Set.range (parameter A m))

@[simp] theorem parameter_sq (i : Fin m) : parameter A m i ^ 2 = 0 := by
  unfold parameter
  rw [←map_pow,Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

@[simp] theorem augmentation_parameter (i : Fin m) : augmentation A m (parameter A m i)=0 := by
  change (MvPolynomial.eval₂Hom (RingHom.id A) (fun _ : Fin m => 0)) (MvPolynomial.X i)=0
  simp

@[simp] theorem augmentation_algebraMap (a : A) :
    augmentation A m (algebraMap A (Parameters A m) a)=a := by
  change (MvPolynomial.eval₂Hom (RingHom.id A) (fun _ : Fin m => 0)) (MvPolynomial.C a)=a
  exact MvPolynomial.eval₂Hom_C _ _ _

theorem parameterIdeal_le_nilradical : parameterIdeal A m ≤ nilradical (Parameters A m) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact mem_nilradical.mpr ⟨2,parameter_sq A m i⟩

theorem hasSubst_parameters {υ σ : Type*} [Finite σ] [Finite υ]
    (H : υ → MvPowerSeries σ (Parameters A m))
    (hH : ∀ i,MvPowerSeries.constantCoeff (H i)∈parameterIdeal A m) :
    MvPowerSeries.HasSubst H := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
  intro i
  exact mem_nilradical.mp (parameterIdeal_le_nilradical A m (hH i))

variable {A m} {B : Type*} [CommRing B]

def mapParameters (f : A →+* B) : Parameters A m →+* Parameters B m :=
  Ideal.Quotient.lift (squareIdeal A m)
    ((Ideal.Quotient.mk (squareIdeal B m)).comp (MvPolynomial.map f)) (by
      have h : squareIdeal A m ≤ RingHom.ker
          ((Ideal.Quotient.mk (squareIdeal B m)).comp (MvPolynomial.map f)) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change (Ideal.Quotient.mk (squareIdeal B m)) ((MvPolynomial.map f) ((MvPolynomial.X i)^2))=0
        rw [map_pow,MvPolynomial.map_X,map_pow]
        exact parameter_sq B m i
      exact fun a ha => h ha)

@[simp] theorem mapParameters_parameter (f : A →+* B) (i : Fin m) :
    mapParameters f (parameter A m i)=parameter B m i := by
  change Ideal.Quotient.mk (squareIdeal B m) (MvPolynomial.map f (MvPolynomial.X i))=_
  rw [MvPolynomial.map_X]
  rfl

@[simp] theorem mapParameters_algebraMap (f : A →+* B) (a : A) :
    mapParameters (m:=m) f (algebraMap A (Parameters A m) a)=
      algebraMap B (Parameters B m) (f a) := by
  change Ideal.Quotient.mk (squareIdeal B m) (MvPolynomial.map f (MvPolynomial.C a))=_
  rw [MvPolynomial.map_C]
  rfl

@[simp] theorem augmentation_mapParameters (f : A →+* B) (a : Parameters A m) :
    augmentation B m (mapParameters f a)=f (augmentation A m a) := by
  have heq : (augmentation B m).comp (mapParameters (m:=m) f)=f.comp (augmentation A m) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change augmentation B m (mapParameters f (algebraMap A (Parameters A m) a))=
        f (augmentation A m (algebraMap A (Parameters A m) a))
      simp only [mapParameters_algebraMap,augmentation_algebraMap]
    · intro i
      change augmentation B m (mapParameters f (parameter A m i))=f (augmentation A m (parameter A m i))
      simp only [mapParameters_parameter,augmentation_parameter,map_zero]
  exact RingHom.congr_fun heq a

theorem mapParameters_mem (f : A →+* B) {a : Parameters A m}
    (ha : a∈parameterIdeal A m) : mapParameters f a∈parameterIdeal B m := by
  have hle : parameterIdeal A m ≤ Ideal.comap (mapParameters f) (parameterIdeal B m) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change mapParameters f (parameter A m i)∈parameterIdeal B m
    rw [mapParameters_parameter]
    exact Ideal.subset_span (Set.mem_range_self i)
  exact hle ha

end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
universe u
variable (A : Type*) [CommRing A] {l : ℕ} (σ : Fin l → Type u)
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)] (m : ℕ)

def potential (F : ∀ i,MvPowerSeries (σ i) A) : MvPowerSeries ((i : Fin l) × σ i) A :=
  ∑ i,MvPowerSeries.rename (Sigma.mk i) (F i)

def perturbation (active : Fin m ↪ Fin l) (b : ∀ j,MvPowerSeries (σ (active j)) A)
    (j : Fin m) : MvPowerSeries ((i : Fin l) × σ i) A :=
  MvPowerSeries.rename (Sigma.mk (active j)) (b j)

def deformed (F : ∀ i,MvPowerSeries (σ i) A)
    (active : Fin m ↪ Fin l) (b : ∀ j,MvPowerSeries (σ (active j)) A) :
    MvPowerSeries ((i : Fin l) × σ i) (Parameters A m) :=
  MvPowerSeries.map (algebraMap A (Parameters A m)) (potential A σ F) +
    ∑ j,MvPowerSeries.C (parameter A m j)*MvPowerSeries.map (algebraMap A (Parameters A m))
      (perturbation A σ m active b j)

def tangent {d c : ℕ} (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c)
    (H : ((i : Fin l) × σ i) → MvPowerSeries (Fin d) (Parameters A m))
    (G : ((i : Fin l) × σ i) → MvPowerSeries (Fin c) A) :
    Matrix ((i : Fin l) × σ i) ((i : Fin l) × σ i) A :=
  fun i j => Sum.elim
    (fun k => augmentation A m (MvPowerSeries.coeff (Finsupp.single k 1) (H i)))
    (fun k => MvPowerSeries.coeff (Finsupp.single k 1) (G i)) (e j)

 

structure TensorModel (d c : ℕ) (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c)
    (active : Fin m ↪ Fin l) where
  F : ∀ i,MvPowerSeries (σ i) A
  b : ∀ j,MvPowerSeries (σ (active j)) A
  F_zero : ∀ i,MvPowerSeries.constantCoeff (F i)=0
  b_zero : ∀ j,MvPowerSeries.constantCoeff (b j)=0
  H : ((i : Fin l) × σ i) → MvPowerSeries (Fin d) (Parameters A m)
  G : ((i : Fin l) × σ i) → MvPowerSeries (Fin c) A
  H_zero : ∀ i,MvPowerSeries.constantCoeff (H i)∈parameterIdeal A m
  G_zero : ∀ i,MvPowerSeries.constantCoeff (G i)=0
  tangent_unit : IsUnit (tangent A σ m e H G).det
  left_vanishing : MvPowerSeries.subst H (deformed A σ m F active b)=0
  right_vanishing : MvPowerSeries.subst G (potential A σ F)=0
  left_triple : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
    MvPowerSeries.C (parameter A m i*parameter A m j*parameter A m k)∈Ideal.span
      (Set.range (fun x => MvPowerSeries.subst H
        (MvPowerSeries.pderiv x (deformed A σ m F active b))))
  right_triple : ∀ i j k : Fin m,i≠j → i≠k → j≠k →
    MvPowerSeries.subst G (perturbation A σ m active b i*perturbation A σ m active b j*
      perturbation A σ m active b k)∈Ideal.span
      (Set.range (fun x => MvPowerSeries.subst G (MvPowerSeries.pderiv x (potential A σ F))))

end
end PD4Tensor.Spreading

namespace PD4Tensor.Spreading
noncomputable section
open scoped BigOperators
universe u
variable {A B : Type*} [CommRing A] [CommRing B] {l : ℕ} {σ : Fin l → Type u}
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)] {m : ℕ}

omit [∀ i,DecidableEq (σ i)] in
 theorem map_potential (f : A →+* B) (F : ∀ i,MvPowerSeries (σ i) A) :
    MvPowerSeries.map f (potential A σ F)=
      potential B σ (fun i => MvPowerSeries.map f (F i)) := by
  simp only [potential,map_sum,←MvPowerSeries.rename_map]

omit [∀ i,DecidableEq (σ i)] in
 theorem map_perturbation (f : A →+* B) (active : Fin m ↪ Fin l)
    (b : ∀ j,MvPowerSeries (σ (active j)) A) (j : Fin m) :
    MvPowerSeries.map f (perturbation A σ m active b j)=
      perturbation B σ m active (fun j => MvPowerSeries.map f (b j)) j := by
  exact (MvPowerSeries.rename_map _ _ _).symm

 theorem map_coefficient_extension (f : A →+* B) {υ : Type*} (F : MvPowerSeries υ A) :
    MvPowerSeries.map (mapParameters (m:=m) f)
        (MvPowerSeries.map (algebraMap A (Parameters A m)) F)=
      MvPowerSeries.map (algebraMap B (Parameters B m)) (MvPowerSeries.map f F) := by
  ext j
  simp only [MvPowerSeries.coeff_map,mapParameters_algebraMap]

omit [∀ i,DecidableEq (σ i)] in
 theorem map_deformed (f : A →+* B) (F : ∀ i,MvPowerSeries (σ i) A)
    (active : Fin m ↪ Fin l) (b : ∀ j,MvPowerSeries (σ (active j)) A) :
    MvPowerSeries.map (mapParameters f) (deformed A σ m F active b)=
      deformed B σ m (fun i => MvPowerSeries.map f (F i)) active
        (fun j => MvPowerSeries.map f (b j)) := by
  simp only [deformed,map_add,map_sum,map_mul,MvPowerSeries.map_C,
    mapParameters_parameter,map_coefficient_extension,map_potential,map_perturbation]

omit [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)] in
 theorem map_tangent (f : A →+* B) {d c : ℕ}
    (e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c)
    (H : ((i : Fin l) × σ i) → MvPowerSeries (Fin d) (Parameters A m))
    (G : ((i : Fin l) × σ i) → MvPowerSeries (Fin c) A) :
    (tangent A σ m e H G).map f = tangent B σ m e
      (fun i => MvPowerSeries.map (mapParameters f) (H i))
      (fun i => MvPowerSeries.map f (G i)) := by
  ext i j
  simp only [Matrix.map_apply,tangent,MvPowerSeries.coeff_map,augmentation_mapParameters]
  cases e j <;> rfl

 

def TensorModel.map {d c : ℕ} {e : ((i : Fin l) × σ i) ≃ Fin d ⊕ Fin c}
    {active : Fin m ↪ Fin l} (M : TensorModel A σ m d c e active) (f : A →+* B) :
    TensorModel B σ m d c e active where
  F := fun i => MvPowerSeries.map f (M.F i)
  b := fun j => MvPowerSeries.map f (M.b j)
  F_zero := fun i => by simp only [MvPowerSeries.constantCoeff_map,M.F_zero,map_zero]
  b_zero := fun j => by simp only [MvPowerSeries.constantCoeff_map,M.b_zero,map_zero]
  H := fun i => MvPowerSeries.map (mapParameters f) (M.H i)
  G := fun i => MvPowerSeries.map f (M.G i)
  H_zero := fun i => mapParameters_mem f (M.H_zero i)
  G_zero := fun i => by simp only [MvPowerSeries.constantCoeff_map,M.G_zero,map_zero]
  tangent_unit := by
    rw [←map_tangent]
    change IsUnit (f.mapMatrix (tangent A σ m e M.H M.G)).det
    rw [←f.map_det]
    exact f.isUnit_map M.tangent_unit
  left_vanishing := by
    have Hsub := hasSubst_parameters A m M.H M.H_zero
    have hh := congrArg (MvPowerSeries.map (mapParameters f)) M.left_vanishing
    simpa only [MvPowerSeries.map_subst Hsub,map_deformed,map_zero] using hh
  right_vanishing := by
    have Gsub := MvPowerSeries.hasSubst_of_constantCoeff_zero M.G_zero
    have hh := congrArg (MvPowerSeries.map f) M.right_vanishing
    simpa only [MvPowerSeries.map_subst Gsub,map_potential,map_zero] using hh
  left_triple := by
    intro i j k hij hik hjk
    have Hsub := hasSubst_parameters A m M.H M.H_zero
    have hh := PD4Tensor.map_formal_gradient (mapParameters f) M.H Hsub
      (deformed A σ m M.F active M.b)
      (MvPowerSeries.C (parameter A m i*parameter A m j*parameter A m k))
      (by simpa only [MvPowerSeries.subst_C] using M.left_triple i j k hij hik hjk)
    rw [MvPowerSeries.map_C,MvPowerSeries.subst_C] at hh
    simpa only [map_mul,mapParameters_parameter,map_deformed] using hh
  right_triple := by
    intro i j k hij hik hjk
    have Gsub := MvPowerSeries.hasSubst_of_constantCoeff_zero M.G_zero
    have hh := PD4Tensor.map_formal_gradient f M.G Gsub (potential A σ M.F) _
      (M.right_triple i j k hij hik hjk)
    simpa only [map_mul,map_potential,map_perturbation] using hh

end
end PD4Tensor.Spreading

namespace PD4Tensor
variable {K υ σ τ : Type*} [Field K] [Fintype υ] [DecidableEq υ]
  [Fintype σ] [Fintype τ]

 

theorem joinedMatrix_complementary (e : υ ≃ σ ⊕ τ) (L : Matrix υ σ K) (R : Matrix υ τ K)
    (hdet : (joinedMatrix e L R).det ≠ 0) :
    Function.Injective (Matrix.mulVecLin L) ∧ Function.Injective (Matrix.mulVecLin R) ∧
      IsCompl (Matrix.mulVecLin L).range (Matrix.mulVecLin R).range := by
  classical
  let join (v : σ → K) (w : τ → K) : υ → K := fun i => Sum.elim v w (e i)
  have hj (v : σ → K) (w : τ → K) :
      (joinedMatrix e L R).mulVec (join v w)=L.mulVec v+R.mulVec w := by
    rw [joinedMatrix_mulVec]
    simp only [join,Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr]
  have hu : IsUnit (joinedMatrix e L R) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hi : Function.Injective (joinedMatrix e L R).mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hs : Function.Surjective (joinedMatrix e L R).mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  have hL : Function.Injective (Matrix.mulVecLin L) := by
    intro v w hvw
    have heq : join v 0=join w 0 := hi (by rw [hj,hj]; exact congrArg (fun x => x+R.mulVec 0) hvw)
    ext j
    simpa only [join,Equiv.apply_symm_apply,Sum.elim_inl] using congr_fun heq (e.symm (Sum.inl j))
  have hR : Function.Injective (Matrix.mulVecLin R) := by
    intro v w hvw
    have heq : join 0 v=join 0 w := hi (by rw [hj,hj]; exact congrArg (fun x => L.mulVec 0+x) hvw)
    ext j
    simpa only [join,Equiv.apply_symm_apply,Sum.elim_inr] using congr_fun heq (e.symm (Sum.inr j))
  refine ⟨hL,hR,⟨?_,?_⟩⟩
  · apply Submodule.disjoint_def.mpr
    intro z hzL hzR
    obtain ⟨v,rfl⟩ := hzL
    obtain ⟨w,hw⟩ := hzR
    change R.mulVec w=L.mulVec v at hw
    have heq : join v 0=join 0 w := hi (by
      rw [hj,hj]
      simpa only [Matrix.mulVec_zero,add_zero,zero_add] using hw.symm)
    have hv : v=0 := by
      ext j
      simpa only [join,Equiv.apply_symm_apply,Sum.elim_inl,Pi.zero_apply] using
        congr_fun heq (e.symm (Sum.inl j))
    simp only [hv,map_zero]
  · apply codisjoint_iff.mpr
    apply top_unique
    intro z _
    obtain ⟨v,rfl⟩ := hs z
    rw [joinedMatrix_mulVec]
    exact Submodule.add_mem_sup ⟨_,rfl⟩ ⟨_,rfl⟩

end PD4Tensor
end

end OAI
