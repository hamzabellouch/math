import Mathlib
import OAI.Algebra.FiniteTensor.FormBaseChange

namespace OAI

/-! Relative Koszul operators and specialization of deformed separated forms. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct BigOperators
open PD4Tensor.Forms PD4Tensor.TruncatedForms
variable (K R σ : Type*) [Field K] [CommRing R] [Algebra K R]
  [Fintype σ] [DecidableEq σ] (p : ℕ) [CharP K p]

 
def relativeD : Ω K (Ring R σ (fun _ => p)) σ →ₗ[R] Ω K (Ring R σ (fun _ => p)) σ :=
  ((formsBaseChange K R σ (fun _ => p)).symm.toLinearMap).comp
    (((D K σ p).baseChange R).comp (formsBaseChange K R σ (fun _ => p)).toLinearMap)

theorem relativeD_eq [CharP R p] (ω : Ω K (Ring R σ (fun _ => p)) σ) :
    relativeD K R σ p ω=
      differential K (Ring R σ (fun _ => p)) σ (chartDerivative K R σ p) ω := by
  have h := relative_differential_baseChange K R σ p
    (formsBaseChange K R σ (fun _ => p) ω)
  rw [AlgEquiv.symm_apply_apply] at h
  exact h.symm

def relativeKoszul (S : Ring R σ (fun _ => p)) :
    Ω K (Ring R σ (fun _ => p)) σ →ₗ[R] Ω K (Ring R σ (fun _ => p)) σ :=
  LinearMap.mulLeft R (relativeD K R σ p (scalar K (Ring R σ (fun _ => p)) σ S))

theorem relativeKoszul_eq [CharP R p] (S : Ring R σ (fun _ => p))
    (ω : Ω K (Ring R σ (fun _ => p)) σ) :
    relativeKoszul K R σ p S ω=
      oneForm K (Ring R σ (fun _ => p)) σ (fun i => chartDerivative K R σ p i S) * ω := by
  rw [relativeKoszul,LinearMap.mulLeft_apply,relativeD_eq,differential_scalar]

omit [Fintype σ] [DecidableEq σ] [CharP K p] in
theorem scalar_parameter_smul (r : R) (a : Ring R σ (fun _ => p)) :
    scalar K (Ring R σ (fun _ => p)) σ (r • a)=
      r • scalar K (Ring R σ (fun _ => p)) σ a := by
  exact (TensorProduct.smul_tmul' r a (1 : E K σ)).symm

@[simp] theorem relativeKoszul_add (S b : Ring R σ (fun _ => p)) :
    relativeKoszul K R σ p (S+b)=relativeKoszul K R σ p S + relativeKoszul K R σ p b := by
  apply LinearMap.ext
  intro ω
  change relativeD K R σ p _ * ω = _
  simp only [relativeKoszul,scalar_add,map_add,LinearMap.add_apply,LinearMap.mulLeft_apply,add_mul]

@[simp] theorem relativeKoszul_zero : relativeKoszul K R σ p 0=0 := by
  apply LinearMap.ext
  intro ω
  change relativeD K R σ p _ * ω = _
  simp only [scalar_zero,map_zero,zero_mul,LinearMap.zero_apply]

@[simp] theorem relativeKoszul_smul (r : R) (S : Ring R σ (fun _ => p)) :
    relativeKoszul K R σ p (r • S)=r • relativeKoszul K R σ p S := by
  apply LinearMap.ext
  intro ω
  change relativeD K R σ p _ * ω = _
  simp only [relativeKoszul,scalar_parameter_smul,map_smul,LinearMap.smul_apply,
    LinearMap.mulLeft_apply,smul_mul_assoc]

theorem relativeKoszul_sum {ι : Type*} (s : Finset ι) (S : ι → Ring R σ (fun _ => p)) :
    relativeKoszul K R σ p (∑ i∈s, S i)=∑ i∈s, relativeKoszul K R σ p (S i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha,relativeKoszul_add,ih]

 

theorem relativeKoszul_coefficientMap (S : Ring K σ (fun _ => p))
    (v : R ⊗[K] Ω K (Ring K σ (fun _ => p)) σ) :
    relativeKoszul K R σ p (coefficientMap K R σ (fun _ => p) S)
      ((formsBaseChange K R σ (fun _ => p)).symm v)=
      (formsBaseChange K R σ (fun _ => p)).symm ((koszul K σ p S).baseChange R v) := by
  have hscalar : scalar K (Ring R σ (fun _ => p)) σ (coefficientMap K R σ (fun _ => p) S)=
      (formsBaseChange K R σ (fun _ => p)).symm
        ((1 : R) ⊗ₜ[K] scalar K (Ring K σ (fun _ => p)) σ S) := by
    exact (formsBaseChange_symm_one_tmul K R σ (fun _ => p) S 1).symm
  have hD : relativeD K R σ p
      (scalar K (Ring R σ (fun _ => p)) σ (coefficientMap K R σ (fun _ => p) S))=
      (formsBaseChange K R σ (fun _ => p)).symm
        ((1 : R) ⊗ₜ[K] D K σ p (scalar K (Ring K σ (fun _ => p)) σ S)) := by
    rw [hscalar]
    change (formsBaseChange K R σ (fun _ => p)).symm
      ((D K σ p).baseChange R
        (formsBaseChange K R σ (fun _ => p)
          ((formsBaseChange K R σ (fun _ => p)).symm
            ((1 : R) ⊗ₜ[K] scalar K (Ring K σ (fun _ => p)) σ S))))=_
    rw [AlgEquiv.apply_symm_apply]
    exact congrArg (formsBaseChange K R σ (fun _ => p)).symm
      (LinearMap.baseChange_tmul (D K σ p) (1 : R) (scalar K (A K σ p) σ S))
  change relativeD K R σ p _ * (formsBaseChange K R σ (fun _ => p)).symm v=_
  rw [hD,←map_mul]
  apply congrArg (formsBaseChange K R σ (fun _ => p)).symm
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => rw [mul_add,hv,hw]; exact (map_add _ v w).symm
  | tmul r ω =>
    erw [Algebra.TensorProduct.tmul_mul_tmul,one_mul,LinearMap.baseChange_tmul]
    rfl

 

theorem relativeKoszul_deformation {ι : Type*} [Fintype ι]
    (S : Ring K σ (fun _ => p)) (b : ι → Ring K σ (fun _ => p)) (t : ι → R)
    (v : R ⊗[K] Ω K (Ring K σ (fun _ => p)) σ) :
    relativeKoszul K R σ p
      (coefficientMap K R σ (fun _ => p) S +
        ∑ i, t i • coefficientMap K R σ (fun _ => p) (b i))
      ((formsBaseChange K R σ (fun _ => p)).symm v)=
      (formsBaseChange K R σ (fun _ => p)).symm
        (((koszul K σ p S).baseChange R + ∑ i, t i • (koszul K σ p (b i)).baseChange R) v) := by
  rw [relativeKoszul_add,relativeKoszul_sum]
  simp only [LinearMap.add_apply,LinearMap.sum_apply,relativeKoszul_smul,
    LinearMap.smul_apply,relativeKoszul_coefficientMap]
  erw [LinearMap.add_apply,LinearMap.sum_apply]
  erw [map_add,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  erw [LinearMap.smul_apply,map_smul]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation FiniteCoordinates
universe u
variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]
  (p : ℕ) [CharP K p]
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

 
def sigmaExtendedForms :
    R ⊗[K] (⨂[K] i,Space K (σ i) p) →ₗ[R]
      Ω K (Ring R ((i : Fin (n+1)) × σ i) (fun _ => p)) ((i : Fin (n+1)) × σ i) :=
  ((formsBaseChange K R ((i : Fin (n+1)) × σ i) (fun _ => p)).symm.toLinearMap).comp
    ((sigmaSeparatedEquiv K p σ).toLinearMap.baseChange R)

 

theorem relativeKoszul_sigmaExtended (S b : ∀ i,A K (σ i) p) (t : Fin (n+1) → R)
    (κ : R ⊗[K] (⨂[K] i,Space K (σ i) p)) :
    relativeKoszul K R ((i : Fin (n+1)) × σ i) p
      (coefficientMap K R _ (fun _ => p) (sigmaPotential K p σ S) +
        ∑ i,t i • coefficientMap K R _ (fun _ => p) (sigmaBlock K p σ i (b i)))
      (sigmaExtendedForms K R p σ κ)=
      sigmaExtendedForms K R p σ
        (deformedTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
          (fun i => koszul K (σ i) p (S i)) (fun i => koszul K (σ i) p (b i)) t κ) := by
  change relativeKoszul K R ((i : Fin (n+1)) × σ i) p _
      ((formsBaseChange K R ((i : Fin (n+1)) × σ i) (fun _ => p)).symm
        ((sigmaSeparatedEquiv K p σ).toLinearMap.baseChange R κ))=
    (formsBaseChange K R ((i : Fin (n+1)) × σ i) (fun _ => p)).symm
      ((sigmaSeparatedEquiv K p σ).toLinearMap.baseChange R _)
  erw [relativeKoszul_deformation]
  apply congrArg (formsBaseChange K R ((i : Fin (n+1)) × σ i) (fun _ => p)).symm
  induction κ using TensorProduct.inductionOn with
  | add v w hv hw =>
    simp only [map_add,hv,hw]; rfl
  | tmul r v =>
    simp only [LinearMap.baseChange_tmul,LinearMap.add_apply,LinearMap.sum_apply,
      LinearMap.smul_apply,LinearEquiv.coe_coe,
      deformedTensor,TensorProduct.map_tmul,LinearMap.id_apply,
      LinearMap.mulLeft_apply,map_add,map_sum]
    congr 1
    · exact congrArg (fun w => r ⊗ₜ[K] w) (koszul_sigmaSeparated K p σ S v)
    · apply Finset.sum_congr rfl
      intro i _
      erw [koszul_sigmaBlock]
      exact TensorProduct.smul_tmul' (t i) r _

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct
open Forms FrobeniusTruncation FiniteCoordinates
universe u
variable (K R : Type*) [Field K] [CommRing R] [Algebra K R]
  (p : ℕ)
  {n : ℕ} (σ : Fin (n+1) → Type u) [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]

theorem sigmaExtendedForms_specialization (ε : R →ₐ[K] K)
    (κ : R ⊗[K] (⨂[K] i,Space K (σ i) p)) :
    mapCoefficients K (Ring R ((i : Fin (n+1)) × σ i) (fun _ => p))
      (Ring K ((i : Fin (n+1)) × σ i) (fun _ => p)) ((i : Fin (n+1)) × σ i)
      (coefficientHom K R K _ (fun _ => p) ε) (sigmaExtendedForms K R p σ κ)=
    sigmaSeparatedEquiv K p σ (specializeTensor ε κ) := by
  induction κ using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add,hv,hw]; rfl
  | tmul r v =>
    change mapCoefficients K _ _ _ _
      ((formsBaseChange K R ((i : Fin (n+1)) × σ i) (fun _ => p)).symm
        ((sigmaSeparatedEquiv K p σ).toLinearMap.baseChange R (r ⊗ₜ[K] v)))=_
    erw [LinearMap.baseChange_tmul,forms_specialization_tmul,specializeTensor_tmul]
    exact ((sigmaSeparatedEquiv K p σ).map_smul (ε r) v).symm

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor
namespace FrobeniusTruncation
noncomputable section

variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ] (p : ℕ)

 
 
 
 
variable [CharP K p]

 
 

 
 
variable [Fact p.Prime]

 
 
 
 
 
 
 

 
 
 

 
 

 
 
 

 
 

 
end
end FrobeniusTruncation
end PD4Tensor

 

namespace PD4Tensor.FrobeniusTruncation
noncomputable section
variable (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
  (p : ℕ) [CharP K p] [Fact p.Prime]

 

 
 

 

end
end PD4Tensor.FrobeniusTruncation

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (K R S υ : Type*) [Field K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] [Fintype υ] [DecidableEq υ]
  (p : ℕ) [CharP R p] [CharP S p]
  {σ : Type*} {c : ℕ}

 

theorem chartNormal_specialization
    (r : R →ₐ[K] S) (e : υ ≃ σ ⊕ Fin c)
    (qR : Ring R υ (fun _ => p) ≃ₐ[R] Ring R υ (fun _ => p))
    (qS : Ring S υ (fun _ => p) ≃ₐ[S] Ring S υ (fun _ => p))
    (hq : ∀ a, coefficientHom K R S υ (fun _ => p) r (qR a)=
      qS (coefficientHom K R S υ (fun _ => p) r a)) :
    mapCoefficients K (Ring R υ (fun _ => p)) (Ring S υ (fun _ => p)) υ
      (coefficientHom K R S υ (fun _ => p) r) (chartNormal K R υ p e qR)=
      chartNormal K S υ p e qS := by
  rw [chartNormal,mapCoefficients_normalCycle K _ _ υ _
    (chartDerivative K R υ p) (chartDerivative K S υ p)
    (coefficientHom_partial K R S υ p r)]
  change normalCycle K (Ring S υ (fun _ => p)) υ (chartDerivative K S υ p) p _=_
  congr 1
  simp only [normalCoordinates,List.map_ofFn,Function.comp_def]
  congr 1
  funext j
  apply qS.injective
  rw [←hq,qR.apply_symm_apply,coefficientHom_coord,qS.apply_symm_apply]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor
noncomputable section
variable (K : Type*) [Field K] (m p : ℕ) [CharP K p]

 
theorem parameterCharP : CharP (T K m) p := by
  apply charP_of_injective_ringHom (f:=algebraMap K (T K m))
  apply Function.LeftInverse.injective (g:=augmentationAlg K m)
  intro b
  exact (augmentationAlg K m).commutes b

end
end PD4Tensor

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open PD4Tensor.Forms
variable (K R σ : Type*) [Field K] [CommRing R] [Algebra K R]
  (e : σ → ℕ)

theorem scalar_parameter_mul (r : R) (ω : Ω K (Ring R σ e) σ) :
    scalar K (Ring R σ e) σ (algebraMap R (Ring R σ e) r)*ω=r • ω := by
  induction ω using TensorProduct.inductionOn with
  | add u v hu hv => simp only [mul_add,smul_add,hu,hv]
  | tmul a v =>
    rw [scalar,Algebra.TensorProduct.tmul_mul_tmul,one_mul]
    rw [TensorProduct.smul_tmul']
    congr 1
    convert (Algebra.smul_def r a).symm using 1

end
end PD4Tensor.FiniteCoordinates
end

end OAI
