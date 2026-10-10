import Mathlib
import OAI.Algebra.FiniteTensor.ChartPairings

namespace OAI

/-! Coefficient specialization and base change of form functionals. -/

noncomputable section
open scoped BigOperators

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct BigOperators
open PD4Tensor.Forms PD4Tensor.TruncatedForms
variable (K υ : Type*) [Field K] [Fintype υ] [DecidableEq υ] (p : ℕ)
  [CharP K p]

theorem centralD_eq (ω : Space K υ p) :
    D K υ p ω=differential K (Ring K υ (fun _ => p)) υ (chartDerivative K K υ p) ω := rfl

theorem centralKoszul_eq (S : Ring K υ (fun _ => p)) (ω : Space K υ p) :
    koszul K υ p S ω=
      Mul.mul (α:=Space K υ p) (oneForm K (Ring K υ (fun _ => p)) υ (fun i => chartDerivative K K υ p i S)) ω := by
  change Mul.mul (α:=Ω K (Ring K υ (fun _ => p)) υ)
    (differential K (Ring K υ (fun _ => p)) υ (chartDerivative K K υ p)
      (scalar K (Ring K υ (fun _ => p)) υ S)) ω = _
  rw [differential_scalar]
  rfl

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.TruncatedForms
noncomputable section
open scoped TensorProduct BigOperators
open Forms FrobeniusTruncation FiniteCoordinates
universe u
variable (K : Type*) [Field K] (p : ℕ)
  {n : ℕ} (σ : Fin (n+1) → Type u)

theorem sigmaSelected_zero_of_not_subset (b : ∀ i,A K (σ i) p)
    (active s : Finset (Fin (n+1))) (hb : ∀ i,i∉active → b i=0) (hs : ¬s⊆active) :
    sigmaSelected K p σ b s=0 := by
  classical
  obtain ⟨i,his,hia⟩ := Finset.not_subset.mp hs
  apply Finset.prod_eq_zero his
  simp only [sigmaBlock,hb i hia,map_zero]

variable [CharP K p] [Fact p.Prime] [Invertible (2 : K)]
  [∀ i,Fintype (σ i)] [∀ i,DecidableEq (σ i)]
 

theorem exists_three_graph_tensor_cycle {d c : ℕ}
    (r : ((i : Fin (n+1)) × σ i) ≃ Fin (c+d))
    (e : ((i : Fin (n+1)) × σ i) ≃ Fin d ⊕ Fin c)
    (q0 : Ring K ((i : Fin (n+1)) × σ i) (fun _ => p) ≃ₐ[K]
      Ring K ((i : Fin (n+1)) × σ i) (fun _ => p))
    (S b : ∀ i,A K (σ i) p) (active : Finset (Fin (n+1)))
    (hb : ∀ i,i∉active → b i=0) (hA : 5≤active.card)
    (hL : splitRestriction (Fact.out : p.Prime).pos e q0 (sigmaPotential K p σ S)=0)
    (hR : splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
      (sigmaPotential K p σ S)=0)
    (htrip : ∀ s : Finset (Fin (n+1)), s⊆active → s.card=3 →
      splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
        (sigmaSelected K p σ b s) ∈ Ideal.span (Set.range (fun i =>
          splitRestriction (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0
            (chartDerivative K K _ p i (sigmaPotential K p σ S))))) :
    ∃ (q : Fin 3 ↪ Fin (n+1)) (κ : T K 3 ⊗[K] (⨂[K] i,Space K (σ i) p)),
      (∀ j,q j∈active) ∧
      deformedTensor (fun i => (parity K (A K (σ i) p) (σ i)).toLinearMap)
        (fun i => koszul K (σ i) p (S i)) (fun i => koszul K (σ i) p (b i))
        (threeParameters (K:=K) q) κ=0 ∧
      orientedResidue K _ p (Fact.out : p.Prime).pos r
        (Mul.mul (α:=Space K ((i : Fin (n+1)) × σ i) p) (chartNormal K K _ p e q0)
          (sigmaSeparatedEquiv K p σ (specializeTensor (augmentationAlg K 3) κ)))≠0 := by
  classical
  let α : Space K ((i : Fin (n+1)) × σ i) p := chartNormal K K ((i : Fin (n+1)) × σ i) p (e.trans (Equiv.sumComm _ _)) q0
  let lam : Space K ((i : Fin (n+1)) × σ i) p := chartNormal K K ((i : Fin (n+1)) × σ i) p e q0
  let L : Space K ((i : Fin (n+1)) × σ i) p →ₗ[K] K :=
    (orientedResidue K _ p (Fact.out : p.Prime).pos r).comp (LinearMap.mulLeft K lam)
  have hlam : Mul.mul (α:=Space K ((i : Fin (n+1)) × σ i) p) (oneForm K _ _ (fun i => chartDerivative K K _ p i (sigmaPotential K p σ S))) lam=0 :=
    chartNormal_koszul K K _ p (Fact.out : p.Prime).pos e q0 _ hL
  refine exists_three_tensor_form_cycle K p σ S b active hA α ?_ ?_ ?_ L ?_ ?_ ?_
  · erw [centralKoszul_eq]
    exact chartNormal_koszul K K _ p (Fact.out : p.Prime).pos (e.trans (Equiv.sumComm _ _)) q0 _ hR
  · rw [centralD_eq]
    exact chartNormal_closed K K _ p (e.trans (Equiv.sumComm _ _)) q0
  · intro s hs
    by_cases hsa : s⊆active
    · obtain ⟨β,hβ⟩ := chartNormal_boundary K K _ p (Fact.out : p.Prime).pos
        (e.trans (Equiv.sumComm _ _)) q0 _ hR _ (htrip s hsa hs)
      refine ⟨β,?_⟩
      erw [centralKoszul_eq]
      exact hβ
    · rw [sigmaSelected_zero_of_not_subset K p σ b active s hb hsa]
      change scalar K _ _ 0 * α ∈ _
      rw [scalar_zero,zero_mul]
      exact Submodule.zero_mem _
  · intro v
    change orientedResidue K _ p (Fact.out : p.Prime).pos r
      (lam * koszul K _ p (sigmaPotential K p σ S) v)=0
    erw [centralKoszul_eq,←mul_assoc,(oneForm_mul_zero_iff _ _).mp hlam,zero_mul,map_zero]
  · intro v
    change orientedResidue K _ p (Fact.out : p.Prime).pos r (lam * D K _ p v)=0
    rw [centralD_eq]
    apply orientedResidue_closed_exact
    exact chartNormal_closed K K _ p e q0
  · exact orientedResidue_chartNormal_pair K _ p r e q0

end
end PD4Tensor.TruncatedForms

namespace PD4Tensor.Forms
noncomputable section
open scoped TensorProduct
variable (K A B σ : Type*) [Field K] [CommRing A] [Algebra K A]
  [CommRing B] [Algebra K B]

def mapCoefficients (r : A →ₐ[K] B) : Ω K A σ →ₐ[K] Ω K B σ :=
  Algebra.TensorProduct.map r (AlgHom.id K (E K σ))

@[simp] theorem mapCoefficients_tmul (r : A →ₐ[K] B) (a : A) (e : E K σ) :
    mapCoefficients K A B σ r (a ⊗ₜ[K] e)=r a ⊗ₜ[K] e := rfl

@[simp] theorem mapCoefficients_scalar (r : A →ₐ[K] B) (a : A) :
    mapCoefficients K A B σ r (scalar K A σ a)=scalar K B σ (r a) := rfl

variable [Fintype σ] [DecidableEq σ]

@[simp] theorem mapCoefficients_oneForm (r : A →ₐ[K] B) (v : σ → A) :
    mapCoefficients K A B σ r (oneForm K A σ v)=oneForm K B σ (fun i => r (v i)) := by
  simp [oneForm]

theorem mapCoefficients_differential (r : A →ₐ[K] B)
    (da : σ → A →ₗ[K] A) (db : σ → B →ₗ[K] B)
    (hr : ∀ i a, r (da i a)=db i (r a)) (ω : Ω K A σ) :
    mapCoefficients K A B σ r (differential K A σ da ω)=
      differential K B σ db (mapCoefficients K A B σ r ω) := by
  induction ω using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx,hy]
  | tmul a e => simp [differential_tmul,hr]

theorem mapCoefficients_normalCycle (r : A →ₐ[K] B)
    (da : σ → A →ₗ[K] A) (db : σ → B →ₗ[K] B)
    (hr : ∀ i a, r (da i a)=db i (r a)) (p : ℕ) (cs : List A) :
    mapCoefficients K A B σ r (normalCycle K A σ da p cs)=
      normalCycle K B σ db p (cs.map r) := by
  simp only [normalCycle,map_list_prod,List.map_map,Function.comp_def,normalFactor,
    map_mul,mapCoefficients_scalar,map_pow]
  congr 2
  funext a
  rw [mapCoefficients_differential K A B σ r da db hr,mapCoefficients_scalar]

end
end PD4Tensor.Forms

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K R S σ : Type*) [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S] (e : σ → ℕ)

 
def coefficientHom (r : R →ₐ[K] S) : Ring R σ e →ₐ[K] Ring S σ e :=
  Ideal.Quotient.liftₐ (ideal R σ e)
    ((Ideal.Quotient.mkₐ K (ideal S σ e)).comp (MvPolynomial.mapAlgHom r)) (by
      have hh : ideal R σ e ≤ RingHom.ker
          (((Ideal.Quotient.mkₐ K (ideal S σ e)).comp (MvPolynomial.mapAlgHom r)).toRingHom) := by
        apply Ideal.span_le.mpr
        rintro _ ⟨i,rfl⟩
        change Ideal.Quotient.mk (ideal S σ e) ((MvPolynomial.map r.toRingHom)
          ((MvPolynomial.X i)^e i))=0
        rw [map_pow,MvPolynomial.map_X,map_pow]
        exact coord_pow S σ e i
      exact fun a ha => hh ha)

@[simp] theorem coefficientHom_mk (r : R →ₐ[K] S) (f : MvPolynomial σ R) :
    coefficientHom K R S σ e r (Ideal.Quotient.mk (ideal R σ e) f)=
      Ideal.Quotient.mk (ideal S σ e) ((MvPolynomial.map r.toRingHom) f) := rfl

@[simp] theorem coefficientHom_coord (r : R →ₐ[K] S) (i : σ) :
    coefficientHom K R S σ e r (coord R σ e i)=coord S σ e i := by
  rw [coord,coefficientHom_mk,MvPolynomial.map_X]
  rfl

@[simp] theorem coefficientHom_scalar (r : R →ₐ[K] S) (a : R) :
    coefficientHom K R S σ e r (algebraMap R (Ring R σ e) a)=
      algebraMap S (Ring S σ e) (r a) := by
  change Ideal.Quotient.mk (ideal S σ e) ((MvPolynomial.map r.toRingHom) (MvPolynomial.C a))=_
  rw [MvPolynomial.map_C]
  rfl

variable (p : ℕ) [CharP R p] [CharP S p]

theorem coefficientHom_partial (r : R →ₐ[K] S) (i : σ) (a : Ring R σ (fun _ => p)) :
    coefficientHom K R S σ (fun _ => p) r (relativeDeriv R σ p i a)=
      relativeDeriv S σ p i (coefficientHom K R S σ (fun _ => p) r a) := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective a
  simp only [partial_mk,coefficientHom_mk,MvPolynomial.pderiv_map]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
variable (K ι σ : Type*) [Field K]
  (e : ι → ℕ) (f : σ → ℕ) (he : ∀ i, 0<e i)

 
theorem specialization_eq_coefficientHom :
    coefficientSpecialization K ι σ e f he=
      coefficientHom K (Ring K ι e) K σ f (constantMap K ι e he) := by
  apply Ideal.Quotient.algHom_ext
  apply AlgHom.coe_ringHom_injective
  apply MvPolynomial.ringHom_ext
  · intro a
    change coefficientSpecialization K ι σ e f he
      (algebraMap (Ring K ι e) (Ring (Ring K ι e) σ f) a)=_
    rw [coefficientSpecialization_scalar]
    exact (coefficientHom_scalar K (Ring K ι e) K σ f (constantMap K ι e he) a).symm
  · intro i
    exact (coefficientSpecialization_coord K ι σ e f he i).trans
      (coefficientHom_coord K (Ring K ι e) K σ f (constantMap K ι e he) i).symm

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
open PD4Tensor.Forms
variable (K R σ : Type*) [Field K] [CommRing R] [Algebra K R]
  (e : σ → ℕ)

 

def formsBaseChange : Ω K (Ring R σ e) σ ≃ₐ[R] R ⊗[K] Ω K (Ring K σ e) σ :=
  (Algebra.TensorProduct.congr (baseChangeEquiv K R σ e) (AlgEquiv.refl : E K σ ≃ₐ[K] E K σ)).trans
    (Algebra.TensorProduct.assoc K K R R (Ring K σ e) (E K σ))

@[simp] theorem formsBaseChange_tmul (a : Ring R σ e) (v : E K σ) :
    formsBaseChange K R σ e (a ⊗ₜ[K] v)=
      TensorProduct.assoc K R (Ring K σ e) (E K σ)
        (baseChangeEquiv K R σ e a ⊗ₜ[K] v) := rfl

@[simp] theorem formsBaseChange_symm_tmul (r : R) (a : Ring K σ e) (v : E K σ) :
    (formsBaseChange K R σ e).symm (r ⊗ₜ[K] (a ⊗ₜ[K] v))=
      (r • coefficientMap K R σ e a) ⊗ₜ[K] v := by
  change baseFromTensor K R σ e (r ⊗ₜ[K] a) ⊗ₜ[K] v=_
  rw [baseFromTensor_tmul]

@[simp] theorem formsBaseChange_symm_one_tmul (a : Ring K σ e) (v : E K σ) :
    (formsBaseChange K R σ e).symm ((1 : R) ⊗ₜ[K] (a ⊗ₜ[K] v))=
      coefficientMap K R σ e a ⊗ₜ[K] v := by
  rw [formsBaseChange_symm_tmul,one_smul]

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
open PD4Tensor.Forms
variable (K R σ : Type*) [Field K] [CommRing R] [Algebra K R]
  (p : ℕ)

theorem coefficientMap_eq_coefficientHom :
    coefficientMap K R σ (fun _ => p)=
      coefficientHom K K R σ (fun _ => p) (Algebra.ofId K R) := by
  apply hom_ext
  intro i
  rw [coefficientMap_coord,coefficientHom_coord]

variable [CharP K p] [CharP R p]

@[simp] theorem partial_coefficientMap (i : σ) (a : Ring K σ (fun _ => p)) :
    relativeDeriv R σ p i (coefficientMap K R σ (fun _ => p) a)=
      coefficientMap K R σ (fun _ => p) (FrobeniusTruncation.derivative K σ p i a) := by
  rw [coefficientMap_eq_coefficientHom]
  exact (coefficientHom_partial K K R σ p (Algebra.ofId K R) i a).symm

variable [Fintype σ] [DecidableEq σ]
 

theorem relative_differential_baseChange
    (v : R ⊗[K] Ω K (Ring K σ (fun _ => p)) σ) :
    differential K (Ring R σ (fun _ => p)) σ (chartDerivative K R σ p)
      ((formsBaseChange K R σ (fun _ => p)).symm v)=
      (formsBaseChange K R σ (fun _ => p)).symm
        ((differential K (Ring K σ (fun _ => p)) σ
          (chartDerivative K K σ p)).baseChange R v) := by
  induction v using TensorProduct.inductionOn with
  | add v w hv hw => simp only [map_add,hv,hw]
  | tmul r ω =>
    induction ω using TensorProduct.inductionOn with
    | add ω η hω hη => simp only [TensorProduct.tmul_add,map_add,hω,hη]
    | tmul a e =>
      rw [formsBaseChange_symm_tmul,differential_tmul,LinearMap.baseChange_tmul,
        differential_tmul,TensorProduct.tmul_sum,map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [formsBaseChange_symm_tmul]
      change relativeDeriv R σ p i (r • coefficientMap K R σ (fun _ => p) a) ⊗ₜ[K] _=_
      rw [map_smul,partial_coefficientMap]
      rfl

end
end PD4Tensor.FiniteCoordinates

namespace PD4Tensor.FiniteCoordinates
noncomputable section
open scoped TensorProduct
open PD4Tensor.Forms
variable (K R σ : Type*) [Field K] [CommRing R] [Algebra K R]
  (e : σ → ℕ)

@[simp] theorem formsBaseChange_symm_tmul_form (r : R) (ω : Ω K (Ring K σ e) σ) :
    (formsBaseChange K R σ e).symm (r ⊗ₜ[K] ω)=
      r • mapCoefficients K (Ring K σ e) (Ring R σ e) σ (coefficientMap K R σ e) ω := by
  induction ω using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.tmul_add,map_add,smul_add,hu,hv]
  | tmul a v => rw [formsBaseChange_symm_tmul,mapCoefficients_tmul,TensorProduct.smul_tmul']

 
def extendFormFunctional (L : Ω K (Ring K σ e) σ →ₗ[K] K) :
    Ω K (Ring R σ e) σ →ₗ[R] R :=
  (TensorProduct.AlgebraTensorModule.rid K R R).toLinearMap.comp
    ((L.baseChange R).comp (formsBaseChange K R σ e).toLinearMap)

@[simp] theorem extendFormFunctional_tmul (L : Ω K (Ring K σ e) σ →ₗ[K] K)
    (r : R) (ω : Ω K (Ring K σ e) σ) :
    extendFormFunctional K R σ e L ((formsBaseChange K R σ e).symm (r ⊗ₜ[K] ω))=
      L ω • r := by
  simp only [extendFormFunctional,LinearMap.comp_apply,AlgEquiv.toLinearMap_apply,
    AlgEquiv.apply_symm_apply,LinearMap.baseChange_tmul,LinearEquiv.coe_coe,
    TensorProduct.AlgebraTensorModule.rid_tmul]

theorem coefficientHom_coefficientMap (ε : R →ₐ[K] K) (a : Ring K σ e) :
    coefficientHom K R K σ e ε (coefficientMap K R σ e a)=a := by
  have hh : (coefficientHom K R K σ e ε).comp (coefficientMap K R σ e)=
      AlgHom.id K (Ring K σ e) := by
    apply hom_ext
    intro i
    simp only [AlgHom.comp_apply,coefficientMap_coord,coefficientHom_coord,AlgHom.id_apply]
  exact AlgHom.congr_fun hh a

 
theorem forms_specialization_tmul (ε : R →ₐ[K] K) (r : R)
    (ω : Ω K (Ring K σ e) σ) :
    mapCoefficients K (Ring R σ e) (Ring K σ e) σ (coefficientHom K R K σ e ε)
      ((formsBaseChange K R σ e).symm (r ⊗ₜ[K] ω))=ε r • ω := by
  induction ω using TensorProduct.inductionOn with
  | add u v hu hv => simp only [TensorProduct.tmul_add,map_add,smul_add,hu,hv]
  | tmul a v =>
    rw [formsBaseChange_symm_tmul,mapCoefficients_tmul]
    have hs : r • coefficientMap K R σ e a =
        algebraMap R (Ring R σ e) r * coefficientMap K R σ e a := by
      convert Algebra.smul_def (A:=Ring R σ e) r (coefficientMap K R σ e a) using 1
    rw [hs,map_mul,coefficientHom_scalar,coefficientHom_coefficientMap]
    rw [←Algebra.smul_def,TensorProduct.smul_tmul']

 

theorem extendFormFunctional_specialization (L : Ω K (Ring K σ e) σ →ₗ[K] K)
    (ε : R →ₐ[K] K) (ω : Ω K (Ring R σ e) σ) :
    ε (extendFormFunctional K R σ e L ω)=
      L (mapCoefficients K (Ring R σ e) (Ring K σ e) σ
        (coefficientHom K R K σ e ε) ω) := by
  obtain ⟨v,rfl⟩ := (formsBaseChange K R σ e).symm.surjective ω
  induction v using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add,hu,hv]
  | tmul r ω =>
    rw [extendFormFunctional_tmul,forms_specialization_tmul,map_smul,map_smul]
    change L ω * ε r=ε r * L ω
    exact mul_comm _ _

end
end PD4Tensor.FiniteCoordinates
end

end OAI
