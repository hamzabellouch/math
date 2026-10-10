import Mathlib
import OAI.Algebra.FrobeniusObstruction.TopResidue

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}

                                                              
def oneFormLinear : (Fin n → A) →ₗ[A] Forms (k := k) (A := A) (ι := Fin n) where
  toFun v := ∑ i, v i ⊗ₜ[k] gen (k := k) i
  map_add' v w := by simp [TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (TensorProduct.smul_tmul' c (v i) (gen (k := k) i)).symm

                                                                           
                              
def exteriorBase : ExteriorAlgebra A (Fin n → A) →ₐ[A]
    Forms (k := k) (A := A) (ι := Fin n) :=
  ExteriorAlgebra.lift A ⟨oneFormLinear, fun v => oneform_sq v⟩

@[simp] theorem exteriorBase_ι (v : Fin n → A) :
    exteriorBase (k := k) (ExteriorAlgebra.ι A v) = ∑ i, v i ⊗ₜ[k] gen i := by
  exact ExteriorAlgebra.lift_ι_apply A (oneFormLinear (k := k)) (fun v => oneform_sq v) v

                                                                                   
theorem alternating_det {M : Type*} [AddCommGroup M] [Module A M]
    (f : (Fin n → A) [⋀^Fin n]→ₗ[A] M) (v : Fin n → Fin n → A) :
    f v = Matrix.det v • f (Pi.basisFun A (Fin n)) := by
  let b := Pi.basisFun A (Fin n)
  let g : (Fin n → A) [⋀^Fin n]→ₗ[A] M :=
    (LinearMap.toSpanSingleton A M (f b)).compAlternatingMap Matrix.detRowAlternating
  have hfg : f = g := by
    apply b.ext_alternating
    intro i hi
    let σ := Equiv.ofBijective i (Finite.injective_iff_bijective.mp hi)
    change f (b ∘ σ) = g (b ∘ σ)
    simp only [AlternatingMap.map_perm]
    congr 1
    change f b = Matrix.det (fun i => b i) • f b
    have hb : (fun i => b i) = (1 : Matrix (Fin n) (Fin n) A) := by
      funext i j
      simp [b, Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [hb, Matrix.det_one, one_smul]
  calc
    f v = g v := congrArg (fun u => u v) hfg
    _ = _ := rfl

                                                                                
theorem oneForms_product (v : Fin n → Fin n → A) :
    (List.ofFn fun i => oneFormLinear (k := k) (v i)).prod =
      Matrix.det v • (List.ofFn fun i => (1 : A) ⊗ₜ[k] gen (k := k) i).prod := by
  have h := alternating_det
    ((exteriorBase (k := k) (A := A)).toLinearMap.compAlternatingMap
      (ExteriorAlgebra.ιMulti A n)) v
  simpa only [LinearMap.compAlternatingMap_apply, AlgHom.toLinearMap_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def,
    exteriorBase_ι, oneFormLinear, Pi.basisFun_apply, Pi.single_apply,
    LinearMap.coe_mk, AddHom.coe_mk, TensorProduct.ite_tmul, TensorProduct.zero_tmul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] {n : ℕ}

                                                                             
                          
def volumeCoeff : Ext (k := k) (ι := Fin n) →ₗ[k] k :=
  ExteriorAlgebra.liftAlternating fun m =>
    if h : m = n then h.symm ▸ Matrix.detRowAlternating else 0

@[simp] theorem volumeCoeff_volume :
    volumeCoeff (k := k) ((List.ofFn fun i : Fin n => gen (k := k) i).prod) = 1 := by
  have hm : ExteriorAlgebra.ιMulti k n (Pi.basisFun k (Fin n)) =
      (List.ofFn fun i : Fin n => gen (k := k) i).prod := by
    simp only [ExteriorAlgebra.ιMulti_apply, Pi.basisFun_apply, gen]
  rw [← hm]
  rw [volumeCoeff, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  rw [dite_eq_left rfl]
  change Matrix.det (fun i => Pi.basisFun k (Fin n) i) = 1
  have hb : (fun i => Pi.basisFun k (Fin n) i) = (1 : Matrix (Fin n) (Fin n) k) := by
    ext i j
    simp [Pi.basisFun_apply, Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [hb, Matrix.det_one]

                                                                         
                                                                                 
def residue (ρ : A →ₗ[k] k) : Forms (k := k) (A := A) (ι := Fin n) →ₗ[k] k :=
  (LinearMap.mul' k k).comp (TensorProduct.map ρ volumeCoeff)

@[simp] theorem residue_tmul (ρ : A →ₗ[k] k) (a : A) (e : Ext (k := k) (ι := Fin n)) :
    residue ρ (a ⊗ₜ[k] e) = ρ a * volumeCoeff e := rfl

                                                                        
                                    
theorem residue_d (pd : Fin n → Derivation k A A) (ρ : A →ₗ[k] k)
    (hρ : ∀ i a, ρ (pd i a) = 0) (x : Forms (k := k) (A := A) (ι := Fin n)) :
    residue ρ (d pd x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a e => simp [d_tmul, hρ]

                                                                               
theorem residue_mul_d (pd : Fin n → Derivation k A A) (ρ : A →ₗ[k] k)
    (hρ : ∀ i a, ρ (pd i a) = 0)
    (x y : Forms (k := k) (A := A) (ι := Fin n)) (hx : d pd x = 0) :
    residue ρ (x * d pd y) = 0 := by
  have h := residue_d pd ρ hρ (parity x * y)
  rw [d_mul, d_parity, hx, map_zero, neg_zero, zero_mul,
    parity_sq, zero_add] at h
  exact h

                                                               
theorem mul_delta_of_cycle (pd : Fin n → Derivation k A A) (F : A)
    (x y : Forms (k := k) (A := A) (ι := Fin n)) (hx : delta pd F x = 0) :
    x * delta pd F y = 0 := by
  have hp : gradient pd F * parity x = 0 := by
    have h := congrArg parity hx
    simpa only [delta_apply, map_mul, parity_gradient, neg_mul,
      map_zero, neg_eq_zero] using h
  rw [gradient_supercommute, parity_sq] at hp
  rw [delta_apply, ← mul_assoc, hp, zero_mul]

theorem residue_mul_delta (pd : Fin n → Derivation k A A) (F : A) (ρ : A →ₗ[k] k)
    (x y : Forms (k := k) (A := A) (ι := Fin n)) (hx : delta pd F x = 0) :
    residue ρ (x * delta pd F y) = 0 := by
  rw [mul_delta_of_cycle pd F x y hx, map_zero]

                                                                             
                                                                      
theorem normal_factor (pd : Fin n → Derivation k A A) (e : ℕ) (us : List A) :
    normal pd e us = coeff ((us.map (fun u => u^e)).prod) *
      (us.map (gradient pd)).prod := by
  induction us with
  | nil => simp only [normal_nil, List.map_nil, List.prod_nil, map_one, mul_one]
  | cons u us ih =>
      simp only [normal_cons, ih, cartier, List.map_cons, List.prod_cons, map_mul]
      rw [mul_assoc, ← mul_assoc (gradient pd u), ← coeff_commute,
        mul_assoc, ← mul_assoc]

@[simp] theorem normal_append (pd : Fin n → Derivation k A A) (e : ℕ) (us vs : List A) :
    normal pd e (us ++ vs) = normal pd e us * normal pd e vs := by
  simp [normal, List.map_append, List.prod_append]

                                                                       
theorem normal_ofFn (pd : Fin n → Derivation k A A) (e : ℕ) (u : Fin n → A) :
    normal pd e (List.ofFn u) =
      ((∏ i, u i ^ e) * Matrix.det (fun i j => pd j (u i))) ⊗ₜ[k]
        (List.ofFn fun i => gen (k := k) i).prod := by
  rw [normal_factor]
  simp only [List.map_ofFn, Function.comp_def, List.prod_ofFn]
  have hg : (fun i => gradient pd (u i)) = (fun i => oneFormLinear (fun j => pd j (u i))) := by
    funext i
    exact gradient_eq pd (u i)
  rw [hg]
  have hw := oneForms_product (k := k) (fun i j => pd j (u i))
  rw [hw]
  have hv : (List.ofFn fun i : Fin n => (1 : A) ⊗ₜ[k] gen (k := k) i).prod =
      (1 : A) ⊗ₜ[k] (List.ofFn fun i => gen (k := k) i).prod := by
    have h := map_list_prod (Algebra.TensorProduct.includeRight (R := k) (A := A))
      (List.ofFn fun i : Fin n => gen (k := k) i)
    simpa only [List.map_ofFn, Function.comp_def,
      Algebra.TensorProduct.includeRight_apply] using h.symm
  rw [hv, TensorProduct.smul_tmul', smul_eq_mul, mul_one, coeff_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (hell : 0 < ell)

omit [DecidableEq ι] in
theorem topMonomial_eq_prod : topMonomial (ι := ι) (k := k) ell =
    ∏ i, coordinate ell i ^ (ell - 1) := by
  rw [topMonomial, MvPowerSeries.monomial_one_eq]
  simp only [Finsupp.prod, map_prod, map_pow, coordinate]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hx : topExponent ell i = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hi
  simpa only [topExponent_apply, pow_zero] using congrArg (fun e =>
    Ideal.Quotient.mk (powerIdeal (ι := ι) (k := k) ell) (MvPowerSeries.X i)^e) hx

variable [CharP k ell] (htwo : 1 < ell)

@[simp] theorem augmentation_partial (i : ι) (x : Ring (ι := ι) (k := k) ell) :
    augmentation ell hell (partialDeriv ell i x) = tangentCoeff ell htwo i x := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [partial_mk, tangentCoeff_mk]
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv i f) = _
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.NormalPairing
open Frobenius MixedForms
variable {k : Type*} [Field k] {n : ℕ} (ell : ℕ) (htwo : 1 < ell)
  [CharP k ell]

abbrev Scalar := Frobenius.Ring (ι := Fin n) (k := k) ell
abbrev OriginalForms := Forms (k := k) (A := Scalar (n := n) (k := k) ell) (ι := Fin n)

def res : OriginalForms (n := n) (k := k) ell →ₗ[k] k :=
  residue (quotientCoeff ell (topExponent ell) (topExponent_good (by omega)))

theorem jacobian_augmentation
    (f : Scalar (n := n) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell) :
    augmentation ell (by omega)
      (Matrix.det (fun i j : Fin n => partialDeriv ell j (f (coordinate ell i)))) =
    Matrix.det (fun i j : Fin n => tangentCoeff ell htwo j (f (coordinate ell i))) := by
  change (augmentation (ι := Fin n) (k := k) ell (by omega)).toRingHom
    (Matrix.det _) = _
  refine (RingHom.map_det (augmentation (ι := Fin n) (k := k) ell (by omega)).toRingHom
    (fun i j : Fin n => partialDeriv ell j (f (coordinate ell i)))).trans ?_
  apply congrArg Matrix.det
  ext i j
  exact augmentation_partial ell (by omega) htwo j _

omit [CharP k ell] in
theorem chart_top_product
    (f : Scalar (n := n) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell)
    (c : k) (hq : f (topMonomial ell) = c • topMonomial ell) :
    (∏ i : Fin n, f (coordinate ell i) ^ (ell-1)) = c • topMonomial ell := by
  rw [← hq, topMonomial_eq_prod, map_prod]
  simp only [map_pow]

theorem residue_chart_formula
    (f : Scalar (n := n) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell)
    (c : k) (hq : f (topMonomial ell) = c • topMonomial ell) :
    res ell htwo (normal (partialDeriv ell) (ell-1)
      (List.ofFn fun i : Fin n => f (coordinate ell i))) =
      c * Matrix.det (fun i j : Fin n => tangentCoeff ell htwo j (f (coordinate ell i))) := by
  unfold res
  rw [normal_ofFn, residue_tmul, volumeCoeff_volume, mul_one,
    chart_top_product ell f c hq, smul_mul_assoc,
    topMonomial_mul (ι := Fin n) (k := k) (ell := ell) (by omega)]
  rw [map_smul, map_smul,
    topMonomial_coefficient (ι := Fin n) (k := k) (ell := ell) (by omega)]
  change c * (augmentation (ι := Fin n) (k := k) ell (by omega)
    (Matrix.det (fun i j : Fin n => partialDeriv ell j (f (coordinate ell i)))) * 1) = _
  rw [mul_one, jacobian_augmentation ell htwo f]

                                                                         
                                                                              
                                            
theorem coordinate_residue_ne_zero
    (f : Scalar (n := n) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell)
    (hf : Function.Bijective f)
    (hM : IsUnit (Matrix.det (fun i j => tangentCoeff ell htwo j (f (coordinate ell i))))) :
    res ell htwo (normal (partialDeriv ell) (ell-1)
      (List.ofFn fun i : Fin n => f (coordinate ell i))) ≠ 0 := by
  obtain ⟨c,hc,hq⟩ := automorphism_top ell (by omega) f hf
  rw [residue_chart_formula ell htwo f c hq]
  exact mul_ne_zero hc hM.ne_zero

                                                                         
                                                                             
theorem normals_pair_ne_zero
    (f : Scalar (n := n) (k := k) ell →ₐ[k] Scalar (n := n) (k := k) ell)
    (hf : Function.Bijective f)
    (hM : IsUnit (Matrix.det (fun i j => tangentCoeff ell htwo j (f (coordinate ell i)))))
    (us vs : List (Scalar (n := n) (k := k) ell))
    (huv : us ++ vs = List.ofFn fun i : Fin n => f (coordinate ell i)) :
    res ell htwo (normal (partialDeriv ell) (ell-1) us *
      normal (partialDeriv ell) (ell-1) vs) ≠ 0 := by
  rw [← normal_append, huv]
  exact coordinate_residue_ne_zero ell htwo f hf hM

end BoundaryOnly.FormalObstruction.NormalPairing

end

end OAI
