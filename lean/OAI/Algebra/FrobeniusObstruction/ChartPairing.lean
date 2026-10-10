import Mathlib
import OAI.Algebra.FrobeniusObstruction.ResiduePairing
import OAI.Algebra.FrobeniusObstruction.NormalPrimitives

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FormsReindex
open Frobenius MixedForms
variable {ι κ k : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [CommRing k] (ell : ℕ) [CharP k ell]

@[simp] theorem equiv_cartier (e : ι ≃ κ) (a : Ring (ι := ι) (k := k) ell) (m : ℕ) :
    equiv ell e (cartier (partialDeriv ell) m a) =
      cartier (partialDeriv ell) m (Frobenius.reindex ell e a) := by
  simp only [cartier, map_mul, equiv_coeff, map_pow, equiv_gradient]

@[simp] theorem equiv_normal (e : ι ≃ κ) (us : List (Ring (ι := ι) (k := k) ell)) (m : ℕ) :
    equiv ell e (normal (partialDeriv ell) m us) =
      normal (partialDeriv ell) m (us.map (Frobenius.reindex ell e)) := by
  simp only [normal, map_list_prod, List.map_map, Function.comp_def, equiv_cartier]

end BoundaryOnly.FormalObstruction.FormsReindex

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

                                                                            
def swapEquiv : InternalVar n ≃ InternalVar n where
  toFun := swapBlocks n
  invFun := swapBlocks n
  left_inv c := by simp [swapBlocks]
  right_inv c := by simp [swapBlocks]

@[simp] theorem swapEquiv_apply (c : InternalVar n) :
    swapEquiv (n := n) c = (!c.1,c.2) := rfl

@[simp] theorem swapEquiv_symm : (swapEquiv (n := n)).symm = swapEquiv := rfl

@[simp] theorem complementaryMatrix_swap (Y : InternalVar n → MvPowerSeries (GraphVar n) k) :
    (complementaryMatrix n Y).submatrix swapEquiv swapEquiv = complementaryMatrix n Y := by
  ext i j
  obtain ⟨b,t⟩ := j
  cases b <;> simp [Matrix.submatrix_apply, complementaryMatrix, swapEquiv, swapBlocks]

                                                                                
theorem inverseChart_tangent (D : FormalData (k := k) n) :
    tangentJacobian ell htwo (specialChartEquiv ell htwo D).symm.toAlgHom =
      (complementaryMatrix n D.Y)⁻¹ := by
  have he : (specialChartEquiv ell htwo D).symm.toAlgHom.comp
      (specialChartEquiv ell htwo D).toAlgHom = AlgHom.id k _ := by
    ext x
    exact (specialChartEquiv ell htwo D).symm_apply_apply x
  have h := tangentJacobian_comp ell htwo (specialChartEquiv ell htwo D).symm.toAlgHom
    (specialChartEquiv ell htwo D).toAlgHom
  rw [he, tangentJacobian_id] at h
  have hM : tangentJacobian ell htwo (specialChartEquiv ell htwo D).toAlgHom =
      complementaryMatrix n D.Y := specialChart_tangent_matrix ell htwo D
  rw [hM] at h
  exact (Matrix.inv_eq_right_inv h.symm).symm

theorem inverseChart_tangent_swap (D : FormalData (k := k) n) (i j : InternalVar n) :
    tangentCoeff ell htwo (swapEquiv j)
      ((specialChartEquiv ell htwo D).symm (coordinate ell (swapEquiv i))) =
    tangentCoeff ell htwo j ((specialChartEquiv ell htwo D).symm (coordinate ell i)) := by
  have hs := congrArg (fun M : Matrix (InternalVar n) (InternalVar n) k => M⁻¹)
    (complementaryMatrix_swap D.Y)
  rw [Matrix.inv_submatrix_equiv] at hs
  have h := congrArg (fun M : Matrix (InternalVar n) (InternalVar n) k => M i j) hs
  rw [← inverseChart_tangent ell htwo D] at h
  exact h

omit [Fact ell.Prime] in
theorem tangentCoeff_swap (j : InternalVar n)
    (x : Frobenius.Ring (ι := InternalVar n) (k := k) ell) :
    tangentCoeff ell htwo j (Frobenius.reindex ell swapEquiv x) =
      tangentCoeff ell htwo (swapEquiv j) x := by
  calc
    _ = augmentation ell (by omega) (partialDeriv ell j (Frobenius.reindex ell swapEquiv x)) :=
      tangentCoeff_eq_augmentation_partial ell htwo j _
    _ = augmentation ell (by omega) (Frobenius.reindex ell swapEquiv
        (partialDeriv ell (swapEquiv j) x)) := by
      congr 1
      simpa only [swapEquiv_apply, Bool.not_not, Prod.eta] using
        partial_reindex ell (swapEquiv (n := n)) (swapEquiv j) x
    _ = augmentation ell (by omega) (partialDeriv ell (swapEquiv j) x) :=
      AlgHom.congr_fun (augmentation_natural ell htwo
        (Frobenius.reindex (k := k) ell (swapEquiv (n := n))).toAlgHom) _
    _ = _ := (tangentCoeff_eq_augmentation_partial ell htwo _ x).symm

def jointNormalCoordinate (D : FormalData (k := k) n) (c : InternalVar n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  if c.1 then (specialChartEquiv ell htwo D).symm (coordinate ell c)
  else Frobenius.reindex ell swapEquiv
    ((specialChartEquiv ell htwo D).symm (coordinate ell (swapEquiv c)))

theorem jointNormalCoordinate_pow (D : FormalData (k := k) n) (c : InternalVar n) :
    jointNormalCoordinate ell htwo D c ^ ell = 0 := by
  unfold jointNormalCoordinate
  split <;> simp only [← map_pow, coordinate_pow, map_zero]

def jointNormalChart (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := InternalVar n) (k := k) ell →ₐ[k]
      Frobenius.Ring (ι := InternalVar n) (k := k) ell :=
  eval ell (jointNormalCoordinate ell htwo D) (jointNormalCoordinate_pow ell htwo D)

@[simp] theorem jointNormalChart_coordinate (D : FormalData (k := k) n) (c : InternalVar n) :
    jointNormalChart ell htwo D (coordinate ell c) = jointNormalCoordinate ell htwo D c :=
  eval_coordinate ell _ _ _

 theorem jointNormalChart_tangent (D : FormalData (k := k) n) :
    tangentJacobian ell htwo (jointNormalChart ell htwo D) =
      tangentJacobian ell htwo (specialChartEquiv ell htwo D).symm.toAlgHom := by
  ext i j
  change tangentCoeff ell htwo j (jointNormalChart ell htwo D (coordinate ell i)) = _
  rw [jointNormalChart_coordinate, jointNormalCoordinate]
  split
  · rfl
  · rw [tangentCoeff_swap]
    exact inverseChart_tangent_swap ell htwo D i j

 theorem jointNormalChart_bijective (D : FormalData (k := k) n) :
    Function.Bijective (jointNormalChart ell htwo D) := by
  apply bijective_of_tangent_matrix ell htwo
  change IsUnit (tangentJacobian ell htwo (jointNormalChart ell htwo D)).det
  rw [jointNormalChart_tangent]
  exact tangentJacobian_det_unit ell htwo (specialChartEquiv ell htwo D).symm

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction.Frobenius
variable {ι κ k : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Field k] (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

theorem reindex_mk (e : ι ≃ κ) (p : MvPowerSeries ι k) :
    reindex ell e (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPowerSeries.rename e p) := by
  let a : ι → MvPowerSeries κ k := fun i => MvPowerSeries.X (e i)
  have ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0 := by intro i; simp [a]
  have hh : (reindex (k := k) ell e).toAlgHom = substitute ell a ha := by
    apply algHom_ext
    intro i
    rw [AlgEquiv.coe_toAlgHom, reindex_coordinate,
      substitute_coordinate]
    rfl
  change (reindex ell e).toAlgHom (Ideal.Quotient.mk _ p) = _
  rw [hh, substitute_mk, MvPowerSeries.rename_eq_subst]
  rfl

omit [DecidableEq ι] [DecidableEq κ] [Fact ell.Prime] in
theorem embDomain_top (e : ι ≃ κ) :
    Finsupp.embDomain e.toEmbedding (topExponent (ι := ι) ell) = topExponent (ι := κ) ell := by
  ext i
  obtain ⟨j,rfl⟩ := e.surjective i
  exact (Finsupp.embDomain_apply_self e.toEmbedding (topExponent ell) j).trans
    (topExponent_apply ell j)

 theorem topCoeff_reindex (e : ι ≃ κ) (x : Ring (ι := ι) (k := k) ell) :
    quotientCoeff ell (topExponent ell) (topExponent_good (by omega)) (reindex ell e x) =
      quotientCoeff ell (topExponent ell) (topExponent_good (by omega)) x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [reindex_mk ell e p, quotientCoeff_mk, quotientCoeff_mk, ← embDomain_top ell e]
  exact MvPowerSeries.coeff_embDomain_rename e.toEmbedding p (topExponent ell)

end BoundaryOnly.FormalObstruction.Frobenius

namespace BoundaryOnly.FormalObstruction.MixedForms
variable {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [Fintype ι] [DecidableEq ι]

                                                                                        
def fixedResidue (ρ : A →ₗ[k] k) (v : Ext (k := k) (ι := ι) →ₗ[k] k) :
    Forms (k := k) (A := A) (ι := ι) →ₗ[k] k :=
  (LinearMap.mul' k k).comp (TensorProduct.map ρ v)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem fixedResidue_tmul (ρ : A →ₗ[k] k) (v : Ext (k := k) (ι := ι) →ₗ[k] k)
    (a : A) (x : Ext (k := k) (ι := ι)) :
    fixedResidue ρ v (a ⊗ₜ[k] x) = ρ a * v x := rfl

 theorem fixedResidue_d (pd : ι → Derivation k A A) (ρ : A →ₗ[k] k)
    (v : Ext (k := k) (ι := ι) →ₗ[k] k) (hρ : ∀ i a, ρ (pd i a) = 0)
    (x : Forms (k := k) (A := A) (ι := ι)) : fixedResidue ρ v (d pd x) = 0 := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]
  | tmul a x => simp only [d_tmul, map_sum, fixedResidue_tmul, hρ, zero_mul, Finset.sum_const_zero]

 theorem fixedResidue_mul_d (pd : ι → Derivation k A A) (ρ : A →ₗ[k] k)
    (v : Ext (k := k) (ι := ι) →ₗ[k] k) (hρ : ∀ i a, ρ (pd i a) = 0)
    (x y : Forms (k := k) (A := A) (ι := ι)) (hx : d pd x = 0) :
    fixedResidue ρ v (x * d pd y) = 0 := by
  have h := fixedResidue_d pd ρ v hρ (parity x * y)
  rw [d_mul, d_parity, hx, map_zero, neg_zero, zero_mul, parity_sq, zero_add] at h
  exact h

end BoundaryOnly.FormalObstruction.MixedForms

namespace BoundaryOnly.FormalObstruction.FormsReindex
open Frobenius MixedForms
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
  (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime] {N : ℕ}

 theorem residue_equiv (e : ι ≃ Fin N) (x : QForms (k := k) ell ι) :
    NormalPairing.res ell htwo (equiv ell e x) =
      fixedResidue (quotientCoeff ell (topExponent ell) (topExponent_good (by omega)))
        ((volumeCoeff (k := k)).comp (exterior e).toLinearMap) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
      simp only [equiv_tmul, NormalPairing.res, residue_tmul, fixedResidue_tmul,
        topCoeff_reindex ell htwo, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply]

end BoundaryOnly.FormalObstruction.FormsReindex

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {d : ℕ} {n : Fin d → ℕ}

def fullNormalIndexList : List (InternalVar n) :=
  (normalIndices (n := n)).toList ++ (normalIndices (n := n)).toList.map swapEquiv

 theorem fullNormalIndexList_nodup : (fullNormalIndexList (n := n)).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨Finset.nodup_toList _, (Finset.nodup_toList _).map swapEquiv.injective, ?_⟩
  intro c hc c' hc' hcc
  subst c'
  have hct : c.1 = true := mem_normalIndices c |>.mp (Finset.mem_toList.mp hc)
  obtain ⟨j,hj,hjc⟩ := List.mem_map.mp hc'
  have hjt : j.1 = true := mem_normalIndices j |>.mp (Finset.mem_toList.mp hj)
  have hb := congrArg Prod.fst hjc
  simp only [swapEquiv_apply, hjt, Bool.not_true, hct] at hb
  cases hb

 theorem mem_fullNormalIndexList (c : InternalVar n) : c ∈ fullNormalIndexList (n := n) := by
  obtain ⟨b,t⟩ := c
  cases b
  · apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(true,t), by simp [normalIndices], rfl⟩
  · apply List.mem_append_left
    simp [normalIndices]

                                                                                    
def normalEnumeration : Fin (fullNormalIndexList (n := n)).length ≃ InternalVar n :=
  Equiv.ofBijective (fullNormalIndexList (n := n)).get
    ⟨fullNormalIndexList_nodup.injective_get,
      fun x => List.mem_iff_get.mp (mem_fullNormalIndexList x)⟩

 theorem normalEnumeration_list :
    List.ofFn (normalEnumeration (n := n)) = fullNormalIndexList (n := n) :=
  List.ofFn_get _

end BoundaryOnly.FormalObstruction

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms
variable {k : Type*} [Field k] {d : ℕ} {n : Fin d → ℕ}
variable (ell : ℕ) (htwo : 1 < ell) [CharP k ell] [Fact ell.Prime]

                                                                                  
def negativeNormal (D : FormalData (k := k) n) :
    Forms (k := k) (A := Frobenius.Ring (ι := InternalVar n) (k := k) ell) (ι := InternalVar n) :=
  FormsReindex.equiv ell swapEquiv (specialNormal ell htwo D)

 theorem jointNormal_list (D : FormalData (k := k) n) :
    (fullNormalIndexList (n := n)).map (jointNormalCoordinate ell htwo D) =
      normalCoordinateList ell (specialChartEquiv ell htwo D).symm normalIndices ++
        (normalCoordinateList ell (specialChartEquiv ell htwo D).symm normalIndices).map
          (Frobenius.reindex ell swapEquiv) := by
  simp only [fullNormalIndexList, List.map_append, List.map_map, normalCoordinateList]
  congr 1
  · apply List.map_congr_left
    intro c hc
    have hct := (mem_normalIndices c).mp (Finset.mem_toList.mp hc)
    simp only [jointNormalCoordinate, hct, ite_true]
  · apply List.map_congr_left
    intro c hc
    have hct := (mem_normalIndices c).mp (Finset.mem_toList.mp hc)
    simp only [Function.comp_apply, jointNormalCoordinate, swapEquiv_apply,
      hct, Bool.not_true, Bool.false_eq_true, ite_false, Bool.not_false]
    congr 3
    exact Prod.ext hct.symm rfl

 theorem specialNormal_product (D : FormalData (k := k) n) :
    specialNormal ell htwo D * negativeNormal ell htwo D =
      normal (partialDeriv ell) (ell-1)
        ((fullNormalIndexList (n := n)).map (jointNormalCoordinate ell htwo D)) := by
  rw [jointNormal_list]
  rw [negativeNormal, specialNormal, chartNormal, FormsReindex.equiv_normal]
  simp only [normal, List.map_append, List.prod_append]

 def finiteNormalChart (D : FormalData (k := k) n) :
    Frobenius.Ring (ι := Fin (fullNormalIndexList (n := n)).length) (k := k) ell ≃ₐ[k]
      Frobenius.Ring (ι := Fin (fullNormalIndexList (n := n)).length) (k := k) ell :=
  ((Frobenius.reindex ell normalEnumeration).trans
    (AlgEquiv.ofBijective (jointNormalChart ell htwo D) (jointNormalChart_bijective ell htwo D))).trans
      (Frobenius.reindex ell normalEnumeration.symm)

@[simp] theorem finiteNormalChart_coordinate (D : FormalData (k := k) n)
    (i : Fin (fullNormalIndexList (n := n)).length) :
    finiteNormalChart ell htwo D (coordinate ell i) =
      Frobenius.reindex ell normalEnumeration.symm
        (jointNormalCoordinate ell htwo D (normalEnumeration i)) := by
  change Frobenius.reindex ell normalEnumeration.symm
    (jointNormalChart ell htwo D (Frobenius.reindex ell normalEnumeration (coordinate ell i))) = _
  rw [reindex_coordinate, jointNormalChart_coordinate]

 theorem specialNormal_product_reindex (D : FormalData (k := k) n) :
    FormsReindex.equiv ell normalEnumeration.symm
      (specialNormal ell htwo D * negativeNormal ell htwo D) =
      normal (partialDeriv ell) (ell-1)
        (List.ofFn fun i => finiteNormalChart ell htwo D (coordinate ell i)) := by
  rw [specialNormal_product, FormsReindex.equiv_normal]
  congr 1
  calc
    _ = ((List.ofFn (normalEnumeration (n := n))).map
        (jointNormalCoordinate ell htwo D)).map
        (Frobenius.reindex ell normalEnumeration.symm) :=
      congrArg (fun l : List (InternalVar n) =>
        (l.map (jointNormalCoordinate ell htwo D)).map
          (Frobenius.reindex ell normalEnumeration.symm)) normalEnumeration_list.symm
    _ = _ := by
      simp only [List.map_ofFn]
      congr 1
      funext i
      exact (finiteNormalChart_coordinate ell htwo D i).symm

                                                                          
                                                                                        
theorem specialNormal_pairing (D : FormalData (k := k) n) :
    ∃ v : Ext (k := k) (ι := InternalVar n) →ₗ[k] k,
      fixedResidue (quotientCoeff ell (topExponent ell) (topExponent_good (by omega))) v
        (specialNormal ell htwo D * negativeNormal ell htwo D) ≠ 0 := by
  let v := (volumeCoeff (k := k)).comp
    (FormsReindex.exterior (normalEnumeration (n := n)).symm).toLinearMap
  refine ⟨v, ?_⟩
  rw [← FormsReindex.residue_equiv ell htwo normalEnumeration.symm,
    specialNormal_product_reindex]
  exact NormalPairing.coordinate_residue_ne_zero ell htwo
    (finiteNormalChart ell htwo D).toAlgHom (finiteNormalChart ell htwo D).bijective
    (tangentJacobian_det_unit ell htwo (finiteNormalChart ell htwo D))

end BoundaryOnly.FormalObstruction

end

end OAI
