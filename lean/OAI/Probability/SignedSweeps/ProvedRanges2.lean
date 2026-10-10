import OAI.Probability.SignedSweeps.OccurrenceDimension
import OAI.Probability.SignedSweeps.ProvedRanges

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical ComplexOrder
variable {G : Type*} [Fintype G] [Group G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

lemma coefficientAction_eq_of_right_intertwines
    (T : EuclideanSpace ℂ G →ₗ[ℂ] EuclideanSpace ℂ G)
    (hT : ∀ g x, T (bilateralRepresentation (1, g) x) = bilateralRepresentation (1, g) (T x)) :
    coefficientAction finiteRegularRepresentation
      (fun g => T (EuclideanSpace.basisFun G ℂ 1) g) = T := by
  apply (EuclideanSpace.basisFun G ℂ).toBasis.ext
  intro j
  have he : bilateralRepresentation (1, j⁻¹) (EuclideanSpace.basisFun G ℂ 1) =
      EuclideanSpace.basisFun G ℂ j := by
    ext i
    simp [EuclideanSpace.basisFun_apply, mul_inv_eq_one]
  change coefficientAction finiteRegularRepresentation
    (fun g => T (EuclideanSpace.basisFun G ℂ 1) g) (EuclideanSpace.basisFun G ℂ j) =
      T (EuclideanSpace.basisFun G ℂ j)
  rw [← he, hT]
  ext i
  rw [he, finiteRegular_coefficient_kernel, bilateralRepresentation_apply]
  simp

def supportedCoefficients (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ) : G → ℂ :=
  fun g => (subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f)
    (EuclideanSpace.basisFun G ℂ 1) g

omit [FiniteDimensional ℂ E] in
lemma supportedCoefficients_action (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ) :
    coefficientAction finiteRegularRepresentation (supportedCoefficients H ρ f) =
      subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f := by
  apply coefficientAction_eq_of_right_intertwines
  intro g x
  simp only [Module.End.mul_apply, coefficientAction_right, subgroupCoefficientProjection_intertwines]

omit [FiniteDimensional ℂ E] in
lemma supportedCoefficients_positive (H : Subgroup G) (ρ : Representation ℂ H E) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    (coefficientAction finiteRegularRepresentation (supportedCoefficients H ρ f)).IsPositive := by
  rw [supportedCoefficients_action]
  exact positive_commuting_projection _ _ hf (subgroupCoefficientProjection_symmetric H ρ)
    (subgroupCoefficientProjection_idempotent H ρ) (subgroupCoefficientProjection_commutes H ρ f)

lemma supportedCoefficients_subgroup_action (H : Subgroup G) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ) :
    coefficientAction ρ (fun h : H => supportedCoefficients H ρ f h) =
      coefficientAction ρ (fun h : H => f h) := by
  let i : Fin (finrank ℂ E) := ⟨0, Module.finrank_pos⟩
  let v := stdOrthonormalBasis ℂ E i
  have hv : inner ℂ v v = 1 := by
    simpa only [v, ite_true] using
      orthonormal_iff_ite.mp (stdOrthonormalBasis ℂ E).orthonormal i i
  have hc (a : G → ℂ) (x y : E) :
      inner ℂ x (coefficientAction ρ (fun h : H => a h) y) =
      inner ℂ (subgroupExtension H (normalizedCoefficient ρ v x))
        (coefficientAction finiteRegularRepresentation a
          (subgroupExtension H (normalizedCoefficient ρ v y))) := by
    rw [subgroup_coefficient_compression, ← normalizedCoefficient_action,
      normalizedCoefficient_inner ρ hρ, hv, one_mul]
  ext y
  apply ext_inner_left ℂ
  intro x
  rw [hc, hc, supportedCoefficients_action, Module.End.mul_apply,
    ← subgroupCoefficientProjection_symmetric H ρ, subgroupCoefficientProjection_fixes]

theorem subgroup_supported_trace_bound (H : Subgroup G) (ρ : Representation ℂ H E)
    [ρ.IsIrreducible] [Nontrivial E] (hρ : ∀ h x, ‖ρ h x‖ = ‖x‖) (f : G → ℂ)
    (hf : (coefficientAction finiteRegularRepresentation f).IsPositive) :
    0 ≤ (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ∧
    (finrank ℂ E : ℝ) *
        (LinearMap.trace ℂ E (coefficientAction ρ (fun h : H => f h))).re ≤
      ((Fintype.card H : ℝ) / (Fintype.card G : ℝ)) *
        (LinearMap.trace ℂ (EuclideanSpace ℂ G)
          (subgroupCoefficientProjection H ρ * coefficientAction finiteRegularRepresentation f)).re := by
  have hb := subgroup_irreducible_trace_bound H ρ hρ (supportedCoefficients H ρ f)
    (supportedCoefficients_positive H ρ f hf)
  rw [supportedCoefficients_subgroup_action H ρ hρ, supportedCoefficients_action] at hb
  exact hb

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {G : Type*} [Fintype G] [Group G]

lemma finiteRegularRepresentation_norm (g : G) (x : EuclideanSpace ℂ G) :
    ‖finiteRegularRepresentation g x‖ = ‖x‖ :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Equiv.mulLeft g)).norm_map x

lemma finiteRegularRepresentation_single (g h : G) (z : ℂ) :
    finiteRegularRepresentation g (EuclideanSpace.single h z) =
      EuclideanSpace.single (g * h) z := by
  ext k
  simp only [finiteRegularRepresentation_apply, PiLp.single_apply]
  rw [show g⁻¹ * k = h ↔ k = g * h by exact inv_mul_eq_iff_eq_mul]

lemma invariant_projection_diagonal (S : Subrepresentation (finiteRegularRepresentation (G := G)))
    (g : G) :
    S.toSubmodule.starProjection (EuclideanSpace.single g 1) g =
      S.toSubmodule.starProjection (EuclideanSpace.single 1 1) 1 := by
  have h := congrArg (fun f : EuclideanSpace ℂ G => f g)
    (invariant_starProjection_intertwines finiteRegularRepresentation
      finiteRegularRepresentation_norm S g (EuclideanSpace.single 1 1))
  simpa only [finiteRegularRepresentation_single, mul_one,
    finiteRegularRepresentation_apply, inv_mul_cancel] using h

lemma invariant_projection_diagonal_trace
    (S : Subrepresentation (finiteRegularRepresentation (G := G))) :
    (Fintype.card G : ℂ) *
      S.toSubmodule.starProjection (EuclideanSpace.single 1 1) 1 =
        (finrank ℂ S.toSubmodule : ℂ) := by
  have htrace := (LinearMap.IsIdempotentElem.isProj_range _
    (S.toSubmodule.isSymmetricProjection_starProjection).isIdempotentElem).trace
  rw [Submodule.range_starProjection] at htrace
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)] at htrace
  simpa only [EuclideanSpace.basisFun_apply, ContinuousLinearMap.coe_coe,
    EuclideanSpace.inner_single_left, map_one, one_mul, invariant_projection_diagonal,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using htrace

theorem invariant_evaluation_dimension_bound
    (S : Subrepresentation (finiteRegularRepresentation (G := G)))
    (f : EuclideanSpace ℂ G) (hf : f ∈ S.toSubmodule) :
    (Fintype.card G : ℝ) * ‖f 1‖ ^ 2 ≤ (finrank ℂ S.toSubmodule : ℝ) * ‖f‖ ^ 2 := by
  let p := S.toSubmodule.starProjection
  let v := p (EuclideanSpace.single 1 1)
  have hp : p f = f := S.toSubmodule.starProjection_eq_self_iff.mpr hf
  have hv : p v = v := S.toSubmodule.starProjection_eq_self_iff.mpr
    (S.toSubmodule.starProjection_apply_mem _)
  have he : inner ℂ v f = f 1 := by
    change inner ℂ (p (EuclideanSpace.single 1 1)) f = _
    rw [S.toSubmodule.inner_starProjection_left_eq_right, hp,
      EuclideanSpace.inner_single_left, map_one, one_mul]
  have hvnorm : ‖v‖ ^ 2 = (v 1).re := by
    calc
      ‖v‖ ^ 2 = (inner ℂ v v).re := by simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
      _ = (v 1).re := ?_
    · change (inner ℂ (p (EuclideanSpace.single 1 1)) v).re = _
      rw [S.toSubmodule.inner_starProjection_left_eq_right, hv,
        EuclideanSpace.inner_single_left, map_one, one_mul]
  have ht : (Fintype.card G : ℝ) * ‖v‖ ^ 2 = (finrank ℂ S.toSubmodule : ℝ) := by
    rw [hvnorm]
    have h := congrArg Complex.re (invariant_projection_diagonal_trace S)
    simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using h
  have hb := pow_le_pow_left₀ (norm_nonneg (inner ℂ v f))
    (norm_inner_le_norm (𝕜 := ℂ) v f) 2
  rw [he, mul_pow] at hb
  calc
    _ ≤ (Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by rw [← mul_assoc, ht]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma column_row_product_injective {n : ℕ} (lam : Partition n) :
    Function.Injective (fun p : colSubgroup lam × rowSubgroup lam => p.1.1 * p.2.1) := by
  rintro ⟨c, a⟩ ⟨c', a'⟩ h
  have he : c'.1⁻¹ * c.1 = a'.1 * a.1⁻¹ := by
    have := congrArg (fun g => c'.1⁻¹ * g * a.1⁻¹) h
    simpa [mul_assoc] using this
  have hz : c'.1⁻¹ * c.1 = 1 := mem_row_col_eq_one lam
    (he ▸ (rowSubgroup lam).mul_mem a'.property ((rowSubgroup lam).inv_mem a.property))
    ((colSubgroup lam).mul_mem ((colSubgroup lam).inv_mem c'.property) c.property)
  have hc : c = c' := Subtype.ext (inv_mul_eq_one.mp hz).symm
  subst c'
  have ha : a = a' := Subtype.ext (mul_left_cancel h)
  subst a'
  rfl

lemma polytabloid_norm_sq {n : ℕ} (lam : Partition n) :
    ‖polytabloid lam‖ ^ 2 =
      (Fintype.card (colSubgroup lam) : ℝ) * Fintype.card (rowSubgroup lam) := by
  let v := fun p : colSubgroup lam × rowSubgroup lam =>
    EuclideanSpace.single (p.1.1 * p.2.1) (1 : ℂ)
  have hv : Orthonormal ℂ v := by
    convert (EuclideanSpace.basisFun (SymmetricGroup n) ℂ).orthonormal.comp
      (fun p : colSubgroup lam × rowSubgroup lam => p.1.1 * p.2.1)
      (column_row_product_injective lam) using 1
    ext pair permutation
    simp [v, EuclideanSpace.basisFun_apply]
  have he : polytabloid lam = ∑ p, complexSign n p.1.1 • v p := by
    simp only [polytabloid, Fintype.sum_prod_type, v]
    rfl
  have hh := hv.inner_sum (fun p => complexSign n p.1.1) (fun p => complexSign n p.1.1)
    Finset.univ
  rw [← he] at hh
  have hsign (p : colSubgroup lam × rowSubgroup lam) :
      starRingEnd ℂ (complexSign n p.1.1) * complexSign n p.1.1 = 1 := by
    simp only [complexSign, MonoidHom.coe_mk, OneHom.coe_mk, map_intCast]
    exact complexSign_mul_self p.1.1
  simp only [hsign, Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul,
    mul_one, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal] at hh
  exact_mod_cast hh

theorem spechtDimension_row_column_lower {n : ℕ} (lam : Partition n) :
    (Nat.factorial n : ℝ) ≤ (spechtDimension lam : ℝ) *
      (Fintype.card (colSubgroup lam) : ℝ) * Fintype.card (rowSubgroup lam) := by
  have hb := invariant_evaluation_dimension_bound
    (show Subrepresentation (finiteRegularRepresentation (G := SymmetricGroup n)) from
      spechtSubrepresentation lam) (polytabloid lam) (spechtGenerator lam).property
  rw [polytabloid_at_one, norm_one, one_pow, mul_one, polytabloid_norm_sq] at hb
  change (Fintype.card (SymmetricGroup n) : ℝ) ≤
    (spechtDimension lam : ℝ) *
      ((Fintype.card (colSubgroup lam) : ℝ) * (Fintype.card (rowSubgroup lam) : ℝ)) at hb
  simpa only [SymmetricGroup, Fintype.card_perm, Fintype.card_fin, mul_assoc] using hb

def fiberPermEquiv {A I : Type*} (c : A → I) :
    fiberSubgroup c ≃ (∀ i, Equiv.Perm {x : A // c x = i}) where
  toFun g i := g.1.subtypeEquiv (fun x => by rw [g.property x])
  invFun σ := ⟨(Equiv.sigmaFiberEquiv c).permCongr (Equiv.sigmaCongrRight σ), by
    intro x
    exact (σ (c x) ⟨x, rfl⟩).property⟩
  left_inv g := by
    apply Subtype.ext
    ext x
    rfl
  right_inv σ := by
    funext i
    apply Equiv.ext
    rintro ⟨x,hx⟩
    apply Subtype.ext
    subst i
    rfl

lemma card_fiberSubgroup {A I : Type*} [Fintype A] [Fintype I] (c : A → I) :
    Fintype.card (fiberSubgroup c) = ∏ i, (Fintype.card {x : A // c x = i}).factorial := by
  rw [Fintype.card_congr (fiberPermEquiv c), Fintype.card_pi]
  exact Finset.prod_congr rfl (fun i _ => Fintype.card_perm)

lemma fiber_product_injective {A I J : Type*} (c : A → I) (d : A → J)
    (h : Function.Injective (fun x => (c x, d x))) :
    Function.Injective (fun p : fiberSubgroup c × fiberSubgroup d => p.1.1 * p.2.1) := by
  rintro ⟨a,b⟩ ⟨a',b'⟩ hab
  have he : a'.1⁻¹ * a.1 = b'.1 * b.1⁻¹ := by
    have := congrArg (fun g => a'.1⁻¹ * g * b.1⁻¹) hab
    simpa [mul_assoc] using this
  have hf : a'.1⁻¹ * a.1 = 1 := by
    have hc := (fiberSubgroup c).mul_mem ((fiberSubgroup c).inv_mem a'.property) a.property
    have hd : a'.1⁻¹ * a.1 ∈ fiberSubgroup d :=
      he ▸ (fiberSubgroup d).mul_mem b'.property ((fiberSubgroup d).inv_mem b.property)
    ext x
    exact h (Prod.ext (hc x) (hd x))
  have ha : a = a' := Subtype.ext (inv_mul_eq_one.mp hf).symm
  subst a'
  have hb : b = b' := Subtype.ext (mul_left_cancel hab)
  subst b'
  rfl

lemma card_fiber_product_le {A I J : Type*} [Fintype A]
    (c : A → I) (d : A → J) (h : Function.Injective (fun x => (c x,d x))) :
    Fintype.card (fiberSubgroup c) * Fintype.card (fiberSubgroup d) ≤
      (Fintype.card A).factorial := by
  simpa only [Fintype.card_prod, Fintype.card_perm] using
    Fintype.card_le_of_injective _ (fiber_product_injective c d h)

lemma rowIndex_fiber_card {n : ℕ} (lam : Partition n) (i : Fin (lam.1.colLen 0)) :
    Fintype.card {x : Fin n // lam.rowIndex x = i} = lam.1.rowLen i := by
  let e : {x : Fin n // lam.rowIndex x = i} ≃ Fin (lam.1.rowLen i) := {
    toFun := fun x => ⟨lam.colOf x.1, by
      have hr : lam.rowOf x.1 = i := congrArg Fin.val x.property
      rw [← hr]
      exact lam.colOf_lt_rowLen x.1⟩
    invFun := fun j => ⟨lam.tableau ⟨(i,j.1), YoungDiagram.mem_iff_lt_rowLen.mpr j.2⟩,
      by apply Fin.ext; simp [Partition.rowIndex, Partition.rowOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext (congrArg Fin.val x.property).symm rfl
    right_inv := by
      intro j
      apply Fin.ext
      simp [Partition.colOf] }
  simpa using Fintype.card_congr e

lemma colIndex_fiber_card {n : ℕ} (lam : Partition n) (j : Fin (lam.1.rowLen 0)) :
    Fintype.card {x : Fin n // lam.colIndex x = j} = lam.1.colLen j := by
  let e : {x : Fin n // lam.colIndex x = j} ≃ Fin (lam.1.colLen j) := {
    toFun := fun x => ⟨lam.rowOf x.1, by
      have hc : lam.colOf x.1 = j := congrArg Fin.val x.property
      rw [← hc]
      exact YoungDiagram.mem_iff_lt_colLen.mp (lam.tableau.symm x.1).property⟩
    invFun := fun i => ⟨lam.tableau ⟨(i.1,j), YoungDiagram.mem_iff_lt_colLen.mpr i.2⟩,
      by apply Fin.ext; simp [Partition.colIndex, Partition.colOf]⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply lam.tableau.symm.injective
      apply Subtype.ext
      simp only [Equiv.symm_apply_apply]
      exact Prod.ext rfl (congrArg Fin.val x.property).symm
    right_inv := by
      intro i
      apply Fin.ext
      simp [Partition.rowOf] }
  simpa using Fintype.card_congr e

lemma card_rowSubgroup {n : ℕ} (lam : Partition n) :
    Fintype.card (rowSubgroup lam) = ∏ i : Fin (lam.1.colLen 0), (lam.1.rowLen i).factorial := by
  let e : rowSubgroup lam ≃ (∀ i : Fin (lam.1.colLen 0), Equiv.Perm {x : Fin n // lam.rowIndex x = i}) :=
    (Equiv.subtypeEquivRight (fun g => by rw [fiberSubgroup_rowIndex])).trans
      (fiberPermEquiv lam.rowIndex)
  calc
    _ = Fintype.card (∀ i : Fin (lam.1.colLen 0), Equiv.Perm {x : Fin n // lam.rowIndex x = i}) :=
      Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun i _ => (Fintype.card_perm).trans
        (congrArg Nat.factorial (rowIndex_fiber_card lam i)))

lemma card_colSubgroup {n : ℕ} (lam : Partition n) :
    Fintype.card (colSubgroup lam) = ∏ j : Fin (lam.1.rowLen 0), (lam.1.colLen j).factorial := by
  let e : colSubgroup lam ≃ (∀ j : Fin (lam.1.rowLen 0), Equiv.Perm {x : Fin n // lam.colIndex x = j}) :=
    (Equiv.subtypeEquivRight (fun g => by rw [fiberSubgroup_colIndex])).trans
      (fiberPermEquiv lam.colIndex)
  calc
    _ = Fintype.card (∀ j : Fin (lam.1.rowLen 0), Equiv.Perm {x : Fin n // lam.colIndex x = j}) :=
      Fintype.card_congr e
    _ = _ := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl (fun j _ => (Fintype.card_perm).trans
        (congrArg Nat.factorial (colIndex_fiber_card lam j)))

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma factorial_fiber_pair_bound {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
    (c : A → I) (d : A → J) (h : Function.Injective (fun x => (c x,d x))) :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) *
      (∏ j, (Fintype.card {x : A // d x = j}).factorial) ≤ (Fintype.card A).factorial := by
  rw [← card_fiberSubgroup c, ← card_fiberSubgroup d]
  exact card_fiber_product_le c d h

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical
variable {A I J : Type*} [Fintype A] [Fintype I] [Fintype J]
variable (c : A → I) (d : A → J) (i₀ : I)
variable (hinj : Function.Injective (fun x => (c x,d x)))
variable (hfull : ∀ j, ∃ x, c x = i₀ ∧ d x = j)

omit [Fintype I] in
lemma row_removed_same_fiber (i : I) (hi : i ≠ i₀) :
    Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i} =
      Fintype.card {x : A // c x = i} := by
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨x.1.1, x.2⟩
    invFun := fun x => ⟨⟨x.1, by simpa only [x.2] using hi⟩, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

omit [Fintype I] in
lemma row_removed_top_empty :
    Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i₀} = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun x => x.1.2 x.2⟩

lemma row_removal_factorial_product :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) =
      (Fintype.card {x : A // c x = i₀}).factorial *
        (∏ i, (Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i}).factorial) := by
  classical
  rw [← Finset.mul_prod_erase (s := Finset.univ) (a := i₀) _ (Finset.mem_univ i₀)]
  congr 1
  rw [← Finset.mul_prod_erase (s := Finset.univ) (a := i₀) _ (Finset.mem_univ i₀),
    row_removed_top_empty, Nat.factorial_zero, one_mul]
  exact Finset.prod_congr rfl (fun i hi => (congrArg Nat.factorial
    (row_removed_same_fiber c i₀ i (Finset.mem_erase.mp hi).1)).symm)

include hinj hfull

omit [Fintype I] [Fintype J] in
lemma col_fiber_removal (j : J) :
    Fintype.card {x : A // d x = j} =
      Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j} + 1 := by
  let P : {x : A // d x = j} → Prop := fun x => c x.1 = i₀
  have hP : Fintype.card {x : {x : A // d x = j} // P x} = 1 := by
    obtain ⟨a, ha, hd⟩ := hfull j
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨⟨⟨a, hd⟩, ha⟩, ?_⟩
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact hinj (Prod.ext (x.2.trans ha.symm) (x.1.2.trans hd.symm))
  have hPc : Fintype.card {x : {x : A // d x = j} // ¬ P x} =
      Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j} := by
    apply Fintype.card_congr
    exact {
      toFun := fun x => ⟨⟨x.1.1,x.2⟩, x.1.2⟩
      invFun := fun x => ⟨⟨x.1.1,x.2⟩, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have ht := Fintype.card_subtype_compl P
  rw [hP, hPc] at ht
  have hp : 0 < Fintype.card {x : A // d x = j} := by
    obtain ⟨x, _, hx⟩ := hfull j
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  omega

omit [Fintype I] in
lemma col_removal_factorial_product :
    (∏ j, (Fintype.card {x : A // d x = j}).factorial) =
      (∏ j, (Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j}).factorial) *
        (∏ j, Fintype.card {x : A // d x = j}) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [col_fiber_removal c d i₀ hinj hfull, Nat.factorial_succ]
  exact mul_comm _ _

theorem factorial_product_remove_full_row :
    (∏ i, (Fintype.card {x : A // c x = i}).factorial) *
      (∏ j, (Fintype.card {x : A // d x = j}).factorial) ≤
    (Fintype.card {x : A // c x = i₀}).factorial *
      (Fintype.card {x : A // c x ≠ i₀}).factorial *
        ∏ j, Fintype.card {x : A // d x = j} := by
  rw [row_removal_factorial_product c i₀, col_removal_factorial_product c d i₀ hinj hfull]
  have hb := factorial_fiber_pair_bound
    (fun x : {a : A // c a ≠ i₀} => c x.1) (fun x => d x.1)
    (fun x y h => Subtype.ext (hinj h))
  calc
    _ = (Fintype.card {x : A // c x = i₀}).factorial *
      ((∏ i, (Fintype.card {x : {a : A // c a ≠ i₀} // c x.1 = i}).factorial) *
       (∏ j, (Fintype.card {x : {a : A // c a ≠ i₀} // d x.1 = j}).factorial)) *
       (∏ j, Fintype.card {x : A // d x = j}) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb)

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators Classical

lemma log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := Real.pow_div_factorial_le_exp (n : ℝ) hn'.le n
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) ^ n / n.factorial) hh
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_exp] at hlog
  linarith

lemma log_factorial_upper {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n - n + Real.log n + 1 := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hp : (0 : ℝ) < n := by exact_mod_cast hn
    have hnp : (0 : ℝ) < n + 1 := by positivity
    have hh := Real.log_le_sub_one_of_pos (div_pos hp hnp)
    rw [Real.log_div hp.ne' hnp.ne'] at hh
    have hmul := mul_le_mul_of_nonneg_left hh hnp.le
    have hdiv : ((n : ℝ) + 1) * ((n : ℝ) / (n + 1) - 1) = -1 := by
      field_simp
      ring
    rw [hdiv] at hmul
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast
    nlinarith

lemma log_le_quarter_add_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 4 + 1 := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < x / 4)
  rw [Real.log_div hx.ne' (by norm_num)] at h
  have h4 : Real.log (4 : ℝ) ≤ 2 := by
    have hp : 4 ≤ Real.exp 2 := by
      have h₁ : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h₂ : (2 : ℝ) ^ 2 ≤ Real.exp 1 ^ 2 := by simpa using pow_le_pow_left₀ (by norm_num) h₁ 2
      norm_num [← Real.exp_nat_mul] at h₂ ⊢; exact h₂
    exact (Real.log_le_iff_le_exp (by norm_num)).mpr hp
  linarith

lemma Partition.rowColIndex_injective {n : ℕ} (lam : Partition n) :
    Function.Injective (fun x => (lam.rowIndex x, lam.colIndex x)) := by
  intro x y h
  apply lam.tableau.symm.injective
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z => z.1.val) h) (congrArg (fun z => z.2.val) h)

lemma row_column_cell_sum_le {n : ℕ} (lam : Partition n) :
    (∑ x : Fin n, (lam.1.rowLen (lam.rowOf x) : ℝ) * (lam.1.colLen (lam.colOf x) : ℝ)) ≤
      (n : ℝ) ^ 2 := by
  let f : Fin (lam.1.colLen 0) × Fin (lam.1.rowLen 0) → ℝ :=
    fun x => (lam.1.rowLen x.1 : ℝ) * (lam.1.colLen x.2 : ℝ)
  calc
    _ = ∑ x ∈ Finset.univ.image (fun x => (lam.rowIndex x, lam.colIndex x)), f x := by
      rw [Finset.sum_image (fun x _ y _ h => lam.rowColIndex_injective h)]
      rfl
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by
      intros; exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = (n : ℝ) ^ 2 := by
      rw [Fintype.sum_prod_type]
      simp only [f, ← Finset.mul_sum]
      rw [← Nat.cast_sum, lam.sum_colLen, ← Finset.sum_mul, ← Nat.cast_sum, lam.sum_rowLen]
      ring

lemma row_column_entropy_sum_le {n : ℕ} (lam : Partition n) (hn : 0 < n) :
    (∑ i : Fin (lam.1.colLen 0), (lam.1.rowLen i : ℝ) * Real.log (lam.1.rowLen i)) +
    (∑ j : Fin (lam.1.rowLen 0), (lam.1.colLen j : ℝ) * Real.log (lam.1.colLen j)) ≤
      (n : ℝ) * Real.log n := by
  have hp : (0 : ℝ) < n := by exact_mod_cast hn
  have hr (x : Fin n) : (0 : ℝ) < lam.1.rowLen (lam.rowOf x) := by
    exact_mod_cast lam.rowLen_pos (lam.rowIndex x)
  have hc (x : Fin n) : (0 : ℝ) < lam.1.colLen (lam.colOf x) := by
    exact_mod_cast lam.colLen_pos (lam.colIndex x)
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun x _ => Real.log_le_sub_one_of_pos (div_pos (mul_pos (hr x) (hc x)) hp))
  simp_rw [Real.log_div (mul_pos (hr _) (hc _)).ne' hp.ne',
    Real.log_mul (hr _).ne' (hc _).ne'] at hb
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, lam.sum_rowOf (fun i => Real.log (lam.1.rowLen i : ℝ)),
    lam.sum_colOf (fun j => Real.log (lam.1.colLen j : ℝ))] at hb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hb
  have hsum := div_le_div_of_nonneg_right (row_column_cell_sum_le lam) hp.le
  have he : (n : ℝ) ^ 2 / n = n := by field_simp
  rw [he] at hsum
  linarith

end SignedSweeps
end

end OAI
