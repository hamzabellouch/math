import OAI.Algebra.Determinantal.Centralizers

namespace OAI

namespace PermanentBorder.CoordinateNormalization
open Matrix MvPolynomial CoordinateGauge
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Infinite K]
  [Fintype ι] [DecidableEq ι]

theorem exists_base_eval_ne_zero {κ : Type*} (p : MvPolynomial κ L) (hp : p ≠ 0) :
    ∃ x : κ → K, MvPolynomial.eval (algebraMap K L ∘ x) p ≠ 0 := by
  classical
  by_contra! h
  apply hp
  apply MvPolynomial.funext_set (fun _ => Set.range (algebraMap K L))
    (fun _ => Set.infinite_range_of_injective (algebraMap K L).injective)
  intro x hx
  choose y hy using fun i => hx i (Set.mem_univ i)
  have he : algebraMap K L ∘ y = x := funext hy
  simp only [← he, h, map_zero]

noncomputable def basisDeterminant {κ : Type*} [Fintype κ]
    (S : Submodule L ((ι × ι) → L)) (b : Module.Basis κ L S) : MvPolynomial κ L :=
  Matrix.det (of fun i j => ∑ a, C ((b a).val (i,j)) * X a)

theorem eval_basisDeterminant {κ : Type*} [Fintype κ]
    (S : Submodule L ((ι × ι) → L)) (b : Module.Basis κ L S) (v : S) :
    MvPolynomial.eval (fun a => b.repr v a) (basisDeterminant S b) =
      Matrix.det (Function.curry v.val) := by
  classical
  unfold basisDeterminant
  rw [RingHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.eval (fun a => b.repr v a)
    (∑ a, C ((b a).val (i,j)) * X a) = v.val (i,j)
  simp only [map_sum, map_mul, eval_C, eval_X]
  have h := congrArg (fun z : S => z.val (i,j)) (b.sum_repr v)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mul_comm] using h

theorem exists_invertible_coordinate_gauge
    (S : Submodule L ((ι × ι) → L))
    (hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0) :
    ∃ (a : Fin (Module.finrank L S) → ι × ι) (v : S),
      Function.Injective a ∧ Matrix.det (Function.curry v.val) ≠ 0 ∧
      ∀ j, ∃ c : K, v.val (a j) = algebraMap K L c := by
  classical
  obtain ⟨a, hai, hab⟩ := exists_coordinate_gauge S
  let r : S →ₗ[L] (Fin (Module.finrank L S) → L) :=
    LinearMap.pi fun j => (LinearMap.proj (a j)).comp S.subtype
  let e : S ≃ₗ[L] (Fin (Module.finrank L S) → L) := LinearEquiv.ofBijective r hab
  let b := Module.Basis.ofEquivFun e
  have hp : basisDeterminant S b ≠ 0 := by
    obtain ⟨v, hv⟩ := hS
    intro h
    apply hv
    rw [← eval_basisDeterminant S b v, h, map_zero]
  obtain ⟨x, hx⟩ := exists_base_eval_ne_zero (K := K) (basisDeterminant S b) hp
  let v := e.symm (algebraMap K L ∘ x)
  have hre : (fun j => b.repr v j) = algebraMap K L ∘ x := by
    funext j
    simp only [b, Module.Basis.ofEquivFun_repr_apply, v, LinearEquiv.apply_symm_apply]
  refine ⟨a, v, hai, ?_, ?_⟩
  · rwa [← hre, eval_basisDeterminant] at hx
  · intro j
    refine ⟨x j, ?_⟩
    have h := congrFun (e.apply_symm_apply (algebraMap K L ∘ x)) j
    exact h

end PermanentBorder.CoordinateNormalization

namespace PermanentBorder.OrbitNormalization
open Matrix CentralizerDimension CentralizerBaseChange CoordinateNormalization
variable {L ι : Type*} [Field L] [Fintype ι] [DecidableEq ι]

def intertwinerSpace (A C : Matrix ι ι L) : Submodule L (ι × ι → L) where
  carrier := {v | A * Matrix.of (Function.curry v) = Matrix.of (Function.curry v) * C}
  zero_mem' := by change A * 0 = 0 * C; simp
  add_mem' := by
    intro v w hv hw
    change A * (Matrix.of (Function.curry v) + Matrix.of (Function.curry w)) =
      (Matrix.of (Function.curry v) + Matrix.of (Function.curry w)) * C
    rw [mul_add, add_mul, hv, hw]
  smul_mem' := by
    intro c v hv
    change A * (c • Matrix.of (Function.curry v)) =
      (c • Matrix.of (Function.curry v)) * C
    rw [Matrix.mul_smul, hv, Matrix.smul_mul]

def intertwinerEquivCentralizer (A C : Matrix ι ι L)
    (P : (Matrix ι ι L)ˣ) (hP : A * (P : Matrix ι ι L) = (P : Matrix ι ι L) * C) :
    centralizer C ≃ₗ[L] intertwinerSpace A C := by
  have hCP : C * (↑P⁻¹ : Matrix ι ι L) = (↑P⁻¹ : Matrix ι ι L) * A := by
    have h := congrArg (fun M : Matrix ι ι L => (↑P⁻¹ : Matrix ι ι L) * M * (↑P⁻¹ : Matrix ι ι L)) hP
    simp only [← mul_assoc, Units.inv_mul, one_mul] at h
    simpa only [mul_assoc, Units.mul_inv, mul_one] using h.symm
  refine
    { toFun := fun B => ⟨Function.uncurry ((P : Matrix ι ι L) * B.val), by
        change A * ((P : Matrix ι ι L) * B.val) = ((P : Matrix ι ι L) * B.val) * C
        rw [← mul_assoc, hP, mul_assoc, B.property, ← mul_assoc]⟩
      invFun := fun v => ⟨(↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val), by
        change C * ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val)) =
          ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val)) * C
        rw [← mul_assoc, hCP, mul_assoc, v.property, ← mul_assoc]⟩
      left_inv := fun B => by
        apply Subtype.ext
        change (↑P⁻¹ : Matrix ι ι L) * ((P : Matrix ι ι L) * B.val) = B.val
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun v => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) *
          ((↑P⁻¹ : Matrix ι ι L) * Matrix.of (Function.curry v.val))) = v.val
        rw [← mul_assoc, Units.mul_inv, one_mul]
        rfl
      map_add' := fun B D => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) * (B.val + D.val)) = _
        rw [mul_add]
        rfl
      map_smul' := fun c B => by
        apply Subtype.ext
        change Function.uncurry ((P : Matrix ι ι L) * (c • B.val)) = _
        rw [Matrix.mul_smul]
        rfl }

variable {K : Type*} [Field K] [Algebra K L] [Infinite K]

theorem exists_normalized_intertwiner (A : Matrix ι ι L) (C : Matrix ι ι K)
    (P : (Matrix ι ι L)ˣ)
    (hP : A * (P : Matrix ι ι L) = (P : Matrix ι ι L) * C.map (algebraMap K L)) :
    ∃ (a : Fin (Module.finrank K (centralizer C)) → ι × ι)
      (Q : (Matrix ι ι L)ˣ),
      Function.Injective a ∧
      A * (Q : Matrix ι ι L) = (Q : Matrix ι ι L) * C.map (algebraMap K L) ∧
      ∀ j, ∃ c : K, (Q : Matrix ι ι L) (a j).1 (a j).2 = algebraMap K L c := by
  classical
  let S := intertwinerSpace A (C.map (algebraMap K L))
  have hd : Module.finrank L S = Module.finrank K (centralizer C) :=
    (intertwinerEquivCentralizer A _ P hP).finrank_eq.symm.trans
      (finrank_centralizer_map C)
  have hS : ∃ v : S, Matrix.det (Function.curry v.val) ≠ 0 := by
    refine ⟨⟨Function.uncurry (P : Matrix ι ι L), hP⟩, ?_⟩
    exact (Matrix.isUnits_det_units P).ne_zero
  obtain ⟨a, v, hai, hv, hvK⟩ := exists_invertible_coordinate_gauge (K := K) S hS
  obtain ⟨Q, hQ⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  let e := finCongr hd
  refine ⟨a ∘ e.symm, Q, hai.comp e.symm.injective, ?_, ?_⟩
  · rw [hQ]
    exact v.property
  · intro j
    obtain ⟨c, hc⟩ := hvK (e.symm j)
    exact ⟨c, by simpa only [hQ, Function.comp_apply, Function.curry] using hc⟩

end PermanentBorder.OrbitNormalization

namespace PermanentBorder.CentralizerParameters
open Matrix MvPolynomial CentralizerDimension CentralizerBaseChange
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

noncomputable def coefficients (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) :
    Fin (Module.finrank K (centralizer C)) → L :=
  (centralizerBasisMap C (centralizerBasis C)).repr B

theorem entry_expansion (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (i j : ι) :
    B.val i j = ∑ a, coefficients C B a * algebraMap K L ((centralizerBasis C a).val i j) := by
  have h := congrArg (fun D : centralizer (C.map (algebraMap K L)) => D.val i j)
    ((centralizerBasisMap C (centralizerBasis C)).sum_repr B)
  simpa only [coefficients, Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, centralizerBasisMap_apply,
    mapCentralizer, Matrix.map_apply] using h.symm

theorem eval_determinant (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) :
    MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = B.val.det := by
  rw [determinantPolynomial, AlgHom.map_det]
  congr 1
  ext i j
  change MvPolynomial.aeval (coefficients C B)
    (∑ a, MvPolynomial.C ((centralizerBasis C a).val i j) * X a) = B.val i j
  simp only [map_sum, map_mul, aeval_C, aeval_X]
  rw [entry_expansion C B i j]
  apply Finset.sum_congr rfl
  intro a _
  exact mul_comm _ _

theorem determinant_relation (C : Matrix ι ι K)
    (B : centralizer (C.map (algebraMap K L))) (hB : B.val.det = 0) :
    determinantPolynomial C ≠ 0 ∧
      MvPolynomial.aeval (coefficients C B) (determinantPolynomial C) = 0 :=
  ⟨determinantPolynomial_ne_zero C, (eval_determinant C B).trans hB⟩

end PermanentBorder.CentralizerParameters

namespace PermanentBorder.MatrixSubfield
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem mul_mem (F : IntermediateField K L) (A B : Matrix ι ι L)
    (hA : ∀ i j, A i j ∈ F) (hB : ∀ i j, B i j ∈ F) :
    ∀ i j, (A * B) i j ∈ F := by
  intro i j
  exact F.sum_mem fun k _ => F.mul_mem (hA i k) (hB k j)

theorem unit_inv_mem (F : IntermediateField K L) (P : (Matrix ι ι L)ˣ)
    (hP : ∀ i j, (P : Matrix ι ι L) i j ∈ F) :
    ∀ i j, (↑P⁻¹ : Matrix ι ι L) i j ∈ F := by
  let A : Matrix ι ι F := fun i j => ⟨(P : Matrix ι ι L) i j, hP i j⟩
  have hA : A.map (algebraMap F L) = (P : Matrix ι ι L) := rfl
  have hd : A.det ≠ 0 := by
    intro h
    have he : algebraMap F L A.det = (P : Matrix ι ι L).det :=
      (algebraMap F L).map_det A
    rw [h, map_zero] at he
    exact (Matrix.isUnits_det_units P).ne_zero he.symm
  have hi := congrArg (fun M : Matrix ι ι F => M.map (algebraMap F L))
    (Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd))
  simp only [Matrix.map_mul, hA, Matrix.map_one _ (map_zero _) (map_one _)] at hi
  have he : A⁻¹.map (algebraMap F L) = (↑P⁻¹ : Matrix ι ι L) := by
    calc
      _ = (A⁻¹.map (algebraMap F L) * (P : Matrix ι ι L)) * (↑P⁻¹ : Matrix ι ι L) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hi, one_mul]
  intro i j
  rw [← he]
  exact ((A⁻¹) i j).property

end PermanentBorder.MatrixSubfield

namespace PermanentBorder.ParameterBounds
open Algebra MvPolynomial
universe u
variable {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem field_adjoin_trdeg_lt_of_relation_fintype {L : Type u} [Field L] [Algebra K L]
    {κ : Type*} [Fintype κ] (x : κ → L) (p : MvPolynomial κ K) (hp : p ≠ 0)
    (hx : aeval x p = 0) :
    Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) < (Fintype.card κ : Cardinal) := by
  classical
  let e := Fintype.equivFin κ
  let y := x ∘ e.symm
  have hy : Set.range y = Set.range x := e.symm.surjective.range_comp x
  rw [← hy]
  apply field_adjoin_trdeg_lt_of_relation y (MvPolynomial.rename e p)
  · exact fun h => hp ((MvPolynomial.rename_injective e e.injective) (by simpa using h))
  · simpa only [MvPolynomial.aeval_rename, y, Function.comp_assoc,
      Equiv.symm_comp_self, Function.comp_id] using hx

end PermanentBorder.ParameterBounds

namespace PermanentBorder.CommutingPairs
open Matrix CentralizerDimension CentralizerParameters OrbitNormalization
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [Infinite K]

theorem normalized_pair_field_bound {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) L) (C : Matrix (Fin n) (Fin n) K)
    (P : (Matrix (Fin n) (Fin n) L)ˣ)
    (hP : A * (P : Matrix (Fin n) (Fin n) L) =
      (P : Matrix (Fin n) (Fin n) L) * C.map (algebraMap K L))
    (hAB : A * B = B * A) (hB : B.det = 0) :
    ∃ F : IntermediateField K L,
      Algebra.trdeg K F < (n * n : ℕ) ∧
      (∀ i j, A i j ∈ F) ∧ (∀ i j, B i j ∈ F) := by
  classical
  obtain ⟨a, Q, hai, hQ, hQa⟩ := exists_normalized_intertwiner A C P hP
  let j := Module.finrank K (centralizer C)
  let C' := C.map (algebraMap K L)
  have hC' : C' = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * A * (Q : Matrix (Fin n) (Fin n) L) := by
    calc
      _ = (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * ((Q : Matrix (Fin n) (Fin n) L) * C') := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = _ := by rw [← hQ, mul_assoc]
  let B' : centralizer C' := ⟨(↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L), by
    change C' * _ = _ * C'
    rw [hC']
    simp only [mul_assoc]
    simp only [← mul_assoc (Q : Matrix (Fin n) (Fin n) L), Units.mul_inv, one_mul]
    simp only [← mul_assoc]
    rw [mul_assoc (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) A B, hAB, ← mul_assoc]⟩
  let κ := {p : Fin n × Fin n // p ∉ Set.range a} ⊕ Fin j
  let x : κ → L := Sum.elim
    (fun p => (Q : Matrix (Fin n) (Fin n) L) p.val.1 p.val.2)
    (coefficients C B')
  let F := IntermediateField.adjoin K (Set.range x)
  have hx (i : κ) : x i ∈ F := IntermediateField.subset_adjoin K _ (Set.mem_range_self i)
  have ha_card : Fintype.card {p : Fin n × Fin n // p ∈ Set.range a} = j := by
    simpa only [Fintype.card_fin] using (Fintype.card_congr (Equiv.ofInjective a hai)).symm
  have hj : j ≤ n * n := by
    simpa only [Fintype.card_fin, Fintype.card_prod] using Fintype.card_le_of_injective a hai
  have hκ : Fintype.card κ = n * n := by
    simp only [κ, Fintype.card_sum, Fintype.card_subtype_compl, ha_card,
      Fintype.card_prod, Fintype.card_fin]
    exact Nat.sub_add_cancel hj
  have hB' : B'.val.det = 0 := (Matrix.det_units_conj' Q B).trans hB
  obtain ⟨hp, hxp⟩ := determinant_relation C B' hB'
  have hFp : Algebra.trdeg K F < (Fintype.card κ : Cardinal) := by
    apply ParameterBounds.field_adjoin_trdeg_lt_of_relation_fintype x
      (MvPolynomial.rename (Sum.inr : Fin j → κ) (determinantPolynomial C))
    · exact fun h => hp ((MvPolynomial.rename_injective _ Sum.inr_injective) (by simpa using h))
    · simpa only [MvPolynomial.aeval_rename, Function.comp_def, x, Sum.elim_inr] using hxp
  have hQF : ∀ i j, (Q : Matrix (Fin n) (Fin n) L) i j ∈ F := by
    intro i j
    by_cases h : (i,j) ∈ Set.range a
    · obtain ⟨b, hb⟩ := h
      obtain ⟨c, hc⟩ := hQa b
      rw [hb] at hc
      rw [hc]
      exact F.algebraMap_mem c
    · exact hx (Sum.inl ⟨(i,j), h⟩)
  have hQiF := MatrixSubfield.unit_inv_mem F Q hQF
  have hCF : ∀ i j, C' i j ∈ F := fun i j => F.algebraMap_mem (C i j)
  have hBF : ∀ i j, B'.val i j ∈ F := by
    intro i j
    rw [entry_expansion C B' i j]
    exact F.sum_mem fun b _ => F.mul_mem (hx (Sum.inr b)) (F.algebraMap_mem _)
  have hAeq : A = (Q : Matrix (Fin n) (Fin n) L) * C' * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    rw [← hQ, mul_assoc, Units.mul_inv, mul_one]
  have hBeq : B = (Q : Matrix (Fin n) (Fin n) L) * B'.val * (↑Q⁻¹ : Matrix (Fin n) (Fin n) L) := by
    change B = (Q : Matrix (Fin n) (Fin n) L) *
      ((↑Q⁻¹ : Matrix (Fin n) (Fin n) L) * B * (Q : Matrix (Fin n) (Fin n) L)) *
      (↑Q⁻¹ : Matrix (Fin n) (Fin n) L)
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
  refine ⟨F, ?_, ?_, ?_⟩
  · simpa only [hκ] using hFp
  · rw [hAeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hCF) hQiF
  · rw [hBeq]
    exact MatrixSubfield.mul_mem F _ _ (MatrixSubfield.mul_mem F _ _ hQF hBF) hQiF

end PermanentBorder.CommutingPairs

end OAI
