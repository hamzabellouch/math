import OAI.Algebra.Determinantal.PencilSeparability

namespace OAI

namespace PermanentBorder.GradientAlgebra

open Finset

section CharacteristicTwo
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CharP R 2]

theorem permanent_eq_det (M : Matrix ι ι R) : M.permanent = M.det := by
  rw [Matrix.permanent, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simp [h]
  · simp [h, CharTwo.neg_eq]
end CharacteristicTwo

section Derivative
variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable [DecidableEq ι]

theorem derivation_prod (D : Derivation R A A) (s : Finset ι) (f : ι → A) :
    D (∏ i ∈ s, f i) = ∑ i ∈ s, (∏ j ∈ s.erase i, f j) * D (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, D.leibniz, ih]
    simp only [smul_eq_mul, Finset.sum_insert ha, Finset.erase_insert ha,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := by
      intro h
      exact ha (h ▸ hi)
    rw [Finset.erase_insert_of_ne hai, Finset.prod_insert]
    · ring
    · exact Finset.notMem_mono (Finset.erase_subset _ _) ha

variable [Fintype ι]

theorem derivation_det_updateCol (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, (M.updateCol j (fun i => D (M i j))).det := by
  rw [Matrix.det_apply, map_sum]
  simp only [Units.smul_def, map_zsmul, derivation_prod]
  simp only [Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def]
  congr 1
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  rw [Matrix.updateCol_self]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact (Matrix.updateCol_ne (Finset.ne_of_mem_erase hi)).symm

theorem derivation_det (D : Derivation R A A) (M : Matrix ι ι A) :
    D M.det = ∑ j, ∑ i, M.adjugate j i * D (M i j) := by
  rw [derivation_det_updateCol]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl
end Derivative

section Pencil
open MvPolynomial
variable {R ι σ τ : Type*} [CommRing R]

noncomputable def coefficientPart (e : τ →₀ ℕ) :
    MvPolynomial σ (MvPolynomial τ R) →+ MvPolynomial σ R where
  toFun := AddMonoidAlgebra.map (coeffAddMonoidHom e)
  map_zero' := by ext; simp
  map_add' := AddMonoidAlgebra.map_add _

@[simp] theorem coeff_coefficientPart (e : τ →₀ ℕ)
    (P : MvPolynomial σ (MvPolynomial τ R)) (d : σ →₀ ℕ) :
    (coefficientPart e P).coeff d = (P.coeff d).coeff e := rfl

theorem coefficientPart_pderiv (e : τ →₀ ℕ)
    (P : MvPolynomial σ (MvPolynomial τ R)) (i : σ) :
    coefficientPart e (pderiv i P) = pderiv i (coefficientPart e P) := by
  ext d
  simp only [coeff_coefficientPart, coeff_pderiv]
  rw [show (d i + 1 : MvPolynomial τ R) = C (d i + 1 : R) by simp]
  rw [mul_comm, coeff_C_mul, mul_comm]

variable [Fintype ι] [DecidableEq ι]

noncomputable def genericPencil (θ : ι → R) :
    Matrix ι ι (MvPolynomial (ι × ι) (MvPolynomial (Fin 3) R)) :=
  fun i j =>
    C (if i = j then X 0 + C (θ i) * X 1 else 0) + C (X 2) * X (i,j)

omit [Fintype ι] in
@[simp] theorem pderiv_genericPencil (θ : ι → R) (i j a b : ι) :
    pderiv (a,b) (genericPencil θ i j) =
      if (a,b) = (i,j) then C (X (2 : Fin 3)) else 0 := by
  classical
  simp [genericPencil, pderiv_X, Pi.single_apply, eq_comm]

theorem pderiv_det_genericPencil (θ : ι → R) (a b : ι) :
    pderiv (a,b) (genericPencil θ).det =
      C (X (2 : Fin 3)) * (genericPencil θ).adjugate b a := by
  rw [derivation_det]
  simp only [pderiv_genericPencil, Prod.mk.injEq]
  rw [Finset.sum_eq_single b]
  · simp [mul_comm]
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    simp [Ne.symm hj]
  · simp
end Pencil

section CoefficientCalculus
open MvPolynomial
variable {R σ τ : Type*} [CommRing R]

theorem coefficientPart_C_X_mul (e : τ →₀ ℕ) (i : τ)
    (P : MvPolynomial σ (MvPolynomial τ R)) :
    coefficientPart (Finsupp.single i 1 + e) (C (X i) * P) =
      coefficientPart e P := by
  ext d
  simp only [coeff_coefficientPart, coeff_C_mul, coeff_X_mul]

@[simp] theorem coefficientPart_monomial (e : τ →₀ ℕ) (d : σ →₀ ℕ)
    (a : MvPolynomial τ R) :
    coefficientPart e (monomial d a) = monomial d (a.coeff e) := by
  classical
  ext d'
  simp only [coeff_coefficientPart, coeff_monomial]
  split_ifs <;> simp_all

theorem eval_coefficientPart (e : τ →₀ ℕ) (x : σ → R)
    (P : MvPolynomial σ (MvPolynomial τ R)) :
    eval x (coefficientPart e P) =
      (eval (fun i => C (x i)) P).coeff e := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial d a =>
    simp only [coefficientPart_monomial, eval_monomial]
    have hp : d.prod (fun i n => (C (x i) : MvPolynomial τ R) ^ n) =
        C (d.prod (fun i n => x i ^ n)) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hp, mul_comm a, coeff_C_mul, mul_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def fixedPencil (θ : ι → R) (x : Matrix ι ι R) :
    Matrix ι ι (MvPolynomial (Fin 3) R) := fun i j =>
      (if i = j then X 0 + C (θ i) * X 1 else 0) + X 2 * C (x i j)

theorem eval_genericPencil (θ : ι → R) (x : Matrix ι ι R) :
    (eval (fun ij : ι × ι => C (x ij.1 ij.2))).mapMatrix (genericPencil θ) =
      fixedPencil θ x := by
  ext i j
  simp [genericPencil, fixedPencil]

theorem gradient_coefficient_identity (θ : ι → R) (x : Matrix ι ι R)
    (e : Fin 3 →₀ ℕ) (a b : ι) :
    eval (fun ij : ι × ι => x ij.1 ij.2)
      (pderiv (a,b) (coefficientPart (Finsupp.single 2 1 + e)
        (genericPencil θ).det)) =
      ((fixedPencil θ x).adjugate b a).coeff e := by
  rw [← coefficientPart_pderiv, pderiv_det_genericPencil, coefficientPart_C_X_mul,
    eval_coefficientPart]
  have h := congrArg (fun M : Matrix ι ι (MvPolynomial (Fin 3) R) => M b a)
    ((eval (fun ij : ι × ι => C (x ij.1 ij.2))).map_adjugate (genericPencil θ))
  change eval (fun ij : ι × ι => C (x ij.1 ij.2))
    ((genericPencil θ).adjugate b a) = _ at h
  rw [h, eval_genericPencil]

theorem gradient_zero_iff_adjugate_coefficient (θ : ι → R) (x : Matrix ι ι R)
    (e : Fin 3 →₀ ℕ) :
    (∀ a b, eval (fun ij : ι × ι => x ij.1 ij.2)
      (pderiv (a,b) (coefficientPart (Finsupp.single 2 1 + e)
        (genericPencil θ).det)) = 0) ↔
    ∀ i j, ((fixedPencil θ x).adjugate i j).coeff e = 0 := by
  simp_rw [gradient_coefficient_identity]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩
end CoefficientCalculus

section AffinePencil
open MvPolynomial
variable {R σ : Type*} [CommRing R]

noncomputable def biCoefficientPart (a b : ℕ) :
    MvPolynomial σ (Polynomial (Polynomial R)) →+ MvPolynomial σ R where
  toFun := AddMonoidAlgebra.map
    ((Polynomial.lcoeff R b).toAddMonoidHom.comp
      (Polynomial.lcoeff (Polynomial R) a).toAddMonoidHom)
  map_zero' := by ext; simp
  map_add' := AddMonoidAlgebra.map_add _

@[simp] theorem coeff_biCoefficientPart (a b : ℕ)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) (d : σ →₀ ℕ) :
    (biCoefficientPart a b P).coeff d = ((P.coeff d).coeff a).coeff b := rfl

theorem biCoefficientPart_pderiv (a b : ℕ)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) (i : σ) :
    biCoefficientPart a b (pderiv i P) = pderiv i (biCoefficientPart a b P) := by
  ext d
  simp only [coeff_biCoefficientPart, coeff_pderiv]
  simp only [← Nat.cast_add_one, Polynomial.coeff_mul_natCast]

@[simp] theorem biCoefficientPart_monomial (a b : ℕ) (d : σ →₀ ℕ)
    (c : Polynomial (Polynomial R)) :
    biCoefficientPart a b (monomial d c) = monomial d ((c.coeff a).coeff b) := by
  classical
  ext d'
  simp only [coeff_biCoefficientPart, coeff_monomial]
  split_ifs <;> simp_all

theorem eval_biCoefficientPart (a b : ℕ) (x : σ → R)
    (P : MvPolynomial σ (Polynomial (Polynomial R))) :
    eval x (biCoefficientPart a b P) =
      ((eval (fun i => Polynomial.C (Polynomial.C (x i))) P).coeff a).coeff b := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hp hq => simp [hp, hq]
  | monomial d c =>
    simp only [biCoefficientPart_monomial, eval_monomial]
    have hp : d.prod (fun i n => (Polynomial.C (Polynomial.C (x i))) ^ n) =
        Polynomial.C (Polynomial.C (d.prod (fun i n => x i ^ n))) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hp, mul_comm c, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, mul_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def genericAffinePencil (θ : ι → R) :
    Matrix ι ι (MvPolynomial (ι × ι) (Polynomial (Polynomial R))) :=
  fun i j => C (if i = j then Polynomial.X + Polynomial.C
    (Polynomial.X * Polynomial.C (θ i)) else 0) + X (i,j)

noncomputable def fixedAffinePencil (θ : ι → R) (x : Matrix ι ι R) :
    Matrix ι ι (Polynomial (Polynomial R)) := fun i j =>
      (if i = j then Polynomial.X + Polynomial.C
        (Polynomial.X * Polynomial.C (θ i)) else 0) + Polynomial.C (Polynomial.C (x i j))

omit [Fintype ι] in
@[simp] theorem pderiv_genericAffinePencil (θ : ι → R) (i j a b : ι) :
    pderiv (a,b) (genericAffinePencil θ i j) = if (a,b) = (i,j) then 1 else 0 := by
  classical
  simp [genericAffinePencil, pderiv_X, Pi.single_apply, eq_comm]

theorem pderiv_det_genericAffinePencil (θ : ι → R) (a b : ι) :
    pderiv (a,b) (genericAffinePencil θ).det = (genericAffinePencil θ).adjugate b a := by
  classical
  have hd := derivation_det (pderiv (a,b)) (genericAffinePencil θ)
  rw [hd]
  simp only [pderiv_genericAffinePencil, Prod.mk.injEq]
  rw [Finset.sum_eq_single b]
  · simp
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    simp [Ne.symm hj]
  · simp

theorem eval_genericAffinePencil (θ : ι → R) (x : Matrix ι ι R) :
    (eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))).mapMatrix
      (genericAffinePencil θ) = fixedAffinePencil θ x := by
  ext i j
  simp [genericAffinePencil, fixedAffinePencil]

noncomputable def affineSelector (θ : ι → R) (q : ℕ) : MvPolynomial (ι × ι) R :=
  biCoefficientPart q q (genericAffinePencil θ).permanent

theorem gradient_affineSelector [CharP R 2] (θ : ι → R)
    (x : Matrix ι ι R) (q : ℕ) (a b : ι) :
    eval (fun ij : ι × ι => x ij.1 ij.2) (pderiv (a,b) (affineSelector θ q)) =
      (((fixedAffinePencil θ x).adjugate b a).coeff q).coeff q := by
  classical
  have hp := permanent_eq_det (genericAffinePencil θ)
  rw [affineSelector, hp, ← biCoefficientPart_pderiv,
    pderiv_det_genericAffinePencil, eval_biCoefficientPart]
  have h := congrArg (fun M : Matrix ι ι (Polynomial (Polynomial R)) => M b a)
    ((eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))).map_adjugate
      (genericAffinePencil θ))
  change eval (fun ij : ι × ι => Polynomial.C (Polynomial.C (x ij.1 ij.2)))
    ((genericAffinePencil θ).adjugate b a) = _ at h
  rw [h, eval_genericAffinePencil]
end AffinePencil

end PermanentBorder.GradientAlgebra

namespace PermanentBorder.Selector
open MvPolynomial
section
variable {R σ : Type*} [CommRing R]

noncomputable def bivariateToNested : MvPolynomial (Fin 2) R →+* Polynomial (Polynomial R) :=
  (Polynomial.mapRingHom (uniqueAlgEquiv R (Fin 1)).toRingHom).comp
    (finSuccEquiv R 1).toRingHom

lemma bivariateToNested_coeff (P : MvPolynomial (Fin 2) R) (q : ℕ) :
    ((bivariateToNested P).coeff q).coeff q = P.coeff (countIndex q) := by
  change ((Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 P)).coeff q).coeff q = _
  rw [Polynomial.coeff_map]
  change ((uniqueAlgEquiv R (Fin 1)) ((finSuccEquiv R 1 P).coeff q)).coeff q = _
  rw [coeff_uniqueAlgEquiv, finSuccEquiv_coeff_coeff]
  congr 1
  ext i
  fin_cases i
  · simp [countIndex]
  · change (Finsupp.cons q (Finsupp.single (0 : Fin 1) q))
      (Fin.succ (0 : Fin 1)) = q
    change (Finsupp.single (0 : Fin 1) q) 0 = q
    simp

@[simp] lemma bivariateToNested_C (r : R) :
    bivariateToNested (C r) = Polynomial.C (Polynomial.C r) := by
  simp [bivariateToNested, finSuccEquiv_apply]

@[simp] lemma bivariateToNested_X_zero :
    bivariateToNested (X (0 : Fin 2) : MvPolynomial (Fin 2) R) = Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 (X 0)) = _
  rw [finSuccEquiv_X_zero, Polynomial.map_X]

@[simp] lemma bivariateToNested_X_one :
    bivariateToNested (X (1 : Fin 2) : MvPolynomial (Fin 2) R) =
      Polynomial.C Polynomial.X := by
  change Polynomial.map (uniqueAlgEquiv R (Fin 1)).toRingHom
    (finSuccEquiv R 1 (X (Fin.succ (0 : Fin 1)))) = _
  rw [finSuccEquiv_X_succ, Polynomial.map_C]
  congr 1
  simp

lemma commAlgEquiv_coeff_coeff (P : MvPolynomial (Fin 2) (MvPolynomial σ R))
    (a : Fin 2 →₀ ℕ) (b : σ →₀ ℕ) :
    ((commAlgEquiv R (Fin 2) σ P).coeff b).coeff a = (P.coeff a).coeff b := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [hP,hQ]
  | monomial d c =>
    induction c using MvPolynomial.induction_on' with
    | add c e hc he => simp [map_add, hc,he]
    | monomial e c =>
      change ((AddMonoidAlgebra.commAlgEquiv R
        (AddMonoidAlgebra.single d (AddMonoidAlgebra.single e c))).coeff b).coeff a = _
      rw [AddMonoidAlgebra.commAlgEquiv_single_single]
      change ((monomial e (monomial d c)).coeff b).coeff a = _
      simp only [coeff_monomial]
      split_ifs <;> simp_all

noncomputable def interchangeBivariate :
    MvPolynomial (Fin 2) (MvPolynomial σ R) →+*
      MvPolynomial σ (Polynomial (Polynomial R)) :=
  (map bivariateToNested).comp (commAlgEquiv R (Fin 2) σ).toRingHom

lemma biCoefficientPart_interchange (P : MvPolynomial (Fin 2) (MvPolynomial σ R)) (q : ℕ) :
    GradientAlgebra.biCoefficientPart q q (interchangeBivariate P) = P.coeff (countIndex q) := by
  ext d
  rw [GradientAlgebra.coeff_biCoefficientPart]
  change (((map bivariateToNested (commAlgEquiv R (Fin 2) σ P)).coeff d).coeff q).coeff q = _
  rw [coeff_map,bivariateToNested_coeff,commAlgEquiv_coeff_coeff]

@[simp] lemma interchangeBivariate_C_X (i : σ) :
    interchangeBivariate (C (X i) : MvPolynomial (Fin 2) (MvPolynomial σ R)) = X i := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_C_C (r : R) :
    interchangeBivariate (C (C r) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C (Polynomial.C (Polynomial.C r)) := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_X_zero :
    interchangeBivariate (X (0 : Fin 2) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C Polynomial.X := by
  simp [interchangeBivariate]

@[simp] lemma interchangeBivariate_X_one :
    interchangeBivariate (X (1 : Fin 2) : MvPolynomial (Fin 2) (MvPolynomial σ R)) =
      C (Polynomial.C (Polynomial.X : Polynomial R)) := by
  simp [interchangeBivariate]
end

lemma diagonalCoefficient_eq_affineSelector {R I : Type*} [CommRing R]
    [Fintype I] [DecidableEq I] (θ : I → R) (q : ℕ) :
    diagonalCoefficient (Matrix.of fun i j => (X (i,j) : MvPolynomial (I×I) R))
      (fun i => C (θ i)) q = GradientAlgebra.affineSelector θ q := by
  classical
  unfold diagonalCoefficient GradientAlgebra.affineSelector
  rw [← biCoefficientPart_interchange]
  congr 1
  unfold Matrix.permanent
  simp only [map_sum,map_prod]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.prod_congr rfl
  intro i _
  simp only [Matrix.add_apply,Matrix.of_apply,Matrix.diagonal_apply,
    GradientAlgebra.genericAffinePencil]
  split_ifs
  · simp only [map_add,map_mul,interchangeBivariate_C_X,interchangeBivariate_X_zero,
      interchangeBivariate_C_C,interchangeBivariate_X_one]
    simp only [← map_mul,← map_add]
    rw [add_comm]
    congr 2
    rw [mul_comm]
  · simp
end PermanentBorder.Selector

end OAI
