import Mathlib
import OAI.RepresentationTheory.RestrictedTilting.PlaneCharts

namespace OAI

/-! Polynomial additive actions and associated polynomial sections. -/

noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace FiberFunctorProof
section
variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B]

lemma map_aeval_polynomial (f : A →ₐ[k] B) (a : A) (p : Polynomial k) :
    f (Polynomial.aeval a p) = Polynomial.aeval (f a) p := by
  have h : f.comp (Polynomial.aeval a) = Polynomial.aeval (f a) := by
    ext
    simp
  exact AlgHom.congr_fun h p
end

section
variable {k ι : Type*} [Field k] [Infinite k] [Fintype ι] [DecidableEq ι]

 
noncomputable def polynomialMatrixEval (P : Matrix ι ι (Polynomial k))
    {A : Type*} [CommRing A] [Algebra k A] (t : A) : Matrix ι ι A :=
  fun i j => Polynomial.aeval t (P i j)

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma polynomialMatrixEval_map (P : Matrix ι ι (Polynomial k))
    {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (f : A →ₐ[k] B) (t : A) :
    (polynomialMatrixEval P t).map f = polynomialMatrixEval P (f t) := by
  ext i j
  exact map_aeval_polynomial f t (P i j)

omit [DecidableEq ι] in
 

theorem polynomialMatrixEval_add (P : Matrix ι ι (Polynomial k))
    (hP : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)
    {A : Type*} [CommRing A] [Algebra k A] (s t : A) :
    polynomialMatrixEval P (s+t) = polynomialMatrixEval P s * polynomialMatrixEval P t := by
  let X : Fin 2 → MvPolynomial (Fin 2) k := MvPolynomial.X
  have h : polynomialMatrixEval P (X 0 + X 1) =
      polynomialMatrixEval P (X 0) * polynomialMatrixEval P (X 1) := by
    apply Matrix.ext
    intro i j
    apply MvPolynomial.funext
    intro a
    change MvPolynomial.aeval a _ = MvPolynomial.aeval a _
    simp only [polynomialMatrixEval, Matrix.mul_apply, map_sum, map_mul,
      map_aeval_polynomial, map_add, X, MvPolynomial.aeval_X]
    exact congrArg (fun Q : Matrix ι ι k => Q i j) (hP (a 0) (a 1))
  have he := congrArg (fun Q : Matrix ι ι (MvPolynomial (Fin 2) k) =>
    Q.map (MvPolynomial.aeval ![s,t])) h
  simpa only [polynomialMatrixEval_map, map_add, X, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.map_mul] using he

omit [Infinite k] [Fintype ι] in
lemma polynomialMatrixEval_zero (P : Matrix ι ι (Polynomial k))
    (hP : polynomialMatrixEval P (0 : k) = 1)
    (A : Type*) [CommRing A] [Algebra k A] :
    polynomialMatrixEval P (0 : A) = 1 := by
  have he := congrArg (fun Q : Matrix ι ι k => Q.map (algebraMap k A)) hP
  have hm (i j : ι) : algebraMap k A (polynomialMatrixEval P (0 : k) i j) =
      polynomialMatrixEval P (0 : A) i j := by
    simp [polynomialMatrixEval, Polynomial.aeval_def]
  apply Matrix.ext
  intro i j
  have heij := congrArg (fun Q : Matrix ι ι A => Q i j) he
  rw [Matrix.map_apply, hm] at heij
  simpa [Matrix.map_apply, Matrix.one_apply] using heij

 

noncomputable def polynomialAdditiveRepresentation
    (P : Matrix ι ι (Polynomial k))
    (h0 : polynomialMatrixEval P (0 : k) = 1)
    (hadd : ∀ s t : k, polynomialMatrixEval P (s+t) =
      polynomialMatrixEval P s * polynomialMatrixEval P t)
    (A : Type*) [CommRing A] [Algebra k A] :
    Multiplicative A →* Matrix ι ι A where
  toFun t := polynomialMatrixEval P t.toAdd
  map_one' := polynomialMatrixEval_zero P h0 A
  map_mul' s t := polynomialMatrixEval_add P hadd s.toAdd t.toAdd

end

section
universe u
variable (k : Type u) [Field k] [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma additive_rep_apply_add (s t : k) (v : ι → k) :
    ρ (Multiplicative.ofAdd (s+t)) v =
      ρ (Multiplicative.ofAdd s) (ρ (Multiplicative.ofAdd t) v) := by
  change ρ (Multiplicative.ofAdd s * Multiplicative.ofAdd t) v = _
  rw [map_mul]
  rfl

noncomputable def associatedLocalExpression (P : Matrix ι ι (Polynomial k))
    (a : Fin 2) (f : ι → planeCoordinateChart k a) (i : ι) :
    regularCoordinateLocalization k a :=
  ∑ j, Polynomial.aeval
    (-(algebraMap (regularSL2Functions k) (regularCoordinateLocalization k a)
      (regularEntry k a 1)) * regularCoordinateInverse k a) (P i j) *
        planeChartPullback k a (f j)

omit [Infinite k] in
lemma associatedLocalExpression_evaluation (P : Matrix ι ι (Polynomial k))
    (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
    (a : Fin 2) (f : ι → planeCoordinateChart k a) (g : regularTorusPoints k) :
    (fun i => regularLocalizationEvaluation k a (associatedLocalExpression k ι P a f i) g) =
      ρ (Multiplicative.ofAdd (-(g.val a 1 / g.val a 0)))
        (fun j => planeChartEvaluation k a (f j) (regularToPlaneTorus k g)) := by
  have h := LinearMap.toMatrix'_mulVec
    (ρ (Multiplicative.ofAdd (-(g.val a 1 / g.val a 0))))
    (fun j => planeChartEvaluation k a (f j) (regularToPlaneTorus k g))
  rw [← hP] at h
  rw [← h]
  funext i
  let ev : regularCoordinateLocalization k a →ₐ[k] k :=
    (Pi.evalAlgHom k _ g).comp (regularLocalizationEvaluation k a)
  change ev (associatedLocalExpression k ι P a f i) = _
  simp only [associatedLocalExpression, map_sum, map_mul,
    map_aeval_polynomial (k := k) (A := regularCoordinateLocalization k a) (B := k) ev,
    map_neg]
  change (∑ j, Polynomial.aeval
    (-(regularLocalizationEvaluation k a
      (algebraMap (regularSL2Functions k) (regularCoordinateLocalization k a)
        (regularEntry k a 1)) g) *
      regularLocalizationEvaluation k a (regularCoordinateInverse k a) g) (P i j) *
        regularLocalizationEvaluation k a (planeChartPullback k a (f j)) g) = _
  rw [regularLocalizationEvaluation_algebraMap]
  change (∑ j, Polynomial.aeval
    (-(regularEntry k a 1).val g.val *
      regularLocalizationEvaluation k a (regularCoordinateInverse k a) g) (P i j) *
        regularLocalizationEvaluation k a (planeChartPullback k a (f j)) g) = _
  simp only [regularEntry_apply, regularCoordinateInverse_evaluation,
    planeChartPullback_evaluation, Matrix.mulVec, dotProduct, polynomialMatrixEval,
    div_eq_mul_inv, neg_mul]

noncomputable def associatedTorusValue (f : ι → planeCoordinateChart k 0)
    (g : regularTorusPoints k) : ι → k :=
  ρ (Multiplicative.ofAdd (-(g.val 0 1 / g.val 0 0)))
    (fun j => planeChartEvaluation k 0 (f j) (regularToPlaneTorus k g))

omit [Infinite k] in
lemma associatedChartPair_local_compatible
    (P : Matrix ι ι (Polynomial k))
    (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
    (f₀ : ι → planeCoordinateChart k 0) (f₁ : ι → planeCoordinateChart k 1)
    (hf : ∀ x : planeTorusPoints k,
      (fun j => planeChartEvaluation k 1 (f₁ j) x) =
        ρ (Multiplicative.ofAdd ((x.val 0 * x.val 1)⁻¹))
          (fun j => planeChartEvaluation k 0 (f₀ j) x)) (g : regularTorusPoints k) :
    (fun i => regularLocalizationEvaluation k 1 (associatedLocalExpression k ι P 1 f₁ i) g) =
      associatedTorusValue k ι ρ f₀ g := by
  rw [associatedLocalExpression_evaluation k ι ρ P hP, hf,
    ← additive_rep_apply_add]
  unfold associatedTorusValue
  congr 2
  change -(g.val 1 1 / g.val 1 0) + (g.val 0 0 * g.val 1 0)⁻¹ =
    -(g.val 0 1 / g.val 0 0)
  have hd : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.val.property
  field_simp [g.property 0, g.property 1]
  linear_combination -hd

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma secondColumn_unipotent_mul (g : SL2 k) (t : k) (i : Fin 2) :
    (g * unipotent k t) i 1 = g i 0 * t + g i 1 := by
  change (((g : Matrix (Fin 2) (Fin 2) k) *
    (unipotent k t : Matrix (Fin 2) (Fin 2) k)) i 1) = _
  simp [Matrix.mul_apply, Fin.sum_univ_two, unipotent]

noncomputable def regularTorusRightUnipotent (g : regularTorusPoints k) (t : k) :
    regularTorusPoints k :=
  ⟨g.val * unipotent k t, by intro i; rw [firstColumn_unipotent_mul]; exact g.property i⟩

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma associatedTorusValue_unipotent (f : ι → planeCoordinateChart k 0)
    (g : regularTorusPoints k) (t : k) :
    associatedTorusValue k ι ρ f (regularTorusRightUnipotent k g t) =
      ρ (Multiplicative.ofAdd (-t)) (associatedTorusValue k ι ρ f g) := by
  have hx : regularToPlaneTorus k (regularTorusRightUnipotent k g t) =
      regularToPlaneTorus k g := by
    apply Subtype.ext
    funext i
    exact firstColumn_unipotent_mul k g.val t i
  unfold associatedTorusValue
  rw [hx, ← additive_rep_apply_add]
  apply congrArg (fun s : k => ρ (Multiplicative.ofAdd s)
    (fun j => planeChartEvaluation k 0 (f j) (regularToPlaneTorus k g)))
  change -((g.val * unipotent k t) 0 1 / (g.val * unipotent k t) 0 0) = _
  rw [secondColumn_unipotent_mul, firstColumn_unipotent_mul]
  field_simp [g.property 0]
  ring

noncomputable def regularVectorCombination (L : (ι → k) →ₗ[k] (ι → k))
    (f : ι → regularSL2Functions k) (i : ι) : regularSL2Functions k :=
  ∑ j, (LinearMap.toMatrix' L i j) • f j

omit [Infinite k] in
lemma regularVectorCombination_evaluation (L : (ι → k) →ₗ[k] (ι → k))
    (f : ι → regularSL2Functions k) (g : SL2 k) :
    regularVectorEvaluation k ι g (regularVectorCombination k ι L f) =
      L (regularVectorEvaluation k ι g f) := by
  rw [← LinearMap.toMatrix'_mulVec L]
  funext i
  change (Subalgebra.val (regularSL2Functions k)
    (∑ j, (LinearMap.toMatrix' L i j) • f j)) g = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Matrix.mulVec, dotProduct]
  rfl

 

theorem associatedChartPair_glue
    (P : Matrix ι ι (Polynomial k))
    (hP : ∀ t : k, polynomialMatrixEval P t = LinearMap.toMatrix' (ρ (Multiplicative.ofAdd t)))
    (f₀ : ι → planeCoordinateChart k 0) (f₁ : ι → planeCoordinateChart k 1)
    (hf : ∀ x : planeTorusPoints k,
      (fun j => planeChartEvaluation k 1 (f₁ j) x) =
        ρ (Multiplicative.ofAdd ((x.val 0 * x.val 1)⁻¹))
          (fun j => planeChartEvaluation k 0 (f₀ j) x)) :
    ∃ f : associatedSectionsSubmodule k ι ρ,
      associatedXChart k ι ρ f = f₀ ∧ associatedYChart k ι ρ f = f₁ := by
  have hg (i : ι) : ∃ f : regularSL2Functions k,
      regularTorusRestriction k f = fun g => associatedTorusValue k ι ρ f₀ g i := by
    apply regularTorus_glue k _ (associatedLocalExpression k ι P 0 f₀ i)
      (associatedLocalExpression k ι P 1 f₁ i)
    · funext g
      exact congrFun (associatedLocalExpression_evaluation k ι ρ P hP 0 f₀ g) i
    · funext g
      exact congrFun (associatedChartPair_local_compatible k ι ρ P hP f₀ f₁ hf g) i
  choose f hfg using hg
  have hev (g : regularTorusPoints k) : regularVectorEvaluation k ι g.val f =
      associatedTorusValue k ι ρ f₀ g := by
    funext i
    exact congrFun (hfg i) g
  have hmem : f ∈ associatedSectionsSubmodule k ι ρ := by
    intro g t
    funext i
    have hz : regularRightTranslation k (unipotent k t) (f i) -
        regularVectorCombination k ι (ρ (Multiplicative.ofAdd (-t))) f i = 0 := by
      apply regularSL2_torus_dense k
      intro h ha hc
      let h' : regularTorusPoints k := ⟨h, by intro j; fin_cases j; exact ha; exact hc⟩
      have he := associatedTorusValue_unipotent k ι ρ f₀ h' t
      rw [← hev, ← hev] at he
      have he' := congrFun he i
      change (f i).val (h * unipotent k t) = _ at he'
      change (f i).val (h * unipotent k t) -
        (regularVectorCombination k ι (ρ (Multiplicative.ofAdd (-t))) f i).val h = 0
      rw [he']
      exact sub_eq_zero.mpr
        (congrFun (regularVectorCombination_evaluation k ι
          (ρ (Multiplicative.ofAdd (-t))) f h) i).symm
    have he := congrArg (fun a : regularSL2Functions k => a.val g) (sub_eq_zero.mp hz)
    change (f i).val (g * unipotent k t) = _ at he
    exact he.trans (congrFun (regularVectorCombination_evaluation k ι
      (ρ (Multiplicative.ofAdd (-t))) f g) i)
  let F : associatedSectionsSubmodule k ι ρ := ⟨f,hmem⟩
  have hx : associatedXChart k ι ρ F = f₀ := by
    funext i
    apply planeChartEvaluation_injective k 0
    funext x
    have he := hev ⟨planeXSection k x, by
      intro j
      fin_cases j <;> simpa [planeXSection] using x.property _⟩
    have hx' : regularToPlaneTorus k ⟨planeXSection k x, by
        intro j; fin_cases j <;> simpa [planeXSection] using x.property _⟩ = x := by
      apply Subtype.ext
      funext j
      fin_cases j <;> simp [regularToPlaneTorus, planeXSection]
    unfold associatedTorusValue at he
    rw [hx'] at he
    change regularVectorEvaluation k ι (planeXSection k x) f =
      ρ (Multiplicative.ofAdd (-(0 / x.val 0)))
        (fun j => planeChartEvaluation k 0 (f₀ j) x) at he
    simp only [zero_div, neg_zero] at he
    change regularVectorEvaluation k ι (planeXSection k x) f =
      ρ 1 (fun j => planeChartEvaluation k 0 (f₀ j) x) at he
    rw [map_one] at he
    exact (congrFun (associatedXChart_evaluation k ι ρ F x) i).trans (congrFun he i)
  refine ⟨F,hx,?_⟩
  funext i
  apply planeChartEvaluation_injective k 1
  funext x
  have he := associatedCharts_transition k ι ρ F x
  rw [hx, ← hf x] at he
  exact congrFun he i

end

universe u
variable (k : Type u) [Field k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

noncomputable instance regularPlaneAlgebra :
    Algebra (MvPolynomial (Fin 2) k) (regularSL2Functions k) :=
  (regularPlane k).toRingHom.toAlgebra

instance regularPlaneScalarTower :
    IsScalarTower k (MvPolynomial (Fin 2) k) (regularSL2Functions k) :=
  IsScalarTower.of_algHom (regularPlane k)

lemma regularPlane_algebraMap (P : MvPolynomial (Fin 2) k) :
    algebraMap (MvPolynomial (Fin 2) k) (regularSL2Functions k) P = regularPlane k P := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma regularVector_plane_smul (P : MvPolynomial (Fin 2) k)
    (f : ι → regularSL2Functions k) (g : SL2 k) :
    regularVectorEvaluation k ι g (P • f) =
      MvPolynomial.eval (fun i => g i 0) P • regularVectorEvaluation k ι g f := by
  funext i
  change (P • f i).val g = _
  rw [Algebra.smul_def, regularPlane_algebraMap]
  change (regularPlane k P).val g * (f i).val g = _
  rw [regularPlane_evaluation]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma associatedSections_plane_smul_mem (P : MvPolynomial (Fin 2) k)
    (f : ι → regularSL2Functions k) (hf : f ∈ associatedSectionsSubmodule k ι ρ) :
    P • f ∈ associatedSectionsSubmodule k ι ρ := by
  intro g t
  rw [regularVector_plane_smul, regularVector_plane_smul, hf, map_smul]
  simp only [firstColumn_unipotent_mul]

noncomputable def associatedPolynomialSections :
    Submodule (MvPolynomial (Fin 2) k) (ι → regularSL2Functions k) where
  carrier := associatedSectionsSubmodule k ι ρ
  zero_mem' := (associatedSectionsSubmodule k ι ρ).zero_mem
  add_mem' := (associatedSectionsSubmodule k ι ρ).add_mem
  smul_mem' := associatedSections_plane_smul_mem k ι ρ

noncomputable instance associatedSectionsAddCommGroup :
    AddCommGroup (associatedSectionsSubmodule k ι ρ) :=
  Submodule.addCommGroup (associatedSectionsSubmodule k ι ρ)

noncomputable instance (priority := 2000) associatedSectionsPolynomialSMul :
    SMul (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) :=
  (Submodule.module (associatedPolynomialSections k ι ρ)).toSMul

noncomputable instance (priority := 2000) associatedSectionsPolynomialModule :
    Module (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) :=
  Submodule.module (associatedPolynomialSections k ι ρ)

instance associatedSectionsScalarTower :
    IsScalarTower k (MvPolynomial (Fin 2) k) (associatedSectionsSubmodule k ι ρ) where
  smul_assoc a P f := Subtype.ext (smul_assoc a P f.val)

variable [Infinite k]
noncomputable def associatedXChartPolynomial :
    (associatedSectionsSubmodule k ι ρ) →ₗ[MvPolynomial (Fin 2) k]
      (ι → planeCoordinateChart k 0) where
  toFun := associatedXChart k ι ρ
  map_add' := (associatedXChart k ι ρ).map_add
  map_smul' := by
    intro P f
    funext i
    apply planeChartEvaluation_injective k 0
    funext x
    have he := congrFun (associatedXChart_evaluation k ι ρ (P • f) x) i
    change _ = _ at he
    rw [show (P • f).val = P • f.val from rfl, regularVector_plane_smul] at he
    rw [he]
    change MvPolynomial.eval (fun j => (planeXSection k x) j 0) P *
      regularVectorEvaluation k ι (planeXSection k x) f.val i =
      planeChartEvaluation k 0 (P • associatedXChart k ι ρ f i) x
    rw [Algebra.smul_def, map_mul, planeChartEvaluation_algebraMap]
    change _ = planeTorusEvaluation k P x *
      planeChartEvaluation k 0 (associatedXChart k ι ρ f i) x
    rw [planeTorusEvaluation_apply, congrFun (associatedXChart_evaluation k ι ρ f x) i]
    congr 2
    apply congrArg MvPolynomial.eval
    funext j
    fin_cases j <;> simp [planeXSection]

end FiberFunctorProof

 

open scoped TensorProduct
end

end OAI
