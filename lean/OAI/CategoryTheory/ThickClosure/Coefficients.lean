import OAI.CategoryTheory.ThickClosure.ActionDerived

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentDg
open CategoryTheory CategoryTheory.Limits
universe u
variable (R : Type u) [Ring R] (D : ℕ)
abbrev coefficientModule := HahnWilson.LaurentCriterion.coefficient R D

def coefficientConst (i : ℤ) (r : R) : (coefficientModule R D).X i := fun _ => r

def coefficientEval (i : ℤ) (h : (i : ZMod D) = 0) :
    (coefficientModule R D).X i →ₗ[R] R := LinearMap.proj (PLift.up h)

noncomputable def coefficientToPiece (i : ℤ) :
    (coefficientModule R D).X i →ₗ[R] LaurentPolynomial R := by
  classical
  exact if h : (i : ZMod D) = 0 then
    (AddMonoidAlgebra.lsingle ((i : ℤ) / (D:ℤ))).comp (coefficientEval R D i h) else 0

noncomputable def coefficientTo : total (coefficientModule R D) →ₗ[R] LaurentPolynomial R :=
  DirectSum.toModule R ℤ (LaurentPolynomial R) (coefficientToPiece R D)

lemma coefficientTo_inc (i : ℤ) (x : (coefficientModule R D).X i) :
    coefficientTo R D (inc (coefficientModule R D) i x) = coefficientToPiece R D i x := by
  simp [coefficientTo, inc]

noncomputable def coefficientFrom : LaurentPolynomial R →ₗ[R] total (coefficientModule R D) :=
  (Finsupp.linearCombination R (fun q : ℤ => inc (coefficientModule R D) ((D:ℤ)*q)
    (coefficientConst R D _ 1))).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

lemma coefficientFrom_single (q : ℤ) (r : R) :
    coefficientFrom R D (AddMonoidAlgebra.single q r) =
      inc (coefficientModule R D) ((D:ℤ)*q) (coefficientConst R D _ r) := by
  change (Finsupp.linearCombination R _) (Finsupp.single q r) = _
  rw [Finsupp.linearCombination_single]
  rw [← map_smul]
  congr 1
  change (fun _ : PLift ((((D:ℤ)*q : ℤ) : ZMod D) = 0) => r • (1:R)) = _
  funext h
  exact mul_one r

lemma coefficientTo_monomial (hD : 0 < D) (q : ℤ) (r : R) :
    coefficientTo R D (inc (coefficientModule R D) ((D:ℤ)*q) (coefficientConst R D _ r)) =
      AddMonoidAlgebra.single q r := by
  rw [coefficientTo_inc]
  have hc : (((D:ℤ)*q : ℤ) : ZMod D) = 0 := by simp
  have hD' : (D:ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  rw [coefficientToPiece, dite_eq_left hc]
  change AddMonoidAlgebra.single (((D:ℤ)*q) / (D:ℤ)) r = _
  rw [Int.mul_ediv_cancel_left _ hD']

lemma coefficientTo_from (hD : 0 < D) (a : LaurentPolynomial R) :
    coefficientTo R D (coefficientFrom R D a) = a := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single q r => rw [coefficientFrom_single, coefficientTo_monomial R D hD]

lemma coefficientFrom_to (hD : 0 < D) (z : total (coefficientModule R D)) :
    coefficientFrom R D (coefficientTo R D z) = z := by
  have he : (coefficientFrom R D).comp (coefficientTo R D) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro i
    ext x : 1
    change coefficientFrom R D (coefficientTo R D (inc (coefficientModule R D) i x)) =
      inc (coefficientModule R D) i x
    by_cases h : (i : ZMod D) = 0
    · obtain ⟨q, hq, hqu⟩ := (exponent_exists_unique hD 0 i).mp (by simpa using h.symm)
      have hq' : i = (D:ℤ)*q := by simpa using hq
      clear hq hqu
      subst i
      have hc : (((D:ℤ)*q : ℤ) : ZMod D) = 0 := by simp
      let r : R := x (PLift.up hc)
      have hx : x = coefficientConst R D _ r := by
        change x = (fun _ => r)
        funext h
        exact congrArg x (Subsingleton.elim _ _)
      rw [hx, coefficientTo_monomial R D hD, coefficientFrom_single]
    · have hx : x = 0 := by
        change x = (0 : PLift ((i:ZMod D) = 0) → R)
        funext a
        exact (h a.down).elim
      rw [hx]
      simp
  exact congrArg (fun f : total (coefficientModule R D) →ₗ[R] total (coefficientModule R D) => f z) he

noncomputable def coefficientEquiv (hD : 0 < D) :
    total (coefficientModule R D) ≃ₗ[R] LaurentPolynomial R :=
  LinearEquiv.ofLinearMap (coefficientTo R D) (coefficientFrom R D)
    (by apply LinearMap.ext; intro a; exact coefficientTo_from R D hD a)
    (by apply LinearMap.ext; intro z; exact coefficientFrom_to R D hD z)

lemma coefficient_power_const (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)) (r : R) :
    ((coefficientModule R D).power i j h).hom (coefficientConst R D i r) =
      coefficientConst R D j r := by
  have hh {a b : ZMod D} (h : a = b) :
      ((HahnWilson.PeriodicDual.cell R D 0).XIsoOfEq h).hom (fun _ => r) = fun _ => r := by
    subst b
    rfl
  exact hh h

lemma coefficient_act_const (q j : ℤ) (r s : R) :
    laurentRepresentation (coefficientModule R D) (AddMonoidAlgebra.single q r)
      (inc (coefficientModule R D) ((D:ℤ)*j) (coefficientConst R D _ s)) =
    inc (coefficientModule R D) ((D:ℤ)*(q+j)) (coefficientConst R D _ (r*s)) := by
  rw [laurentRepresentation_single, coefficient_power_const]
  have h : (D:ℤ)*j+(D:ℤ)*q = (D:ℤ)*(q+j) := by ring
  generalize (D:ℤ)*j+(D:ℤ)*q = a at *
  generalize (D:ℤ)*(q+j) = b at *
  subst b
  rfl

lemma coefficient_act_from (a b : LaurentPolynomial R) :
    laurentRepresentation (coefficientModule R D) a (coefficientFrom R D b) =
      coefficientFrom R D (a*b) := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [map_add, add_mul, map_add]
    exact congrArg₂ (·+·) ha ha'
  | single q r =>
    induction b using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' => simpa only [map_add, mul_add] using congrArg₂ (·+·) hb hb'
    | single j s =>
      rw [coefficientFrom_single, coefficient_act_const, AddMonoidAlgebra.single_mul_single,
        coefficientFrom_single]

lemma coefficient_differential_zero : totalDifferential (coefficientModule R D) = 0 := by
  apply DirectSum.linearMap_ext
  intro n
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, n = i+1 := ⟨n-1, by omega⟩
  ext x : 1
  simp only [LinearMap.comp_apply, totalDifferential_inc_succ]
  have hd : (coefficientModule R D).d i = 0 := by
    change (HahnWilson.PeriodicDual.cell R D 0).d ((i+1:ℤ):ZMod D) (i:ZMod D) = 0
    exact HahnWilson.PeriodicSplitting.diagonalComplex_d _ _ _
  rw [hd]
  simp

theorem coefficient_regular_aux (hD : 0 < D) :
    ∃ e : total (HahnWilson.LaurentCriterion.coefficient R D) ≃+ LaurentPolynomial R,
      (∀ (q : ℤ) (r : R),
        e (inc (HahnWilson.LaurentCriterion.coefficient R D) ((D:ℤ)*q) (coefficientConst R D _ r)) =
          AddMonoidAlgebra.single q r) ∧
      (∀ (a : LaurentPolynomial R) (z : total (HahnWilson.LaurentCriterion.coefficient R D)),
        e (laurentRepresentation (HahnWilson.LaurentCriterion.coefficient R D) a z) = a * e z) ∧
      totalDifferential (HahnWilson.LaurentCriterion.coefficient R D) = 0 := by
  refine ⟨(coefficientEquiv R D hD).toAddEquiv, coefficientTo_monomial R D hD, ?_,
    coefficient_differential_zero R D⟩
  intro a z
  change coefficientTo R D (laurentRepresentation (coefficientModule R D) a z) = a * coefficientTo R D z
  nth_rw 1 [← coefficientFrom_to R D hD z]
  rw [coefficient_act_from, coefficientTo_from R D hD]

theorem coefficient_regular (hD : 0 < D) :
    ∃ e : total (HahnWilson.LaurentCriterion.coefficient R D) ≃+ LaurentPolynomial R,
      (∀ (q : ℤ) (r : R),
        e (inc (HahnWilson.LaurentCriterion.coefficient R D) ((D:ℤ)*q) (fun _ => r)) =
          AddMonoidAlgebra.single q r) ∧
      (∀ (a : LaurentPolynomial R) (z : total (HahnWilson.LaurentCriterion.coefficient R D)),
        e (laurentRepresentation (HahnWilson.LaurentCriterion.coefficient R D) a z) = a * e z) ∧
      totalDifferential (HahnWilson.LaurentCriterion.coefficient R D) = 0 := by
  exact coefficient_regular_aux R D hD
end HahnWilson.LaurentDg

end

end OAI
