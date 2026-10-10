import OAI.Algebra.Finitistic.Bimodule.BimoduleTotalTerms

namespace OAI
noncomputable section
open CategoryTheory
namespace LittleFinitistic.BimoduleTotal
open ExternalTensor.Section4
universe u
variable (k B : Type u) [Field k] [Ring B] [Algebra k B]
variable (P : BiComplex k B) {l : ℕ} (p : Fin l → ℤ) (hp : StrictMono p)
variable (Z : CochainComplex (ModuleCat.{u} B) ℤ)

abbrev TotalTerm (n : ℤ) := ∀ i : Fin l, Term k B P Z (p i) (n + -(p i))
abbrev vectorTotal := ComplexTensor.finiteTotal k B (right k B P) Z p hp

theorem matrix_smul (n : ℤ) (b : B) (x : TotalTerm k B P p Z n) :
    ComplexTensor.matrix k B (right k B P) Z p n (b • x) =
      b • (show TotalTerm k B P p Z (n+1) from
        ComplexTensor.matrix k B (right k B P) Z p n x) := by
  funext j
  change ComplexTensor.matrix k B (right k B P) Z p n (b • x) j =
    b • (show Term k B P Z (p j) ((n+1) + -(p j)) from
      ComplexTensor.matrix k B (right k B P) Z p n x j)
  erw [ComplexTensor.matrix_apply, ComplexTensor.matrix_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold ComplexTensor.entry
  split_ifs with h
  · exact horizontal_smul k B P Z n (p i) (p j) h b (x i)
  · simp
    rfl

theorem differential_smul (n m : ℤ) (b : B) (x : TotalTerm k B P p Z n) :
    ((vectorTotal k B P p hp Z).d n m).hom (b • x) =
      b • (show TotalTerm k B P p Z m from ((vectorTotal k B P p hp Z).d n m).hom x) := by
  by_cases h : n+1=m
  · subst m
    simp only [vectorTotal, ComplexTensor.finiteTotal, FiniteColumnComplex.total,
      FiniteColumnComplex.complex_d_hom]
    change (FiniteColumnComplex.diagonal _ n (b • x) +
      ComplexTensor.matrix k B (right k B P) Z p n (b • x)) =
      b • (show TotalTerm k B P p Z (n+1) from
        FiniteColumnComplex.diagonal _ n x + ComplexTensor.matrix k B (right k B P) Z p n x)
    funext i
    exact (congrArg₂ HAdd.hAdd
      (column_d_smul k B P Z (p i) n (n+1) b (x i))
      (congrFun (matrix_smul k B P p Z n b x) i)).trans
      (smul_add b
        (show Term k B P Z (p i) ((n+1) + -(p i)) from
          ((ComplexTensor.column k B (right k B P) Z (p i)).d n (n+1)).hom (x i))
        (show Term k B P Z (p i) ((n+1) + -(p i)) from
          ComplexTensor.matrix k B (right k B P) Z p n x i)).symm
  · have hz := (vectorTotal k B P p hp Z).shape n m h
    rw [hz]
    change (0 : TotalTerm k B P p Z m) = b • (0 : TotalTerm k B P p Z m)
    funext i
    exact (smul_zero b : b • (0 : Term k B P Z (p i) (m + -(p i))) = 0).symm

/-- The same signed finite tensor total, retaining the full left B action. -/
def total : CochainComplex (ModuleCat.{u} B) ℤ where
  X n := ModuleCat.of B (TotalTerm k B P p Z n)
  d n m := ModuleCat.ofHom
    { __ := ((vectorTotal k B P p hp Z).d n m).hom.toAddMonoidHom
      map_smul' := differential_smul k B P p hp Z n m }
  shape n m h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) ((vectorTotal k B P p hp Z).shape n m h)
  d_comp_d' n m t _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) ((vectorTotal k B P p hp Z).d_comp_d n m t)

variable {Z} {Z' Z'' : CochainComplex (ModuleCat.{u} B) ℤ}

/-- The original input tensor map is B-linear in every degree. -/
def totalMap (f : Z ⟶ Z') : total k B P p hp Z ⟶ total k B P p hp Z' where
  f n := ModuleCat.ofHom
    { __ := ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom.toAddMonoidHom
      map_smul' := by
        intro b x
        funext i
        change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom (b • x) i =
          b • (show Term k B P Z' (p i) (n + -(p i)) from
            ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i)
        erw [ComplexTensor.finiteTotalMap_apply,ComplexTensor.finiteTotalMap_apply]
        exact inputMap_smul k B P f (p i) (n + -(p i)) b (x i) }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun g => g.hom x)
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).comm n m)

/-- Tensoring with the fixed bimodule complex acts on every left-module complex. -/
def functor : CochainComplex (ModuleCat.{u} B) ℤ ⥤ CochainComplex (ModuleCat.{u} B) ℤ where
  obj Z := total k B P p hp Z
  map f := totalMap k B P p hp f
  map_id Z := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => (f.f n).hom x)
      ((ComplexTensor.finiteTotalFunctor k B (right k B P) p hp).map_id Z)
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => (f.f n).hom x)
      ((ComplexTensor.finiteTotalFunctor k B (right k B P) p hp).map_comp f g)

instance additive : (functor k B P p hp).Additive where
  map_add {Z Z'} {f g} := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext i
    change ((ComplexTensor.finiteTotalMap k B (right k B P) p hp (f+g)).f n).hom x i =
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp f).f n).hom x i +
      ((ComplexTensor.finiteTotalMap k B (right k B P) p hp g).f n).hom x i
    erw [ComplexTensor.finiteTotalMap_apply, ComplexTensor.finiteTotalMap_apply, ComplexTensor.finiteTotalMap_apply]
    induction x i using BalancedTensor.induction_on with
    | hz =>
      simp
      exact (zero_add _).symm
    | ht a b => exact (BalancedTensor.mk k B _ _ a).map_add _ _
    | ha a b ha hb => simp_all [map_add]; abel
end LittleFinitistic.BimoduleTotal

end

end OAI
