import OAI.Algebra.AuslanderReiten.Modules.TInductionHomology
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "C" => BaseAlgebra k q
local notation "T" => ArExplicit.T k q

def tInducedCochain : CochainComplex (ModuleCat T) ℤ :=
  (TrivialInduction.inducedComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat

omit [CharP k 2] in
private theorem inducedE_hom_zero (hq1 : 1 + q ≠ 0)
    (f : Induction.Object (V := E q) (TrivialExtension.inlHom (k := k) (A := C)) →ₗ[T] Simple q) : f = 0 := by
  let e := Induction.homEquiv (V := E q) (W := Simple q)
    (TrivialExtension.inlHom (k := k) (A := C)) (fun _ _ => rfl)
  exact e.injective (by rw [map_zero]; exact hom_E_simple_eq_zero q hq1 (e f))

theorem tInduced_term_hom_zero (hq1 : 1 + q ≠ 0) (n : ℕ)
    (f : (TrivialInduction.inducedComplex (k := k) (complex q)).X (n + 1) ⟶
      ModuleCat.of T (Simple q)) : f = 0 := by
  let := moduleCatBaseModule (k := k) (R := C) ((complex q).X (n + 1))
  let := moduleCatBaseTower (k := k) (R := C) ((complex q).X (n + 1))
  let e := Induction.homEquiv (V := (complex q).X (n + 1)) (W := Simple q)
    (TrivialExtension.inlHom (k := k) (A := C)) (fun _ _ => rfl)
  apply ModuleCat.hom_ext
  exact e.injective ((hom_E_simple_eq_zero q hq1 (e f.hom)).trans (e.map_zero).symm)

theorem tInducedCochain_term_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (f : (tInducedCochain q).X n ⟶ ModuleCat.of T (Simple q)) : f = 0 := by
  dsimp [tInducedCochain] at f ⊢
  by_cases hh : ∃ m : ℕ, -(m : ℤ) = n
  · obtain ⟨m, hm⟩ := hh
    have hm0 : m ≠ 0 := by intro h; subst m; simp at hm; exact hn hm.symm
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    let e := (TrivialInduction.inducedComplex (k := k) (complex q)).extendXIso
      ComplexShape.embeddingDownNat hm
    apply (cancel_epi e.inv).mp
    exact (tInduced_term_hom_zero q hq1 r (e.inv ≫ f)).trans (Limits.comp_zero).symm
  · exact ((TrivialInduction.inducedComplex (k := k) (complex q)).isZero_extend_X
      ComplexShape.embeddingDownNat n (by intro m hm; exact hh ⟨m, hm⟩)).eq_of_src f 0

theorem tInduced_fullCochain_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 0)
    (a : CochainComplex.HomComplex.Cochain (tInducedCochain q)
      ((CochainComplex.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))) n) : a = 0 := by
  apply (CochainComplex.HomComplex.Cochain.toSingleEquiv (p := -n) (by omega)).injective
  rw [map_zero]
  exact tInducedCochain_term_hom_zero q hq1 (-n) (by omega) _

instance tInducedCochain_kprojective : (tInducedCochain q).IsKProjective := by
  let (n : ℕ) : Projective ((TrivialInduction.inducedComplex (k := k) (complex q)).X n) :=
    ModuleCat.projective_of_categoryTheory_projective _
  change CochainComplex.IsKProjective ((TrivialInduction.inducedComplex (k := k) (complex q)).extend ComplexShape.embeddingDownNat)
  infer_instance

end ArExplicit.Resolution

end

end OAI
