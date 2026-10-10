import OAI.Algebra.AuslanderReiten.Modules.TInductionTriangle
import Mathlib.Algebra.Category.ModuleCat.Algebra
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit.Resolution
universe u
variable {k : Type u} [Field k] [CharP k 2] (q : k)
local notation "T" => ArExplicit.T k q
variable [hD : HasDerivedCategory (ModuleCat.{u} (ArExplicit.T k q))]
include hD

def tConnecting (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    ShiftedHom (tSimpleDerived q) (tSimpleDerived q) (3 : ℤ) :=
  tTriangleD q hq hq1 h ≫
    (shiftFunctorAdd' (DerivedCategory (ModuleCat T)) (2 : ℤ) 1 3 (by decide)).inv.app _

theorem tInducedDerived_shift_hom_zero (hq1 : 1 + q ≠ 0) (n : ℤ) (hn : n ≠ 1)
    (f : (tInducedDerived q)⟦(1 : ℤ)⟧ ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  let e := TriangleRecurrence.shiftedMapEquiv (tInducedDerived q) (tSimpleDerived q)
    1 (n - 1) n (by omega)
  obtain ⟨g, rfl⟩ := e.surjective f
  rw [tInducedDerived_hom_zero q hq1 (n - 1) (by omega) g]
  simp [e, TriangleRecurrence.shiftedMapEquiv]

omit [CharP k 2] in
theorem tSimpleDerived_negative_zero (n : ℤ) (hn : n < 0)
    (f : tSimpleDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  let : (tSimpleDerived q).IsLE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))).IsLE 0)
  let : (tSimpleDerived q).IsGE 0 := inferInstanceAs
    (((DerivedCategory.singleFunctor (ModuleCat T) 0).obj (ModuleCat.of T (Simple q))).IsGE 0)
  let : ((tSimpleDerived q)⟦n⟧).IsGE (-n) :=
    DerivedCategory.TStructure.t.isGE_shift (tSimpleDerived q) 0 n (-n) (by omega)
  exact DerivedCategory.TStructure.t.zero f 0 (-n) (by omega)

theorem tConnecting_multiply_bijective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : 0 ≤ n) :
    Function.Bijective (fun b : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) n =>
      ShiftedHom.comp (tConnecting q hq hq1 h) b rfl) :=
  TriangleRecurrence.degreeThreeComposition_bijective _ _ _ _ _
    (tInductionTriangle_distinguished q hq hq1 h) n
    (tInducedDerived_hom_zero q hq1 (n + 3) (by omega))
    (tInducedDerived_shift_hom_zero q hq1 (n + 3) (by omega))

theorem tConnecting_multiply_surjective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : n + 3 ≠ 0) :
    Function.Surjective (fun b : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) n =>
      ShiftedHom.comp (tConnecting q hq hq1 h) b rfl) := by
  let e := TriangleRecurrence.shiftedMapEquiv (tSimpleDerived q) (tSimpleDerived q) 3 n (n + 3) rfl
  let e' := ((shiftFunctorAdd' (DerivedCategory (ModuleCat T)) (2 : ℤ) 1 3 (by decide)).app
    (tSimpleDerived q)).homFromEquiv (Z := (tSimpleDerived q)⟦n + 3⟧)
  have hh := (TriangleRecurrence.connecting_surjective (tInductionTriangle q hq hq1 h)
    (tInductionTriangle_distinguished q hq hq1 h) ((tSimpleDerived q)⟦n + 3⟧)
    (tInducedDerived_hom_zero q hq1 (n + 3) hn)).comp (e'.surjective.comp e.surjective)
  convert! hh using 1
  ext b
  simp only [e, e', TriangleRecurrence.shiftedMapEquiv,
    ShiftedHom.comp, Category.assoc, tConnecting]
  rfl

theorem tSimpleDerived_low_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℤ) (hn : 0 < n) (hn3 : n < 3)
    (f : tSimpleDerived q ⟶ (tSimpleDerived q)⟦n⟧) : f = 0 := by
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · have hs := tConnecting_multiply_surjective q hq hq1 h (-2) (by decide)
    obtain ⟨b, hb⟩ := hs f
    rw [tSimpleDerived_negative_zero q (-2) (by decide) b] at hb
    simpa only [ShiftedHom.comp_zero] using hb.symm
  · have hs := tConnecting_multiply_surjective q hq hq1 h (-1) (by decide)
    obtain ⟨b, hb⟩ := hs f
    rw [tSimpleDerived_negative_zero q (-1) (by decide) b] at hb
    simpa only [ShiftedHom.comp_zero] using hb.symm

abbrev TSelfExt (n : ℕ) := Abelian.Ext (ModuleCat.of T (Simple q)) (ModuleCat.of T (Simple q)) n

def tTau (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) : TSelfExt q 3 :=
  Abelian.Ext.homEquiv.symm (tConnecting q hq hq1 h)

@[simp] theorem tTau_hom (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) (h : NoPositivePowerOne q) :
    (tTau q hq hq1 h).hom = tConnecting q hq hq1 h :=
  Equiv.apply_symm_apply _ _

theorem tTau_multiply_bijective (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Bijective (fun b : TSelfExt q n => (tTau q hq hq1 h).comp b (by omega : 3 + n = n + 3)) := by
  have hb := tConnecting_multiply_bijective q hq hq1 h (n : ℤ) (by omega)
  constructor
  · intro b c hbc
    apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n)).injective
    apply hb.injective
    have hh := congrArg (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n + 3)) hbc
    simpa only [Abelian.Ext.comp_hom, tTau_hom, Nat.cast_add, Nat.cast_ofNat] using! hh
  · intro z
    let z' : ShiftedHom (tSimpleDerived q) (tSimpleDerived q) ((n : ℤ) + 3) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, tSimpleDerived] using! z.hom
    obtain ⟨b, hbb⟩ := hb.surjective z'
    let b' : TSelfExt q n := Abelian.Ext.homEquiv.symm b
    have hb' : b'.hom = b := Equiv.apply_symm_apply _ _
    refine ⟨b', ?_⟩
    apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
      (Y := ModuleCat.of T (Simple q)) (n := n + 3)).injective
    simpa only [Abelian.Ext.comp_hom, tTau_hom, hb', Nat.cast_add, Nat.cast_ofNat] using! hbb

theorem tSelfExt_low_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0)
    (h : NoPositivePowerOne q) (n : ℕ) (hn : 0 < n) (hn3 : n < 3) (x : TSelfExt q n) : x = 0 := by
  apply (Abelian.Ext.homEquiv (X := ModuleCat.of T (Simple q))
    (Y := ModuleCat.of T (Simple q)) (n := n)).injective
  simpa only [Abelian.Ext.zero_hom, tSimpleDerived] using! tSimpleDerived_low_zero q hq hq1 h (n : ℤ) (by omega) (by omega) x.hom

end ArExplicit.Resolution

end

end OAI
