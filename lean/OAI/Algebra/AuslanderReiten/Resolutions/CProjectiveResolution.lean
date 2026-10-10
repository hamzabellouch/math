import OAI.Algebra.AuslanderReiten.Resolutions.Resolution
import OAI.Algebra.AuslanderReiten.Parameters
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

local notation "C" => BaseAlgebra k q

abbrev Simple := (F q) ⧸ LinearMap.range (dU q)

def objects : ℕ → ModuleCat C
  | 0 => ModuleCat.of C (F q)
  | _ + 1 => ModuleCat.of C (E q)

def differential : (n : ℕ) → objects q (n + 1) ⟶ objects q n
  | 0 => ModuleCat.ofHom (dU q)
  | n + 1 => ModuleCat.ofHom (dEll q (q ^ n))

theorem differential_comp (n : ℕ) : differential q (n + 1) ≫ differential q n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    change (dU q).comp (dEll q (q ^ 0)) = 0
    simpa only [pow_zero] using dU_comp_dEll_one q
  | succ n =>
    apply ModuleCat.hom_ext
    change (dEll q (q ^ n)).comp (dEll q (q ^ (n + 1))) = 0
    simpa only [pow_succ'] using dEll_comp_successor q (q ^ n)

def complex : ChainComplex (ModuleCat C) ℕ :=
  ChainComplex.of (objects q) (differential q) (differential_comp q)

instance complex_projective (n : ℕ) : CategoryTheory.Projective ((complex q).X n) := by
  cases n <;> dsimp [complex, objects] <;> infer_instance

instance complex_scalar (n : ℕ) : Module k ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : Module k (F q))
  | succ n => exact (inferInstance : Module k (E q))

instance complex_finite (n : ℕ) : Module.Finite k ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : Module.Finite k (F q))
  | succ n => exact (inferInstance : Module.Finite k (E q))

def NoPositivePowerOne : Prop := ∀ m : ℕ, 0 < m → 1 + q ^ m ≠ 0

omit [CharP k 2] in
theorem denominator_power_ne (h : NoPositivePowerOne q) (n : ℕ) :
    1 + q ^ 2 * q ^ n ≠ 0 := by
  rw [← pow_add]
  exact h (2 + n) (by omega)

theorem differential_exact (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Exact (differential q (n + 1)) (differential q n) := by
  cases n with
  | zero =>
    change Function.Exact (dEll q (q ^ 0)) (dU q)
    simpa only [pow_zero] using exact_dU q (by simpa using h 1 (by decide)) (h 2 (by decide))
  | succ n =>
    change Function.Exact (dEll q (q ^ (n + 1))) (dEll q (q ^ n))
    simpa only [pow_succ'] using exact_dEll q (q ^ n)
      (denominator_power_ne q h n)
      (by simpa [pow_succ'] using denominator_power_ne q h (n + 1))

theorem complex_exactAt_succ (h : NoPositivePowerOne q) (n : ℕ) :
    (complex q).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  simpa [complex, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    ChainComplex.of_d] using! differential_exact q h n

def augmentation : (complex q).X 0 ⟶ ModuleCat.of C (Simple q) :=
  ModuleCat.ofHom (LinearMap.range (dU q)).mkQ

instance augmentation_epi : Epi (augmentation q) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

theorem differential_augmentation : (complex q).d 1 0 ≫ augmentation q = 0 := by
  apply ModuleCat.hom_ext
  change (LinearMap.range (dU q)).mkQ.comp (dU q) = 0
  exact LinearMap.range_mkQ_comp (dU q)

def toSimple : complex q ⟶ (ChainComplex.single₀ (ModuleCat C)).obj (ModuleCat.of C (Simple q)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentation q, differential_augmentation q⟩

@[simp] theorem toSimple_zero : (toSimple q).f 0 = augmentation q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem augmentation_exact :
    (ShortComplex.mk ((complex q).d 1 0) (augmentation q) (differential_augmentation q)).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (dU q) (LinearMap.range (dU q)).mkQ
  exact LinearMap.exact_map_mkQ_range (dU q)

theorem toSimple_quasiIso (h : NoPositivePowerOne q) : QuasiIso (toSimple q) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · change (ShortComplex.mk ((complex q).d 1 0) ((toSimple q).f 0) _).Exact ∧
        Epi ((toSimple q).f 0)
      simpa only [toSimple_zero, ChainComplex.single₀_obj_zero] using And.intro (augmentation_exact q) (augmentation_epi q)
    · rfl
    · rfl
    · rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ q h n
    · exact ChainComplex.exactAt_succ_single_obj _ _

def projectiveResolution (h : NoPositivePowerOne q) :
    CategoryTheory.ProjectiveResolution (ModuleCat.of C (Simple q)) where
  complex := complex q
  π := toSimple q
  quasiIso := toSimple_quasiIso q h

theorem baseField_noPositivePowerOne : NoPositivePowerOne ArExplicit.q := by
  intro m hm
  simpa [add_comm] using ArExplicit.q_pow_add_one_ne_zero m hm

def baseFieldProjectiveResolution :
    CategoryTheory.ProjectiveResolution
      (ModuleCat.of (BaseAlgebra BaseField ArExplicit.q) (Simple ArExplicit.q)) :=
  projectiveResolution ArExplicit.q baseField_noPositivePowerOne

end ArExplicit.Resolution

end

end OAI
