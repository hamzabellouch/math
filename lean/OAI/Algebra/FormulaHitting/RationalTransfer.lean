import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.RingTheory.Artinian.Module
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
open PowerSeries
namespace NCHitting

variable {F : Type*} [Field F]

def jet (d : ℕ) : PowerSeries F →ₗ[F] (Fin d → F) where
  toFun a r := PowerSeries.coeff r.val a
  map_add' a b := by ext r; simp
  map_smul' c a := by ext r; simp

@[simp] theorem jet_apply (d : ℕ) (a : PowerSeries F) (r : Fin d) :
    jet d a r = PowerSeries.coeff r.val a := rfl

section FiniteFamily
variable {ι : Type*} [Fintype ι]

def jetKernel (a : ι → PowerSeries F) (d : ℕ) : Submodule F (ι → F) :=
  LinearMap.ker ((jet d).comp (Fintype.linearCombination F a))

@[simp] theorem mem_jetKernel (a : ι → PowerSeries F) (d : ℕ) (c : ι → F) :
    c ∈ jetKernel a d ↔ ∀ r < d,
      PowerSeries.coeff r (Fintype.linearCombination F a c) = 0 := by
  simp only [jetKernel, LinearMap.mem_ker, LinearMap.comp_apply]
  constructor
  · intro h r hr
    exact congrFun h ⟨r, hr⟩
  · intro h
    ext r
    exact h r.val r.isLt

theorem jetKernel_antitone (a : ι → PowerSeries F) : Antitone (jetKernel a) := by
  intro d e hde c hc
  rw [mem_jetKernel] at hc ⊢
  exact fun r hr => hc r (lt_of_lt_of_le hr hde)

theorem exists_independent_jet (a : ι → PowerSeries F) (ha : LinearIndependent F a) :
    ∃ d : ℕ, LinearIndependent F (fun i => jet d (a i)) := by
  classical
  obtain ⟨d, hd⟩ := IsArtinian.monotone_stabilizes
    (R := F) (M := ι → F) ⟨jetKernel a, jetKernel_antitone a⟩
  refine ⟨d, Fintype.linearIndependent_iff.mpr ?_⟩
  intro c hc i
  have hcd : c ∈ jetKernel a d := by
    simp only [jetKernel, LinearMap.mem_ker, LinearMap.comp_apply,
      Fintype.linearCombination_apply, map_sum, map_smul]
    exact hc
  have hcz : Fintype.linearCombination F a c = 0 := by
    apply PowerSeries.ext
    intro r
    have hce : c ∈ jetKernel a (max d (r+1)) := by
      have hstab := hd (max d (r+1)) (le_max_left _ _)
      change jetKernel a d = jetKernel a (max d (r+1)) at hstab
      rwa [← hstab]
    exact (mem_jetKernel a _ c).mp hce r (by omega)
  have he : c = 0 := ha.fintypeLinearCombination_injective (by simpa using hcz)
  exact congrFun he i

theorem rational_series_independent [CharZero F] (a : ι → PowerSeries ℚ)
    (ha : LinearIndependent ℚ a) :
    LinearIndependent F (fun i => PowerSeries.map (algebraMap ℚ F) (a i)) := by
  classical
  obtain ⟨d, hd⟩ := exists_independent_jet a ha
  have ht : LinearIndependent F (fun i =>
      (algebraMap ℚ F) ∘ (jet d (a i))) :=
    linearIndependent_algebraMap_comp_iff.mpr hd
  apply LinearIndependent.of_comp (jet d)
  simpa [Function.comp_def, jet] using ht

theorem rational_minor_ne_zero [DecidableEq ι] [CharZero F]
    (A : Matrix ι ι ℚ) (hA : A.det ≠ 0) :
    (A.map (algebraMap ℚ F)).det ≠ 0 := by
  change ((algebraMap ℚ F).mapMatrix A).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ F)).mpr hA

theorem independent_of_rational_minor [DecidableEq ι] [CharZero F]
    (a : ι → PowerSeries ℚ) (rows : ι → ℕ)
    (hA : Matrix.det (fun r i => PowerSeries.coeff (rows r) (a i) : Matrix ι ι ℚ) ≠ 0) :
    LinearIndependent F (fun i => PowerSeries.map (algebraMap ℚ F) (a i)) := by
  classical
  let A : Matrix ι ι ℚ := fun r i => PowerSeries.coeff (rows r) (a i)
  have hunit : IsUnit (A.map (algebraMap ℚ F)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    exact isUnit_iff_ne_zero.mpr (rational_minor_ne_zero A hA)
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hunit
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  have he : (A.map (algebraMap ℚ F)).mulVec c = 0 := by
    ext r
    change (∑ i, (algebraMap ℚ F) (PowerSeries.coeff (rows r) (a i)) * c i) = 0
    have hr := congrArg (PowerSeries.coeff (rows r)) hc
    simpa [mul_comm] using hr
  have hz : c = 0 := hinj (by simpa using he)
  exact congrFun hz i

end FiniteFamily
end NCHitting

end

end OAI
