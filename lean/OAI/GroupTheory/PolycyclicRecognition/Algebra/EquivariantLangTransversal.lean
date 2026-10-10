import OAI.GroupTheory.PolycyclicRecognition.Geometry.JordanLangTransversal
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationAction

namespace OAI

/-! # Lang decomposition preserves commuting symmetries

Uniqueness of the finite-filtration inverse ensures that a correction of a
fixed element can be chosen fixed by every commuting symmetry already imposed.
-/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [C : PolynomialExponentialCoordinates L]

theorem polynomial_transversal_equivariant (A T : L ≃ₗ⁅ℝ⁆ L) (P : Module.End ℝ L)
    (hTP : Commute T.toLinearMap P) (hTA : Commute T.toLinearMap A.toLinearMap) (x : L) :
    (T x - P (T x))⁻¹ * P (T x) * A (T x - P (T x)) =
      T ((x - P x)⁻¹ * P x * A (x - P x)) := by
  have hp : P (T x) = T (P x) := (LinearMap.congr_fun hTP.eq x).symm
  have hq : T x - P (T x) = T (x - P x) := by rw [hp, map_sub]
  have ha : A (T (x - P x)) = T (A (x - P x)) :=
    (LinearMap.congr_fun hTA.eq _).symm
  rw [hq, hp, ha]
  let t := PolynomialExponentialCoordinates.groupAutomorphism (P := C) T
  change (t (x - P x))⁻¹ * t (P x) * t (A (x - P x)) =
    t ((x - P x)⁻¹ * P x * A (x - P x))
  rw [map_mul, map_mul, map_inv]

variable [LieRing.IsNilpotent L]

theorem jordan_lang_decomposition_fixed (A S U T : L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : Commute T.toLinearMap S.toLinearMap)
    (hTA : Commute T.toLinearMap A.toLinearMap) (u : L) (htu : T u = u) :
    ∃ v w : L, S w = w ∧ T v = v ∧ T w = w ∧ u = v⁻¹ * w * A v := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hTP : Commute T.toLinearMap P :=
    (semisimpleKernelProjection_commute B T.toLinearMap hB
      (hTS.symm.sub_left (Commute.one_left _))).symm
  let f := fun x : L => (x - P x)⁻¹ * P x * A (x - P x)
  have hf : Function.Bijective f := jordan_lang_transversal_bijective A S U hS hU hSU hA
  obtain ⟨x, hx⟩ := hf.surjective u
  have htx : T x = x := hf.injective (by
    change (T x - P (T x))⁻¹ * P (T x) * A (T x - P (T x)) = f x
    rw [polynomial_transversal_equivariant A T P hTP hTA]
    change T (f x) = f x
    rw [hx, htu])
  have hp : T (P x) = P x := by
    have hh : T (P x) = P (T x) := LinearMap.congr_fun hTP.eq x
    rwa [htx] at hh
  exact ⟨x - P x, P x, sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x),
    by rw [map_sub, htx, hp], hp, hx.symm⟩

theorem jordan_lang_decomposition_fixed_family {ι : Type*}
    (A S U : L ≃ₗ⁅ℝ⁆ L) (T : ι → L ≃ₗ⁅ℝ⁆ L)
    (hS : Module.End.IsSemisimple S.toLinearMap)
    (hU : IsNilpotent (U.toLinearMap - 1))
    (hSU : Commute S.toLinearMap U.toLinearMap)
    (hA : A.toLinearMap = S.toLinearMap * U.toLinearMap)
    (hTS : ∀ i, Commute (T i).toLinearMap S.toLinearMap)
    (hTA : ∀ i, Commute (T i).toLinearMap A.toLinearMap) (u : L) (htu : ∀ i, T i u = u) :
    ∃ v w : L, S w = w ∧ (∀ i, T i v = v) ∧ (∀ i, T i w = w) ∧
      u = v⁻¹ * w * A v := by
  let B : Module.End ℝ L := S.toLinearMap - 1
  have hB : B.IsSemisimple := semisimple_sub_one S.toLinearMap hS
  let P := semisimpleKernelProjection B hB
  have hTP (i : ι) : Commute (T i).toLinearMap P :=
    (semisimpleKernelProjection_commute B (T i).toLinearMap hB
      ((hTS i).symm.sub_left (Commute.one_left _))).symm
  let f := fun x : L => (x - P x)⁻¹ * P x * A (x - P x)
  have hf : Function.Bijective f := jordan_lang_transversal_bijective A S U hS hU hSU hA
  obtain ⟨x, hx⟩ := hf.surjective u
  have htx (i : ι) : T i x = x := hf.injective (by
    change (T i x - P (T i x))⁻¹ * P (T i x) * A (T i x - P (T i x)) = f x
    rw [polynomial_transversal_equivariant A (T i) P (hTP i) (hTA i)]
    change T i (f x) = f x
    rw [hx, htu i])
  have hp (i : ι) : T i (P x) = P x := by
    have hh : T i (P x) = P (T i x) := LinearMap.congr_fun (hTP i).eq x
    rwa [htx] at hh
  exact ⟨x - P x, P x, sub_eq_zero.mp (semisimpleKernelProjection_mem B hB x),
    fun i => by rw [map_sub, htx, hp], hp, hx.symm⟩

end PolycyclicRecognition

end

end OAI
