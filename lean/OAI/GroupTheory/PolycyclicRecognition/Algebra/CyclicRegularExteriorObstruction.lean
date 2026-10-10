import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RepresentationTheory.Basic
import OAI.GroupTheory.PolycyclicRecognition.Algebra.MonoidRingOrbitSpan

namespace OAI

/-! # The exterior square detects a free cyclic orbit

The difference of two indices is invariant under simultaneous translation.
It gives an equivariant map from the exterior square of the regular
cyclic module to a trivial module with unboundedly many independent coordinates.
-/

noncomputable section
namespace PolycyclicRecognition
variable {K : Type} [Field K]
open scoped MonoidAlgebra

abbrev CyclicOrbitModule := ℤ →₀ K

def cyclicShiftRepresentation :
    Representation K (Multiplicative ℤ) (CyclicOrbitModule (K := K)) where
  toFun g := Finsupp.lmapDomain K K (fun i => g.toAdd + i)
  map_one' := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro c
    simp [Finsupp.lmapDomain_apply]
  map_mul' g h := by
    apply Finsupp.lhom_ext'
    intro i
    apply LinearMap.ext
    intro c
    simp [Finsupp.lmapDomain_apply, add_assoc]

@[simp] theorem cyclicShiftRepresentation_single (g : Multiplicative ℤ) (i : ℤ) (c : K) :
    cyclicShiftRepresentation g (Finsupp.single i c) =
      Finsupp.single (g.toAdd + i) c := by
  simp [cyclicShiftRepresentation, Finsupp.lmapDomain_apply]

def cyclicDifferenceBilinear :
    (CyclicOrbitModule (K := K)) →ₗ[K] (CyclicOrbitModule (K := K)) →ₗ[K] (CyclicOrbitModule (K := K)) :=
  Finsupp.linearCombination K (fun i =>
    Finsupp.linearCombination K (fun j => Finsupp.single (j - i) (1 : K)))

@[simp] theorem cyclicDifferenceBilinear_single (i j : ℤ) (r s : K) :
    cyclicDifferenceBilinear (Finsupp.single i r) (Finsupp.single j s) =
      Finsupp.single (j - i) (r * s) := by
  simp [cyclicDifferenceBilinear, LinearMap.smul_apply]

def cyclicDifferenceAlternating :
    (CyclicOrbitModule (K := K)) [⋀^Fin 2]→ₗ[K] (CyclicOrbitModule (K := K)) where
  toFun v := cyclicDifferenceBilinear (v 0) (v 1) -
    cyclicDifferenceBilinear (v 1) (v 0)
  map_update_add' := by
    intro _ v i x y
    fin_cases i <;> simp [Function.update, map_add, LinearMap.add_apply] <;> abel
  map_update_smul' := by
    intro _ v i c x
    fin_cases i <;> simp [Function.update, map_smul, LinearMap.smul_apply, smul_sub]
  map_eq_zero_of_eq' := by
    intro v i j h hij
    fin_cases i <;> fin_cases j <;> simp_all

def cyclicExteriorDifference :
    (⋀[K]^2 (CyclicOrbitModule (K := K))) →ₗ[K] (CyclicOrbitModule (K := K)) :=
  exteriorPower.alternatingMapLinearEquiv cyclicDifferenceAlternating

@[simp] theorem cyclicExteriorDifference_single (i j : ℤ) :
    (cyclicExteriorDifference (K := K)) (exteriorPower.ιMulti K 2
      ![Finsupp.single i 1, Finsupp.single j 1]) =
      Finsupp.single (j - i) 1 - Finsupp.single (i - j) 1 := by
  rw [cyclicExteriorDifference, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  simp [cyclicDifferenceAlternating]

theorem cyclicDifferenceBilinear_shift (g : Multiplicative ℤ) (x y : (CyclicOrbitModule (K := K))) :
    cyclicDifferenceBilinear (cyclicShiftRepresentation g x)
      (cyclicShiftRepresentation g y) = cyclicDifferenceBilinear x y := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x z hx hz => simp [map_add, LinearMap.add_apply, hx, hz]
  | single i r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | single j s =>
      simp only [cyclicShiftRepresentation_single, cyclicDifferenceBilinear_single]
      congr 1
      omega

theorem cyclicExteriorDifference_shift (g : Multiplicative ℤ) :
    (cyclicExteriorDifference (K := K)).comp (exteriorPower.map 2 (cyclicShiftRepresentation g)) =
      cyclicExteriorDifference := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, cyclicExteriorDifference,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact congrArg₂ (fun x y : (CyclicOrbitModule (K := K)) => x - y)
    (cyclicDifferenceBilinear_shift g (v 0) (v 1))
    (cyclicDifferenceBilinear_shift g (v 1) (v 0))

def rationalCyclicExteriorRepresentation :
    Representation K (Multiplicative ℤ) (⋀[K]^2 (CyclicOrbitModule (K := K))) where
  toFun g := exteriorPower.map 2 (cyclicShiftRepresentation g)
  map_one' := by rw [map_one]; exact exteriorPower.map_id
  map_mul' g h := by rw [map_mul]; exact exteriorPower.map_comp _ _

/-- An invariant map from a finite cyclic module to a direct sum has one
finite support bound valid for every element. -/
theorem finite_cyclic_invariant_support {M : Type} [AddCommGroup M] [Module K M]
    (ρ : Representation K (Multiplicative ℤ) M)
    [Module.Finite K[Multiplicative ℤ] ρ.asModule]
    (L : M →ₗ[K] (CyclicOrbitModule (K := K))) (hinv : ∀ g x, L (ρ g x) = L x) :
    ∃ T : Finset ℤ, ∀ x k, k ∉ T → L x k = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top :
    (⊤ : Submodule K[Multiplicative ℤ] ρ.asModule).FG)
  let D : ρ.asModule →ₗ[K] (CyclicOrbitModule (K := K)) := L.comp ρ.asModuleEquiv.toLinearMap
  let T : Finset ℤ := s.biUnion (fun x => (D x).support)
  refine ⟨T, ?_⟩
  intro x k hk
  let U := (Finsupp.lapply k : (CyclicOrbitModule (K := K)) →ₗ[K] K).comp D |>.ker
  have hstable (g : Multiplicative ℤ) (y : ρ.asModule) (hy : y ∈ U) :
      MonoidAlgebra.of K (Multiplicative ℤ) g • y ∈ U := by
    change L (ρ.asModuleEquiv (MonoidAlgebra.single g 1 • y)) k = 0
    rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
      LinearMap.smul_apply, one_smul, hinv]
    exact hy
  let W : Submodule K[Multiplicative ℤ] ρ.asModule :=
    MonoidAlgebra.submoduleOfSMulMem U hstable
  have hW : Submodule.span K[Multiplicative ℤ] (s : Set ρ.asModule) ≤ W := by
    apply Submodule.span_le.mpr
    intro y hy
    change D y k = 0
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    exact hk (Finset.mem_biUnion.mpr ⟨y, hy, hmem⟩)
  have hx : ρ.asModuleEquiv.symm x ∈ W := hW (hs ▸ Submodule.mem_top)
  change L (ρ.asModuleEquiv (ρ.asModuleEquiv.symm x)) k = 0 at hx
  simpa only [LinearEquiv.apply_symm_apply] using hx

theorem rationalCyclicExterior_not_finite :
    ¬Module.Finite K[Multiplicative ℤ]
      (rationalCyclicExteriorRepresentation (K := K)).asModule := by
  classical
  intro h
  let := h
  obtain ⟨T, hT⟩ := finite_cyclic_invariant_support (rationalCyclicExteriorRepresentation (K := K))
    cyclicExteriorDifference (fun g x => LinearMap.congr_fun (cyclicExteriorDifference_shift g) x)
  let k : ℤ := (T.sup Int.natAbs : ℕ) + 1
  have hkpos : 0 < k := by omega
  have hknat : k.natAbs = T.sup Int.natAbs + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (T.sup Int.natAbs + 1)
  have hk : k ∉ T := by
    intro hmem
    have hle := Finset.le_sup (f := Int.natAbs) hmem
    rw [hknat] at hle
    omega
  have hz := hT (exteriorPower.ιMulti K 2
    ![Finsupp.single (0 : ℤ) 1, Finsupp.single k 1]) k hk
  rw [cyclicExteriorDifference_single] at hz
  simp only [sub_zero, zero_sub, Finsupp.sub_apply, Finsupp.single_eq_same] at hz
  have hkneg : k ≠ -k := by omega
  rw [Finsupp.single_eq_of_ne hkneg, sub_zero] at hz
  exact one_ne_zero hz

end PolycyclicRecognition

end

end OAI
