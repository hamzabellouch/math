import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace OAI

namespace SiegelZeros

section

namespace WeightedTorusJets.W12

variable {K : Type*} [Field K] [CharZero K]

def directions (a b : K) : Fin 3 → (Fin 4 → K) :=
  ![![1, a, b, a*b], ![1, -a, b, -(a*b)], ![1, -a, -b, a*b]]

def omega (a b : K) : (Fin 4 → K) →ₗ[K] K where
  toFun x := x 0 + x 1 / a - x 2 / b - x 3 / (a*b)
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem omega_scaled (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (x : Fin 4 → K) :
    (a*b) * omega a b x = a*b*x 0 + b*x 1 - a*x 2 - x 3 := by
  simp only [omega, LinearMap.coe_mk, AddHom.coe_mk]
  field_simp [ha, hb]

theorem omega_direction (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (i : Fin 3) :
    omega a b (directions a b i) = 0 := by
  fin_cases i <;> simp [omega, directions, ha, hb]

theorem directions_linearIndependent (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent K (directions a b) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  have h2 := congrFun hc 2
  simp [Fin.sum_univ_succ, directions] at h0 h1 h2
  have h1' : c 0 - c 1 - c 2 = 0 := by
    apply (mul_eq_zero.mp (show a * (c 0 - c 1 - c 2) = 0 by
      linear_combination h1)).resolve_left ha
  have h2' : c 0 + c 1 - c 2 = 0 := by
    apply (mul_eq_zero.mp (show b * (c 0 + c 1 - c 2) = 0 by
      linear_combination h2)).resolve_left hb
  fin_cases i
  · change c 0 = 0
    linear_combination (1/2 : K) * h0 + (1/2 : K) * h1'
  · change c 1 = 0
    linear_combination (1/2 : K) * h2' - (1/2 : K) * h1'
  · change c 2 = 0
    linear_combination (1/2 : K) * h0 - (1/2 : K) * h2'

theorem kernel_decomposition (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (x : Fin 4 → K) (hx : omega a b x = 0) :
    x = ((x 0 + x 1 / a) / 2) • directions a b 0 +
      ((x 2 / b - x 1 / a) / 2) • directions a b 1 +
      ((x 0 - x 2 / b) / 2) • directions a b 2 := by
  have hs : a*b*x 0 + b*x 1 - a*x 2 - x 3 = 0 := by
    rw [← omega_scaled a b ha hb x, hx, mul_zero]
  have h3 : x 3 = a*b*x 0 + b*x 1 - a*x 2 := by
    linear_combination -hs
  ext i
  fin_cases i <;> simp [directions, Pi.add_apply, smul_eq_mul]
  · field_simp [ha, hb]; ring
  · field_simp [ha, hb]; ring
  · field_simp [ha, hb]; ring
  · rw [h3]
    field_simp [ha, hb]; ring

theorem span_directions_eq_kernel (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Submodule.span K (Set.range (directions a b)) = LinearMap.ker (omega a b) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact omega_direction a b ha hb i
  · intro x hx
    rw [kernel_decomposition a b ha hb x hx]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩)

theorem finrank_kernel_omega (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.finrank K (LinearMap.ker (omega a b)) = 3 := by
  rw [← span_directions_eq_kernel a b ha hb]
  simpa using finrank_span_eq_card (directions_linearIndependent a b ha hb)

end WeightedTorusJets.W12

end

end SiegelZeros

end OAI
