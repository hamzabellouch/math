import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.LinearAlgebra.Pi

namespace OAI

namespace Laughlin.Fock

abbrev Orbital (Q : ℕ) := Fin (Q+1) → ℂ
abbrev Space (Q : ℕ) := ExteriorAlgebra ℂ (Orbital Q)

noncomputable def mode {Q : ℕ} (i : Fin (Q+1)) : Orbital Q := Pi.single i 1

noncomputable def create {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) where
  toFun x := ExteriorAlgebra.ι ℂ (mode i) * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by simp

noncomputable def annihilate {Q : ℕ} (i : Fin (Q+1)) : Module.End ℂ (Space Q) :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Orbital Q))) (LinearMap.proj i)

theorem annihilate_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * annihilate j + annihilate j * annihilate i = 0 := by
  ext x
  change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (CliffordAlgebra.contractLeft (LinearMap.proj j) x) +
    CliffordAlgebra.contractLeft (LinearMap.proj j)
      (CliffordAlgebra.contractLeft (LinearMap.proj i) x) = 0
  rw [CliffordAlgebra.contractLeft_comm]
  exact neg_add_cancel _

theorem create_anticommute {Q : ℕ} (i j : Fin (Q+1)) :
    create i * create j + create j * create i = 0 := by
  ext x
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ExteriorAlgebra.ι_add_mul_swap, zero_mul]

theorem mixed_car {Q : ℕ} (i j : Fin (Q+1)) :
    annihilate i * create j + create j * annihilate i =
      (if i = j then (1 : ℂ) else 0) • (1 : Module.End ℂ (Space Q)) := by
  ext x
  change CliffordAlgebra.contractLeft (LinearMap.proj i)
      (ExteriorAlgebra.ι ℂ (mode j) * x) +
    ExteriorAlgebra.ι ℂ (mode j) * CliffordAlgebra.contractLeft (LinearMap.proj i) x =
      (if i = j then (1 : ℂ) else 0) • x
  rw [CliffordAlgebra.contractLeft_ι_mul, sub_add_cancel]
  by_cases h : i = j
  · subst j
    simp [mode, LinearMap.proj]
  · simp [mode, LinearMap.proj, h]

theorem annihilate_sq {Q : ℕ} (i : Fin (Q+1)) : annihilate i * annihilate i = 0 := by
  have h : (2 : ℂ) • (annihilate i * annihilate i) = 0 := by
    simpa only [two_smul] using annihilate_anticommute i i
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

theorem create_sq {Q : ℕ} (i : Fin (Q+1)) : create i * create i = 0 := by
  ext x
  change ExteriorAlgebra.ι ℂ (mode i) * (ExteriorAlgebra.ι ℂ (mode i) * x) = 0
  rw [← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

end Laughlin.Fock

end OAI
