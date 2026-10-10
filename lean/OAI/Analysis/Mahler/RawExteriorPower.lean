import OAI.Analysis.Mahler.ExteriorAlternatization
import OAI.Analysis.Mahler.WedgeAlgebra

namespace OAI

open scoped TensorProduct

namespace Mahler
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Tensor product of scalar multilinear forms before alternatization. -/
def rawProduct (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    MultilinearMap ℝ (fun _ : ι ⊕ κ => E) ℂ :=
  (LinearMap.mul' ℝ ℂ).compMultilinearMap (a.domCoprod b)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
@[simp] lemma rawProduct_apply [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) (v : ι ⊕ κ → E) :
    rawProduct a b v = a (fun i => v (Sum.inl i)) * b (fun i => v (Sum.inr i)) := rfl

/-- The actual shuffle normalization is exactly full alternatization of a
raw tensor product; no factorial is silently inserted. -/
theorem rawProduct_alternatization (a : MultilinearMap ℝ (fun _ : ι => E) ℂ)
    (b : MultilinearMap ℝ (fun _ : κ => E) ℂ) :
    (rawProduct a b).alternatization = wedge a.alternatization b.alternatization := by
  unfold rawProduct wedge
  rw [← MultilinearMap.domCoprod_alternization,
    ← LinearMap.compMultilinearMap_alternatization]

/-- The raw ordered product of k bilinear factors. -/
def rawPower (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) :
    (k : ℕ) → MultilinearMap ℝ (fun _ : WedgePowerSlots k => E) ℂ
  | 0 => MultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℂ)
  | k+1 => rawProduct B (rawPower B k)

theorem rawPower_alternatization (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    (rawPower B k).alternatization = wedgePower B.alternatization k := by
  induction k with
  | zero =>
    change ((AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℂ)).toMultilinearMap).alternatization =
      AlternatingMap.constOfIsEmpty ℝ E (Fin 0) (1 : ℂ)
    rw [AlternatingMap.coe_alternatization]
    exact one_nsmul _
  | succ k ih =>
    rw [show wedgePowerSlotsDecidableEq (k+1) =
      (inferInstance : DecidableEq (Fin 2 ⊕ WedgePowerSlots k)) from Subsingleton.elim _ _]
    change (rawProduct B (rawPower B k)).alternatization = _
    rw [rawProduct_alternatization, ih]
    rfl

def rawCovector (a : E →ₗ[ℝ] ℂ) : MultilinearMap ℝ (fun _ : Fin 1 => E) ℂ :=
  MultilinearMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a

@[simp] lemma rawCovector_apply (a : E →ₗ[ℝ] ℂ) (v : Fin 1 → E) : rawCovector a v = a (v 0) := rfl

lemma rawCovector_alternatization (a : E →ₗ[ℝ] ℂ) :
    (rawCovector a).alternatization = AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a := by
  ext v
  simp [MultilinearMap.alternatization_apply, MultilinearMap.domDomCongr_apply]

def rawBoundary (a : E →ₗ[ℝ] ℂ) (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    MultilinearMap ℝ (fun _ : Fin 1 ⊕ WedgePowerSlots k => E) ℂ :=
  rawProduct (rawCovector a) (rawPower B k)

theorem rawBoundary_alternatization (a : E →ₗ[ℝ] ℂ)
    (B : MultilinearMap ℝ (fun _ : Fin 2 => E) ℂ) (k : ℕ) :
    (rawBoundary a B k).alternatization =
      wedge (AlternatingMap.ofSubsingleton ℝ E ℂ (0 : Fin 1) a)
        (wedgePower B.alternatization k) := by
  rw [rawBoundary, rawProduct_alternatization, rawCovector_alternatization, rawPower_alternatization]

end
end Mahler

end OAI
