import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FiniteTensorProjection

namespace OAI

/-! Exact coefficient norms for finite tensor synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem finiteTensorState_mass {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (c : (Fin n → α) → ℂ) :
    Coulomb.mass (finiteTensorState v hv hL2 hpartial c) = ∑ b, ‖c b‖^2 := by
  rw [← Coulomb.H1Vector.toHilbert_norm_sq,finiteTensorState_toHilbert]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  calc
    (↑(‖∑ b, c b • Coulomb.tensorHilbert v hL2 b‖^2) : ℂ) =
        inner ℂ (∑ b, c b • Coulomb.tensorHilbert v hL2 b)
          (∑ b, c b • Coulomb.tensorHilbert v hL2 b) := by
      simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
      rfl
    _ = ∑ b, (starRingEnd ℂ) (c b)*c b :=
      (Coulomb.tensorHilbert_orthonormal v hL2 ho).inner_sum c c Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [starRingEnd_apply,Complex.ofReal_pow] using Complex.conj_mul' (c b)

theorem finiteTensorProjection_mass_le {n : ℕ} {α : Type*} [Fintype α]
    (v : α → Position → Fin 2 → ℂ)
    (hv : ∀ a s, ContDiff ℝ 1 (fun x => v a x s))
    (hL2 : ∀ a s, MemLp (fun x => v a x s) 2)
    (hpartial : ∀ a s b, MemLp (fun x => fderiv ℝ (fun y => v a y s) x
      (EuclideanSpace.single b 1)) 2)
    (ho : ∀ a b, (∑ t : Fin 2, ∫ y, star (v a y t)*v b y t) =
      if a=b then (1:ℂ) else 0) (u : Coulomb.H1Vector n) :
    Coulomb.mass (finiteTensorProjection v hv hL2 hpartial u) ≤ Coulomb.mass u := by
  rw [finiteTensorProjection_mass_decomposition v hv hL2 hpartial ho u]
  exact le_add_of_nonneg_right (Coulomb.mass_nonneg _)

end ContinuumCoulomb

end

end OAI
