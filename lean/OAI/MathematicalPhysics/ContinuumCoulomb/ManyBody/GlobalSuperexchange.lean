import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.HubbardExcitation

namespace OAI

/-! Exact global Hubbard second-order compression on the spin sector. -/

noncomputable section
namespace ContinuumCoulomb.HubbardGlobal
open Laughlin.Fock
open scoped BigOperators

variable {Edge : Type*} [Fintype Edge]

def graphHopping (m : ℕ) (left right : Edge → Fin (m + 1)) (t : Edge → ℂ) :
    Module.End ℂ (Space (2 * m + 1)) := ∑ e, t e • siteHopping m (left e) (right e)

/-- Only the matching graph edge survives an inverse compression. -/
theorem hopping_inverse_graphHopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (s : SourceSpinBasis (m + 1)) (e : Edge) :
    lowProjection m (siteHopping m (left e) (right e)
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) =
        t e • (((U - V (left e) (right e))⁻¹ : ℝ) : ℂ) •
          ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap (left e) (right e) s))) := by
  classical
  simp only [graphHopping, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  rw [Finset.sum_eq_single e]
  · rw [hopping_inverse_hopping_spinWedge m U V hsymm hdiag s (left e) (right e) (hloop e)]
  · intro f _ hfe
    obtain ⟨hparallel, hreverse⟩ := hsimple e f (Ne.symm hfe)
    rw [cross_hopping_inverse_hopping_spinWedge m U V hsymm hdiag s
      (left e) (right e) (left f) (right f) (hloop e) (hloop f) hparallel hreverse, smul_zero]
  · intro he
    exact (he (Finset.mem_univ e)).elim

/-- The actual global inverse compression is the sum of the local
exchange terms, with the Coulomb-corrected denominator on every edge. -/
theorem graphHopping_inverse_graphHopping_spinWedge (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (s : SourceSpinBasis (m + 1)) :
    lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) =
        ∑ e, t e ^ 2 • (((U - V (left e) (right e))⁻¹ : ℝ) : ℂ) •
          ((2 : ℂ) • (spinWedge m s - spinWedge m (sourceSpinSwap (left e) (right e) s))) := by
  classical
  change lowProjection m ((∑ e, t e • siteHopping m (left e) (right e))
    (chargeInverse m U V (graphHopping m left right t (spinWedge m s)))) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro e _
  rw [hopping_inverse_graphHopping_spinWedge m U V hsymm hdiag left right t hloop hsimple s e]
  simp only [smul_smul, pow_two, mul_assoc]

/-- Choosing `t_e² = J_e (U-V_e)` gives the genuine Heisenberg inverse
term, including the scalar `-J_e I` on every edge. -/
theorem graphSuperexchange_calibrated (m : ℕ) (U : ℝ)
    (V : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hsymm : ∀ i j, V i j = V j i) (hdiag : ∀ i, V i i = 0)
    (left right : Edge → Fin (m + 1)) (t J : Edge → ℂ)
    (hloop : ∀ e, left e ≠ right e)
    (hsimple : ∀ e f, e ≠ f →
      ¬(left e = left f ∧ right e = right f) ∧ ¬(left e = right f ∧ right e = left f))
    (hgap : ∀ e, U - V (left e) (right e) ≠ 0)
    (hcal : ∀ e, t e ^ 2 = J e * ((U - V (left e) (right e) : ℝ) : ℂ))
    (s : SourceSpinBasis (m + 1)) :
    -(lowProjection m (graphHopping m left right t
      (chargeInverse m U V (graphHopping m left right t (spinWedge m s))))) =
        ∑ e, J e • ((siteHeisenberg (siteMode m (left e) 0) (siteMode m (left e) 1)
          (siteMode m (right e) 0) (siteMode m (right e) 1) - 1) (spinWedge m s)) := by
  rw [graphHopping_inverse_graphHopping_spinWedge m U V hsymm hdiag left right t hloop hsimple s,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro e _
  have hgapC : ((U - V (left e) (right e) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hgap e
  have hcoeff : t e ^ 2 * ((((U - V (left e) (right e))⁻¹ : ℝ) : ℂ)) = J e := by
    rw [hcal e, Complex.ofReal_inv, mul_assoc, mul_inv_cancel₀ hgapC, mul_one]
  rw [smul_smul, hcoeff]
  simp only [LinearMap.sub_apply, Module.End.one_apply,
    siteHeisenberg_spinWedge m s (left e) (right e) (hloop e), smul_sub, two_smul, smul_add]
  abel

end ContinuumCoulomb.HubbardGlobal

end

end OAI
