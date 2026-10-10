import OAI.Probability.InvariantIsing.Cavity.CavityFieldPath
import OAI.Probability.InvariantIsing.Fields.FieldPublishedPairInput

namespace OAI

/-! The scalar variances in the published field marking input coincide
with the finite spectral cavity covariance increments. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepVariance_eq_height_sub (h : FieldStep) (i : Fin h.depth) :
    (fieldStepVariance h i : ℝ) = h.height i.succ - h.height i.castSucc := by
  rw [fieldStepVariance, dite_eq_left i.isLt]
  have hg : (scalarFieldIncrements h).get
      ⟨i, by simpa only [scalarFieldIncrements_length] using i.isLt⟩ =
      ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
    exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
      NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) _
  rw [hg]
  change (fieldIncrement h i.succ).2 = _
  simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero,
    dite_false, Nat.add_sub_cancel]
  rfl

variable {ι : Type*} [Fintype ι]

theorem cavityFieldStep_variance (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (i : Fin n) :
    (fieldStepVariance
      (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i : ℝ) =
      (finiteR rho lam hrho hsum (deficit p (q i.castSucc)) -
        finiteR rho lam hrho hsum (deficit p (q i.succ))) / cut i.castSucc.succ := by
  rw [fieldStepVariance_eq_height_sub
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0) i]
  change cavityFieldPrimitive rho lam hrho hsum p (q i.succ) -
    cavityFieldPrimitive rho lam hrho hsum p (q i.castSucc) = _
  rw [cavityFieldPrimitive_sub]
  calc
    _ = ∫ r in q i.castSucc..q i.succ,
        deriv (finiteR rho lam hrho hsum) (deficit p r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le
        (hq (Fin.castSucc_lt_succ (i := i))).le
      intro r hr
      exact cavityRDerivative_eq_deriv rho lam hrho hsum
        (finite_overlap_deficit_pos p cut hfirst hlast q hq.monotone hp htop
          (hr.2.le.trans (hq.monotone (Fin.le_last _))))
    _ = _ := finite_overlap_field_increment rho lam hrho hsum p cut hcut
      hfirst hlast q hq hp htop i

theorem cavityFieldStep_root_variance (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {n : ℕ} (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : Monotone q) (hq0 : ∀ i, 0 ≤ q i)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) :
    (cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq hq0).height 0 =
      q 0 * deriv (finiteR rho lam hrho hsum) (deficit p (q 0)) := by
  change (∫ r in 0..q 0, cavityFieldDensity rho lam hrho hsum p r) = _
  calc
    _ = ∫ r in 0..q 0, deriv (finiteR rho lam hrho hsum) (deficit p r) := by
      apply intervalIntegral.integral_congr_Ioo_of_le (hq0 0)
      intro r hr
      exact cavityRDerivative_eq_deriv rho lam hrho hsum
        (finite_overlap_deficit_pos p cut hfirst hlast q hq hp htop
          (hr.2.le.trans (hq (Fin.le_last _))))
    _ = _ := finite_overlap_field_root rho lam hrho hsum p cut hcut
      hfirst hlast q hq hp

end InvariantIsing

end

end OAI
