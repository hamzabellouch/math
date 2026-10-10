import OAI.Probability.FreeIsing.Estimates.RelabelMeasure
import OAI.Probability.FreeIsing.Spectral.KoopmanInvolutions
import OAI.Probability.FreeIsing.Spectral.LocalOrthogonality
import OAI.Probability.FreeIsing.Trees.Escape

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

theorem local_koopman_inner_eq_zero_of_depth {d : ℕ}
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0)
    (g : TreeAut d)
    (hdepth : s.sup (fun v => v.1.length) + s.sup (fun v => v.1.length) <
      (g.toEquiv TreeEscape.root).1.length) :
    inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f) = 0 := by
  classical
  have hdisj : Disjoint s (s.map g.toEquiv.symm.toEmbedding) := by
    rw [Finset.map_eq_image]
    exact (TreeEscape.disjoint_inverse_image_of_root_depth g s s hdepth).symm
  have hFzero : (∫ U, F (fun i => U i) ∂labelMeasure d) = 0 :=
    (integral_congr_ae hf).symm.trans hzero
  have hright := (measurePreserving_relabel g).quasiMeasurePreserving.ae hf
  have hkoop := Lp.coeFn_compMeasurePreserving f (measurePreserving_relabel g)
  calc
    inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f) =
        ∫ U, F (fun i => U i) * F (fun i => U (g.toEquiv.symm i))
          ∂labelMeasure d := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf, hright, hkoop] with U hU hUg hK
      change koopmanL2 (relabel g) (measurePreserving_relabel g) f U = f (relabel g U) at hK
      simp [hK, hU, hUg, relabel, mul_comm]
    _ = 0 := integral_mul_reindex_eq_zero_of_disjoint uniform01 s s g.toEquiv.symm
      hdisj F F hF hF hFzero

theorem exists_local_koopman_radial_bound {d : ℕ}
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0)
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
        C * q ^ (g.toEquiv TreeEscape.root).1.length := by
  let N := s.sup (fun v => v.1.length) + s.sup (fun v => v.1.length)
  let C := ‖f‖ ^ 2 / q ^ N
  have hC : 0 ≤ C := div_nonneg (sq_nonneg _) (pow_nonneg hq.le _)
  refine ⟨C, hC, ?_⟩
  intro g
  by_cases hn : N < (g.toEquiv TreeEscape.root).1.length
  · rw [local_koopman_inner_eq_zero_of_depth s f F hF hf hzero g hn, abs_zero]
    exact mul_nonneg hC (pow_nonneg hq.le _)
  · have hpow : q ^ N ≤ q ^ (g.toEquiv TreeEscape.root).1.length :=
      pow_le_pow_of_le_one hq.le hq1 (Nat.le_of_not_gt hn)
    calc
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
          ‖f‖ * ‖koopmanL2 (relabel g) (measurePreserving_relabel g) f‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖f‖ ^ 2 := by rw [koopmanL2_norm, pow_two]
      _ = C * q ^ N := by
        dsimp [C]
        rw [div_mul_cancel₀ _ (pow_ne_zero _ hq.ne')]
      _ ≤ C * q ^ (g.toEquiv TreeEscape.root).1.length :=
        mul_le_mul_of_nonneg_left hpow hC

theorem exists_local_koopman_critical_bound {d : ℕ} (hd : 3 ≤ d)
    (s : Finset (TreeVertex d)) (f : Lp ℝ 2 (labelMeasure d))
    (F : (s → ℝ) → ℝ) (hF : Measurable F)
    (hf : f =ᵐ[labelMeasure d] fun U => F (fun i => U i))
    (hzero : (∫ U, f U ∂labelMeasure d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : TreeAut d,
      |inner ℝ f (koopmanL2 (relabel g) (measurePreserving_relabel g) f)| ≤
        C * (Real.sqrt ((d : ℝ) - 1))⁻¹ ^ (g.toEquiv TreeEscape.root).1.length := by
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : 0 < Real.sqrt ((d : ℝ) - 1) := Real.sqrt_pos.mpr (by linarith)
  apply exists_local_koopman_radial_bound s f F hF hf hzero (inv_pos.mpr hs)
  apply inv_le_one_of_one_le₀
  apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 0 ≤ (d : ℝ) - 1)).2
  norm_num
  linarith

end Problem367

end

end OAI
