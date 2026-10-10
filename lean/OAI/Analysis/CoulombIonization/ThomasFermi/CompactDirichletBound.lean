import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchCoulombControl

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff NNReal

namespace CoulombAnalysis

lemma tfPartial_lipschitz_bound {g : TFSpace → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (i : Fin 3) (x : TFSpace) :
    |tfPartial g i x| ≤ (L:ℝ) := by
  have hh := (fderiv ℝ g x).le_opNorm (EuclideanSpace.single i 1)
  simp only [PiLp.norm_single,norm_one,mul_one] at hh
  exact hh.trans (norm_fderiv_le_of_lipschitz ℝ hg)

lemma tfPartial_support {g : TFSpace → ℝ} (i : Fin 3) :
    Function.support (tfPartial g i) ⊆ tsupport g :=
  subset_tsupport _ |>.trans (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1))

lemma compact_partial_energy_bound {g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (hl : LipschitzWith L g)
    (hs : tsupport g ⊆ closedBall 0 r) (i : Fin 3) :
    (∫ x, (tfPartial g i x)^2) ≤ volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 := by
  have hi : Integrable (fun x => (tfPartial g i x)^2) :=
    ((tfPartial_continuous hg i).pow 2).integrable_of_hasCompactSupport
      (by simpa only [pow_two] using (tfPartial_compact hcg i).mul_right (f' := tfPartial g i))
  have hzero : ∀ x, x ∉ closedBall (0 : TFSpace) r → (tfPartial g i x)^2 = 0 := by
    intro x hx
    have hz : tfPartial g i x = 0 := Function.notMem_support.mp (fun hh => hx (hs (tfPartial_support i hh)))
    simp [hz]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  calc
    _ ≤ ∫ _x in closedBall (0 : TFSpace) r, (L:ℝ)^2 :=
      integral_mono hi.integrableOn (integrableOn_const (measure_closedBall_lt_top.ne))
        (fun x => by
          have hh := tfPartial_lipschitz_bound hl i x
          nlinarith [sq_abs (tfPartial g i x),abs_nonneg (tfPartial g i x),L.coe_nonneg])
    _ = _ := by rw [setIntegral_const,smul_eq_mul]

lemma compact_dirichlet_bound {g : TFSpace → ℝ} {L : ℝ≥0} {r : ℝ}
    (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g) (hl : LipschitzWith L g)
    (hs : tsupport g ⊆ closedBall 0 r) :
    (∑ i : Fin 3, ∫ x, (tfPartial g i x)^2) ≤
      3*volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 := by
  calc
    _ ≤ ∑ _i : Fin 3, volume.real (closedBall (0 : TFSpace) r)*(L:ℝ)^2 :=
      Finset.sum_le_sum (fun i _ => compact_partial_energy_bound hg hcg hl hs i)
    _ = _ := by simp; ring

end CoulombAnalysis

end

end OAI
