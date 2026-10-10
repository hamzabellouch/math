import OAI.Geometry.CylinderCovering.Beams.Radial
import OAI.Geometry.CylinderCovering.Radial.Riemann

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CylinderCovering.BeamNeighborhoodRealization
open RadialRiemann

lemma taggedSum_error_of_lipschitz {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (htag : IsTagged 0 1 N tag) :
    |(∑ i : Fin N, step 0 1 N*f (tag i))-(∫ t in (0:ℝ)..1, f t)| ≤
      (K:ℝ)*step 0 1 N := by
  have hcont := hf.continuousOn
  have hF : ContinuousOn (fun p : ℝ × ℝ => f p.2)
      ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1)) :=
    hcont.comp continuous_snd.continuousOn (fun _ hp => hp.2)
  have he := mixedSum_error (F := fun _ t => f t) (by norm_num : (0:ℝ)<1) hF hN tag tag
    (E := (K:ℝ)*step 0 1 N) (by
      intro i t ht
      have hh := hf.dist_le_mul (tag i) (cell_subset (by norm_num) i (htag i))
        t (cell_subset (by norm_num) i ht)
      rw [Real.dist_eq] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left (cell_dist_le (htag i) ht) K.coe_nonneg))
  simpa only [mixedSum, sub_zero, mul_one] using he

lemma beamWeight_contDiff (a : ℝ) :
    ContDiff ℝ 1 (fun p => 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)) := by
  have hfun : (fun p => 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)) =
      (fun p => 1/Real.sqrt (1+((1-a*(2-a)*p^2)^2+
        (-1+a*(2-a)*(1-p)^2)^2)/2)) := by
    funext p
    rw [ShortenedBeam.velocity_norm_sq]
  rw [hfun]
  apply ContDiff.div contDiff_const
  · apply ContDiff.sqrt
    · fun_prop
    · intro p
      positivity
  · intro p
    positivity

lemma beamWeight_lipschitz (a : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K
      (fun p => 1/Real.sqrt (1+‖ShortenedBeam.velocity a p‖^2)) (Icc (0:ℝ) 1) :=
  (beamWeight_contDiff a).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_Icc _ _) isCompact_Icc

lemma padded_radius_area_bound {N δ s : ℝ} (hN : 0 ≤ N) (hN2 : N ≤ 2)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hs : 1 ≤ s) :
    δ*(N+11*δ+2*δ^2)^2/(4*s) ≤ δ*N^2/(4*s)+56*δ^2 := by
  have hs0 : 0 < s := by linarith
  have hδ2 : δ^2 ≤ δ := by nlinarith
  have hR : N+11*δ+2*δ^2 ≤ N+13*δ := by nlinarith
  have hR0 : 0 ≤ N+11*δ+2*δ^2 := by positivity
  have hsq := mul_self_le_mul_self hR0 hR
  have hNd := mul_le_mul_of_nonneg_right hN2 hδ
  have hsq' : (N+11*δ+2*δ^2)^2 ≤ N^2+221*δ := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hsq' hδ
  have hss := mul_le_mul_of_nonneg_right hs (sq_nonneg δ)
  apply (div_le_iff₀ (by positivity : 0 < 4*s)).mpr
  rw [add_mul,div_mul_cancel₀ _ (by positivity : 4*s ≠ 0)]
  nlinarith

lemma summed_padding_bound {f : ℝ → ℝ} {K : NNReal}
    (hf : LipschitzOnWith K f (Icc (0:ℝ) 1)) {N : ℕ} (hN : 0 < N)
    (tag : Fin N → ℝ) (htag : IsTagged 0 1 N tag) (c : Fin N → ℝ) (R : ℝ)
    (hc : ∀ i, c i ≤ R^2/4*(step 0 1 N*f (tag i))+56*(step 0 1 N)^2) :
    (∑ i, c i) ≤ R^2/4*(∫ t in (0:ℝ)..1, f t)+
      (R^2*(K:ℝ)/4+56)*step 0 1 N := by
  have he := (abs_le.mp (taggedSum_error_of_lipschitz hf hN tag htag)).2
  have hsum : (∑ i, c i) ≤
      R^2/4*(∑ i : Fin N, step 0 1 N*f (tag i))+56*step 0 1 N := by
    calc
      _ ≤ ∑ i : Fin N, (R^2/4*(step 0 1 N*f (tag i))+56*(step 0 1 N)^2) :=
        Finset.sum_le_sum (fun i _ => hc i)
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        congr 1
        have hcount := count_step (a:=0) (b:=1) hN
        calc
          (N:ℝ)*(56*(step 0 1 N)^2) = 56*step 0 1 N*((N:ℝ)*step 0 1 N) := by ring
          _ = _ := by rw [hcount]; ring
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ R^2/4)
  nlinarith

end CylinderCovering.BeamNeighborhoodRealization

end

end OAI
