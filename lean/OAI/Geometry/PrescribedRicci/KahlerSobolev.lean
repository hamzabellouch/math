import Mathlib
import OAI.Geometry.PrescribedRicci.GlobalKahlerIntegral
import OAI.Geometry.PrescribedRicci.KahlerEnergyCutoff
import OAI.Geometry.PrescribedRicci.KahlerSobolevLocal

namespace OAI

/-! Kahler Sobolev. -/

section

 

noncomputable section
open Matrix Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped ContDiff Classical NNReal ENNReal
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {A : ComplexAtlas d X}

lemma partition_lpNorm_le (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {q : ℝ≥0} (hq : 1 ≤ q) :
    lpNorm φ.value q g.volumeMeasure ≤
      ∑ i, lpNorm ((chartPartition i).product φ).value q g.volumeMeasure := by
  have he : φ.value = ∑ i : Fin A.count, ((chartPartition i).product φ).value := by
    funext x
    simp only [Finset.sum_apply, SmoothRealFunction.product]
    rw [← Finset.sum_mul, chartPartition_sum, one_mul]
  rw [he]
  apply lpNorm_sum_le
  · intro i _
    exact ((chartPartition i).product φ).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact_mod_cast hq

lemma partition_lpNorm_sq_le (g : KaehlerMetric A) (φ : SmoothRealFunction A)
    {q : ℝ≥0} (hq : 1 ≤ q) :
    (lpNorm φ.value q g.volumeMeasure)^2 ≤
      (A.count:ℝ) * ∑ i, (lpNorm ((chartPartition i).product φ).value q g.volumeMeasure)^2 := by
  have hh := g.partition_lpNorm_le φ hq
  have hs := (sq_le_sq₀ lpNorm_nonneg (Finset.sum_nonneg (fun _ _ => lpNorm_nonneg))).mpr hh
  refine hs.trans ?_
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : Fin A.count => (1:ℝ))
      (fun i => lpNorm ((chartPartition i).product φ).value q g.volumeMeasure)

 

theorem sobolev (g : KaehlerMetric A) (hd : 2 ≤ d) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ S : ℝ, 0 < S ∧ ∀ φ : SmoothRealFunction A,
      (lpNorm φ.value q g.volumeMeasure)^2 ≤
        S * (g.integral (g.energy φ φ).value + g.integral (fun x => φ.value x^2)) := by
  obtain ⟨q,hq,hqe⟩ := critical_exponent hd
  have hc (i : Fin A.count) := g.chart_sobolev i
    (isClosed_tsupport (chartPartition (A:=A) i).value).isCompact
    (chartPartition_support i) hq (by omega : 0 < d) hqe
  choose C hC hClocal using hc
  have hb (i : Fin A.count) := g.cutoff_integral_energy_bound (chartPartition i)
  choose B hB hBcut using hb
  let T : ℝ := (A.count:ℝ) * ∑ i, C i * B i
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun i _ => mul_nonneg (hC i).le (hB i).le))
  refine ⟨q,hq,1+T,by linarith,fun φ => ?_⟩
  let J := g.integral (g.energy φ φ).value + g.integral (fun x => φ.value x^2)
  have hJ : 0 ≤ J := add_nonneg (g.integral_nonneg (g.energy_nonneg φ))
    (g.integral_nonneg (fun _ => sq_nonneg _))
  have hlocal (i : Fin A.count) :
      (lpNorm ((chartPartition i).product φ).value q g.volumeMeasure)^2 ≤ C i * B i * J := by
    have hh := hClocal i ((chartPartition i).product φ) (product_support_left _ _)
    calc
      _ ≤ C i * g.integral (g.energy ((chartPartition i).product φ) ((chartPartition i).product φ)).value := hh
      _ ≤ C i * (B i * J) := mul_le_mul_of_nonneg_left (hBcut i φ) (hC i).le
      _ = _ := by ring
  calc
    _ ≤ (A.count:ℝ) * ∑ i, (lpNorm ((chartPartition i).product φ).value q g.volumeMeasure)^2 :=
      g.partition_lpNorm_sq_le φ (le_trans (by norm_num) hq.le)
    _ ≤ (A.count:ℝ) * ∑ i, C i * B i * J :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hlocal i)) (Nat.cast_nonneg _)
    _ = T * J := by rw [← Finset.sum_mul]; simp only [T, mul_assoc]
    _ ≤ _ := by change T*J ≤ (1+T)*J; nlinarith

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
