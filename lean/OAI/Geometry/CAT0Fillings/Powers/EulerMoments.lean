import Mathlib
import OAI.Geometry.CAT0Fillings.Powers.Absorption
import OAI.Geometry.CAT0Fillings.Powers.ClosedLimit

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_euler_power (hz : IsCycle T) (P : q.Sobolev) {γ p A n S C : ℝ}
    (hγ : 1 < γ) (hp : 2 < p) (hA : 0 < A) (hn : 0 < n) (hS : 0 < S) (hC : 0 ≤ C)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    (hv : MemLp (fun x => (q.inclusion P x)^γ) 2 (MassMeasure.currentMassMeasure hT))
    (hs : ∀ R : q.Sobolev,
      MemLp (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ∧
      S*(lpNorm (q.inclusion R) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT))^2 ≤
        A*‖q.closedGradient R‖^2+C*‖q.inclusion R‖^2)
    (heuler : ∀ R : q.Sobolev,
      A*inner ℝ (q.closedGradient P) (q.closedGradient R)+n*inner ℝ (q.inclusion P) (q.inclusion R) =
      n*(∫ x, (q.inclusion P x)^(p-1)*q.inclusion R x ∂MassMeasure.currentMassMeasure hT)) :
    ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => (q.inclusion P x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion P (q.atlasParam w))^(γ-1)) • q.closedGradient P w) := by
  classical
  have hQ (j : ℕ) := q.closed_truncated_power hz P hP hγ (show 0 < (j:ℝ)+1 by positivity)
  choose Q hQv hQG using hQ
  have hR (j : ℕ) := q.closed_truncated_power hz P hP (show 1 < 2*γ-1 by linarith)
    (show 0 < (j:ℝ)+1 by positivity)
  choose R hRv hRG using hR
  let M := ∫ x, ((q.inclusion P x)^γ)^2 ∂MassMeasure.currentMassMeasure hT
  have hM : 0 ≤ M := integral_nonneg fun _ => sq_nonneg _
  have hvI : Integrable (fun x => ((q.inclusion P x)^γ)^2) (MassMeasure.currentMassMeasure hT) := by
    simpa only [Real.norm_eq_abs,sq_abs] using hv.integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  have hMj (j : ℕ) : ‖q.inclusion (Q j)‖^2 ≤ M := by
    rw [l2_norm_sq]
    simp only [Real.norm_eq_abs,sq_abs]
    apply integral_mono_ae (by simpa only [Real.norm_eq_abs,sq_abs] using
      (Lp.memLp (q.inclusion (Q j))).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)) hvI
    filter_upwards [hQv j,hP] with x hx hp
    rw [hx]
    exact (sq_le_sq₀ (truncatedPower_nonneg (by positivity)) (Real.rpow_nonneg hp _)).mpr
      (truncatedPower_le_power hγ (by positivity) hp)
  obtain ⟨L,B,hL,hB,hLj,hBj⟩ := power_absorption hp hA hn (power_ratio_pos hγ) hS hC hM
    (q.inclusion P) (hs P).1 (fun j => q.inclusion (Q j)) (fun j => ‖q.closedGradient (Q j)‖^2)
    (fun j => (hs (Q j)).1) (fun j => sq_nonneg _) hMj (fun j => (hs (Q j)).2)
    (fun j => q.truncated_power_energy hz P (Q j) (R j) hγ (by positivity) hp hA.le hn.le hP
      (hQv j) (hRv j) (hQG j) (hRG j) (heuler (R j)))
  apply q.closed_power_of_truncated_bound P hγ hP hv Q hQv hQG
  intro j
  exact (Real.le_sqrt (norm_nonneg _) hB).mpr (hBj j)

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.ClosedCalculus
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma memLp_power_iff {f : α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ f x) {a b : ℝ} (ha : 0 < a) :
    MemLp (fun x => (f x)^a) (ENNReal.ofReal b) μ ↔ MemLp f (ENNReal.ofReal (a*b)) μ := by
  have he : ENNReal.ofReal (a*b) / ENNReal.ofReal a = ENNReal.ofReal b := by
    rw [←ENNReal.ofReal_div_of_pos ha]
    congr 1
    field_simp
  have hh := memLp_norm_rpow_iff (p := ENNReal.ofReal (a*b)) hf
    (show ENNReal.ofReal a ≠ 0 by positivity) ENNReal.ofReal_ne_top
  rw [he,ENNReal.toReal_ofReal ha.le] at hh
  have hae : (fun x => ‖f x‖^a) =ᵐ[μ] (fun x => (f x)^a) := by
    filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg hx]
  exact (memLp_congr_ae hae).symm.trans hh

lemma all_moments_of_power_gain [IsFiniteMeasure μ] {f : α → ℝ} {p : ℝ}
    (hp : 2 < p) (hpos : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hfp : MemLp f (ENNReal.ofReal p) μ)
    (hgain : ∀ a : ℝ, 1 < a → MemLp (fun x => (f x)^a) 2 μ →
      MemLp (fun x => (f x)^a) (ENNReal.ofReal p) μ) :
    ∀ b : ℝ, 0 < b → MemLp f (ENNReal.ofReal b) μ := by
  let l (j : ℕ) : ℝ := p*(p/2)^j
  have hl (j : ℕ) : p ≤ l j := by
    exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ (by linarith : 1 ≤ p/2))
  have hlj : ∀ j, MemLp f (ENNReal.ofReal (l j)) μ := by
    intro j
    induction j with
    | zero => simpa only [l,pow_zero,mul_one] using hfp
    | succ j hj =>
      have ha : 1 < l j/2 := by have := hl j; linarith
      have hi : MemLp (fun x => (f x)^(l j/2)) 2 μ := by
        have hb := (memLp_power_iff hfp.aestronglyMeasurable hpos (show 0 < l j/2 by linarith) (b := 2)).mpr
          (show MemLp f (ENNReal.ofReal (l j/2*2)) μ by simpa only [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] using hj)
        simpa using hb
      have hh := (memLp_power_iff hfp.aestronglyMeasurable hpos (show 0 < l j/2 by linarith) (b := p)).mp
        (hgain (l j/2) ha hi)
      convert hh using 1
      dsimp [l]
      rw [pow_succ]
      ring_nf
  have ht : Tendsto l atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by linarith : 1 < p/2)).const_mul_atTop (by linarith : 0 < p)
  intro b hb
  obtain ⟨j,hj⟩ := Filter.Eventually.exists (ht.eventually (eventually_ge_atTop b))
  exact (hlj j).mono_exponent (ENNReal.ofReal_le_ofReal hj)

end CAT0Fillings.ClosedCalculus
end

end OAI
