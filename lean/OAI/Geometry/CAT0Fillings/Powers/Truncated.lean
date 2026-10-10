import Mathlib
import OAI.Geometry.CAT0Fillings.Swept.Current
import OAI.Geometry.CAT0Fillings.Calculus.Piecewise

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def truncatedPower (γ N t : ℝ) : ℝ :=
  max t 0 * (min (max t 0) N)^(γ-1)

lemma truncatedPower_nonneg {γ N t : ℝ} (hN : 0 ≤ N) : 0 ≤ truncatedPower γ N t :=
  mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (le_min (le_max_right _ _) hN) _)

lemma truncatedPower_of_nonneg {γ N t : ℝ} (ht : 0 ≤ t) :
    truncatedPower γ N t = t*(min t N)^(γ-1) := by
  simp only [truncatedPower,max_eq_left ht]

lemma truncatedPower_of_le {γ N t : ℝ} (hγ : 1 < γ) (ht : 0 ≤ t) (htN : t ≤ N) :
    truncatedPower γ N t = t^γ := by
  rw [truncatedPower_of_nonneg ht,min_eq_left htN]
  by_cases ht0 : t = 0
  · simp only [ht0,zero_mul,Real.zero_rpow (by linarith : γ ≠ 0)]
  · have htp : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    calc
      t*t^(γ-1) = t^(1:ℝ)*t^(γ-1) := by rw [Real.rpow_one]
      _ = t^(1+(γ-1)) := (Real.rpow_add htp _ _).symm
      _ = t^γ := by congr 1; ring

lemma truncatedPower_of_ge {γ N t : ℝ} (ht : 0 ≤ t) (hNt : N ≤ t) :
    truncatedPower γ N t = t*N^(γ-1) := by
  rw [truncatedPower_of_nonneg ht,min_eq_right hNt]

lemma truncatedPower_lipschitz {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    ∃ K : ℝ≥0, LipschitzWith K (truncatedPower γ N) := by
  let C : ℝ≥0 := ⟨γ*N^(γ-1),mul_nonneg (by linarith) (Real.rpow_nonneg hN.le _)⟩
  have hp : LipschitzOnWith C (fun t : ℝ => t^γ) (Icc 0 N) := by
    apply (convex_Icc (0:ℝ) N).lipschitzOnWith_of_nnnorm_deriv_le
    · intro t ht
      exact (Real.hasDerivAt_rpow_const (Or.inr (by linarith : 1 ≤ γ))).differentiableAt
    · intro t ht
      rw [←NNReal.coe_le_coe,coe_nnnorm,
        (Real.hasDerivAt_rpow_const (x := t) (Or.inr (by linarith : 1 ≤ γ))).deriv,
        Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1 _))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1 ht.2 (by linarith)) (by linarith)
  let b (t : ℝ) := min (max t 0) N
  have hb : LipschitzWith 1 b := (LipschitzWith.id.max_const (0:ℝ)).min_const N
  have hbS (t : ℝ) : b t ∈ Icc 0 N := ⟨le_min (le_max_right _ _) hN.le,min_le_right _ _⟩
  have hbp : LipschitzWith C (fun t => (b t)^γ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hp.dist_le_mul (b x) (hbS x) (b y) (hbS y)).trans
      (mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul] using hb.dist_le_mul x y) C.coe_nonneg)
  have hr := (LipschitzWith.id.max_const (0:ℝ)).sub hb
  have hl := hbp.add ((lipschitzWith_smul (N^(γ-1))).comp hr)
  refine ⟨C + ‖N ^ (γ - 1)‖₊ * (1 + 1),?_⟩
  convert hl using 1
  funext t
  symm
  dsimp [Function.comp_def,b,id_eq]
  by_cases htN : max t 0 ≤ N
  · rw [min_eq_left htN,sub_self,mul_zero,add_zero]
    exact (truncatedPower_of_le hγ (le_max_right t 0) htN).symm.trans (by simp only [truncatedPower,max_eq_left (le_max_right t 0)])
  · rw [min_eq_right (le_of_not_ge htN)]
    dsimp [truncatedPower]
    rw [min_eq_right (le_of_not_ge htN)]
    have hpN : N^γ = N*N^(γ-1) := (truncatedPower_of_le hγ hN.le le_rfl).symm.trans (by rw [truncatedPower_of_nonneg hN.le,min_self])
    rw [hpN]
    ring

lemma truncatedPower_hasDerivAt_low {γ N t : ℝ} (hγ : 1 < γ) (ht : 0 < t) (htN : t < N) :
    HasDerivAt (truncatedPower γ N) (γ*t^(γ-1)) t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun s : ℝ => s^γ) := by
    filter_upwards [Ioo_mem_nhds ht htN] with s hs
    exact truncatedPower_of_le hγ hs.1.le hs.2.le
  exact (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).congr_of_eventuallyEq he

lemma truncatedPower_hasDerivAt_high {γ N t : ℝ} (hN : 0 < N) (ht : N < t) :
    HasDerivAt (truncatedPower γ N) (N^(γ-1)) t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun s : ℝ => s*N^(γ-1)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    exact truncatedPower_of_ge (hN.trans hs).le hs.le
  simpa only [one_mul] using ((hasDerivAt_id t).mul_const (N^(γ-1))).congr_of_eventuallyEq he

lemma truncatedPower_hasDerivAt_neg {γ N t : ℝ} (ht : t < 0) :
    HasDerivAt (truncatedPower γ N) 0 t := by
  have he : truncatedPower γ N =ᶠ[𝓝 t] (fun _ : ℝ => (0:ℝ)) := by
    filter_upwards [eventually_lt_nhds ht] with s hs
    simp only [truncatedPower,max_eq_right hs.le,zero_mul]
  exact (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq he

lemma truncatedPower_differentiable {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N)
    (ht : t ∉ ({0,N} : Set ℝ)) : DifferentiableAt ℝ (truncatedPower γ N) t := by
  simp only [mem_insert_iff,mem_singleton_iff,not_or] at ht
  rcases lt_or_gt_of_ne ht.1 with h | h
  · exact (truncatedPower_hasDerivAt_neg h).differentiableAt
  · rcases lt_or_gt_of_ne ht.2 with h' | h'
    · exact (truncatedPower_hasDerivAt_low hγ h h').differentiableAt
    · exact (truncatedPower_hasDerivAt_high hN h').differentiableAt

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ClosedCalculus
noncomputable def truncatedPowerSlope (γ N t : ℝ) : ℝ :=
  if t < N then γ*t^(γ-1) else N^(γ-1)
lemma truncatedPower_deriv_smul {E : Type*} [AddCommGroup E] [Module ℝ E]
    {γ N t : ℝ} (hγ : 1 < γ) (hN : 0 < N) (ht : 0 ≤ t) (v : E)
    (h0 : t = 0 → v = 0) (hNs : t = N → v = 0) :
    deriv (truncatedPower γ N) t • v = truncatedPowerSlope γ N t • v := by
  by_cases ht0 : t = 0
  · rw [h0 ht0,smul_zero,smul_zero]
  by_cases htN : t = N
  · rw [hNs htN,smul_zero,smul_zero]
  have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
  rcases lt_or_gt_of_ne htN with hlt | hgt
  · rw [(truncatedPower_hasDerivAt_low hγ htpos hlt).deriv,truncatedPowerSlope,ite_eq_left hlt]
  · rw [(truncatedPower_hasDerivAt_high hN hgt).deriv,truncatedPowerSlope,ite_eq_right hgt.not_gt]

end CAT0Fillings.ClosedCalculus

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma truncated_deriv_ae (hz : IsCycle T) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    (fun w => deriv (truncatedPower γ N) (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) =ᵐ[q.atlasMeasure]
      (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  have hp : ∀ᵐ w ∂q.atlasMeasure, 0 ≤ q.inclusion P (q.atlasParam w) :=
    q.atlas_preserving.quasiMeasurePreserving.ae (p := fun x : X => 0 ≤ q.inclusion P x) hP
  filter_upwards [hp,q.closedGradient_level_zero hz P 0,q.closedGradient_level_zero hz P N]
    with w hp hz0 hzN
  exact truncatedPower_deriv_smul hγ hN hp _ hz0 hzN

lemma closed_truncated_power (hz : IsCycle T) (P : q.Sobolev)
    (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x)
    {γ N : ℝ} (hγ : 1 < γ) (hN : 0 < N) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => truncatedPower γ N (q.inclusion P x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => truncatedPowerSlope γ N (q.inclusion P (q.atlasParam w)) • q.closedGradient P w) := by
  obtain ⟨K,hK⟩ := truncatedPower_lipschitz hγ hN
  obtain ⟨Q,hQ,hG⟩ := q.closed_chain_countable hK (((Set.finite_singleton N).insert 0).to_countable)
    (fun t ht => truncatedPower_differentiable hγ hN ht) hz P
  exact ⟨Q,hQ,hG.trans (q.truncated_deriv_ae hz P hP hγ hN)⟩

end CAT0Fillings.ChartGeometry
end

end OAI
