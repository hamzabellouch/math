import Mathlib
import OAI.Geometry.CAT0Fillings.Compactness.Ascoli
import OAI.Geometry.CAT0Fillings.Compactness.Atlas

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace CAT0Fillings.JointBV
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

lemma lintegral_enorm_rpow_eq (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ^p ∂μ) = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le,←ENNReal.rpow_mul]
  simp [hp.ne']

lemma eLpNorm_two_interpolation (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 2 < p) :
    eLpNorm f 2 μ ^ (2:ℝ) ≤ eLpNorm f 1 μ ^ ((p-2)/(p-1)) *
      eLpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) := by
  have hp1 : 0 < p-1 := by linarith
  let a := (p-2)/(p-1)
  let b := 1/(p-1)
  have ha : 0 ≤ a := div_nonneg (by linarith) hp1.le
  have hb : 0 ≤ b := div_nonneg zero_le_one hp1.le
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hsum : a+p*b=2 := by dsimp [a,b]; field_simp; ring
  have hh := ENNReal.lintegral_mul_norm_pow_le hf.aemeasurable.enorm
    (hf.aemeasurable.enorm.pow_const p) ha hb hab
  have he : (fun x => ‖f x‖ₑ^a*(‖f x‖ₑ^p)^b) = fun x => ‖f x‖ₑ^(2:ℝ) := by
    ext x
    rw [←ENNReal.rpow_mul,←ENNReal.rpow_add_of_nonneg a (p*b) ha (mul_nonneg (by linarith) hb),hsum]
  rw [he,lintegral_enorm_rpow_eq hf (by norm_num : (0:ℝ)<2),
    lintegral_enorm_rpow_eq hf (by linarith : 0<p),←eLpNorm_one_eq_lintegral_enorm hf,
    ←ENNReal.rpow_mul] at hh
  simpa only [ENNReal.ofReal_ofNat,a,b,mul_one_div] using hh

lemma lpNorm_two_sq_interpolation (h1 : MemLp f 1 μ) {p : ℝ} (hp : 2 < p)
    (hpMem : MemLp f (ENNReal.ofReal p) μ) :
    lpNorm f 2 μ ^ 2 ≤ lpNorm f 1 μ ^ ((p-2)/(p-1)) *
      lpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) := by
  have hh := eLpNorm_two_interpolation h1.aestronglyMeasurable hp
  have hp1 : 0 < p-1 := by linarith
  have hp2 : 0 < p-2 := by linarith
  have hp0 : 0 < p := by linarith
  have hr : eLpNorm f 1 μ ^ ((p-2)/(p-1)) * eLpNorm f (ENNReal.ofReal p) μ ^ (p/(p-1)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity) h1.eLpNorm_ne_top
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity) hpMem.eLpNorm_ne_top
  have hh' := ENNReal.toReal_mono hr hh
  simpa only [ENNReal.toReal_mul,←ENNReal.toReal_rpow,toReal_eLpNorm,
    Real.rpow_two] using hh'

end CAT0Fillings.JointBV
end

section

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open JointBV Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

omit [Nonempty X] in
lemma dist_value [Nonempty X] {u v : X → ℝ} {K J : ℝ≥0}
    (hu : LipschitzWith K u) (hv : LipschitzWith J v) :
    dist (value (hT := hT) hu) (value hv) =
      lpNorm (fun x => u x-v x) 2 (MassMeasure.currentMassMeasure hT) := by
  rw [dist_eq_norm,value,value,←MemLp.toLp_sub ((boundedLip_of_lipschitz hu).memLp 2)
    ((boundedLip_of_lipschitz hv).memLp 2),Lp.norm_toLp,toReal_eLpNorm]
  rfl

lemma totallyBounded_value_of_lpBound {ι : Type*} {p : ℝ} (hp : 2 < p)
    (u : ι → X → ℝ) (L : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (h1 : TotallyBounded (range fun j => value1 (hT := hT) (hu j)))
    (C : ℝ≥0) (hC : ∀ j, lpNorm (u j) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ C) :
    TotallyBounded (range fun j => value (hT := hT) (hu j)) := by
  let μ := MassMeasure.currentMassMeasure hT
  let a := (p-2)/(p-1)
  let b := p/(p-1)
  have ha : 0 < a := div_pos (by linarith) (by linarith)
  have hb : 0 ≤ b := div_nonneg (by linarith) (by linarith)
  have hp' : 1 ≤ ENNReal.ofReal p := by rw [←ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  apply totallyBounded_range_of_control h1
  intro ε hε
  have ht : Tendsto (fun t : ℝ => t^a*(2*(C:ℝ))^b) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq,Real.zero_rpow ha.ne',zero_mul] using
      ((continuous_id.tendsto (0:ℝ)).rpow_const (Or.inr ha.le)).mul_const ((2*(C:ℝ))^b)
  obtain ⟨δ,hδ,hd⟩ := Metric.mem_nhds_iff.mp (ht (Iio_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨δ,hδ,?_⟩
  intro i j hij
  have hmem1 : MemLp (fun x => u i x-u j x) 1 μ :=
    ((boundedLip_of_lipschitz (hu i)).memLp 1).sub ((boundedLip_of_lipschitz (hu j)).memLp 1)
  have hmemp : MemLp (fun x => u i x-u j x) (ENNReal.ofReal p) μ :=
    ((boundedLip_of_lipschitz (hu i)).memLp _).sub ((boundedLip_of_lipschitz (hu j)).memLp _)
  have hh := lpNorm_two_sq_interpolation hmem1 hp hmemp
  have he1 : lpNorm (fun x => u i x-u j x) 1 μ = dist (value1 (hT := hT) (hu i)) (value1 (hu j)) := by
    rw [dist_value1,lpNorm_one_eq_integral_norm hmem1.aestronglyMeasurable]
    rfl
  have hep : lpNorm (fun x => u i x-u j x) (ENNReal.ofReal p) μ ≤ 2*(C:ℝ) := by
    have hh := lpNorm_sub_le (g := u j) ((boundedLip_of_lipschitz (hu i)).memLp (μ := μ) (ENNReal.ofReal p)) hp'
    change lpNorm (u i-u j) (ENNReal.ofReal p) μ ≤ 2*(C:ℝ)
    exact hh.trans ((add_le_add (hC i) (hC j)).trans_eq (by ring))
  have hmono := Real.rpow_le_rpow lpNorm_nonneg hep hb
  have hsmall : (dist (value1 (hT := hT) (hu i)) (value1 (hu j)))^a*(2*(C:ℝ))^b < ε^2 := by
    apply hd
    simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hij
  rw [he1] at hh
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg dist_nonneg a))
  have hd2 := (hh'.trans_lt hsmall)
  rw [←dist_value (hT := hT) (hu i) (hu j)] at hd2
  nlinarith [dist_nonneg (x := value (hT := hT) (hu i)) (y := value (hT := hT) (hu j))]

theorem totallyBounded_value {ι : Type*}
    (h : Slicing.NormalApprox (k+1) T) (hz : boundarySucc T = 0) (hX : IsCAT0 X)
    (u : ι → X → ℝ) (L U : ι → ℝ≥0) (hu : ∀ j, LipschitzWith (L j) (u j))
    (hU : ∀ j x, |u j x| ≤ U j)
    (M : ℝ≥0) (hMv : ∀ j, ‖value (hT := hT) (hu j)‖ ≤ M)
    (hMg : ∀ j, ‖q.gradient (hu j)‖ ≤ M)
    {p : ℝ} (hp : 2 < p) (C : ℝ≥0)
    (hC : ∀ j, lpNorm (u j) (ENNReal.ofReal p) (MassMeasure.currentMassMeasure hT) ≤ C) :
    TotallyBounded (range fun j => value (hT := hT) (hu j)) :=
  totallyBounded_value_of_lpBound (hT := hT) hp u L hu
    (q.totallyBounded_value1 h hz hX u L U hu hU M hMv hMg) C hC

end CAT0Fillings.ChartGeometry
end

end OAI
