import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.IntegratedStability

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
namespace CoulombAnalysis
open CoulombAtom

private theorem grid_increment_error {G d P D : ℝ → ℝ}
    (hG : DeficitSecants G d) (hP : DeficitSecants P D)
    {a h η : ℝ} (ha : 0 < a) (hh : 0 < h) {N : ℕ}
    (hclose : ∀ i ≤ N, |d (a + i * h) - D (a + i * h)| ≤ η) :
    |(G (a + N * h) - G a) - (P (a + N * h) - P a)| ≤
      h * (D (a + N * h) - D a) + N * h * η := by
  have hind : ∀ i ≤ N,
      |(G (a + i * h) - G a) - (P (a + i * h) - P a)| ≤
        h * (D (a + i * h) - D a) + i * h * η := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
      have hiN : i ≤ N := Nat.le_trans (Nat.le_succ i) hi
      have hix : 0 < a + i * h := by positivity
      have hxy : a + i * h < a + (i + 1 : ℕ) * h := by
        push_cast
        nlinarith
      have hsG := hG (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hsP := hP (a + i * h) (a + (i + 1 : ℕ) * h) hix hxy
      have hcl := (abs_le.mp (hclose i hiN))
      have hcr := (abs_le.mp (hclose (i + 1) hi))
      have hcl' := mul_le_mul_of_nonneg_left hcl.1 hh.le
      have hcr' := mul_le_mul_of_nonneg_left hcr.2 hh.le
      have heq : a + (i + 1 : ℕ) * h - (a + i * h) = h := by
        push_cast
        ring
      rw [heq] at hsG hsP
      have hstep : |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| ≤
          h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η := by
        apply abs_le.mpr
        constructor <;> nlinarith [hsG.1, hsG.2, hsP.1, hsP.2]
      have htel : (G (a + (i + 1 : ℕ) * h) - G a) -
          (P (a + (i + 1 : ℕ) * h) - P a) =
          ((G (a + i * h) - G a) - (P (a + i * h) - P a)) +
          ((G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
          (P (a + (i + 1 : ℕ) * h) - P (a + i * h))) := by ring
      rw [htel]
      calc
        _ ≤ |(G (a + i * h) - G a) - (P (a + i * h) - P a)| +
            |(G (a + (i + 1 : ℕ) * h) - G (a + i * h)) -
            (P (a + (i + 1 : ℕ) * h) - P (a + i * h))| := abs_add_le _ _
        _ ≤ (h * (D (a + i * h) - D a) + i * h * η) +
            (h * (D (a + (i + 1 : ℕ) * h) - D (a + i * h)) + h * η) :=
          add_le_add (ih hiN) hstep
        _ = _ := by push_cast; ring
  exact hind N le_rfl

theorem deficit_secant_increments_tendsto_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {P D : ℝ → ℝ}
    (hG : ∀ n, DeficitSecants (G n) (d n)) (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (D t)))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => G n b - G n a) l (𝓝 (P b - P a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * ((b - a) * (D b - D a)) / ε))
  have hN1 : (1 : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hNpos : (0 : ℝ) < N := lt_trans zero_lt_one hN1
  have hwidth : 0 < b - a := sub_pos.mpr hab
  let h : ℝ := (b - a) / N
  let η : ℝ := ε / (2 * (b - a))
  have hh : 0 < h := div_pos hwidth hNpos
  have hη : 0 < η := div_pos hε (by positivity)
  have hxN : a + N * h = b := by dsimp [h]; field_simp; ring
  have hmesh : h * (D b - D a) < ε / 2 := by
    have hnr : 2 * ((b - a) * (D b - D a)) / ε < N :=
      (le_max_right _ _).trans_lt hN
    have hnr' := (div_lt_iff₀ hε).mp hnr
    dsimp [h]
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff₀ hNpos (show (0 : ℝ) < 2 by norm_num)).mpr
    nlinarith
  have hηeq : (N : ℝ) * h * η = ε / 2 := by
    dsimp [h, η]
    field_simp
  have hev : ∀ i : Fin (N + 1), ∀ᶠ n in l,
      |d n (a + (i : ℕ) * h) - D (a + (i : ℕ) * h)| ≤ η := by
    intro i
    have hxi : 0 < a + (i : ℕ) * h := by positivity
    exact ((Metric.tendsto_nhds.mp (hd _ hxi)) η hη).mono fun n hn =>
      le_of_lt (by simpa only [Real.dist_eq] using hn)
  filter_upwards [Filter.eventually_all.mpr hev] with n hn
  rw [Real.dist_eq]
  have he := grid_increment_error (hG n) hP ha hh
    (N := N) (η := η) (fun i hi => hn ⟨i, Nat.lt_succ_iff.mpr hi⟩)
  rw [hxN, hηeq] at he
  linarith

theorem deficit_secant_energy_tendsto_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {P D : ℝ → ℝ}
    {err : ι → ℝ} (hG : ∀ n, DeficitSecants (G n) (d n))
    (hP : DeficitSecants P D)
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (D t)))
    (he : Tendsto err l (𝓝 0))
    (hzero : ∀ v, 0 < v → ∀ᶠ n in l, -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    (hPc : ContinuousAt P 0) (hP0 : P 0 = 0) (hDc : ContinuousAt D 0)
    {t : ℝ} (ht : 0 < t) : Tendsto (fun n => G n t) l (𝓝 (P t)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hc : ContinuousAt (fun v : ℝ => |P v| + |v * D v|) 0 :=
    hPc.abs.add ((continuousAt_id.mul hDc).abs)
  have hevent : ∀ᶠ v in 𝓝 (0 : ℝ), |P v| + |v * D v| < ε / 4 := by
    have hconv : Tendsto (fun v : ℝ => |P v| + |v * D v|) (𝓝 0) (𝓝 0) := by
      simpa [hP0] using hc.tendsto
    exact hconv.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by positivity))
  obtain ⟨δ, hδ, hδevent⟩ := Metric.eventually_nhds_iff.mp hevent
  let v : ℝ := min (t / 2) (δ / 2)
  have hv : 0 < v := lt_min (by positivity) (by positivity)
  have hvt : v < t := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hvδ : dist v 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hv]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hsmall := hδevent hvδ
  have hinc := deficit_secant_increments_tendsto_filter hG hP hd hv hvt
  have hbound : Tendsto (fun n => err n + v * d n v) l (𝓝 (v * D v)) := by
    simpa using he.add ((hd v hv).const_mul v)
  filter_upwards [(Metric.tendsto_nhds.mp hinc) (ε / 4) (by positivity),
    (Metric.tendsto_nhds.mp hbound) (ε / 4) (by positivity), hzero v hv] with n hn hb hz
  rw [Real.dist_eq] at hn hb ⊢
  have hGv : |G n v| ≤ err n + v * d n v := by
    rw [abs_of_nonpos hz.2]
    linarith [hz.1]
  have hbound' : err n + v * d n v < |v * D v| + ε / 4 := by
    have hb' := (abs_lt.mp hb).2
    linarith [le_abs_self (v * D v)]
  have halg : G n t - P t =
      ((G n t - G n v) - (P t - P v)) + (G n v - P v) := by ring
  rw [halg]
  have htri := abs_add_le ((G n t - G n v) - (P t - P v)) (G n v - P v)
  have hsub := abs_sub (G n v) (P v)
  linarith

theorem priced_energy_limits_filter {ι : Type*} {l : Filter ι} {G d : ι → ℝ → ℝ} {err : ι → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hG : ∀ n, DeficitSecants (G n) (d n))
    (hd : ∀ t : ℝ, 0 < t → Tendsto (fun n => d n t) l (𝓝 (limitDeficit q t)))
    (he : Tendsto err l (𝓝 0))
    (hzero : ∀ n v, 0 < v → -err n - v * d n v ≤ G n v ∧ G n v ≤ 0)
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => G n t) l (𝓝 (limitPriceEnergy q t)) ∧
    Tendsto (fun n => G n t + t * d n t) l (𝓝 (limitSectorEnergy q t)) := by
  have hprice := deficit_secant_energy_tendsto_filter hG (deficitSecants_limitPriceEnergy hq)
    hd he (fun v hv => Eventually.of_forall fun n => hzero n v hv) (continuous_limitPriceEnergy q).continuousAt
    (by simp [limitPriceEnergy]) (continuous_limitDeficit q).continuousAt ht
  exact ⟨hprice, by simpa only [limitPriceEnergy_add ht] using hprice.add ((hd t ht).const_mul t)⟩

end CoulombAnalysis

open MeasureTheory Filter Set Metric Topology

end

end OAI
