import Mathlib
import OAI.Probability.SLE.ChartMeasurability
import OAI.Probability.SLE.SpatialMeans
import OAI.Probability.SLE.StoppedMeasures

namespace OAI

/-! Window Geometry for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def sourceSpatialWindowSet (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : Set ℝ≥0 :=
  {t | liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) ∧
    (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t)}
noncomputable def sourceSpatialWindowTime (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : WithTop ℝ≥0 :=
  if (sourceSpatialWindowSet γ z r ε R).Nonempty then
    ↑(sInf (sourceSpatialWindowSet γ z r ε R)) else ⊤
noncomputable def sourceSpatialWindowH (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
    z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
    dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z ≤ ε then 1 else 0
noncomputable def sourceSpatialWindowB (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
    z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
    R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z then 1 else 0

 

def SourceSpatialWindowGeometryTarget : Prop :=
  ∀ (U : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
  Continuous U → IsCapacityTwoWitness U γ G F →
  ∀ (κ : ℝ), 0 < κ → κ < 8 → ∀ (z : ℂ) (ε r R : ℝ),
  0 < ε → ε < r → r < R → r ≤ z.im →
  let σ := liveSpatialHitTime γ z r
  let τ := sourceSpatialWindowTime γ z r ε R
  let H := sourceSpatialWindowH γ z r ε R
  let B := sourceSpatialWindowB γ z r ε R
  let W := spatialGreenWeight κ U γ G z ε
  σ ≤ τ ∧
  (∀ t : ℝ≥0, σ ≤ (t : WithTop ℝ≥0) → (t : WithTop ℝ≥0) < τ →
    z ∈ survivingDomain γ t ∧ ε < dist (γ t) z ∧ dist (γ t) z < R) ∧
  (τ = ⊤ → H = 0 ∧ B = 0) ∧
  (σ = ⊤ → τ = ⊤) ∧
  0 ≤ H ∧ H ≤ 1 ∧ 0 ≤ B ∧ B ≤ 1 ∧
  H ≤ (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ∧
  (B = 1 → ∃ t : ℝ≥0, σ ≤ (t : WithTop ℝ≥0) ∧
    z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z ∧
    (t : WithTop ℝ≥0) < liveSpatialHitTime γ z ε) ∧
  (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ≤ H+B ∧
  W ≤ W*H + ε^(-codimension κ)*B

lemma source_liveHit_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) (t : ℝ≥0)
    (ht : liveSpatialHitTime γ z r = t) :
    z ∈ survivingDomain γ t ∧ dist (γ t) z = r := by
  rw [liveSpatialHitTime_eq hc z r hs] at ht
  split_ifs at ht with hn hl
  · exact (WithTop.coe_ne_top ht.symm).elim
  · constructor
    · simpa only [ht, WithTop.untopD_coe] using hl
    · exact spatialHitTime_mem hc z r t ht
  · exact (WithTop.coe_ne_top ht.symm).elim

lemma source_liveHit_le (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) (t : ℝ≥0)
    (hl : z ∈ survivingDomain γ t) (hd : dist (γ t) z ≤ r) :
    liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) := by
  unfold liveSpatialHitTime
  rw [ite_eq_left ⟨t, hl, hd⟩]
  exact WithTop.coe_le_coe.mpr (csInf_le ⟨0, fun _ _ => bot_le⟩ ⟨hl, hd⟩)

lemma source_liveHit_antitone {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) {ε r : ℝ} (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r ≤ liveSpatialHitTime γ z ε := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hmem := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
  rw [← ht]
  exact source_liveHit_le γ z r t hmem.1 (hmem.2.le.trans her)

lemma source_windowSet_closed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) : IsClosed (sourceSpatialWindowSet γ z r ε R) := by
  have hl : IsOpen {t : ℝ≥0 | z ∈ survivingDomain γ t} := by
    let gp : C(ℝ≥0,ℂ) := ⟨γ,hc⟩
    exact source_survival_open.preimage
      ((continuous_const.prodMk continuous_id).prodMk continuous_const :
        Continuous (fun t : ℝ≥0 => ((gp,t),z)))
  exact (isClosed_le continuous_const (WithTop.continuous_coe : Continuous ((↑) : ℝ≥0 → WithTop ℝ≥0))).inter
    ((isClosed_le (hc.dist continuous_const) continuous_const).union
      ((isClosed_le continuous_const (hc.dist continuous_const)).union hl.isClosed_compl))

lemma source_window_le_of_mem (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ)
    (t : ℝ≥0) (ht : t ∈ sourceSpatialWindowSet γ z r ε R) :
    sourceSpatialWindowTime γ z r ε R ≤ (t : WithTop ℝ≥0) := by
  unfold sourceSpatialWindowTime
  rw [ite_eq_left ⟨t,ht⟩]
  exact WithTop.coe_le_coe.mpr (csInf_le ⟨0,fun _ _ => bot_le⟩ ht)

lemma source_window_mem {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (t : ℝ≥0)
    (ht : sourceSpatialWindowTime γ z r ε R = t) :
    t ∈ sourceSpatialWindowSet γ z r ε R := by
  unfold sourceSpatialWindowTime at ht
  split_ifs at ht with hn
  · have he := WithTop.coe_injective ht
    rw [← he]
    exact (source_windowSet_closed hc z r ε R).csInf_mem hn ⟨0,fun _ _ => bot_le⟩
  · exact (WithTop.coe_ne_top ht.symm).elim

lemma source_window_start_le {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) :
    liveSpatialHitTime γ z r ≤ sourceSpatialWindowTime γ z r ε R := by
  by_cases hn : sourceSpatialWindowTime γ z r ε R = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← ht]
  exact (source_window_mem hc z r ε R t ht.symm).1

lemma source_before_window (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ)
    (t : ℝ≥0) (hs : liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0))
    (ht : (t : WithTop ℝ≥0) < sourceSpatialWindowTime γ z r ε R) :
    z ∈ survivingDomain γ t ∧ ε < dist (γ t) z ∧ dist (γ t) z < R := by
  have hh : ¬ (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t) := by
    intro hh
    exact not_le_of_gt ht (source_window_le_of_mem γ z r ε R t ⟨hs,hh⟩)
  push Not at hh
  exact ⟨hh.2.2,hh.1,hh.2.1⟩

lemma source_window_le_fine {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowTime γ z r ε R ≤ liveSpatialHitTime γ z ε := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · rw [hn]; exact le_top
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hm := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
  rw [← ht]
  exact source_window_le_of_mem γ z r ε R t
    ⟨by simpa only [← ht] using source_liveHit_antitone hc z her hs, Or.inl hm.2.le⟩

lemma source_windowH_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    sourceSpatialWindowH γ z r ε R = 1 ↔
      sourceSpatialWindowTime γ z r ε R = liveSpatialHitTime γ z ε ∧
      liveSpatialHitTime γ z ε ≠ ⊤ := by
  constructor
  · intro hH
    have hh : sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
        z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
        dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z ≤ ε := by
      simpa only [sourceSpatialWindowH, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using hH
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hh.1
    have hm : z ∈ survivingDomain γ t ∧ dist (γ t) z ≤ ε := by
      simpa only [← ht, WithTop.untopD_coe] using hh.2
    have hf := source_liveHit_le γ z ε t hm.1 hm.2
    rw [ht] at hf
    have he := le_antisymm (source_window_le_fine hc z r ε R her hs) hf
    exact ⟨he, he ▸ hh.1⟩
  · rintro ⟨he,hn⟩
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
    have hm := source_liveHit_mem hc z ε (her.trans hs) t ht.symm
    simp only [sourceSpatialWindowH, he, ← ht, WithTop.coe_ne_top, ne_eq, not_false_eq_true,
      WithTop.untopD_coe, hm.1, hm.2.le, and_self, ite_true]

lemma source_windowB_before {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hrR : r < R)
    (hs : r ≤ dist (γ 0) z) (hB : sourceSpatialWindowB γ z r ε R = 1) :
    ∃ t : ℝ≥0, liveSpatialHitTime γ z r ≤ (t : WithTop ℝ≥0) ∧
      z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z ∧
      (t : WithTop ℝ≥0) < liveSpatialHitTime γ z ε := by
  have hh : sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
        z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopD 0) ∧
        R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopD 0)) z := by
    simpa only [sourceSpatialWindowB, ite_eq_left_iff, zero_ne_one, imp_false, not_not] using hB
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hh.1
  have hm : z ∈ survivingDomain γ t ∧ R ≤ dist (γ t) z := by
    simpa only [← ht, WithTop.untopD_coe] using hh.2
  refine ⟨t,(source_window_mem hc z r ε R t ht.symm).1,hm.1,hm.2,?_⟩
  apply lt_of_le_of_ne (by simpa only [← ht] using source_window_le_fine hc z r ε R her hs)
  intro he
  have hf := (source_liveHit_mem hc z ε (her.trans hs) t he.symm).2
  linarith

lemma source_window_missed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (her : ε ≤ r) (hs : r ≤ dist (γ 0) z) :
    (if liveSpatialHitTime γ z ε = ⊤ then (0 : ℝ) else 1) ≤
      sourceSpatialWindowH γ z r ε R + sourceSpatialWindowB γ z r ε R := by
  by_cases hn : liveSpatialHitTime γ z ε = ⊤
  · simp only [ite_eq_left hn]
    unfold sourceSpatialWindowH sourceSpatialWindowB
    split_ifs <;> norm_num
  rw [ite_eq_right hn]
  obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
  have hle := source_window_le_fine hc z r ε R her hs
  have hwn : sourceSpatialWindowTime γ z r ε R ≠ ⊤ :=
    ne_top_of_le_ne_top hn hle
  obtain ⟨s,hs'⟩ := WithTop.ne_top_iff_exists.mp hwn
  have hst : s ≤ t := WithTop.coe_le_coe.mp (by simpa only [← ht,← hs'] using hle)
  have hl : z ∈ survivingDomain γ s := survivingDomain_antitone γ hst
    (source_liveHit_mem hc z ε (her.trans hs) t ht.symm).1
  have hm := (source_window_mem hc z r ε R s hs'.symm).2
  rcases hm with hd | hd | hd
  · have hH : sourceSpatialWindowH γ z r ε R = 1 := by
      simp only [sourceSpatialWindowH, ← hs', WithTop.coe_ne_top, ne_eq, not_false_eq_true,
        WithTop.untopD_coe, hl, hd, and_self, ite_true]
    rw [hH]; unfold sourceSpatialWindowB; split_ifs <;> norm_num
  · have hB : sourceSpatialWindowB γ z r ε R = 1 := by
      simp only [sourceSpatialWindowB, ← hs', WithTop.coe_ne_top, ne_eq, not_false_eq_true,
        WithTop.untopD_coe, hl, hd, and_self, ite_true]
    rw [hB]; unfold sourceSpatialWindowH; split_ifs <;> norm_num
  · exact (hd hl).elim

theorem sourceSpatialWindowGeometry_proved : SourceSpatialWindowGeometryTarget := by
  intro U γ G F hU hw κ hκ hκ8 z ε r R he her hrR hry
  have hs : r ≤ dist (γ 0) z := by
    rw [hw.2.1, dist_zero_left]
    exact hry.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
  dsimp only
  have hH0 : 0 ≤ sourceSpatialWindowH γ z r ε R := by
    unfold sourceSpatialWindowH; split_ifs <;> norm_num
  have hH1 : sourceSpatialWindowH γ z r ε R ≤ 1 := by
    unfold sourceSpatialWindowH; split_ifs <;> norm_num
  have hB0 : 0 ≤ sourceSpatialWindowB γ z r ε R := by
    unfold sourceSpatialWindowB; split_ifs <;> norm_num
  have hB1 : sourceSpatialWindowB γ z r ε R ≤ 1 := by
    unfold sourceSpatialWindowB; split_ifs <;> norm_num
  refine ⟨source_window_start_le hw.1 z r ε R,
    source_before_window γ z r ε R, ?_, ?_, hH0,hH1,hB0,hB1,?_,
    source_windowB_before hw.1 z r ε R her.le hrR hs,
    source_window_missed hw.1 z r ε R her.le hs, ?_⟩
  · intro ht
    simp only [sourceSpatialWindowH, sourceSpatialWindowB, ht, ne_eq, not_true_eq_false,
      false_and, ite_false, and_self]
  · intro ht
    exact top_le_iff.mp (by simpa only [ht] using source_window_start_le hw.1 z r ε R)
  · by_cases hn : liveSpatialHitTime γ z ε = ⊤
    · rw [ite_eq_left hn]
      have hh : sourceSpatialWindowH γ z r ε R ≠ 1 := by
        intro hh
        exact ((source_windowH_iff hw.1 z r ε R her.le hs).mp hh).2 hn
      unfold sourceSpatialWindowH at hh ⊢
      split_ifs at hh ⊢ <;> norm_num at *
    · rw [ite_eq_right hn]; exact hH1
  · have hW := hw.spatialGreenWeight_bound hU hκ hκ8 he z (her.le.trans hry)
    have hR : 0 ≤ ε ^ (-codimension κ) := Real.rpow_nonneg he.le _
    by_cases hh : sourceSpatialWindowH γ z r ε R = 1
    · rw [hh,mul_one]; exact le_add_of_nonneg_right (mul_nonneg hR hB0)
    have hh0 : sourceSpatialWindowH γ z r ε R = 0 := by
      unfold sourceSpatialWindowH at hh ⊢
      split_ifs at hh ⊢ <;> norm_num at *
    rw [hh0,mul_zero,zero_add]
    by_cases hn : liveSpatialHitTime γ z ε = ⊤
    · rw [spatialGreenWeight_eq_live hw.1 κ U G z ε (her.le.trans hs), ite_eq_left hn]
      exact mul_nonneg hR hB0
    · have hm := source_window_missed hw.1 z r ε R her.le hs
      rw [ite_eq_right hn,hh0,zero_add] at hm
      have hb := le_antisymm hB1 hm
      rw [hb,mul_one]
      exact hW.2

end
end SLEExactGauge

end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
local instance windowGeometryPathMeasurableSpace : MeasurableSpace C(ℝ≥0,ℂ) := borel _
local instance windowGeometryPathBorelSpace : BorelSpace C(ℝ≥0,ℂ) := ⟨rfl⟩
 
noncomputable def sourceCollarStart (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r : ℝ) : WithTop ℝ≥0 :=
  if z ∈ D then liveSpatialHitTime γ z r else ⊤
noncomputable def sourceCollarFinish (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : WithTop ℝ≥0 :=
  if z ∈ D then sourceSpatialWindowTime γ z r ε R else ⊤
noncomputable def sourceCollarH (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if z ∈ D then sourceSpatialWindowH γ z r ε R else 0
noncomputable def sourceCollarB (D : Set ℂ) (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) : ℝ :=
  if z ∈ D then sourceSpatialWindowB γ z r ε R else 0
 

def SourceSpatialWindowMeasurableTarget : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (κ : ℝ),
  0 < κ → κ < 8 → ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (D : Set ℂ), MeasurableSet D → ∀ ε r R : ℝ,
  0 < ε → ε < r → r < R → (∀ z ∈ D, r ≤ z.im) →
  let σ := fun z (ω : a.samples) => sourceCollarStart D (γ ω) z r
  let τ := fun z (ω : a.samples) => sourceCollarFinish D (γ ω) z r ε R
  let H := fun z (ω : a.samples) => sourceCollarH D (γ ω) z r ε R
  let B := fun z (ω : a.samples) => sourceCollarB D (γ ω) z r ε R
  let V := fun z (ω : a.samples) => spatialGreenWeight κ
    (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) z ε * H z ω
  (∃ (hσ : ∀ z, IsStoppingTime a.filtration (σ z))
    (hτ : ∀ z, IsStoppingTime a.filtration (τ z)),
    (∀ z, Measurable[(hτ z).measurableSpace] (H z) ∧
      Measurable[(hτ z).measurableSpace] (B z) ∧
      Measurable[(hτ z).measurableSpace] (V z)) ∧
    (∀ z, Measurable[(hσ z).measurableSpace] (fun ω =>
      if z ∈ D then spatialGreenWeight κ (fun t => Real.sqrt κ * a.B t ω)
        (γ ω) (a.G ω) z r else 0))) ∧
  Measurable (fun p : ℂ × a.samples => σ p.1 p.2) ∧
  Measurable (fun p : ℂ × a.samples => τ p.1 p.2) ∧
  Measurable (fun p : ℂ × a.samples => H p.1 p.2) ∧
  Measurable (fun p : ℂ × a.samples => B p.1 p.2) ∧
  Measurable (fun p : ℂ × a.samples => V p.1 p.2)

lemma source_window_le_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (T : ℝ≥0) :
    sourceSpatialWindowTime γ z r ε R ≤ (T : WithTop ℝ≥0) ↔
      ∃ t ∈ Icc (0 : ℝ≥0) T, t ∈ sourceSpatialWindowSet γ z r ε R := by
  constructor
  · intro hh
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hh)
    exact ⟨t,⟨bot_le, WithTop.coe_le_coe.mp (by simpa only [← ht] using hh)⟩,
      source_window_mem hc z r ε R t ht.symm⟩
  · rintro ⟨t,ht,hmem⟩
    exact (source_window_le_of_mem γ z r ε R t hmem).trans (WithTop.coe_le_coe.mpr ht.2)

lemma source_liveTime_eq_killed {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r : ℝ) (hs : r ≤ dist (γ 0) z) :
    liveSpatialHitTime γ z r =
      if z ∈ survivingDomain γ (spatialHitTime γ z r).untopA
      then spatialHitTime γ z r else ⊤ := by
  rw [liveSpatialHitTime_eq hc z r hs]
  by_cases hn : spatialHitTime γ z r = ⊤
  · simp only [hn, ite_self]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hn
    rw [ite_eq_right hn, ← ht]
    rfl

lemma source_live_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    {τ : a.samples → WithTop ℝ≥0} (hτ : IsStoppingTime a.filtration τ) :
    MeasurableSet[hτ.measurableSpace] {ω | z ∈ survivingDomain (γ ω) (τ ω).untopA} := by
  have hm := measurable_stoppedValue
    (source_killedChart_progressive a.measurable_B a.continuous_B κ
      (fun ω : a.samples => γ ω) a.G a.F a.witness z) hτ
  have he : {ω : a.samples | z ∈ survivingDomain (γ ω) (τ ω).untopA} =
      {ω : a.samples | 0 < (stoppedValue (fun t (ω : a.samples) =>
        if z ∈ survivingDomain (γ ω) t then a.G ω t z else 0) τ ω).im} := by
    ext ω
    change (z ∈ survivingDomain (γ ω) (τ ω).untopA) ↔
      0 < (if z ∈ survivingDomain (γ ω) (τ ω).untopA then a.G ω (τ ω).untopA z else 0).im
    by_cases hl : z ∈ survivingDomain (γ ω) (τ ω).untopA
    · simp only [hl, true_iff]
      exact (a.witness ω).2.2.2.2.2.1 _ hl
    · simp [hl]
  rw [he]
  exact measurableSet_lt measurable_const (Complex.measurable_im.comp hm)

lemma source_liveHit_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r : ℝ) (hy : r ≤ z.im) :
    IsStoppingTime a.filtration (fun ω : a.samples => liveSpatialHitTime (γ ω) z r) := by
  have hσ : IsStoppingTime a.filtration (fun ω : a.samples => spatialHitTime (γ ω) z r) :=
    a.diskHitAfter_stopping (fun _ => 0) (isStoppingTime_const a.filtration 0) z r
  have hA := source_live_stopped_measurable a z hσ
  intro T
  have he : {ω : a.samples | liveSpatialHitTime (γ ω) z r ≤ (T : WithTop ℝ≥0)} =
      {ω : a.samples | z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA} ∩
      {ω : a.samples | spatialHitTime (γ ω) z r ≤ (T : WithTop ℝ≥0)} := by
    ext ω
    have hs : r ≤ dist (γ ω 0) z := by
      rw [(a.witness ω).2.1, dist_zero_left]
      exact hy.trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z))
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [source_liveTime_eq_killed (a.trace_continuous ω) z r hs]
    by_cases hl : z ∈ survivingDomain (γ ω) (spatialHitTime (γ ω) z r).untopA
    · simp only [hl, true_and, ite_true]
    · simp only [hl, false_and, iff_false, ite_false]
      exact not_le_of_gt (WithTop.coe_lt_top _)
  rw [he]
  exact hA.2 T

 
lemma source_windowKernel_closed (T : ℝ≥0) (ε R : ℝ) :
    IsClosed {p : (ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ | ∃ t ∈ Icc (0 : ℝ≥0) T,
      p.1.1 ≤ t ∧ (dist (p.1.2 t) p.2 ≤ ε ∨ R ≤ dist (p.1.2 t) p.2 ∨
        p.2 ∉ survivingDomain p.1.2 t)} := by
  let A : Set (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) :=
    {p | p.1.1.1 ≤ p.2.1 ∧ (dist (p.1.1.2 p.2.1) p.1.2 ≤ ε ∨
      R ≤ dist (p.1.1.2 p.2.1) p.1.2 ∨ p.1.2 ∉ survivingDomain p.1.1.2 p.2.1)}
  have ht : Continuous (fun p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  have hv : Continuous (fun p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) =>
      p.1.1.2 p.2.1) := continuous_eval.comp (continuous_fst.fst.snd.prodMk ht)
  have hl : IsOpen {p : (((ℝ≥0 × C(ℝ≥0,ℂ)) × ℂ) × Icc (0 : ℝ≥0) T) |
      p.1.2 ∈ survivingDomain p.1.1.2 p.2.1} := source_survival_open.preimage
      ((continuous_fst.fst.snd.prodMk ht).prodMk continuous_fst.snd)
  have hA : IsClosed A := (isClosed_le continuous_fst.fst.fst ht).inter
    ((isClosed_le (hv.dist continuous_fst.snd) continuous_const).union
      ((isClosed_le continuous_const (hv.dist continuous_fst.snd)).union hl.isClosed_compl))
  have hp := isClosedMap_fst_of_compactSpace A hA
  convert hp using 1
  ext p
  simp only [A, Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Subtype.exists,
    exists_and_right, exists_eq_right]
  aesop

lemma source_min_time_coe (σ : WithTop ℝ≥0) (T : ℝ≥0) :
    (((min σ (T : WithTop ℝ≥0)).untopD 0 : ℝ≥0) : WithTop ℝ≥0) = min σ T := by
  have hn : min σ (T : WithTop ℝ≥0) ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  obtain ⟨s,hs⟩ := WithTop.ne_top_iff_exists.mp hn
  rw [← hs, WithTop.untopD_coe]

lemma source_window_kernel_iff {γ : ℝ≥0 → ℂ} (hc : Continuous γ)
    (z : ℂ) (r ε R : ℝ) (T : ℝ≥0) :
    sourceSpatialWindowTime γ z r ε R ≤ (T : WithTop ℝ≥0) ↔
    liveSpatialHitTime γ z r ≤ (T : WithTop ℝ≥0) ∧
    ∃ t ∈ Icc (0 : ℝ≥0) T, (min (liveSpatialHitTime γ z r) T).untopD 0 ≤ t ∧
      (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t) := by
  rw [source_window_le_iff hc z r ε R T]
  constructor
  · rintro ⟨t,ht,hs,he⟩
    have hT := hs.trans (WithTop.coe_le_coe.mpr ht.2)
    refine ⟨hT,t,ht,?_,he⟩
    apply WithTop.coe_le_coe.mp
    rw [source_min_time_coe, min_eq_left hT]
    exact hs
  · rintro ⟨hT,t,ht,hs,he⟩
    refine ⟨t,ht,?_,he⟩
    have hs' := WithTop.coe_le_coe.mpr hs
    rw [source_min_time_coe, min_eq_left hT] at hs'
    exact hs'

def sourceCapPath (γ : C(ℝ≥0,ℂ)) (T : ℝ≥0) : C(ℝ≥0,ℂ) :=
  ⟨fun t => γ (min t T), γ.continuous.comp (continuous_id.min continuous_const)⟩

lemma source_cap_domain (γ : C(ℝ≥0,ℂ)) (T t : ℝ≥0) (ht : t ≤ T) :
    survivingDomain (sourceCapPath γ T) t = survivingDomain γ t := by
  have he : sourceCapPath γ T '' Icc 0 t = γ '' Icc 0 t := by
    apply Set.image_congr
    intro s hs
    change γ (min s T) = γ s
    rw [min_eq_left (hs.2.trans ht)]
  simp only [survivingDomain, he]

lemma source_window_kernel_cap (γ : C(ℝ≥0,ℂ)) (z : ℂ) (ε R : ℝ) (T b : ℝ≥0) :
    (∃ t ∈ Icc (0 : ℝ≥0) T, b ≤ t ∧
      (dist (sourceCapPath γ T t) z ≤ ε ∨ R ≤ dist (sourceCapPath γ T t) z ∨
        z ∉ survivingDomain (sourceCapPath γ T) t)) ↔
    (∃ t ∈ Icc (0 : ℝ≥0) T, b ≤ t ∧
      (dist (γ t) z ≤ ε ∨ R ≤ dist (γ t) z ∨ z ∉ survivingDomain γ t)) := by
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  rw [source_cap_domain γ T t ht.2]
  have he : sourceCapPath γ T t = γ t := by dsimp [sourceCapPath]; rw [min_eq_left ht.2]
  rw [he]

lemma source_tracePath_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) :
    Measurable (fun ω : a.samples => (⟨γ ω,a.trace_continuous ω⟩ : C(ℝ≥0,ℂ))) := by
  apply source_path_measurable
  intro t
  exact (a.trace_adapted t).mono (a.filtration.le t) le_rfl

lemma source_capPath_adapted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (T : ℝ≥0) :
    Measurable[a.filtration T] (fun ω : a.samples =>
      sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T) := by
  refine @source_path_measurable a.samples ℂ (a.filtration T) _ _ _ _ _ _ _ _ ?_
  intro t
  exact (a.trace_adapted (min t T)).mono (a.filtration.mono (min_le_right _ _)) le_rfl

lemma source_window_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ) (hy : r ≤ z.im) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R) := by
  let σ := fun ω : a.samples => liveSpatialHitTime (γ ω) z r
  have hσ : IsStoppingTime a.filtration σ := source_liveHit_stopping a z r hy
  intro T
  have hm : Measurable[a.filtration T] (fun ω : a.samples => (min (σ ω) T).untopD 0) :=
    ((hσ.min_const T).measurable_of_le (fun _ => min_le_right _ _)).untopD 0
  have hp : Measurable[a.filtration T] (fun ω : a.samples =>
      (((min (σ ω) T).untopD 0, sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T),z)) :=
    (hm.prodMk (source_capPath_adapted a T)).prodMk measurable_const
  have hK := (source_windowKernel_closed T ε R).measurableSet.preimage hp
  have he : {ω : a.samples | sourceSpatialWindowTime (γ ω) z r ε R ≤ (T : WithTop ℝ≥0)} =
      {ω : a.samples | σ ω ≤ (T : WithTop ℝ≥0)} ∩
      {ω : a.samples | ∃ t ∈ Icc (0 : ℝ≥0) T, (min (σ ω) T).untopD 0 ≤ t ∧
        (dist (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T t) z ≤ ε ∨
         R ≤ dist (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T t) z ∨
         z ∉ survivingDomain (sourceCapPath ⟨γ ω,a.trace_continuous ω⟩ T) t)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [source_window_kernel_iff (a.trace_continuous ω) z r ε R T,
      source_window_kernel_cap]
    rfl
  rw [he]
  exact (hσ T).inter hK

lemma source_collarStart_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceCollarStart D (γ ω) z r) := by
  by_cases hz : z ∈ D
  · simpa only [sourceCollarStart, ite_eq_left hz] using source_liveHit_stopping a z r (hy z hz)
  · simpa only [sourceCollarStart, ite_eq_right hz] using (show IsStoppingTime a.filtration (fun _ => (⊤ : WithTop ℝ≥0)) from fun _ => MeasurableSet.const _)

lemma source_collarFinish_stopping
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) (z : ℂ) :
    IsStoppingTime a.filtration (fun ω : a.samples => sourceCollarFinish D (γ ω) z r ε R) := by
  by_cases hz : z ∈ D
  · simpa only [sourceCollarFinish, ite_eq_left hz] using source_window_stopping a z r ε R (hy z hz)
  · simpa only [sourceCollarFinish, ite_eq_right hz] using (show IsStoppingTime a.filtration (fun _ => (⊤ : WithTop ℝ≥0)) from fun _ => MeasurableSet.const _)

lemma source_joint_survival_measurable
    {X : Type*} [MeasurableSpace X] (g : X → C(ℝ≥0,ℂ)) (t : X → ℝ≥0) (z : X → ℂ)
    (hg : Measurable g) (ht : Measurable t) (hz : Measurable z) :
    MeasurableSet {x | z x ∈ survivingDomain (g x) (t x)} :=
  source_survival_open.measurableSet.preimage ((hg.prodMk ht).prodMk hz)

lemma source_collarStart_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarStart D (γ p.2) p.1 r) := by
  have hhit := spatialHitTime_measurable (fun ω : a.samples => γ ω) a.trace_continuous
    (fun t => (a.trace_adapted t).mono (a.filtration.le t) le_rfl) r
  have hl := source_joint_survival_measurable
    (fun p : ℂ × a.samples => (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ)))
    (fun p => (spatialHitTime (γ p.2) p.1 r).untopA) Prod.fst
    ((source_tracePath_measurable a).comp measurable_snd)
    (WithTop.measurable_untopA.comp hhit) measurable_fst
  have hm : Measurable (fun p : ℂ × a.samples =>
      if p.1 ∈ D then (if p.1 ∈ survivingDomain (γ p.2) (spatialHitTime (γ p.2) p.1 r).untopA
      then spatialHitTime (γ p.2) p.1 r else ⊤) else ⊤) :=
    Measurable.ite (hD.preimage measurable_fst)
    (Measurable.ite hl hhit (measurable_const (a := (⊤ : WithTop ℝ≥0))))
    (measurable_const (a := (⊤ : WithTop ℝ≥0)))
  convert hm using 1
  funext p
  by_cases hz : p.1 ∈ D
  · simp only [sourceCollarStart, ite_eq_left hz]
    apply source_liveTime_eq_killed (a.trace_continuous p.2)
    rw [(a.witness p.2).2.1, dist_zero_left]
    exact (hy p.1 hz).trans ((le_abs_self p.1.im).trans (Complex.abs_im_le_norm _))
  · simp only [sourceCollarStart, ite_eq_right hz]

lemma source_collarFinish_joint
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (D : Set ℂ)
    (hD : MeasurableSet D) (r ε R : ℝ) (hy : ∀ z ∈ D, r ≤ z.im) :
    Measurable (fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R) := by
  have hσ := source_collarStart_joint a D hD r hy
  apply measurable_of_Iic
  intro b
  by_cases hb : b = ⊤
  · subst b
    simp only [preimage, mem_Iic, le_top, ofPred_true]
    exact MeasurableSet.univ
  obtain ⟨T,hT⟩ := WithTop.ne_top_iff_exists.mp hb
  subst b
  have hp : Measurable (fun p : ℂ × a.samples =>
      (((min (sourceCollarStart D (γ p.2) p.1 r) T).untopD 0,
      (⟨γ p.2,a.trace_continuous p.2⟩ : C(ℝ≥0,ℂ))),p.1)) :=
    (((hσ.min measurable_const).untopD 0).prodMk
      ((source_tracePath_measurable a).comp measurable_snd)).prodMk measurable_fst
  have hK := (source_windowKernel_closed T ε R).measurableSet.preimage hp
  have he : (fun p : ℂ × a.samples => sourceCollarFinish D (γ p.2) p.1 r ε R) ⁻¹' Iic (T : WithTop ℝ≥0) =
      (Prod.fst ⁻¹' D) ∩ {p : ℂ × a.samples | sourceCollarStart D (γ p.2) p.1 r ≤ (T : WithTop ℝ≥0)} ∩
      {p : ℂ × a.samples | ∃ t ∈ Icc (0 : ℝ≥0) T,
      (min (sourceCollarStart D (γ p.2) p.1 r) T).untopD 0 ≤ t ∧
      (dist (γ p.2 t) p.1 ≤ ε ∨ R ≤ dist (γ p.2 t) p.1 ∨ p.1 ∉ survivingDomain (γ p.2) t)} := by
    ext p
    simp only [mem_preimage, mem_Iic, mem_inter_iff, mem_ofPred_eq]
    by_cases hz : p.1 ∈ D
    · simp only [hz, true_and, sourceCollarStart, sourceCollarFinish]
      exact source_window_kernel_iff (a.trace_continuous p.2) p.1 r ε R T
    · simp only [hz, false_and, sourceCollarFinish, iff_false]
      exact not_le_of_gt (WithTop.coe_lt_top _)
  rw [he]
  exact ((hD.preimage measurable_fst).inter (measurableSet_le hσ measurable_const)).inter hK

lemma source_spatialWeight_stopping_measurable
    {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) (F ω)) (z : ℂ) (r : ℝ)
    (hτ : IsStoppingTime (Filtration.natural B (fun t => (hm t).stronglyMeasurable))
      (fun ω => spatialHitTime (γ ω) z r)) :
    Measurable[hτ.measurableSpace] (fun ω => spatialGreenWeight κ
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z r) := by
  have hmG := measurable_stoppedValue (source_killedGreen_progressive hm hc κ γ G F hw z) hτ
  have he : MeasurableSet[hτ.measurableSpace] {ω | spatialHitTime (γ ω) z r = ⊤} :=
    measurableSet_eq_fun hτ.measurable measurable_const
  have hmo : Measurable[hτ.measurableSpace] (fun ω =>
      if spatialHitTime (γ ω) z r = ⊤ then (0:ℝ) else
        greenDensity κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω)
          (spatialHitTime (γ ω) z r).untopA z) :=
    Measurable.ite he measurable_const hmG
  convert hmo using 1
  funext ω
  by_cases ht : spatialHitTime (γ ω) z r = ⊤
  · simp only [spatialGreenWeight, ite_eq_left ht]
  · obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.mp ht
    simp only [spatialGreenWeight, ite_eq_right ht]
    rw [← hv]
    rfl

lemma source_windowH_untopA (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    sourceSpatialWindowH γ z r ε R =
    if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopA) ∧
      dist (γ ((sourceSpatialWindowTime γ z r ε R).untopA)) z ≤ ε then 1 else 0 := by
  by_cases ht : sourceSpatialWindowTime γ z r ε R = ⊤
  · simp only [sourceSpatialWindowH, ht, ne_eq, not_true_eq_false, false_and, ite_false]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ht
    unfold sourceSpatialWindowH
    rw [← ht]
    rfl

lemma source_windowB_untopA (γ : ℝ≥0 → ℂ) (z : ℂ) (r ε R : ℝ) :
    sourceSpatialWindowB γ z r ε R =
    if sourceSpatialWindowTime γ z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain γ ((sourceSpatialWindowTime γ z r ε R).untopA) ∧
      R ≤ dist (γ ((sourceSpatialWindowTime γ z r ε R).untopA)) z then 1 else 0 := by
  by_cases ht : sourceSpatialWindowTime γ z r ε R = ⊤
  · simp only [sourceSpatialWindowB, ht, ne_eq, not_true_eq_false, false_and, ite_false]
  · obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp ht
    unfold sourceSpatialWindowB
    rw [← ht]
    rfl

lemma source_windowHB_stopped_measurable
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ}
    {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ) (z : ℂ)
    (r ε R : ℝ)
    (hτ : IsStoppingTime a.filtration (fun ω : a.samples => sourceSpatialWindowTime (γ ω) z r ε R)) :
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceSpatialWindowH (γ ω) z r ε R) ∧
    Measurable[hτ.measurableSpace] (fun ω : a.samples => sourceSpatialWindowB (γ ω) z r ε R) := by
  have htp := (show StronglyAdapted a.filtration (fun t (ω : a.samples) => γ ω t) from
    fun t => (a.trace_adapted t).stronglyMeasurable).isStronglyProgressive_of_continuous a.trace_continuous
  have hv := measurable_stoppedValue htp hτ
  let : MeasurableSpace a.samples := hτ.measurableSpace
  have hl := source_live_stopped_measurable a z hτ
  have hn : MeasurableSet[hτ.measurableSpace] {ω : a.samples | sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤} :=
    (measurableSet_eq_fun hτ.measurable measurable_const).compl
  have hd : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z) := hv.dist measurable_const
  have hH : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      if sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain (γ ω) (sourceSpatialWindowTime (γ ω) z r ε R).untopA ∧
      dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z ≤ ε then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le hd measurable_const)))
    (measurable_const (a := (1:ℝ))) (measurable_const (a := (0:ℝ)))
  have hB : Measurable[hτ.measurableSpace] (fun ω : a.samples =>
      if sourceSpatialWindowTime (γ ω) z r ε R ≠ ⊤ ∧
      z ∈ survivingDomain (γ ω) (sourceSpatialWindowTime (γ ω) z r ε R).untopA ∧
      R ≤ dist (γ ω (sourceSpatialWindowTime (γ ω) z r ε R).untopA) z then (1:ℝ) else 0) :=
    Measurable.ite (hn.inter (hl.inter (measurableSet_le measurable_const hd)))
    (measurable_const (a := (1:ℝ))) (measurable_const (a := (0:ℝ)))
  constructor
  · convert hH using 1
    funext ω
    exact source_windowH_untopA (γ ω) z r ε R
  · convert hB using 1
    funext ω
    exact source_windowB_untopA (γ ω) z r ε R

end
end SLEExactGauge
end
end

end OAI
