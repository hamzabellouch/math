import OAI.MeasureTheory.Falconer.Estimates.LocalPacketRegularity
import OAI.MeasureTheory.Falconer.Incidence.VariableBaselineIncidence
import OAI.MeasureTheory.Falconer.Graphs.GraphBallCover

namespace OAI

/-! The exact line map for an isotropically rescaled point cell. It preserves
the original line witnesses and their cardinalities; no direction thinning
is needed for the elementary local incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

noncomputable def localCellLine (Δ y a : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0) ((l 0*y+l 1-a)/Δ)

noncomputable def unlocalCellLine (Δ y a : ℝ) (l : Space 2) : Space 2 :=
  rowPoint (l 0) (Δ*l 1-l 0*y+a)

theorem localCellLine_leftInverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.LeftInverse (unlocalCellLine Δ y a) (localCellLine Δ y a) := by
  intro l
  ext i
  fin_cases i
  · rfl
  · change Δ*((l 0*y+l 1-a)/Δ)-l 0*y+a = l 1
    field_simp
    ring

theorem localCellLine_rightInverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.RightInverse (unlocalCellLine Δ y a) (localCellLine Δ y a) := by
  intro l
  ext i
  fin_cases i
  · rfl
  · change (l 0*y+(Δ*l 1-l 0*y+a)-a)/Δ = l 1
    field_simp
    ring

theorem localCellLine_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localCellLine Δ y a) :=
  (localCellLine_leftInverse hΔ y a).injective

theorem unlocalCellLine_dist {Δ y a : ℝ} (hΔ : 0 ≤ Δ) (hΔ1 : Δ ≤ 1)
    (hy : |y| ≤ 1) (l m : Space 2) :
    dist (unlocalCellLine Δ y a l) (unlocalCellLine Δ y a m) ≤ 3*dist l m := by
  have h0 : |l 0-m 0| ≤ dist l m := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le l m 0
  have h1 : |l 1-m 1| ≤ dist l m := by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le l m 1
  have hb : |(Δ*l 1-l 0*y+a)-(Δ*m 1-m 0*y+a)| ≤ 2*dist l m := by
    calc
      _ = |Δ*(l 1-m 1)-(l 0-m 0)*y| := by congr 1; ring
      _ ≤ |Δ*(l 1-m 1)|+|(l 0-m 0)*y| := abs_sub _ _
      _ = Δ*|l 1-m 1|+|l 0-m 0| * |y| := by rw [abs_mul,abs_mul,abs_of_nonneg hΔ]
      _ ≤ 1*dist l m+dist l m*1 := by gcongr
      _ = _ := by ring
  exact (rowPoint_dist_le_sum (dist_nonneg (x := l) (y := m))
    (by positivity) h0 hb).trans_eq (by ring)

theorem localCellLine_regular {δ Δ s K y a : ℝ}
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hy : |y| ≤ 1)
    (hδΔ : δ ≤ Δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (T : Finset (Space 2)) (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound Δ s (K*3^s) (T.image (localCellLine Δ y a)) := by
  intro z r hr _
  have hr0 : 0 ≤ r := hΔ.le.trans hr
  let w := unlocalCellLine Δ y a z
  have hsub : (T.image (localCellLine Δ y a)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 3*r)).image (localCellLine Δ y a) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨m,Finset.mem_filter.mpr ⟨hm,?_⟩,rfl⟩
    have hh := unlocalCellLine_dist (a := a) hΔ.le hΔ1 hy (localCellLine Δ y a m) z
    rw [localCellLine_leftInverse hΔ y a m] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective hΔ y a)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 3*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(3*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (3*r)
      (hδΔ.trans (by linarith only [hr,hr0]))
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hr0]; ring

theorem localCellLine_residual {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) :
    localPacketPoint Δ y a p 1-localCellLine Δ y a l 0*localPacketPoint Δ y a p 0-
      localCellLine Δ y a l 1 = (p 1-l 0*p 0-l 1)/Δ := by
  change (p 1-a)/Δ-l 0*((p 0-y)/Δ)-(l 0*y+l 1-a)/Δ = _
  field_simp
  ring

theorem localCellLine_incident {δ Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) (hi : TubeIncident δ p l) :
    TubeIncident (δ/Δ) (localPacketPoint Δ y a p) (localCellLine Δ y a l) := by
  unfold TubeIncident at hi ⊢
  rw [localCellLine_residual hΔ,abs_div,abs_of_pos hΔ]
  change (|p 1-l 0*p 0-l 1|/Δ)/Real.sqrt (1+(l 0)^2) ≤ δ/Δ
  calc
    _ = (|p 1-l 0*p 0-l 1|/Real.sqrt (1+(l 0)^2))/Δ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hi hΔ.le

theorem localCellLine_chart {Δ y a : ℝ} (hΔ : 0 < Δ) (hΔsmall : Δ ≤ 1/8)
    (p l : Space 2) (hp0 : |p 0-y| ≤ Δ/4) (hp1 : |p 1-a| ≤ Δ/4)
    (hl0 : |l 0| ≤ 1/2) (hi : TubeIncident (Δ^2) p l) :
    |localCellLine Δ y a l 0| ≤ 1 ∧ |localCellLine Δ y a l 1| ≤ 1 := by
  have hres := tube_residual_le (sq_nonneg Δ) (hl0.trans (by norm_num)) hi
  have hb : |l 0*y+l 1-a| ≤ Δ/4+Δ/8+2*Δ^2 := by
    calc
      _ = |(p 1-a)-l 0*(p 0-y)-(p 1-l 0*p 0-l 1)| := by congr 1; ring
      _ ≤ |(p 1-a)-l 0*(p 0-y)|+|p 1-l 0*p 0-l 1| := abs_sub _ _
      _ ≤ (|p 1-a|+|l 0*(p 0-y)|)+|p 1-l 0*p 0-l 1| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ Δ/4+(1/2)*(Δ/4)+2*Δ^2 := by rw [abs_mul]; gcongr
      _ = _ := by ring
  refine ⟨hl0.trans (by norm_num),?_⟩
  change |(l 0*y+l 1-a)/Δ| ≤ 1
  rw [abs_div,abs_of_pos hΔ,div_le_one hΔ]
  exact hb.trans (by nlinarith only [hΔsmall,mul_nonneg hΔ.le (sub_nonneg.mpr hΔsmall)])

end Falconer

end OAI
