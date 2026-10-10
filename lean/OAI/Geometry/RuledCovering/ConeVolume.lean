import OAI.Geometry.RuledCovering.PlanarIntegration
import OAI.Geometry.RuledCovering.SingularBounds

namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

def coneTriangle (a : ℝ) : Set Plane :=
  {z | 0 ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

lemma coneTriangle_isCompact (a : ℝ) : IsCompact (coneTriangle a) := by
  have hc : IsClosed (coneTriangle a) := by
    unfold coneTriangle
    exact (isClosed_le (f := fun _ : Plane => (0:ℝ)) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  exact (isCompact_closedBall (0:Plane) (2*a)).of_isClosed_subset hc (by
    intro z hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have he := plane_norm_le_sum z
    rw [abs_of_nonneg hz.1] at he
    exact he.trans (by linarith [hz.2.1,hz.2.2]))

lemma coneTriangle_volume {a : ℝ} (ha : 0 ≤ a) : volume.real (coneTriangle a) = a^2 := by
  have heq : ∀ z : Plane, z ∈ coneTriangle a ↔ z 1 ∈ Icc 0 a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneTriangle,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneTriangle_isCompact a).measurableSet
    (coneTriangle_isCompact a).measure_lt_top.ne (s := Icc 0 a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = ∫ r in (0:ℝ)..a, 2*r := by
    rw [intervalIntegral.integral_of_le ha,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc (0:ℝ) a, max (r- -r) 0) = a^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := (0:ℝ)) (b := a) 1
  simp only [pow_one] at hh
  rw [hh]
  norm_num
  ring

def coneBand (d a : ℝ) : Set Plane :=
  {z | d ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1}

lemma coneBand_isCompact (d a : ℝ) : IsCompact (coneBand d a) := by
  apply (coneTriangle_isCompact a).of_isClosed_subset
  · unfold coneBand
    exact (isClosed_le (f := fun _ : Plane => d) (g := fun z => z 1) (by fun_prop) (by fun_prop)).inter
      ((isClosed_le (f := fun z : Plane => z 1) (g := fun _ => a) (by fun_prop) (by fun_prop)).inter
        (isClosed_le (f := fun z : Plane => |z 0|) (g := fun z => z 1) (by fun_prop) (by fun_prop)))
  · intro z hz
    exact ⟨(abs_nonneg _).trans hz.2.2,hz.2⟩

lemma coneBand_volume {d a : ℝ} (hd : 0 ≤ d) (hda : d ≤ a) :
    volume.real (coneBand d a) = a^2-d^2 := by
  have heq : ∀ z : Plane, z ∈ coneBand d a ↔ z 1 ∈ Icc d a ∧ z 0 ∈ Icc (-z 1) (z 1) := by
    intro z
    simp only [coneBand,mem_ofPred_eq,mem_Icc,← abs_le]
    tauto
  rw [plane_volume_horizontal_interval (coneBand_isCompact d a).measurableSet
    (coneBand_isCompact d a).measure_lt_top.ne (s := Icc d a) (l := fun r => -r) (u := id) measurableSet_Icc heq]
  have he : (∫ r in Icc d a, max (r- -r) 0) = ∫ r in d..a, 2*r := by
    rw [intervalIntegral.integral_of_le hda,← integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r hr
    change max (r- -r) 0 = 2*r
    rw [max_eq_left (by linarith [hr.1])]
    ring
  change (∫ r in Icc d a, max (r- -r) 0) = a^2-d^2
  rw [he,intervalIntegral.integral_const_mul]
  have hh := integral_pow (a := d) (b := a) 1
  simp only [pow_one] at hh
  rw [hh]
  norm_num
  ring

lemma coneBand_volume_vertical {d a : ℝ} (ha : a ≤ 2) :
    volume.real (coneBand d a) = ∫ b in Icc (-2:ℝ) 2, max (a-max d |b|) 0 := by
  apply plane_volume_vertical_interval (coneBand_isCompact d a).measurableSet
    (coneBand_isCompact d a).measure_lt_top.ne measurableSet_Icc
  intro z
  change (d ≤ z 1 ∧ z 1 ≤ a ∧ |z 0| ≤ z 1) ↔
    z 0 ∈ Icc (-2:ℝ) 2 ∧ z 1 ∈ Icc (max d |z 0|) a
  simp only [mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.trans (hz.2.1.trans ha))
    exact ⟨hb,⟨⟨hz.1,hz.2.2⟩,hz.2.1⟩⟩
  · rintro ⟨_,⟨⟨hd,hb⟩,ha⟩⟩
    exact ⟨hd,ha,hb⟩

lemma singularDomain_volume_vertical (p gamma c : ℝ)
    (hcap : ∀ b : ℝ, |b| ≤ 2 → (1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ) ≤ 2) :
    volume.real (singularDomain p gamma c) = ∫ b in Icc (-2:ℝ) 2,
      max ((1/2:ℝ)+c^2*ceilingPolynomial p b+c^(5/2:ℝ)-max (c^gamma) |b|) 0 := by
  apply plane_volume_vertical_interval (singularDomain_isCompact p gamma c).measurableSet
    (singularDomain_isCompact p gamma c).measure_lt_top.ne measurableSet_Icc
  intro z
  unfold singularDomain
  simp only [mem_ofPred_eq,mem_Icc,max_le_iff]
  constructor
  · intro hz
    have hb := abs_le.mp (hz.2.2.1.trans hz.2.1)
    exact ⟨hb,⟨⟨hz.1,hz.2.2.1⟩,hz.2.2.2⟩⟩
  · rintro ⟨hb,⟨⟨hd,hb'⟩,hceil⟩⟩
    exact ⟨hd,hceil.trans (hcap (z 0) (abs_le.mpr hb)),hb',hceil⟩

end RuledApproximation

end

end OAI
