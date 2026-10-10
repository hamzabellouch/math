import OAI.MeasureTheory.Falconer.Recursion.SuffixRetainedPairs
import OAI.MeasureTheory.Falconer.Estimates.PositiveDistanceWeight
import OAI.MeasureTheory.Falconer.Geometry.PositiveDistanceBins

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem suffix_distance_variation (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    {p : ℕ} {c : CellPath × CellPath} (hP : c.1.length = p) (hC : c.2.length = p)
    {z z' : Plane × Plane}
    (hz : z.1 ∈ (d.Q.descendant c.1).carrier ∧ z.2 ∈ (d.Q.descendant c.2).carrier)
    (hz' : z'.1 ∈ (d.Q.descendant c.1).carrier ∧ z'.2 ∈ (d.Q.descendant c.2).carrier) :
    |dist z.1 z.2-dist z'.1 z'.2| ≤ 4/(2:ℝ)^p := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have h₁ := (d.Q.descendant c.1).dist_le (d.Q.descendant_side_pos hside _).le hz.1 hz'.1
  have h₂ := (d.Q.descendant c.2).dist_le (d.Q.descendant_side_pos hside _).le hz.2 hz'.2
  rw [DyadicSquare.descendant_side,hP,hQ] at h₁
  rw [DyadicSquare.descendant_side,hC,hQ] at h₂
  have hh := dist_dist_dist_le z.1 z.2 z'.1 z'.2
  rw [Real.dist_eq] at hh
  exact hh.trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem distance_bin_witness (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (w : ℝ) (k : ℤ) (hm : d.distance (realBin w k) ≠ 0) :
    ∃ z : Plane × Plane, dist z.1 z.2 ∈ realBin w k ∧
      z.1 ∈ (d.Q.descendant d.X).carrier ∧ z.2 ∈ (d.Q.descendant d.Y).carrier := by
  rw [d.distance_apply (realBin_measurable w k)] at hm
  obtain ⟨z,hz,hcells⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm
    (d.ae_cellPair_mem.filter_mono (ae_mono Measure.restrict_le_self))
  exact ⟨z,hz.1,hcells⟩

theorem shared_bin_full_coarse_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : d.Q.side = 1) {p : ℕ} (hpt : p ≤ d.t)
    {c b : CellPath × CellPath} (hc : c ∈ d.suffixRetained p) (hb : b ∈ d.suffixRetained p)
    (hbin : ∃ k : ℤ, (d.suffixData c).distance (realBin d.width k) ≠ 0 ∧
      (d.suffixData b).distance (realBin d.width k) ≠ 0) :
    ((d.suffixFullDistance c).prod (d.suffixFullDistance b))
      {z : ℝ × ℝ | |z.1-z.2| ≤ 100/(2:ℝ)^p} =
        (d.suffixFullDistance c univ)*(d.suffixFullDistance b univ) := by
  obtain ⟨hC₁,hC₂,_⟩ := d.suffix_retained_spec hc
  obtain ⟨hB₁,hB₂,_⟩ := d.suffix_retained_spec hb
  obtain ⟨k,hkc,hkb⟩ := hbin
  obtain ⟨x,hxbin,hx⟩ := (d.suffixData c).distance_bin_witness d.width k hkc
  obtain ⟨y,hybin,hy⟩ := (d.suffixData b).distance_bin_witness d.width k hkb
  have hxy := realBin_diameter d.width k hxbin hybin
  have hw : d.width ≤ 1/(2:ℝ)^p := by
    simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num) hpt)
  have hgood : ∀ᵐ z ∂(d.suffixData c).cellPair.prod (d.suffixData b).cellPair,
      |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100/(2:ℝ)^p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (d.suffixData c).ae_cellPair_mem,
      Measure.quasiMeasurePreserving_snd.ae (d.suffixData b).ae_cellPair_mem] with z hz hz'
    have h₁ := d.suffix_distance_variation hQ hC₁ hC₂ hz hx
    have h₂ := d.suffix_distance_variation hQ hB₁ hB₂ hz' hy
    obtain ⟨ha,hb⟩ := abs_le.mp h₁
    obtain ⟨hc,hd⟩ := abs_le.mp h₂
    obtain ⟨he,hf⟩ := abs_le.mp hxy
    apply abs_le.mpr
    simp only [div_eq_mul_inv,one_mul] at ha hb hc hd hw ⊢
    constructor <;> linarith [show 0 < ((2:ℝ)^p)⁻¹ by positivity]
  rw [suffixFullDistance,suffixFullDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change ((d.suffixData c).cellPair.prod (d.suffixData b).cellPair)
    {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100/(2:ℝ)^p} = _
  rw [measure_congr (Filter.eventuallyEqSet_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.map_apply (continuous_fst.dist continuous_snd).measurable MeasurableSet.univ,preimage_univ]

end PositiveDistanceData

end PlanarFalconer

end OAI
