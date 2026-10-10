import OAI.Analysis.LipschitzHilbert.Geometry.SourceWhitneyPacking
import OAI.Analysis.LipschitzHilbert.Estimates.SnappedLattice
import OAI.Analysis.LipschitzHilbert.Estimates.TileLatticeEnvelope
import OAI.Analysis.LipschitzHilbert.Estimates.GeometricScaleWeights

namespace OAI

/-! The short-tree summation uses actual distance to the Whitney strip,
actual sheared center lattices, and a finite dyadic length sum. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid

def stripDistance (c r s : ℝ) : ℝ := max 0 (|s-c|-r/2)

theorem stripDistance_nonneg (c r s : ℝ) : 0 ≤ stripDistance c r s := le_max_left _ _

theorem center_distance_le (c r s : ℝ) : |s-c| ≤ stripDistance c r s+r/2 := by
  have h := le_max_right 0 (|s-c|-r/2)
  change |s-c|-r/2 ≤ stripDistance c r s at h
  linarith only [h]

theorem stripDistance_le_point (s : ℝ) (k j : ℤ) {z : ℝ} (hz : z∈cell 0 k j) :
    stripDistance (center k j) (scale k) s ≤ |z-s| := by
  apply max_le (abs_nonneg _)
  have ht := abs_sub_le s z (center k j)
  have hc := point_center_bound k j hz
  rw [abs_sub_comm s z] at ht
  linarith only [ht,hc]

theorem stripDistance_large {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)
    {k j : ℤ} (h : Allowed tiles x ell k j) {i : ι} (hi : i∈tiles)
    (hlen : ell i≤scale k) : scale k < stripDistance (center k j) (scale k) (x i) := by
  have ha := h i hi hlen
  have hd := center_distance_le (center k j) (scale k) (x i)
  linarith only [ha,hd]

/-- An interval-distance kernel is controlled by a center kernel once the
center distance is at most twice that distance plus one packet length. -/
theorem inverse_quadratic_le_center {s c ell d : ℝ} (hell : 0<ell) (hd : 0≤d)
    (hc : |s-c|≤2*d+ell) :
    (1+(d/ell)^2)⁻¹ ≤ 8*lineEnvelope s ell 1 c := by
  have hu : |s-c|/ell ≤ 2*(d/ell)+1 := by
    apply (div_le_iff₀ hell).mpr
    calc
      _ ≤ 2*d+ell := hc
      _ = (2*(d/ell)+1)*ell := by field_simp
  have hu0 : 0≤|s-c|/ell := div_nonneg (abs_nonneg _) hell.le
  have hv : 0≤d/ell := div_nonneg hd hell.le
  have hs := pow_le_pow_left₀ hu0 hu 2
  have hbase : 1+((c-s)/ell)^2 ≤ 8*(1+(d/ell)^2) := by
    have he : ((c-s)/ell)^2=(|s-c|/ell)^2 := by
      rw [div_pow,div_pow,sq_abs,sub_sq_comm]
    rw [he]
    nlinarith only [hs,sq_nonneg (2*(d/ell)-1)]
  simp only [lineEnvelope,pow_one]
  rw [←one_div,←div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hbase)

theorem strip_kernel_le_center {s c ell r : ℝ} (hell : 0<ell)
    (hrel : ell≤r → r≤stripDistance c r s) :
    (1+(stripDistance c r s/ell)^2)⁻¹^2 ≤ 8*lineEnvelope s ell 1 c := by
  let d := stripDistance c r s
  have hd : 0≤d := stripDistance_nonneg c r s
  have hc : |s-c|≤2*d+ell := by
    have ht := center_distance_le c r s
    change |s-c|≤d+r/2 at ht
    by_cases he : ell≤r
    · have h := hrel he
      change r≤d at h
      linarith only [ht,h,hell,hd]
    · have h : r≤ell := le_of_lt (lt_of_not_ge he)
      linarith only [ht,h,hd,hell]
  have hq := inverse_quadratic_le_center hell hd hc
  have h1 : (1+(d/ell)^2)⁻¹≤1 :=
    (inv_le_one₀ (by positivity)).2 (by nlinarith [sq_nonneg (d/ell)])
  have h0 : 0≤(1+(d/ell)^2)⁻¹ := by positivity
  calc
    _ = (1+(d/ell)^2)⁻¹*(1+(d/ell)^2)⁻¹ := pow_two _
    _ ≤ (1+(d/ell)^2)⁻¹*1 := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ _ := by simpa only [mul_one] using hq

theorem strip_kernel_le_center_decay {s c ell r : ℝ} (hell : 0<ell) (hr : 0<r)
    (hfar : r≤stripDistance c r s) :
    (1+(stripDistance c r s/ell)^2)⁻¹^2 ≤
      8*lineEnvelope s ell 1 c*(ell/r)^2 := by
  let d := stripDistance c r s
  have hd : 0≤d := stripDistance_nonneg c r s
  have hc : |s-c|≤2*d+ell := by
    have ht := center_distance_le c r s
    change |s-c|≤d+r/2 at ht
    change r≤d at hfar
    linarith only [ht,hfar,hell,hd]
  have hq := inverse_quadratic_le_center hell hd hc
  have hrat : r/ell≤d/ell := div_le_div_of_nonneg_right hfar hell.le
  have hs := pow_le_pow_left₀ (div_nonneg hr.le hell.le) hrat 2
  have hinv := inv_anti₀ (pow_pos (div_pos hr hell) 2)
    (show (r/ell)^2≤1+(d/ell)^2 by linarith only [hs])
  have hinv' : (1+(d/ell)^2)⁻¹≤(ell/r)^2 := by
    rw [←inv_pow,inv_div] at hinv
    exact hinv
  calc
    _ = (1+(d/ell)^2)⁻¹*(1+(d/ell)^2)⁻¹ := pow_two _
    _ ≤ (8*lineEnvelope s ell 1 c)*(ell/r)^2 :=
      mul_le_mul hq hinv' (by positivity)
        (mul_nonneg (by norm_num) (lineEnvelope_nonneg _ _ _ _))

/-- A sheared lattice with centers in a strip has uniformly bounded
horizontal envelope sum, without a tile-cardinality factor. -/
theorem sheared_strip_overlap (a b ell W delta c y : ℝ)
    (hell : 0<ell) (hW : 0<W) (S : Finset (ℤ×ℤ))
    (hstrip : ∀ p∈S, |b+delta*ell*p.1+W*p.2-y|≤W) :
    (∑ p∈S, lineEnvelope (a+ell*p.1) ell 1 c) ≤ 18*(4*Real.pi)^2 := by
  classical
  have hfactor (p) (hp : p∈S) :
      1≤2*lineEnvelope (b+delta*ell*p.1+W*p.2) W 1 y := by
    have ht : |(y-(b+delta*ell*p.1+W*p.2))/W|≤1 := by
      rw [abs_div,abs_of_pos hW]
      exact (div_le_one hW).mpr (by simpa only [abs_sub_comm] using hstrip p hp)
    have hs := pow_le_pow_left₀ (abs_nonneg _) ht 2
    simp only [sq_abs,one_pow] at hs
    simp only [lineEnvelope,pow_one]
    rw [←div_eq_mul_inv]
    exact (le_div_iff₀ (by positivity)).mpr (by linarith only [hs])
  calc
    _ ≤ ∑ p∈S, 2*(lineEnvelope (a+ell*p.1) ell 1 c *
        lineEnvelope (b+delta*ell*p.1+W*p.2) W 1 y) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := mul_le_mul_of_nonneg_left (hfactor p hp) (lineEnvelope_nonneg (a+ell*p.1) ell 1 c)
      nlinarith only [h]
    _ ≤ ∑ p∈S, 18*(lineEnvelope (ell*(snappedLatticeSite a b ell W delta p).1) ell 1 c *
        lineEnvelope (W*(snappedLatticeSite a b ell W delta p).2) W 1 y) := by
      apply Finset.sum_le_sum
      intro p _
      have h := snappedLatticeSite_envelope a b ell W delta c y hell hW p 1 1
      norm_num only [pow_one] at h
      nlinarith only [h]
    _ = 18*∑ p∈S.image (snappedLatticeSite a b ell W delta),
        lineEnvelope (ell*p.1) ell 1 c * lineEnvelope (W*p.2) W 1 y := by
      rw [Finset.mul_sum,Finset.sum_image (fun _ _ _ _ he => snappedLatticeSite_injective a b ell W delta he)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by
      simpa only [zero_add] using finite_scaled_plane_lattice_overlap 0 0 ell W c y
        hell.ne' hW.ne' (S.image (snappedLatticeSite a b ell W delta))
        (by decide : 1≤1) (by decide : 1≤1)) (by norm_num)

end LipschitzHilbert.SourceWhitney

end

end OAI
