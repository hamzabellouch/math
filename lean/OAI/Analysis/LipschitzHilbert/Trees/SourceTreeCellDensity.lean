import OAI.Analysis.LipschitzHilbert.Trees.SourceTreeDensityTerm
import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyIntervals

namespace OAI

/-! The density factor for a long-tree cell. A literal admissible test
controls the measure of its angularly restricted cell, with polynomial
loss in the transverse cell index. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

theorem one_le_densityKernel_mul (T : SlopeBox) {R : ℝ}
    {z : ℝ×ℝ} (hz : T.radius z≤R) :
    1≤(1+R)^203*T.densityKernel 203 z := by
  have hr : 0<1+T.radius z := by linarith [T.radius_nonnegative z]
  have hp := pow_le_pow_left₀ hr.le (show 1+T.radius z≤1+R by linarith only [hz]) 203
  have h := mul_le_mul_of_nonneg_right hp
    (inv_nonneg.mpr (pow_nonneg hr.le 203))
  rw [mul_inv_cancel₀ (pow_ne_zero _ hr.ne')] at h
  have heq : T.densityKernel 203 z=((1+T.radius z)^(203:ℕ))⁻¹ := by
    change (1+T.radius z)^(-((203:ℕ):ℝ))=((1+T.radius z)^(203:ℕ))⁻¹
    rw [Real.rpow_neg hr.le,Real.rpow_natCast]
  rw [heq]
  exact h

/-- A density test gives the mass bound on any measurable cell on which
its normalized radius is bounded. The constant function is integrable on
the restricted cell as a consequence, without an extra finiteness premise. -/
theorem density_test_cell_mass (ell0 w W tau : ℝ) (grid : ℤ)
    (tile : OrdinaryDensityTile) (test : OrdinaryDensityTest ell0 w W tau grid tile)
    (E : Set (ℝ×ℝ)) (hE : MeasurableSet E) (u : ℝ×ℝ → ℝ) (hu : Measurable u)
    (S : Set (ℝ×ℝ)) (hS : MeasurableSet S) (R eta : ℝ) (hR : 0≤R)
    (hradius : ∀ z∈S, test.top.radius z≤R)
    (hdensity : tile.density ell0 w W tau grid E u≤eta) :
    let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩S
    IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) ∧
    (volume.prod volume).real A≤(1+R)^203*eta*test.top.area := by
  let A := E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell∩S
  have hA : MeasurableSet A := (hE.inter
    ((scaledAngularCell_measurable _ _ _ _).preimage hu)).inter hS
  have hB : 0≤(1+R)^203 := pow_nonneg (by linarith only [hR]) _
  have hkernel := test.top.densityKernel_integrable (by norm_num : (2:ℝ)<203)
  have hmajor : IntegrableOn (fun z => (1+R)^203*test.top.densityKernel 203 z) A
      (volume.prod volume) := (hkernel.const_mul _).integrableOn
  have hpoint (z : ℝ×ℝ) (hz : z∈A) : 1≤(1+R)^203*test.top.densityKernel 203 z :=
    one_le_densityKernel_mul test.top (hradius z hz.2)
  have hone : IntegrableOn (fun _ : ℝ×ℝ => (1:ℝ)) A (volume.prod volume) :=
    hmajor.mono' measurable_const.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hA] with z hz
      simpa only [norm_one] using hpoint z hz)
  refine ⟨hone,?_⟩
  calc
    _ = ∫ _z in A, (1:ℝ) ∂volume.prod volume := by simp only [setIntegral_const,smul_eq_mul,mul_one]; rfl
    _ ≤ ∫ z in A, (1+R)^203*test.top.densityKernel 203 z ∂volume.prod volume :=
      setIntegral_mono_on hone hmajor hA hpoint
    _ = (1+R)^203*∫ z in A, test.top.densityKernel 203 z ∂volume.prod volume := integral_const_mul _ _
    _ ≤ (1+R)^203*∫ z in E∩u ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell,
        test.top.densityKernel 203 z ∂volume.prod volume := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply setIntegral_mono_set hkernel.integrableOn
        (Filter.Eventually.of_forall (fun z => test.top.densityKernel_nonneg 203 z))
      exact Filter.Eventually.of_forall (fun _ hz => hz.1)
    _ ≤ (1+R)^203*(eta*test.top.area) := mul_le_mul_of_nonneg_left
      ((tile.test_integral_le_density ell0 w W tau grid E u test).trans
        (mul_le_mul_of_nonneg_right hdensity test.top.area_pos.le)) hB
    _ = _ := by ring

namespace SourceWhitney
open DyadicLineGrid

/-- Horizontal Whitney strip crossed with one transverse cell in the
reference coordinates of a tree. -/
def treeCell (slope y W : ℝ) (k j n : ℤ) : Set (ℝ×ℝ) :=
  {z | z.1∈cell 0 k j ∧ |(z.2-slope*z.1)-y-(n:ℝ)*W|≤W/2}

theorem treeCell_measurable (slope y W : ℝ) (k j n : ℤ) :
    MeasurableSet (treeCell slope y W k j n) := by
  exact ((cell_measurable 0 k j).preimage measurable_fst).inter
    (isClosed_le (((continuous_snd.sub (continuous_const.mul continuous_fst)).sub
      continuous_const).sub continuous_const |>.abs) continuous_const).measurableSet

/-- A test centered on the horizontal cell has bounded radius on each
transverse translate. -/
theorem treeCell_radius_bound (T : SlopeBox) (slope y : ℝ) (k j n : ℤ)
    (hx : T.x=center k j) (hy : T.y=y+slope*T.x) (ht : T.slope=slope)
    (hlength : scale k≤T.length) {z : ℝ×ℝ} (hz : z∈treeCell slope y T.width k j n) :
    T.radius z≤1+|(n:ℝ)| := by
  have hX : |T.horizontal z|≤(1/2:ℝ) := by
    have hp := point_center_bound k j hz.1
    rw [←hx] at hp
    rw [SlopeBox.horizontal,abs_div,abs_of_pos T.length_pos]
    apply (div_le_iff₀ T.length_pos).mpr
    linarith only [hp,hlength]
  have hY : |T.transverse z|≤|(n:ℝ)|+1/2 := by
    have hraw : |(z.2-slope*z.1)-y|≤T.width/2+|(n:ℝ)| * T.width := by
      calc
        _ ≤ |(z.2-slope*z.1)-y-(n:ℝ)*T.width|+|(n:ℝ)*T.width| := by simpa only [sub_zero] using abs_sub_le ((z.2-slope*z.1)-y) ((n:ℝ)*T.width) 0
        _ ≤ T.width/2+|(n:ℝ)| * T.width := by
          rw [abs_mul,abs_of_pos T.width_pos]
          linarith only [hz.2]
    rw [SlopeBox.transverse,hy,ht]
    have he : (z.2-(y+slope*T.x))-slope*(z.1-T.x)=(z.2-slope*z.1)-y := by ring
    rw [he,abs_div,abs_of_pos T.width_pos]
    apply (div_le_iff₀ T.width_pos).mpr
    nlinarith only [hraw]
  unfold SlopeBox.radius
  linarith only [hX,hY]

end SourceWhitney
end LipschitzHilbert

end

end OAI
