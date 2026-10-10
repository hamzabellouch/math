import Mathlib
import OAI.MeasureTheory.Falconer.Geometry.BinBands
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.FalconerCompletion.Measures.LocalDistanceCollisionBound

namespace OAI

/-! Quantitative estimates for the distance-set construction. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric MeasureTheory
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma norm_linear_error_identityND (a v : V) (ha : 0<‖a‖) :
    ‖v‖-inner ℝ (‖a‖⁻¹ • a) v = (‖v-a‖^2-(‖v‖-‖a‖)^2)/(2*‖a‖) := by
  rw [real_inner_smul_left,norm_sub_sq_real,real_inner_comm v a]
  field_simp [ne_of_gt ha]
  ring

lemma norm_linear_errorND (a v : V) (ha : 0<‖a‖) :
    0 ≤ ‖v‖-inner ℝ (‖a‖⁻¹ • a) v ∧
    ‖v‖-inner ℝ (‖a‖⁻¹ • a) v ≤ ‖v-a‖^2/(2*‖a‖) := by
  have hn : ‖‖a‖⁻¹ • a‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha),inv_mul_cancel₀ (ne_of_gt ha)]
  constructor
  · have hh := (le_abs_self (inner ℝ (‖a‖⁻¹ • a) v)).trans (abs_real_inner_le_norm _ _)
    rw [hn,one_mul] at hh
    linarith
  · rw [norm_linear_error_identityND a v ha]
    gcongr
    exact sub_le_self _ (sq_nonneg _)

lemma distance_linearizationND (x y c e : V) {δ ρ : ℝ}
    (hρ : 0<ρ) (hsep : ρ ≤ ‖c-e‖) (hx : dist x c ≤ δ) (hy : dist y e ≤ δ) :
    |dist x y-inner ℝ (‖c-e‖⁻¹ • (c-e)) (x-y)| ≤ 2*δ^2/ρ := by
  have hδ : 0 ≤ δ := dist_nonneg.trans hx
  have hce : 0<‖c-e‖ := hρ.trans_le hsep
  have hh := norm_linear_errorND (c-e) (x-y) hce
  have hnear : ‖(x-y)-(c-e)‖ ≤ 2*δ := by
    have he : (x-y)-(c-e)=(x-c)-(y-e) := by abel
    rw [he]
    exact (norm_sub_le _ _).trans (by simpa only [dist_eq_norm, two_mul] using add_le_add hx hy)
  rw [dist_eq_norm,abs_of_nonneg hh.1]
  calc
    _ ≤ ‖(x-y)-(c-e)‖^2/(2*‖c-e‖) := hh.2
    _ ≤ (2*δ)^2/(2*ρ) := by gcongr
    _ = _ := by ring

lemma normalized_direction_distND (a v : V) (ha : 0<‖a‖) (hv : 0<‖v‖) :
    dist (‖a‖⁻¹ • a) (‖v‖⁻¹ • v) ≤ 2*‖a-v‖/‖a‖ := by
  have he : ‖a‖⁻¹ • a-‖v‖⁻¹ • v =
      ‖a‖⁻¹ • (a-v)+(‖a‖⁻¹-‖v‖⁻¹) • v := by
    simp only [smul_sub,sub_smul]; abel
  have hn : ‖(‖a‖⁻¹-‖v‖⁻¹) • v‖=|‖v‖-‖a‖|/‖a‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    have he : ‖a‖⁻¹-‖v‖⁻¹=(‖v‖-‖a‖)/(‖a‖*‖v‖) := by field_simp
    rw [he,abs_div,abs_mul,abs_of_pos ha,abs_of_pos hv]
    field_simp
  rw [dist_eq_norm,he]
  calc
    _ ≤ ‖‖a‖⁻¹ • (a-v)‖+‖(‖a‖⁻¹-‖v‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖a-v‖/‖a‖+|‖v‖-‖a‖|/‖a‖ := by
      rw [hn,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ha)]; ring
    _ ≤ ‖a-v‖/‖a‖+‖a-v‖/‖a‖ := by
      gcongr
      simpa only [norm_sub_rev] using abs_norm_sub_norm_le v a
    _ = _ := by ring

end CurrentFalconer
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer
open Set Metric MeasureTheory
open scoped ENNReal RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
open PlanarFalconer

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
lemma projection_direction_changeND (y y' c e v : V) {δ ε w : ℝ}
    (hy : dist y c ≤ δ) (hy' : dist y' c ≤ δ) (he : dist e v ≤ ε)
    (hproj : |inner ℝ (y-y') e| ≤ w) : |inner ℝ (y-y') v| ≤ w+2*δ*ε := by
  have hδ : 0 ≤ δ := dist_nonneg.trans hy
  have hd : ‖y-y'‖ ≤ 2*δ := by
    rw [← dist_eq_norm]
    exact (dist_triangle y c y').trans (by rw [dist_comm c y']; linarith)
  have hh := abs_real_inner_le_norm (y-y') (v-e)
  rw [inner_sub_right] at hh
  have hev : ‖v-e‖ ≤ ε := by simpa only [← dist_eq_norm,dist_comm v e] using he
  have hh' : |inner ℝ (y-y') v-inner ℝ (y-y') e| ≤ 2*δ*ε :=
    hh.trans (mul_le_mul hd hev (norm_nonneg _) (by positivity))
  have htri := abs_add_le (inner ℝ (y-y') v-inner ℝ (y-y') e) (inner ℝ (y-y') e)
  simp only [sub_add_cancel] at htri
  linarith

theorem suffix_witness_local_collisionND (μ : Measure V) [IsFiniteMeasure μ]
    {P Q : Set V} (hP : MeasurableSet P) (hQ : MeasurableSet Q)
    (c c' x₀ y₀ : V) {δ ρ w W : ℝ}
    (hρ : 0<ρ) (hw : 0<w) (hsep : ρ ≤ ‖c-c'‖)
    (hPcell : ∀ x ∈ P, dist x c ≤ δ) (hQcell : ∀ y ∈ Q, dist y c' ≤ δ)
    (hx₀ : x₀ ∈ P) (hy₀ : y₀ ∈ Q) (hxy₀ : x₀ ≠ y₀)
    (htaylor : 2*δ^2/ρ ≤ w) (hwidth : w+8*δ^2/ρ ≤ W) {B : ℝ≥0∞}
    (hproj : ((ProbabilityTheory.cond μ Q).prod (ProbabilityTheory.cond μ Q))
      {z : V × V | |inner ℝ (z.1-z.2) (‖x₀-y₀‖⁻¹ • (x₀-y₀))| ≤ W} ≤ B) :
    (((μ.restrict P).prod (μ.restrict Q)).prod ((μ.restrict P).prod (μ.restrict Q)))
      {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} ≤
        ((bandOffsets 3).card:ℝ≥0∞)*B*(μ P)^2*(μ Q)^2 := by
  have hδ : 0 ≤ δ := dist_nonneg.trans (hPcell x₀ hx₀)
  have hdiff : ‖(c-c')-(x₀-y₀)‖ ≤ 2*δ := by
    have he : (c-c')-(x₀-y₀)=(c-x₀)-(c'-y₀) := by abel
    rw [he]
    apply (norm_sub_le _ _).trans
    have hp := hPcell x₀ hx₀
    have hq := hQcell y₀ hy₀
    simp only [dist_eq_norm,norm_sub_rev x₀ c,norm_sub_rev y₀ c'] at hp hq
    linarith
  have hdir : dist (‖c-c'‖⁻¹ • (c-c')) (‖x₀-y₀‖⁻¹ • (x₀-y₀)) ≤ 4*δ/ρ := by
    apply (normalized_direction_distND (c-c') (x₀-y₀) (hρ.trans_le hsep)
      (norm_pos_iff.mpr (sub_ne_zero.mpr hxy₀))).trans
    apply (div_le_div₀ (by positivity) (by nlinarith : 2*‖(c-c')-(x₀-y₀)‖ ≤ 4*δ)
      hρ hsep)
  have haff : ∀ x ∈ P, ∀ y ∈ Q,
      |dist x y-inner ℝ (x-y) (‖c-c'‖⁻¹ • (c-c'))| ≤ w := by
    intro x hx y hy
    have hh := distance_linearizationND x y c c' hρ hsep (hPcell x hx) (hQcell y hy)
    rw [real_inner_comm] at hh
    exact hh.trans htaylor
  apply local_distance_conditional_collisionND μ hP hQ (‖c-c'‖⁻¹ • (c-c')) hw haff
  apply le_trans _ hproj
  apply measure_mono_ae
  have hcond : ∀ᵐ y ∂ProbabilityTheory.cond μ Q, y ∈ Q := by
    exact Measure.ae_smul_measure (ae_restrict_mem hQ) _
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcond,
    Measure.quasiMeasurePreserving_snd.ae hcond] with yy hy hy'
  intro hh
  have hi := projection_direction_changeND yy.1 yy.2 c'
    (‖c-c'‖⁻¹ • (c-c')) (‖x₀-y₀‖⁻¹ • (x₀-y₀))
    (hQcell yy.1 hy) (hQcell yy.2 hy') hdir hh
  apply hi.trans
  calc
    w+2*δ*(4*δ/ρ) = w+8*δ^2/ρ := by ring
    _ ≤ W := hwidth

end CurrentFalconer
end GraphLiteralSupport
end
end

end OAI
