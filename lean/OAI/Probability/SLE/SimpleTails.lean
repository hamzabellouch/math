import Mathlib
import OAI.Probability.SLE.GreenCovariance

namespace OAI

/-! Simple Tails for chordal SLE. -/

section
section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open Set Filter MeasureTheory
open scoped Topology NNReal
open Set Filter MeasureTheory Complex
open MeasureTheory ProbabilityTheory Set Filter
open Set Filter Metric Complex InnerProductSpace
open scoped Topology Laplacian
open Set Filter Metric Complex MeasureTheory
open Set Filter Metric Complex MeasureTheory InnerProductSpace
open scoped Topology Laplacian ENNReal
open scoped Topology ENNReal
open scoped Topology Laplacian RealInnerProductSpace
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric
open Set Filter MeasureTheory Metric
open Set Filter Complex
open scoped Topology ComplexConjugate NNReal
open scoped Topology ENNReal NNReal ComplexConjugate
open Set Filter Metric MeasureTheory Complex
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open Set Filter
open scoped Topology NNReal ENNReal ComplexConjugate
open scoped ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology ENNReal
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric Classical
open scoped ENNReal NNReal
open Set Filter MeasureTheory ProbabilityTheory Metric
namespace SLEExactGauge
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem spatial_slab_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (A : Set ℂ) (hA : MeasurableSet A)
    (q ε r R : ℝ) (hq : 0 < q) (hε : 0 < ε) (hqr : q*r ≤ ε)
    (hεr : ε ≤ r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    HasSubgaussianMGF (fun ω : a.samples => spatialSlabIncrement κ
      (fun t => Real.sqrt κ * a.B t ω) (γ ω) (a.G ω) A ε r)
      (⟨slabAmplitude κ q A * r ^ (1 - codimension κ),
        mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hε.trans_le hεr).le _)⟩ ^ 2)
      (P.comap Subtype.val) := by
  apply hasSubgaussianMGF_of_compensated (a.spatialSlabIncrement_measurable A ε r).aemeasurable
  intro θ
  have hv := slabVariance_scale_le A hκ (by linarith) hq (hε.trans_le hεr) hqr
  apply le_trans _ (a.spatial_slab_terminal_exponential hκ hκ4 A hA ε r R hε hεr hrR hheight hbound θ)
  apply lintegral_mono
  intro ω
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  change θ * _ - θ^2 * (slabAmplitude κ q A * r ^ (1 - codimension κ))^2 / 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg θ)]

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

end SLEExactGauge

 

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

end SLEExactGauge

 

open Set Filter Metric Complex
open scoped Topology NNReal
namespace SLEExactGauge

 

end SLEExactGauge

 

open Set Filter
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

end SLEExactGauge

 

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SLEExactGauge

lemma codimension_lt_one (κ : ℝ) (hκ : 0 < κ) : codimension κ < 1 := by
  dsimp [codimension, dimension]
  linarith

lemma integrableOn_abs_heightPower (p R : ℝ) (hp : p < 1) :
    IntegrableOn (fun y : ℝ => |y| ^ (-p)) (Icc (-R) R) volume := by
  have hm : Measurable (fun y : ℝ => |y| ^ (-p)) := measurable_id.abs.pow measurable_const
  have hl : LocallyIntegrable (fun y : ℝ => |y| ^ (-p)) volume := by
    apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := p) (by simp) (by simpa using hp) _ hm.aestronglyMeasurable
    filter_upwards [] with y
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) (-p)), one_mul, le_refl]
  exact hl.integrableOn_isCompact isCompact_Icc

 
lemma integrable_height_power_box (p R : ℝ) (hp : p < 1) :
    IntegrableOn (fun z : ℂ => |z.im| ^ (-p))
      (Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc (-R) R)) volume := by
  have h1 := (integrableOn_abs_heightPower p R hp).comp_snd (volume.restrict (Icc (-R) R))
  rw [Measure.prod_restrict] at h1
  have hpres := Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet (Icc (-R) R ×ˢ Icc (-R) R))
  exact (hpres.integrable_comp_emb Complex.measurableEquivRealProd.measurableEmbedding).mpr h1

lemma integrable_height_power_ball (p R : ℝ) (hp : p < 1) :
    IntegrableOn (fun z : ℂ => |z.im| ^ (-p)) (Metric.closedBall 0 R) volume := by
  apply (integrable_height_power_box p R hp).mono_set
  intro z hz
  have hn : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  have hre := (abs_le.mp ((Complex.abs_re_le_norm z).trans hn))
  have him := (abs_le.mp ((Complex.abs_im_le_norm z).trans hn))
  exact ⟨hre, him⟩

lemma ae_im_ne_zero : ∀ᵐ z : ℂ ∂volume, z.im ≠ 0 := by
  apply ae_iff.mpr
  simp only [not_not]
  have hproper : (LinearMap.ker Complex.imLm) ≠ ⊤ := by
    intro h
    have hi : Complex.I ∈ LinearMap.ker Complex.imLm := by rw [h]; trivial
    simp at hi
  exact Measure.addHaar_submodule volume (LinearMap.ker Complex.imLm) hproper

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal BigOperators
namespace SLEExactGauge

lemma geometric_amplitude_sum (C r q α : ℝ) (hC : 0 ≤ C) (hr : 0 < r)
    (hq : 0 < q) (hq1 : q < 1) (hα : 0 < α) (N : ℕ) :
    ∑ n ∈ Finset.range N, C * (r*q^n)^α ≤ C*r^α / (1-q^α) := by
  have hs : q^α < 1 := Real.rpow_lt_one hq.le hq1 hα
  have he (n : ℕ) : C*(r*q^n)^α = C*r^α*(q^α)^n := by
    rw [Real.mul_rpow hr.le (pow_nonneg hq.le _), ← Real.rpow_pow_comm hq.le]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hgeom : ∑ n ∈ Finset.range N, (q^α)^n ≤ (1-q^α)⁻¹ := by
    rw [geom_sum_eq (ne_of_lt hs)]
    have hpos : 0 < 1-q^α := sub_pos.mpr hs
    rw [show ((q^α)^N-1)/(q^α-1) = (1-(q^α)^N)/(1-q^α) by rw [div_eq_div_iff (sub_ne_zero.mpr (ne_of_lt hs)) hpos.ne']; ring]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by have := pow_nonneg (Real.rpow_nonneg hq.le α) N; linarith) hpos.le
  simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hgeom
    (mul_nonneg hC (Real.rpow_nonneg hr.le _))

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem spatial_geometric_subgaussian [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q r R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hr : 0 < r) (hrR : r ≤ R)
    (hheight : ∀ z ∈ A, r ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) (N : ℕ) :
    HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (NNReal.mk (slabAmplitude κ q A*r^(1-codimension κ)/(1-q^(1-codimension κ)))
        (div_nonneg (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg hr.le _))
          (sub_nonneg.mpr (Real.rpow_lt_one hq.le hq1 (sub_pos.mpr (codimension_lt_one κ hκ))).le)) ^ 2)
      (P.comap Subtype.val) := by
  let rj : ℕ → ℝ := fun n => r*q^n
  have hp (n : ℕ) : 0 < rj n := mul_pos hr (pow_pos hq n)
  have hl (n : ℕ) : rj n ≤ r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ (n := n) hq.le hq1.le) hr.le
  have he (n : ℕ) : rj (n+1) = q*rj n := by dsimp [rj]; rw [pow_succ]; ring
  let X : ℕ → a.samples → ℝ := fun n ω => spatialSlabIncrement κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) A (rj (n+1)) (rj n)
  let b : ℕ → ℝ≥0 := fun n => NNReal.mk (slabAmplitude κ q A*(rj n)^(1-codimension κ))
    (mul_nonneg (slabAmplitude_nonneg κ q A) (Real.rpow_nonneg (hp n).le _))
  have hsub (n : ℕ) : HasSubgaussianMGF (X n) (b n^2) (P.comap Subtype.val) := by
    apply a.spatial_slab_subgaussian hκ hκ4 A hA q (rj (n+1)) (rj n) R hq (hp _) (he n).symm.le
    · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
    · exact (hl n).trans hrR
    · exact fun z hz => (hl n).trans (hheight z hz)
    · exact hbound
  have hsum := subgaussian_sum_amplitudes X b N (fun n _ => hsub n)
  have hfin : volume A ≠ ∞ := (measure_mono (show A ⊆ Metric.closedBall 0 R from
    fun z hz => by simpa only [Metric.mem_closedBall, dist_zero_right] using hbound z hz)).trans_lt
      (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)) |>.ne
  have htel (ω : a.samples) : (∑ n ∈ Finset.range N, X n ω) =
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (r*q^N) A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A := by
    have hm (n : ℕ) : X n ω =
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj (n+1)) A -
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A := by
      symm
      apply a.spatialRealMass_sub_eq_slab hκ (by linarith) A hA hfin _ _ (hp _)
      · rw [he]; exact mul_le_of_le_one_left (hp n).le hq1.le
      · exact fun z hz => (hl n).trans (hheight z hz)
    simp_rw [hm]
    simpa only [rj, pow_zero, mul_one] using Finset.sum_range_sub
      (fun n => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) (rj n) A) N
  simp_rw [htel] at hsum
  apply SLEExactGauge.HasSubgaussianMGF.mono_parameter hsum
  apply pow_le_pow_left₀ (by positivity)
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_sum, b, rj, NNReal.coe_mk] using geometric_amplitude_sum (slabAmplitude κ q A) r q (1-codimension κ)
    (slabAmplitude_nonneg κ q A) hr hq hq1 (sub_pos.mpr (codimension_lt_one κ hκ)) N

end RegularSLEPresentation
end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma exists_exact_geometric_mesh {q δ ε : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hε : 0 < ε) (hεδ : ε ≤ δ) :
    ∃ (N : ℕ) (r : ℝ), q*δ < r ∧ r ≤ δ ∧ ε = r*q^N := by
  have hδ : 0 < δ := hε.trans_le hεδ
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near_of_lt_one (div_pos hε hδ)
    ((div_le_one hδ).mpr hεδ) hq hq1
  refine ⟨N, ε/q^N, ?_, ?_, ?_⟩
  · apply (lt_div_iff₀ (pow_pos hq N)).mpr
    have hh := (lt_div_iff₀ hδ).mp hN1
    rw [pow_succ] at hh
    nlinarith
  · apply (div_le_iff₀ (pow_pos hq N)).mpr
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hN2
  · field_simp

 

lemma mesh_tail_exponent {δ B p : ℝ} (hδ : 0 < δ) (hB : 0 < B) :
    -(δ^(-p))^2 / (2*(B*δ^(1-p))^2) = -(1/(2*B^2))*δ^(-2 : ℝ) := by
  have he : δ ^ (1-p) = δ*δ^(-p) := by
    rw [sub_eq_add_neg, Real.rpow_add hδ, Real.rpow_one]
  rw [he, show δ^(-2 : ℝ) = (δ^2)⁻¹ by rw [Real.rpow_neg hδ.le, Real.rpow_two]]
  have hp : δ^(-p) ≠ 0 := (Real.rpow_pos_of_pos hδ _).ne'
  field_simp [hδ.ne', hB.ne', hp]

end SLEExactGauge

 

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def meshTailAmplitude (κ q : ℝ) (A : Set ℂ) : ℝ :=
  1 + slabAmplitude κ q A / (1-q^(1-codimension κ))

lemma meshTailAmplitude_pos {κ q : ℝ} (A : Set ℂ)
    (hκ : 0 < κ) (hq : 0 < q) (hq1 : q < 1) : 0 < meshTailAmplitude κ q A := by
  have hd : 0 < 1-q^(1-codimension κ) :=
    sub_pos.mpr (Real.rpow_lt_one hq.le hq1 (sub_pos.mpr (codimension_lt_one κ hκ)))
  have := div_nonneg (slabAmplitude_nonneg κ q A) hd.le
  dsimp [meshTailAmplitude]
  linarith

namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)

 

theorem half_plane_mesh_tail [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q ε δ R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδR : δ ≤ R)
    (hheight : ∀ z ∈ A, δ ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R) :
    (P.comap Subtype.val) {ω : a.samples |
      ((volume A).toReal*q^(-codimension κ)+1)*δ^(-codimension κ) ≤
        spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A} ≤
      ENNReal.ofReal (Real.exp (-(1/(2*(meshTailAmplitude κ q A)^2))*δ^(-2 : ℝ))) := by
  obtain ⟨N,r, hqr, hrδ, he⟩ := exists_exact_geometric_mesh hq hq1 hε hεδ
  have hδ : 0 < δ := hε.trans_le hεδ
  have hr : 0 < r := (mul_pos hq hδ).trans hqr
  have hκ8 : κ < 8 := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hα : 0 < 1-codimension κ := sub_pos.mpr (codimension_lt_one κ hκ)
  have hd : 0 < 1-q^(1-codimension κ) := sub_pos.mpr (Real.rpow_lt_one hq.le hq1 hα)
  have hB := meshTailAmplitude_pos A hκ hq hq1
  have ham : slabAmplitude κ q A*r^(1-codimension κ)/(1-q^(1-codimension κ)) ≤
      meshTailAmplitude κ q A*δ^(1-codimension κ) := by
    calc
      _ ≤ slabAmplitude κ q A*δ^(1-codimension κ)/(1-q^(1-codimension κ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hr.le hrδ hα.le) (slabAmplitude_nonneg κ q A)) hd.le
      _ ≤ _ := by
        dsimp [meshTailAmplitude]
        have hx := (Real.rpow_pos_of_pos hδ (1-codimension κ)).le
        rw [add_mul, div_mul_eq_mul_div]
        nlinarith
  let B : ℝ≥0 := NNReal.mk (meshTailAmplitude κ q A*δ^(1-codimension κ))
    (mul_nonneg hB.le (Real.rpow_nonneg hδ.le _))
  have hsg := a.spatial_geometric_subgaussian hκ hκ4 A hA q r R hq hq1 hr
    (hrδ.trans hδR) (fun z hz => hrδ.trans (hheight z hz)) hbound N
  have hsg' : HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (B^2) (P.comap Subtype.val) := by
    rw [he]
    apply SLEExactGauge.HasSubgaussianMGF.mono_parameter hsg
    apply pow_le_pow_left₀ (by positivity)
    exact NNReal.coe_le_coe.mp ham
  have hfin : volume A ≠ ∞ := (measure_mono (show A ⊆ closedBall 0 R from
    fun z hz => by simpa only [mem_closedBall, dist_zero_right] using hbound z hz)).trans_lt
      (measure_closedBall_lt_top (μ := volume) (x := (0 : ℂ)) (r := R)) |>.ne
  have hstart (ω : a.samples) :
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A ≤
      (volume A).toReal*q^(-codimension κ)*δ^(-codimension κ) := by
    apply (a.spatialRealMass_bound hκ hκ8 r hr A hA hfin
      (fun z hz => hrδ.trans (hheight z hz)) ω).2.trans
    have hh := Real.rpow_le_rpow_of_nonpos (mul_pos hq hδ) hqr.le (neg_nonpos.mpr hp.le)
    rw [Real.mul_rpow hq.le hδ.le] at hh
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh ENNReal.toReal_nonneg
  apply (measure_mono (show _ ⊆ {ω : a.samples | δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A} from ?_)).trans
  · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).mpr
    have ht := hsg'.measure_ge_le (Real.rpow_nonneg hδ.le (-codimension κ))
    change (P.comap Subtype.val).real _ ≤ _
    simpa only [B, NNReal.coe_pow, NNReal.coe_mk, mesh_tail_exponent hδ hB] using ht
  · intro ω hω
    have := hstart ω
    change ((volume A).toReal*q^(-codimension κ)+1)*δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A at hω
    change δ^(-codimension κ) ≤
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A
    nlinarith

end RegularSLEPresentation
end SLEExactGauge

end
end

 
end
end
end

end OAI
