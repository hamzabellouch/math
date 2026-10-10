import Mathlib
import OAI.Probability.SLE.SmallKappaSausageMoments
import OAI.Probability.SLE.TracePosCombined

namespace OAI

/-! Simple Past Mesh for chordal SLE. -/

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
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
namespace RegularSLEPresentation
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ} (a : RegularSLEPresentation P κ γ)
theorem source_past_half_plane_mesh_tail [IsProbabilityMeasure P]
    (hκ : 0 < κ) (hκ4 : κ ≤ 4) (A : Set ℂ) (hA : MeasurableSet A)
    (q ε δ R : ℝ) (hq : 0 < q) (hq1 : q < 1) (hε : 0 < ε)
    (hεδ : ε ≤ δ) (hδR : δ ≤ R)
    (hheight : ∀ z ∈ A, δ ≤ z.im) (hbound : ∀ z ∈ A, ‖z‖ ≤ R)
    (s : ℝ≥0) (D : Set a.samples) (hD : MeasurableSet[a.filtration s] D)
    (hbefore : ∀ ω ∈ D, ∀ z ∈ A, (s : WithTop ℝ≥0) ≤ spatialHitTime (γ ω) z δ)
    :
    ((P.comap Subtype.val)[|D]) {ω : a.samples |
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
  have hsg := a.source_past_spatial_geometric_subgaussian hκ hκ4 A hA q r R hq hq1 hr
    (hrδ.trans hδR) (fun z hz => hrδ.trans (hheight z hz)) hbound N s D hD (fun ω hω z hz => (hbefore ω hω z hz).trans
      (spatialHitTime_antitone_radius (a.trace_continuous ω) z hrδ (by
        rw [(a.witness ω).2.1,dist_zero_left]
        exact (hheight z hz).trans ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)))))
  have hsg' : HasSubgaussianMGF (fun ω : a.samples =>
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) ε A -
      spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) r A)
      (B^2) ((P.comap Subtype.val)[|D]) := by
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
    change ((P.comap Subtype.val)[|D]).real _ ≤ _
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
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceSimpleEntranceMeshTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧ δ₀ < 1 ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 4 ≤ z₀.im →
  ∀ rf δ : ℝ, 0 < rf → rf ≤ δ → δ ≤ δ₀ →
    (P.comap Subtype.val) {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      (P.comap Subtype.val) {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} *
        ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ)))
theorem sourceSimpleEntranceMesh_proved : SourceSimpleEntranceMeshTarget := by
  intro κ hκ hκ4
  let C := max 1 ((volume (ball (0:ℂ) 1)).toReal*(1/2:ℝ)^(-codimension κ)+1)
  let c := 1/(2*(meshTailAmplitude κ (1/2) (ball (0:ℂ) 1))^2)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hC : 0 < C := zero_lt_one.trans_le hC1
  have hc : 0 < c := by
    have hh := meshTailAmplitude_pos (κ := κ) (q := (1/2:ℝ)) (ball (0:ℂ) 1) hκ (by norm_num) (by norm_num)
    exact div_pos zero_lt_one (mul_pos (by norm_num) (sq_pos_of_pos hh))
  refine ⟨C,c,1/2,hC,hc,by norm_num,by norm_num,?_⟩
  intro Ω m P hP γ a z₀ hz₀ rf δ hf hfd hd
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let H := {ω : a.samples | C*δ^(-codimension κ) < spatialRealMass κ
    (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)}
  have hH : MeasurableSet H := measurableSet_lt measurable_const (a.spatialRealMass_measurable _ _)
  have hδ : 0 < δ := hf.trans_le hfd
  have hδ1 : δ ≤ 1 := hd.trans (by norm_num)
  have hrf1 : rf ≤ 1 := hfd.trans hδ1
  have hHA : H ⊆ {ω | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} := by
    intro ω hω hn
    have hm : spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1) = 0 := by
      unfold spatialRealMass
      apply setIntegral_eq_zero_of_forall_eq_zero
      exact fun z hz => a.source_simple_weight_zero_no_entrance z₀ hz₀ rf hrf1 ω hn z hz
    change C*δ^(-codimension κ) < _ at hω
    rw [hm] at hω
    exact (not_lt_of_ge (mul_nonneg hC.le (Real.rpow_nonneg hδ.le _))) hω
  apply source_between_stopping_tail (a.source_simple_sphere_stopping z₀ 3)
    (a.source_simple_sphere_stopping z₀ 2) H hH hHA
    (a.source_simple_spheres_separated z₀ hz₀) (ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))))
  intro s D hD hbefore
  have hDm : MeasurableSet D := (a.filtration.le s) _ hD
  have hheight : ∀ z ∈ ball z₀ 1, δ ≤ z.im := by
    intro z hz
    have he := (le_abs_self (z₀.im-z.im)).trans (Complex.abs_im_le_norm (z₀-z))
    have hn : ‖z₀-z‖ < 1 := by simpa only [mem_ball,dist_eq_norm, norm_sub_rev] using hz
    linarith
  have hbound : ∀ z ∈ ball z₀ 1, ‖z‖ ≤ ‖z₀‖+1 := by
    intro z hz
    have hh := norm_le_insert z₀ z
    rw [norm_sub_rev z₀ z] at hh
    have hn : ‖z-z₀‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
    linarith
  have hR : δ ≤ ‖z₀‖+1 := hδ1.trans (by linarith [norm_nonneg z₀])
  have ht := a.source_past_half_plane_mesh_tail hκ hκ4 (ball z₀ 1) measurableSet_ball
    (1/2) rf δ (‖z₀‖+1) (by norm_num) (by norm_num) hf hfd hR hheight hbound s D hD
    (fun ω hω z hz => (hbefore ω hω).trans (a.source_simple_center_before z₀ hz₀ δ hδ1 ω z hz))
  have hv : volume (ball z₀ 1) = volume (ball (0:ℂ) 1) := by rw [Complex.volume_ball,Complex.volume_ball]
  have ha : meshTailAmplitude κ (1/2) (ball z₀ 1) = meshTailAmplitude κ (1/2) (ball (0:ℂ) 1) := by
    simp only [meshTailAmplitude,slabAmplitude,hv]
  have hcoeff : (volume (ball z₀ 1)).toReal*(1/2:ℝ)^(-codimension κ)+1 ≤ C := by
    rw [hv]; exact le_max_right _ _
  have ht' : μ[H|D] ≤ ENNReal.ofReal (Real.exp (-c*δ^(-2:ℝ))) := by
    apply (measure_mono (show H ⊆ _ from ?_)).trans
    · simpa only [ha] using ht
    · intro ω hω
      exact (mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hδ.le _)).trans hω.le
  calc
    μ (D ∩ H) = μ[H|D]*μ D := (cond_mul_eq_inter hDm H μ).symm
    _ ≤ ENNReal.ofReal (Real.exp (-c*δ^(-2:ℝ)))*μ D := mul_le_mul' ht' le_rfl
    _ ≤ μ D*ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))) := by
      rw [mul_comm]
      apply mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
      exact le_mul_of_one_le_left (Real.exp_pos _).le hC1
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_simple_entrance_bound {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz : 4 ≤ z₀.im) (hsmall : 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4))) :
    (P.comap Subtype.val).real {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} ≤
      (uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ)*initialGreen κ z₀ := by
  apply le_trans (measureReal_mono (show {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} ⊆
      {ω | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4} from ?_))
  · have hh := euclidean_approach a.brownian κ hκ hκ8 (fun ω : a.samples => γ ω) a.G a.F
      (Eventually.of_forall a.witness) z₀ (by change 0 < z₀.im; linarith) 4 (by norm_num) hz hsmall
    change ((P.comap Subtype.val) {ω : a.samples | ∃ t : ℝ≥0, dist (γ ω t) z₀ < 4}).toReal ≤ _
    calc
      _ ≤ _ := hh
      _ = _ := by ring
  · intro ω hω
    obtain ⟨t,ht⟩ := WithTop.ne_top_iff_exists.mp hω
    have hs : 3 ≤ dist (γ ω 0) z₀ := by
      rw [(a.witness ω).2.1,dist_zero_left]
      have := (le_abs_self z₀.im).trans (Complex.abs_im_le_norm z₀)
      linarith
    exact ⟨t,by rw [spatialHitTime_mem (a.trace_continuous ω) z₀ 3 t ht.symm]; norm_num⟩
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Metric Complex Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourceSimpleStretchedTailTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ M C c : ℝ, 0 < M ∧ 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | M*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
theorem sourceSimpleStretchedTail_proved : SourceSimpleStretchedTailTarget := by
  intro κ hκ hκ4
  have hκ8 : κ < 8 := by linarith
  obtain ⟨C,c,δ₀,hC,hc,hδ,hδ1,ht⟩ := sourceSimpleEntranceMesh_proved κ hκ hκ4
  let v := (volume (ball (0:ℂ) 1)).toReal
  let M := max C v*δ₀^(-codimension κ)
  let b := c*δ₀^(-2:ℝ)
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hp : 0 < codimension κ := codimension_pos κ hκ8
  have hM : 0 < M := mul_pos (hC.trans_le (le_max_left _ _)) (Real.rpow_pos_of_pos hδ _)
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos hδ _)
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨M,A*C,b,hM,mul_pos hA hC,hb,?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hx (ω : a.samples) : X ω ≤ v*rf^(-codimension κ) := by
    have hh := (a.spatialRealMass_bound hk hκ8 rf hf (ball z₀ 1) measurableSet_ball
      (measure_ball_lt_top (μ := volume) (x := z₀) (r := 1)).ne (fun z hz' => ?_) ω).2
    · simpa only [v,Complex.volume_ball] using hh
    · have hd : abs (z.im-z₀.im) ≤ dist z z₀ := by
        simpa only [dist_eq_norm,Complex.sub_im] using Complex.abs_im_le_norm (z-z₀)
      have hh : dist z z₀ < 1 := hz'
      have ha := neg_abs_le (z.im-z₀.im)
      linarith
  have ht' := source_mesh_tail_to_stretched μ X (codimension κ) C c δ₀ v rf
    (μ.real {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤}) hp hC hc hδ
    ENNReal.toReal_nonneg hf ENNReal.toReal_nonneg hx
    (fun δ hfd hd => by
      have hh := ht Ω m P hP γ a z₀ hz rf δ hf hfd hd
      simpa only [Measure.real, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top _ _)] using hh) u hu
  apply ht'.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (A*initialGreen κ z₀)*C*Real.exp (-b*u^(2/codimension κ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (source_simple_entrance_bound a hk hκ8 z₀ hz hsmall) hC.le) (Real.exp_pos _).le
    _ = _ := by ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
lemma source_simple_entrance_all_tail (κ : ℝ) (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ),
    4 ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*4)) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ 1 → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z₀ 1)} ≤
      ENNReal.ofReal (C*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ))) := by
  have hκ8 : κ < 8 := by linarith
  obtain ⟨M,C,b,hM,hC,hb,ht⟩ := sourceSimpleStretchedTail_proved κ hκ hκ4
  let A := uniformInverseAngleConstant κ 1*(128*Real.pi)^codimension κ*4^codimension κ
  have hk : 0 < κ := by linarith
  have hA : 0 < A := mul_pos (mul_pos (uniformInverseAngleConstant_pos κ 1 hk hκ8 zero_lt_one)
    (Real.rpow_pos_of_pos (by positivity) _)) (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨max C A*Real.exp b,b/(max M 1)^(2/codimension κ),
    mul_pos (hC.trans_le (le_max_left _ _)) (Real.exp_pos _),
    div_pos hb (Real.rpow_pos_of_pos (hM.trans_le (le_max_left _ _)) _),?_⟩
  intro Ω m P hP γ a z₀ hz hsmall rf u hf hf1 hu
  let : IsProbabilityMeasure P := hP
  let μ := P.comap (Subtype.val : a.samples → Ω)
  let X := fun ω : a.samples => spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
    (γ ω) (a.G ω) rf (ball z₀ 1)
  have hK : 0 < initialGreen κ z₀ := initialGreen_pos κ z₀ (by change 0 < z₀.im; linarith)
  have hzero : μ {ω | 0 < X ω} ≤ ENNReal.ofReal (A*initialGreen κ z₀) := by
    apply le_trans (measure_mono (show {ω | 0 < X ω} ⊆
      {ω : a.samples | spatialHitTime (γ ω) z₀ 3 ≠ ⊤} from ?_))
    · apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (mul_pos hA hK).le).mpr
      exact source_simple_entrance_bound a hk hκ8 z₀ hz hsmall
    · intro ω hω hn
      have hx : X ω = 0 := by
        apply setIntegral_eq_zero_of_forall_eq_zero
        intro z hz'
        exact a.source_simple_weight_zero_no_entrance z₀ hz rf hf1 ω hn z hz'
      change 0 < X ω at hω
      rw [hx] at hω
      exact (lt_irrefl 0) hω
  exact source_tail_threshold_normalize μ X M C A b (2/codimension κ) (initialGreen κ z₀)
    hM hC hA hb (div_pos (by norm_num) (codimension_pos κ hκ8)) hK.le hzero
    (fun v hv => ht Ω m P hP γ a z₀ hz hsmall rf v hf hf1 hv) u hu
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceSimplePhysicalBallAllTailTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ ≤ 4 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
theorem sourceSimplePhysicalBallAllTail_proved : SourceSimplePhysicalBallAllTailTarget := by
  intro κ hκ hκ4
  have hκ8 : κ < 8 := by linarith
  obtain ⟨C,b,hC,hb,ht⟩ := source_simple_entrance_all_tail κ hκ hκ4
  refine ⟨C,b,hC,hb,?_⟩
  intro Ω m P hP γ a z r hr hz hsmall rf u hf hfr hu
  let : IsProbabilityMeasure P := hP
  let c : ℝ≥0 := ⟨r⁻¹,(inv_pos.mpr hr).le⟩
  have hc : 0 < c := inv_pos.mpr hr
  have hcR : (c:ℝ) = r⁻¹ := rfl
  let a' := a.sourceScaled c hc
  have him : ((c:ℂ)*z).im = r⁻¹*z.im := by simp [hcR,Complex.mul_im]
  have hcr : (c:ℝ)*r = 1 := by rw [hcR,inv_mul_cancel₀ hr.ne']
  have hheight : 4 ≤ ((c:ℂ)*z).im := by
    rw [him,mul_comm,←div_eq_mul_inv]
    exact (le_div_iff₀ hr).mpr hz
  have hsmall' : 1 ≤ Real.log ((2*((c:ℂ)*z).im)/((128*Real.pi)*4)) := by
    have he : (2*((c:ℂ)*z).im)/((128*Real.pi)*4) = (2*z.im)/((128*Real.pi)*(4*r)) := by
      rw [him]
      field_simp
    rwa [he]
  have hf' : 0 < (c:ℝ)*rf := mul_pos hc hf
  have hfr' : (c:ℝ)*rf ≤ 1 := by rw [←hcr]; exact mul_le_mul_of_nonneg_left hfr hc.le
  have htail := ht Ω m P hP (fun ω => sourceScaleTrace c (γ ω)) a' ((c:ℂ)*z)
    hheight hsmall' ((c:ℝ)*rf) u hf' hfr' hu
  change (P.comap (Subtype.val : a.samples → Ω)) {ω : a.samples | u < spatialRealMass κ
      (fun t => Real.sqrt κ*a'.B t ω) (sourceScaleTrace c (γ ω)) (a'.G ω)
      ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} ≤
      ENNReal.ofReal (C*initialGreen κ ((c:ℂ)*z)*Real.exp (-b*u^(2/codimension κ))) at htail
  have hp : 0 < (c:ℝ)^dimension κ := Real.rpow_pos_of_pos hc _
  have hrp : 0 < r^dimension κ := Real.rpow_pos_of_pos hr _
  have hmr : (c:ℝ)^dimension κ*(r^dimension κ*u) = u := by
    rw [hcR,Real.inv_rpow hr.le]
    field_simp
  have hx (ω : a.samples) : spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1) =
      (c:ℝ)^dimension κ*spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (ball z r) := by
    simpa only [hcr] using a.sourceScaled_mass c hc z r rf ω
  have he : {ω : a.samples | u < spatialRealMass κ (fun t => Real.sqrt κ*a'.B t ω)
      (sourceScaleTrace c (γ ω)) (a'.G ω) ((c:ℝ)*rf) (ball ((c:ℂ)*z) 1)} =
      {ω : a.samples | r^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z r)} := by
    ext ω
    change (u < _) ↔ _
    rw [hx ω]
    conv_lhs => rw [←hmr]
    exact mul_lt_mul_iff_right₀ hp
  rw [he] at htail
  have hg : initialGreen κ ((c:ℂ)*z) = r^codimension κ*initialGreen κ z := by
    rw [source_scale_initialGreen κ c hc z (by nlinarith),hcR,Real.inv_rpow hr.le,Real.rpow_neg hr.le,inv_inv]
  rw [hg] at htail
  convert htail using 1
  congr 1
  ring
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
def SourcePhysicalBallEveryKappaTarget : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ) (r : ℝ),
    0 < r → 4*r ≤ z₀.im → 1 ≤ Real.log ((2*z₀.im)/((128*Real.pi)*(4*r))) →
  ∀ (rf u : ℝ), 0 < rf → rf ≤ r → 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | r^dimension κ*u < spatialRealMass κ
      (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf (Metric.ball z₀ r)} ≤
      ENNReal.ofReal (C*r^codimension κ*initialGreen κ z₀*Real.exp (-c*u^(2/codimension κ)))
theorem sourcePhysicalBallEveryKappa_proved : SourcePhysicalBallEveryKappaTarget := by
  intro κ hκ hκ8
  by_cases hκ4 : κ ≤ 4
  · exact sourceSimplePhysicalBallAllTail_proved κ hκ hκ4
  · exact sourcePhysicalBallAllTail_proved κ (lt_of_not_ge hκ4) hκ8
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
 

def SourceActualSquareTailTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∃ (A c : ℝ) (kmin : ℕ), 0 < A ∧ 0 < c ∧
  ∀ (T : ℝ≥0) (N k : ℕ), kmin ≤ k → k ≤ N → ∀ ij : ℤ × ℤ, ∀ u : ℝ, 1 ≤ u →
    (P.comap Subtype.val) {ω : a.samples | ((2:ℝ)^(-(k:ℝ)))^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω)
        ((2:ℝ)^(-(N:ℝ))) T (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ≤
    ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ*Real.exp (-c*u^(2/codimension κ)))
theorem sourceActualSquareTail_proved_allKappa : SourceActualSquareTailTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀
  obtain ⟨C,c,hC,hc,ht⟩ := sourcePhysicalBallEveryKappa_proved κ hκ hκ8
  let H := z₀.im-2
  have hH : 0 < H := sub_pos.mpr hz₀
  let G := (2:ℝ)^(-codimension κ)*H^(-codimension κ)
  have hG : 0 < G := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos hH _)
  obtain ⟨kmin,hkmin⟩ := source_small_dyadic_level H hH
  refine ⟨C*G,c,kmin,mul_pos hC hG,hc,?_⟩
  intro T N k hk hkN ij u hu
  let l := (2:ℝ)^(-(k:ℝ))
  let rf := (2:ℝ)^(-(N:ℝ))
  have hl : 0 < l := source_dyadic_side_pos k
  have hf : 0 < rf := source_dyadic_side_pos N
  have hfl : rf ≤ l := source_dyadic_side_le k N hkN
  have hpos : 0 < l^dimension κ*u := mul_pos (Real.rpow_pos_of_pos hl _) (zero_lt_one.trans_le hu)
  by_cases hmeet : (closedBall z₀ 1 ∩ retainedDyadicSquare k ij).Nonempty
  · let z := sourceDyadicCenter k ij
    have hheight : H ≤ z.im := source_square_center_height z₀ k ij hmeet
    have hy : 4*l ≤ z.im := (hkmin k hk).1.trans hheight
    have hsmall : 1 ≤ Real.log ((2*z.im)/((128*Real.pi)*(4*l))) := by
      apply (Real.le_log_iff_exp_le (div_pos (by linarith) (by positivity))).mpr
      apply (le_div_iff₀ (by positivity : 0 < (128*Real.pi)*(4*l))).mpr
      exact (hkmin k hk).2.trans (mul_le_mul_of_nonneg_left hheight (by norm_num))
    have hgreen : initialGreen κ z ≤ G := by
      apply (initialGreen_le_height κ (by linarith) hκ8 z (hH.trans_le hheight)).trans
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
      exact Real.rpow_le_rpow_of_nonpos hH hheight (neg_nonpos.mpr (codimension_pos κ hκ8).le)
    have hh := ht Ω m P hP γ a z l hl hy hsmall rf u hf hfl hu
    apply le_trans (measure_mono (show {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} ⊆
      {ω | l^dimension κ*u < spatialRealMass κ (fun t => Real.sqrt κ*a.B t ω)
        (γ ω) (a.G ω) rf (ball z l)} from ?_)) (hh.trans ?_)
    · intro ω hω
      exact hω.trans_le (source_finite_mass_le_ball a (by linarith) hκ8 z l rf hl hy hf hfl T
        _ (fun w hw => source_square_subset_ball k ij hw.2) ω)
    · apply ENNReal.ofReal_le_ofReal
      calc
        C*l^codimension κ*initialGreen κ z*Real.exp (-c*u^(2/codimension κ)) ≤
            C*l^codimension κ*G*Real.exp (-c*u^(2/codimension κ)) := by gcongr
        _ = _ := by ring
  · have he : closedBall z₀ 1 ∩ retainedDyadicSquare k ij = ∅ := not_nonempty_iff_eq_empty.mp hmeet
    have hempty : {ω : a.samples | l^dimension κ*u <
      (finiteSpatialGreenMass κ (fun t => Real.sqrt κ*a.B t ω) (γ ω) (a.G ω) rf T
        (closedBall z₀ 1 ∩ retainedDyadicSquare k ij)).toReal} = ∅ := by
      simp only [he,finiteSpatialGreenMass,Measure.restrict_empty,lintegral_zero_measure,ENNReal.toReal_zero,
        not_lt_of_ge hpos.le,Set.ofPred_false]
    change (P.comap Subtype.val) _ ≤ _
    rw [hempty,measure_empty]
    exact bot_le
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
namespace RegularSLEPresentation
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
variable (a : RegularSLEPresentation P κ γ)
lemma source_actual_retained_experiment_allKappa [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ8 : κ < 8)
    (z₀ : ℂ) (hz₀ : 2 < z₀.im) :
    ∃ (T : ℝ≥0) (D b p : ℝ) (k₀ : ℕ), 0 < T ∧ 1 ≤ D ∧ 0 < b ∧ 0 < p ∧
      ENNReal.ofReal p ≤ (P.comap Subtype.val)
        {ω : a.samples | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
          retainedMeasure κ D (a.sourceFiniteGreenKernel z₀ T) k₀ N ω (closedBall z₀ 1)} := by
  let : IsProbabilityMeasure (P.comap (Subtype.val : a.samples → Ω)) := a.probability
  have hk : 0 < κ := by linarith
  obtain ⟨T,e₀,m₀,m₂,hT,he,hm₀,hm₂,hm⟩ := source_retained_seed_all κ hκ hκ8
    Ω inferInstance P inferInstance γ a z₀ hz₀
  obtain ⟨A,c,k₁,hA,hc,ht⟩ := sourceActualSquareTail_proved_allKappa κ hκ hκ8
    Ω inferInstance P inferInstance γ a z₀ hz₀
  obtain ⟨k₂,hk₂⟩ := source_dyadic_eventually_le he
  let kmin := max k₁ k₂
  let ν := a.sourceFiniteGreenKernel z₀ T
  have hν (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  have hfirst (N : ℕ) (hN : kmin ≤ N) :
      ENNReal.ofReal m₀ ≤ ∫⁻ ω, ν N ω (closedBall z₀ 1) ∂(P.comap Subtype.val) := by
    simp only [ν,a.sourceFiniteGreenKernel_K]
    exact (hm _ (source_dyadic_side_pos N) (hk₂ N ((le_max_right _ _).trans hN))).1
  have hsecond (N : ℕ) (hN : kmin ≤ N) :
      (∫⁻ ω, (ν N ω (closedBall z₀ 1))^2 ∂(P.comap Subtype.val)) ≤ ENNReal.ofReal m₂ := by
    simp only [ν,a.sourceFiniteGreenKernel_K]
    exact (hm _ (source_dyadic_side_pos N) (hk₂ N ((le_max_right _ _).trans hN))).2
  have htail (N k : ℕ) (hkmin : kmin ≤ k) (hkN : k ≤ N) (ij : ℤ × ℤ) (u : ℝ) (hu : 1 ≤ u) :
      (P.comap Subtype.val) {ω : a.samples | ((2:ℝ)^(-(k:ℝ)))^dimension κ*u <
        (ν N ω (retainedDyadicSquare k ij)).toReal} ≤
        ENNReal.ofReal (A*((2:ℝ)^(-(k:ℝ)))^codimension κ*Real.exp (-c*u^(2/codimension κ))) := by
    simp only [ν,a.sourceFiniteGreenKernel_apply z₀ T N _ _ (retainedSquare_measurable k ij)]
    exact ht T N k ((le_max_left _ _).trans hkmin) hkN ij u hu
  obtain ⟨D,b,p,B,k₀,hD,hb,hp,hB,hk₀,hall,hlim⟩ := sourceRetainedConstruction a.samples
    inferInstance (P.comap Subtype.val) inferInstance κ hk hκ8 ν hν
    (closedBall z₀ 1) (isCompact_closedBall _ _) (fun N ω => a.sourceFiniteGreenKernel_supported z₀ T N ω)
    A c m₀ m₂ hA hc hm₀ hm₂ kmin hfirst hsecond htail
  exact ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩
end RegularSLEPresentation
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceActualRetainedLowerTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ (T : ℝ≥0) (E : Set a.samples), 0 < T ∧ MeasurableSet E ∧
    0 < (P.comap Subtype.val) E ∧
    ∀ ω ∈ E, 0 < hausdorffGauge h (γ ω '' Set.Icc 0 T)
theorem sourceActualRetainedLower_proved_allKappa : SourceActualRetainedLowerTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  obtain ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩ := a.source_actual_retained_experiment_allKappa hκ hκ8 z₀ hz₀
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  let E : Set a.samples := {ω | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
    retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)}
  have hE : MeasurableSet E := by
    have heq : E = ⋂ n : ℕ, ⋃ N ≥ n,
        {ω | ENNReal.ofReal b ≤ retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)} := by
      ext ω
      simp [E,frequently_atTop]
    rw [heq]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun N => MeasurableSet.iUnion
      (fun _ => measurableSet_le measurable_const (retainedMeasure_measurable κ D ν k₀ N measurableSet_closedBall))))
  refine ⟨T,E,hT,hE,(ENNReal.ofReal_pos.mpr hp).trans_le hlim,?_⟩
  intro ω hω
  exact a.source_actual_retained_pathwise hk hκ8 z₀ hz₀ T D b (zero_lt_one.trans_le hD) hb
    k₀ h hh hf ω hω
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
attribute [local instance] Classical.propDecidable
 

def SourceInteriorRetainedTransferTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ) (z₀ : ℂ), 2 < z₀.im →
  ∀ h : ℝ → ℝ, IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ (T : ℝ≥0) (E : Set a.samples), 0 < T ∧ MeasurableSet E ∧
    0 < (P.comap Subtype.val) E ∧ ∀ ω ∈ E,
      0 < hausdorffGauge h (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)) ∧
      ∀ (U : ℝ≥0 → ℝ) (η : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ),
        IsCapacityTwoWitness U η G F → ∀ s : ℝ≥0,
          0 < hausdorffGauge h (F s '' (Metric.closedBall z₀ 1 ∩ (γ ω '' Set.Icc 0 T)))

theorem sourceInteriorRetainedTransfer_proved_allKappa : SourceInteriorRetainedTransferTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  obtain ⟨T,D,b,p,k₀,hT,hD,hb,hp,hlim⟩ := a.source_actual_retained_experiment_allKappa hκ hκ8 z₀ hz₀
  let ν := a.sourceFiniteGreenKernel z₀ T
  let (N : ℕ) : IsFiniteKernel (ν N) := a.sourceFiniteGreenKernel_finite hk hκ8 z₀ hz₀ T N
  let E : Set a.samples := {ω | ∃ᶠ N in atTop, ENNReal.ofReal b ≤
    retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)}
  have hE : MeasurableSet E := by
    have heq : E = ⋂ n : ℕ, ⋃ N ≥ n,
        {ω | ENNReal.ofReal b ≤ retainedMeasure κ D ν k₀ N ω (closedBall z₀ 1)} := by
      ext ω
      simp [E,frequently_atTop]
    rw [heq]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun N => MeasurableSet.iUnion
      (fun _ => measurableSet_le measurable_const (retainedMeasure_measurable κ D ν k₀ N measurableSet_closedBall))))
  refine ⟨T,E,hT,hE,(ENNReal.ofReal_pos.mpr hp).trans_le hlim,?_⟩
  intro ω hω
  have hpos := a.source_actual_retained_interior_pathwise hk hκ8 z₀ hz₀ T D b (zero_lt_one.trans_le hD) hb
    k₀ h hh hf ω hω
  refine ⟨hpos,?_⟩
  intro U η G F hw s
  exact source_inverse_chart_gauge_positive κ hk hκ8 h hh hf U η G F hw s
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed)
    (fun z hz => zero_lt_one.trans (source_unit_ball_height hz₀ hz.1)) hpos
end
end SLEExactGauge
end

 
section
open Set Filter MeasureTheory ProbabilityTheory Complex Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
noncomputable section
local instance simplePastMeshDriverMeasurableSpace : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance simplePastMeshTraceMeasurableSpace : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance simplePastMeshDriverBorelSpace : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩
local instance simplePastMeshTraceBorelSpace : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩
lemma source_dilation_gauge_positive_allKappa (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (h : ℝ → ℝ) (hh : IsGauge h) (hf : HasSmallRadiusFormula h (hFormula κ))
    {c : ℂ} (hc : c ≠ 0) {S : Set ℂ} (hS : IsCompact S)
    (hp : 0 < hausdorffGauge h S) : 0 < hausdorffGauge h ((fun z => c*z) '' S) := by
  by_contra hn
  have hz : hausdorffGauge h ((fun z => c*z) '' S) = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have he := source_gauge_holomorphic_compact_null κ hκ hκ8 h hh hf
    (D := univ) (f := fun z => c⁻¹*z) isOpen_univ (hS.image (continuous_const.mul continuous_id))
    (subset_univ _) (by fun_prop) hz
  have hi : (fun z => c⁻¹*z) '' ((fun z => c*z) '' S) = S := by
    rw [←image_comp]
    simp only [Function.comp_def,←mul_assoc,inv_mul_cancel₀ hc,one_mul,image_id']
  change hausdorffGauge h ((fun z => c⁻¹*z) '' ((fun z => c*z) '' S)) = 0 at he
  rw [hi] at he
  exact hp.ne' he

lemma RegularSLEPresentation.source_trace_path_measurable_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) :
    Measurable (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) := by
  apply source_path_measurable
  intro t
  exact (a.trace_adapted t).mono (a.filtration.le t) le_rfl

lemma RegularSLEPresentation.source_scale_trace_law_allKappa
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ : ℝ} {γ : Ω → ℝ≥0 → ℂ}
    (a : RegularSLEPresentation P κ γ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (c : ℝ≥0) (hc : 0 < c) :
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous) =
    (P.comap (Subtype.val : a.samples → Ω)).map
      (sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
        (a.sourceScaled c hc).trace_continuous) := by
  exact sourceTraceLawUnique_proved κ hκ hκ8 a.B (a.sourceScaled c hc).B
    a.brownian (a.sourceScaled c hc).brownian a.measurable_B (a.sourceScaled c hc).measurable_B
    a.continuous_B (a.sourceScaled c hc).continuous_B _ _ a.G a.F
    (a.sourceScaled c hc).G (a.sourceScaled c hc).F a.witness (a.sourceScaled c hc).witness
 

def SourceUniformInteriorSeedTarget_allKappa : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 8 →
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (γ : Ω → ℝ≥0 → ℂ) (a : RegularSLEPresentation P κ γ)
    (h : ℝ → ℝ), IsGauge h → HasSmallRadiusFormula h (hFormula κ) →
  ∃ p : ℝ≥0∞, 0 < p ∧ ∀ δ : ℝ≥0, 0 < δ →
    ∃ K : Set ℂ, IsCompact K ∧ K ⊆ upperHalfPlane ∧
      p ≤ (P.comap (Subtype.val : a.samples → Ω))
        {ω | 0 < hausdorffGauge h (K ∩ (γ ω '' Set.Icc 0 δ))}
theorem sourceUniformInteriorSeed_proved_allKappa : SourceUniformInteriorSeedTarget_allKappa := by
  intro κ hκ hκ8 Ω m P hP γ a h hh hf
  let : IsProbabilityMeasure P := hP
  have hk : 0 < κ := by linarith
  let z₀ : ℂ := 3*I
  have hz₀ : 2 < z₀.im := by norm_num [z₀]
  obtain ⟨T,E,hT,hE,hp,hseed⟩ :=
    sourceInteriorRetainedTransfer_proved_allKappa κ hκ hκ8 Ω m P hP γ a z₀ hz₀ h hh hf
  let Q := P.comap (Subtype.val : a.samples → Ω)
  refine ⟨Q E,hp,?_⟩
  intro δ hδ
  let c := NNReal.sqrt (δ/T)
  have hc : 0 < c := by dsimp [c]; exact NNReal.sqrt_pos.mpr (div_pos hδ hT)
  have hc2 : c^2 = δ/T := NNReal.sq_sqrt _
  have ht : sourceScaleTime c δ = T := by
    unfold sourceScaleTime
    rw [hc2]
    field_simp
  let K := (fun z : ℂ => (c:ℂ)*z) '' closedBall z₀ 1
  have hK : IsCompact K := (isCompact_closedBall z₀ 1).image (continuous_const.mul continuous_id)
  have hKH : K ⊆ upperHalfPlane := by
    rintro _ ⟨z,hz,rfl⟩
    have hz' : 0 < z.im := zero_lt_one.trans (source_unit_ball_height hz₀ hz)
    change 0 < ((c:ℂ)*z).im
    simpa only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero] using mul_pos (show 0 < (c:ℝ) from hc) hz'
  refine ⟨K,hK,hKH,?_⟩
  let gp := sourceTracePath (fun ω : a.samples => γ ω) a.trace_continuous
  let sp := sourceTracePath (fun ω : a.samples => sourceScaleTrace c (γ ω))
    (a.sourceScaled c hc).trace_continuous
  let A : Set C(ℝ≥0,ℂ) := {g | 0 < hausdorffGauge h (K ∩ (g '' Icc 0 δ))}
  have hA : MeasurableSet A := sourceTracePositiveMeasurable_proved h hh K hK.isClosed 0 δ
  have hm : Measurable gp := a.source_trace_path_measurable_allKappa
  have hsm : Measurable sp := (a.sourceScaled c hc).source_trace_path_measurable_allKappa
  have hmap := congrArg (fun μ : Measure C(ℝ≥0,ℂ) => μ A) (a.source_scale_trace_law_allKappa hk hκ8 c hc)
  rw [Measure.map_apply hm hA,Measure.map_apply hsm hA] at hmap
  change Q E ≤ Q (gp ⁻¹' A)
  rw [hmap]
  apply measure_mono
  intro ω hω
  have hpos := (hseed ω hω).1
  have heq : K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ) =
      (fun z : ℂ => (c:ℂ)*z) '' (closedBall z₀ 1 ∩ (γ ω '' Icc 0 T)) := by
    rw [source_scale_past c δ hc,ht, image_inter (mul_right_injective₀ (by exact_mod_cast hc.ne' : (c:ℂ) ≠ 0))]
  change 0 < hausdorffGauge h (K ∩ (sourceScaleTrace c (γ ω) '' Icc 0 δ))
  rw [heq]
  exact source_dilation_gauge_positive_allKappa κ hk hκ8 h hh hf (by exact_mod_cast hc.ne')
    ((isCompact_closedBall z₀ 1).inter_right (isCompact_Icc.image (a.trace_continuous ω)).isClosed) hpos
end
end SLEExactGauge
end

 
end
end
end

end OAI
