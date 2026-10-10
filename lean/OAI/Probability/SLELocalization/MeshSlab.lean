import Mathlib
import OAI.Probability.SLELocalization.MeshExponents
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Mesh Slab estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab

lemma geometric_mesh_mgf {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p K δ rf : ℝ} (hp : p < 1) (hK : 0 < K)
    (hrf : 0 < rf) (hrδ : rf ≤ δ)
    (hX : ∀ r, 0 < r → r ≤ δ → AEMeasurable (X r) P)
    (hslab : ∀ e r, 0 < e → e ≤ r → r/2 ≤ e → r ≤ δ → ∀ θ : ℝ,
      (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(X e ω-X r ω))) ∂P) ≤
        ENNReal.ofReal (Real.exp (θ^2*(K*r^(1-p))^2/2))) (θ : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(X rf ω-X δ ω))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(K*δ^(1-p)/(1-(1/2:ℝ)^(1-p)))^2/2)) := by
  let q : ℝ := (1/2:ℝ)^(1-p)
  have hq : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hδ : 0 < δ := hrf.trans_le hrδ
  let R : ℕ → ℝ := fun n => max rf (δ*(1/2:ℝ)^n)
  have hRpos (n : ℕ) : 0 < R n := hrf.trans_le (le_max_left _ _)
  have hRle (n : ℕ) : R n ≤ δ := max_le hrδ (by
    have hh : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    simpa using mul_le_mul_of_nonneg_left hh hδ.le)
  have hRm (n : ℕ) : R (n+1) ≤ R n := by
    apply max_le_max le_rfl
    rw [pow_succ]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) n]
  have hR0 : R 0 = δ := by dsimp [R]; simp only [pow_zero,mul_one,max_eq_right hrδ]
  have ht : Tendsto (fun n : ℕ => δ*(1/2:ℝ)^n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) < 1)).const_mul δ
  obtain ⟨N,hN⟩ := (ht.eventually (gt_mem_nhds hrf)).exists
  have hRN : R N = rf := max_eq_left hN.le
  let Y := fun n ω => X (R (n+1)) ω-X (R n) ω
  let σ := fun n => K*δ^(1-p)*q^n
  have hσ (n : ℕ) : 0 < σ n := by dsimp [σ]; positivity
  have hYm (n : ℕ) : AEMeasurable (Y n) P :=
    (hX _ (hRpos (n+1)) (hRle (n+1))).sub (hX _ (hRpos n) (hRle n))
  have hmgf (n : ℕ) (s : ℝ) : (∫⁻ ω, ENNReal.ofReal (Real.exp (s*Y n ω)) ∂P) ≤
      ENNReal.ofReal (Real.exp (s^2*(σ n)^2/2)) := by
    by_cases hn : rf ≤ δ*(1/2:ℝ)^n
    · have hRn : R n = δ*(1/2:ℝ)^n := max_eq_right hn
      have hhalf : R n/2 ≤ R (n+1) := by
        rw [hRn]
        apply le_trans _ (le_max_right _ _)
        rw [pow_succ]
        ring_nf
        exact le_rfl
      have hh := hslab _ _ (hRpos (n+1)) (hRm n) hhalf (hRle n) s
      have he : K*(R n)^(1-p) = σ n := by
        rw [hRn,geo_radius_power hδ]
        dsimp [σ,q]
        ring
      simpa only [Y,he] using hh
    · have he : R n = rf := max_eq_left (le_of_not_ge hn)
      have hne : R (n+1) = rf := le_antisymm (by rw [← he]; exact hRm n) (le_max_left _ _)
      have hY0 : ∀ ω, Y n ω = 0 := fun ω => by dsimp [Y]; rw [he,hne]; ring
      simp only [hY0,mul_zero,Real.exp_zero,ENNReal.ofReal_one,lintegral_const,measure_univ,mul_one]
      have hn0 : 0 ≤ s^2*(σ n)^2/2 := by positivity
      have he1 : 1 ≤ Real.exp (s^2*(σ n)^2/2) := Real.one_le_exp hn0
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal he1
  have hsum := finite_mgf_sum (Finset.range N) Y σ (fun n _ => hσ n) (fun n _ => hYm n)
    (fun n _ s => hmgf n s) θ
  have htel (ω : Ω) : (∑ n ∈ Finset.range N, Y n ω) = X rf ω-X δ ω := by
    rw [show (∑ n ∈ Finset.range N, Y n ω) = X (R N) ω-X (R 0) ω from Finset.sum_range_sub (fun n => X (R n) ω) N,
      hRN,hR0]
  simp only [htel] at hsum
  apply hsum.trans
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  apply div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left _ (sq_nonneg θ)) (by norm_num)
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun n _ => (hσ n).le))
  rw [show (∑ n ∈ Finset.range N, σ n) = K*δ^(1-p)*(∑ n ∈ Finset.range N, q^n) by simp only [σ,Finset.mul_sum]]
  have hg : (∑ n ∈ Finset.range N, q^n) ≤ 1/(1-q) := by
    apply (le_div_iff₀ (sub_pos.2 hq1)).2
    rw [geom_sum_mul_neg]
    exact sub_le_self _ (pow_nonneg hq.le N)
  have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ K*δ^(1-p) by positivity)
  simpa only [mul_one_div,q] using hh

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.MeshSlab

lemma tail_scale (p : ℝ) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K) :
    (δ^(-p))^2/(2*(K*δ^(1-p))^2) = (1/(2*K^2))*δ^(-2:ℝ) := by
  have hp : (δ^(-p))^2 = (δ^(1-p))^2*δ^(-2:ℝ) := by
    rw [← Real.rpow_mul_natCast hδ.le,← Real.rpow_mul_natCast hδ.le,← Real.rpow_add hδ]
    congr 1
    norm_num
    ring
  rw [hp,mul_pow]
  field_simp [(Real.rpow_pos_of_pos hδ (1-p)).ne',hK.ne']

end SLEExactGauge.MeshSlab

end

end

section
noncomputable section
open Set Filter Metric MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open MeshSlab

theorem integratedMeshTail_halfPlane_simple (κ : ℝ) (hκ : 0 < κ ∧ κ ≤ 4) :
    ∃ C c δ₀ : ℝ, 0 < C ∧ 0 < c ∧ 0 < δ₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
        (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
        (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
        (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
          (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
        (z₀ : ℂ) (_hcollar : Metric.closedBall z₀ 2 ⊆ halfPlane)
        (r_f δ : ℝ), 0 < r_f → r_f ≤ δ → δ ≤ δ₀ →
        P {sample | ENNReal.ofReal (C*δ^(-codimension κ)) <
          ∫⁻ z in Metric.closedBall z₀ 1,
            physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z r_f ∂volume} ≤
            ENNReal.ofReal (C*Real.exp (-c*δ^(-2:ℝ))) := by
  obtain ⟨K,hK,hslab⟩ := slab_mass_mgf κ hκ
  let p := codimension κ
  have hp : p < 1 := by dsimp [p,codimension,dimension]; linarith [hκ.1]
  let q : ℝ := (1/2:ℝ)^(1-p)
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  let K' := K/(1-q)
  have hK' : 0 < K' := div_pos hK (sub_pos.2 hq)
  let C := max 1 (Real.pi*(4:ℝ)^p+1)
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCbase : Real.pi*(4:ℝ)^p+1 ≤ C := le_max_right _ _
  let c := 1/(2*K'^2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨C,c,1/2,lt_of_lt_of_le zero_lt_one hC1,hc,by norm_num,?_⟩
  intro Ω m P hP B hB γ g f hγ hmaps z₀ hcollar rf δ hrf hrδ hδsmall
  let A := closedBall z₀ (1:ℝ)
  let X := physicalMass A κ B γ g
  have hAc : IsCompact A := isCompact_closedBall _ _
  have hA : MeasurableSet A := hAc.measurableSet
  let : IsFiniteMeasure (volume.restrict A) := isFiniteMeasure_restrict.2 hAc.measure_lt_top.ne
  have hκ' : 0 < κ ∧ κ < 8 := ⟨hκ.1,by linarith [hκ.2]⟩
  have hδ : 0 < δ := hrf.trans_le hrδ
  have hδ1 : δ < 1 := by linarith
  have hy := FiniteTilt.collar_height hcollar
  have hXm (r : ℝ) (hr : 0 < r) : AEMeasurable (X r) P := by
    exact physicalMass_aemeasurable A κ hκ' B hB γ g f hγ hmaps r hr
  have hmgf (θ : ℝ) : (∫⁻ ω, ENNReal.ofReal (Real.exp (θ*(X rf ω-X δ ω))) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ^2*(K'*δ^(1-p))^2/2)) := by
    have hh := geometric_mesh_mgf X hp hK hrf hrδ (fun r hr _ => hXm r hr)
      (fun e r he her hel hrδ θ => hslab B hB γ g f hγ hmaps z₀ hcollar e r he her hel (hrδ.trans_lt hδ1) θ) θ
    convert hh using 1
    congr 3
    dsimp [K',q]
    ring
  have htail := BrownianPredictable.tail_of_exponential_bound (fun ω => X rf ω-X δ ω)
    ((hXm rf hrf).sub (hXm δ hδ)) (sq_pos_of_pos (mul_pos hK' (Real.rpow_pos_of_pos hδ _)))
    hmgf (Real.rpow_pos_of_pos hδ (-p))
  have hbound := physicalMass_bound A κ hκ' B hB γ g f hγ hmaps δ hδ hA
    (fun z hz => hδ1.trans_le (hy z hz))
  have hlint := physicalMass_lintegral A κ hκ' B hB γ g f hγ hmaps rf hrf hA
    (fun z hz => hrδ.trans_lt (hδ1.trans_le (hy z hz)))
  have hv : (volume A).toReal = Real.pi := by dsimp [A]; rw [Complex.volume_closedBall]; norm_num
  have hinit : (volume A).toReal*(δ/4)^(-codimension κ) = Real.pi*(4:ℝ)^p*δ^(-p) := by
    rw [hv,Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),div_inv_eq_mul]
    dsimp [p]
    ring
  have hsub : {ω | ENNReal.ofReal (C*δ^(-codimension κ)) <
      ∫⁻ z in A, physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z rf} ≤ᵐ[P]
      {ω | δ^(-p) < X rf ω-X δ ω} := by
    filter_upwards [hbound,hlint] with ω hb hl hs
    rw [hinit] at hb
    change X δ ω ≤ Real.pi*(4:ℝ)^p*δ^(-p) at hb
    change ENNReal.ofReal (C*δ^(-codimension κ)) <
      (∫⁻ z in A, physicalStoppedDensity κ (fun t => B t ω) (γ ω) (g ω) z rf) at hs
    rw [← hl] at hs
    by_contra hn
    have hd := le_of_not_gt hn
    have hscale := mul_le_mul_of_nonneg_right hCbase (Real.rpow_nonneg hδ.le (-p))
    have he : X rf ω ≤ C*δ^(-codimension κ) := by change X rf ω ≤ C*δ^(-p); nlinarith
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal he)) hs
  apply (measure_mono_ae hsub).trans
  apply htail.trans
  rw [neg_div,tail_scale p hδ hK']
  apply ENNReal.ofReal_le_ofReal
  have he : -(1/(2*K'^2)*δ^(-2:ℝ)) = -c*δ^(-2:ℝ) := by dsimp [c]; ring
  rw [he]
  exact le_mul_of_one_le_left (Real.exp_pos _).le hC1

end SLEExactGauge

end

end

end OAI
