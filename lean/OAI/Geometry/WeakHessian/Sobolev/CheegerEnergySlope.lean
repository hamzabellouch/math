import Mathlib
import OAI.Geometry.WeakHessian.Calculus.ELpNormSq
import OAI.Geometry.WeakHessian.Sobolev.CheegerEnergyCongrAe
import OAI.Geometry.WeakHessian.LocalBounds.L2SlopeGraph

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology
open Set
open scoped NNReal

namespace WeakHessian
open MeasureTheory Filter
open scoped Topology InnerProductSpace

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X}

omit [BorelSpace X] in
lemma cheegerEnergy_le_slope {f : X → ℝ} (hf : GloballyLipschitz f) (hf2 : MemLp f 2 m) :
    cheegerEnergy m f ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope f x^2 ∂m := by
  have H := cheegerEnergy_le_liminf hf2 (fs := fun (_ : ℕ) => f) (fun _ => ⟨hf,hf2⟩)
    (by simp)
  simpa only [liminf_const] using H

lemma slopeGraph_energy_le {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2SlopeGraph m) :
    cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2) := by
  obtain ⟨f,hf,hf2,hpf,hmajor⟩ := hp
  have hm : MemLp (fun x => (localSlope f x).toReal) 2 m :=
    (Lp.memLp p.snd).mono'
      (measurable_localSlope hf.choose_spec.continuous).ennreal_toReal.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg] using hmajor)
  have hn : ‖hm.toLp (fun x => (localSlope f x).toReal)‖ ≤ ‖p.snd‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hmajor,hm.coeFn_toLp] with x hx hy
    rw [hy,Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,Real.norm_eq_abs]
    exact hx.trans (le_abs_self _)
  calc
    cheegerEnergy m (p.fst : X → ℝ) = cheegerEnergy m f :=
      cheegerEnergy_congr_ae (hpf ▸ hf2.coeFn_toLp)
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ∫⁻ x, localSlope f x^2 ∂m := cheegerEnergy_le_slope hf hf2
    _ = ENNReal.ofReal (‖hm.toLp (fun x => (localSlope f x).toReal)‖^2/2) :=
      half_lintegral_localSlope_eq hf.choose_spec hm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg p.snd,norm_nonneg (hm.toLp (fun x => (localSlope f x).toReal))])

lemma relaxedGraph_energy_le {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m)}
    (hp : p ∈ l2RelaxedGraph m) :
    cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2) := by
  have hcl : IsClosed {p : WithLp 2 (Lp ℝ 2 m × Lp ℝ 2 m) |
      cheegerEnergy m (p.fst : X → ℝ) ≤ ENNReal.ofReal (‖p.snd‖^2/2)} := by
    exact (lowerSemicontinuous_iff_isClosed_epigraph.mp lowerSemicontinuous_cheegerEnergy).preimage
      ((WithLp.continuous_fst 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).prodMk
        (ENNReal.continuous_ofReal.comp
          (((WithLp.continuous_snd 2 (Lp ℝ 2 m) (Lp ℝ 2 m)).norm.pow 2).div_const 2)))
  exact (closure_minimal (fun _ => slopeGraph_energy_le) hcl) hp

lemma exists_relaxedGradient_of_cheeger_lt {f : Lp ℝ 2 m} {B : ℝ} (hB : 0 ≤ B)
    (he : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal (B^2/2)) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧ ‖D‖ ≤ B := by
  have happrox (ε : ℝ) (hε : 0 < ε) := cheegerEnergy_lt_approx he hε
  choose fs hLip hfs hdist hEn using fun n : ℕ => happrox (1/((n:ℝ)+1)) (by positivity)
  have hsfin (n : ℕ) : (∫⁻ x, localSlope (fs n) x^2 ∂m) < ∞ := by
    by_contra hh
    have ht := top_le_iff.mp (not_lt.mp hh)
    have H := hEn n
    norm_num [ht] at H
  let hDs (n : ℕ) := memLp_localSlope_of_lintegral_lt_top (hLip n).choose_spec (hsfin n)
  let fn (n : ℕ) := (hfs n).toLp (fs n)
  let Dn (n : ℕ) := (hDs n).toLp (fun x => (localSlope (fs n) x).toReal)
  apply WeakHessianFunctional.exists_snd_of_tendsto_fst_of_bounded
    isClosed_l2RelaxedGraph convex_l2RelaxedGraph (u := fun n => WithLp.toLp 2 (fn n,Dn n))
  · intro n
    apply subset_closure
    exact ⟨fs n,hLip n,hfs n,rfl,by
      filter_upwards [(hDs n).coeFn_toLp] with x hx
      exact hx.ge⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n
    have H := hEn n
    rw [half_lintegral_localSlope_eq (hLip n).choose_spec (hDs n)] at H
    have H' := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).mp H
    change ‖Dn n‖^2/2 < B^2/2 at H'
    change ‖Dn n‖ ≤ B
    nlinarith [norm_nonneg (Dn n)]

lemma exists_relaxedGradient_energy_eq {f : Lp ℝ 2 m}
    (he : cheegerEnergy m (f : X → ℝ) < ∞) :
    ∃ D : Lp ℝ 2 m, WithLp.toLp 2 (f,D) ∈ l2RelaxedGraph m ∧
      (∀ E : Lp ℝ 2 m, WithLp.toLp 2 (f,E) ∈ l2RelaxedGraph m → ‖D‖ ≤ ‖E‖) ∧
      cheegerEnergy m (f : X → ℝ) = ENNReal.ofReal (‖D‖^2/2) := by
  let a := (cheegerEnergy m (f : X → ℝ)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have haB : a < (a+2)^2/2 := by nlinarith [sq_nonneg a]
  have hE : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal ((a+2)^2/2) := by
    rw [← ENNReal.ofReal_toReal he.ne]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha).mpr haB
  obtain ⟨D₀,hD₀,_⟩ := exists_relaxedGradient_of_cheeger_lt (by linarith : 0 ≤ a+2) hE
  obtain ⟨D,hD,hmin⟩ := exists_norm_minimal_relaxedGradient (f := f) ⟨D₀,hD₀⟩
  refine ⟨D,hD,hmin,le_antisymm (relaxedGraph_energy_le (p := WithLp.toLp 2 (f,D)) hD) ?_⟩
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  by_cases hrt : r = ∞
  · rw [hrt]; exact le_top
  let B : ℝ := Real.sqrt (2*r.toReal)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBs : B^2/2 = r.toReal := by
    dsimp only [B]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2*r.toReal)]
    ring
  have hEB : cheegerEnergy m (f : X → ℝ) < ENNReal.ofReal (B^2/2) := by
    rwa [hBs,ENNReal.ofReal_toReal hrt]
  obtain ⟨E,hE,hEn⟩ := exists_relaxedGradient_of_cheeger_lt hB hEB
  have hDE := (hmin E hE).trans hEn
  calc
    ENNReal.ofReal (‖D‖^2/2) ≤ ENNReal.ofReal (B^2/2) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg D])
    _ = r := by rw [hBs,ENNReal.ofReal_toReal hrt]
end WeakHessian

end
end InlinedFile0

end OAI
