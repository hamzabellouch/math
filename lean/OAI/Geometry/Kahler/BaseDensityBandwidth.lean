import OAI.Geometry.Kahler.BaseDensityFourier

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
namespace PinchedHartogs.BaseConstruction

lemma densityCorrection_phase_band {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (R : ℝ) (f b : ℝ → ℝ) (p : Sphere) :
    PhaseBandwidth (densityCorrection k R f b W p) (k+ℓ) := by
  classical
  intro ξ
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z]
      rw [phaseSum_shift]
    have hbound : ∀ n ∈ s.image (fun n => (k:ℤ)+n), |n| ≤ ((k+ℓ:ℕ):ℤ) := by
      intro n hn
      obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hn
      have ht := abs_add_le (k:ℤ) m
      have hm' := hs m hm
      simpa only [Nat.cast_add,abs_of_nonneg (Int.natCast_nonneg k)] using
        le_trans ht (by simpa using add_le_add_right hm' (k:ℤ))
    obtain ⟨b',hb'⟩ := phaseSum_real_band hbound (fun n => A (n-k))
    refine ⟨phaseBand (k+ℓ),b',fun n hn => (mem_phaseBand _ _).mp hn,?_⟩
    intro z
    rw [hh,hb']
  · refine ⟨∅,fun _ => 0,by simp,?_⟩
    intro z
    simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,Complex.ofReal_zero,phaseSum,Finset.sum_empty]

lemma densityCorrection_orbit_zero {W : Base → ℝ} (hW : Differentiable ℝ W)
    {ℓ k : ℕ} (hband : PhaseBandwidth W ℓ) (hℓ : ℓ < k)
    (R : ℝ) (f b : ℝ → ℝ) (p ξ : Sphere) :
    (∫ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) ∂circleMeasure) = 0 := by
  classical
  by_cases hc : Real.exp (-R/k) < ‖bracket (ξ:Base) (p:Base)‖
  · have hξ : bracket (ξ:Base) (p:Base) ≠ 0 := norm_pos_iff.mp (lt_trans (Real.exp_pos _) hc)
    let q : Sphere := ⟨centralPoint p ξ,by simpa only [Metric.mem_sphere,dist_zero_right] using centralPoint_norm p hξ⟩
    obtain ⟨s,a,hs,he⟩ := hband q
    let A : ℤ → ℂ := fun n => (((‖bracket (ξ:Base) (p:Base)‖^2)⁻¹:ℝ) *
          (bracket (ξ:Base) (p:Base)/(‖bracket (ξ:Base) (p:Base)‖:ℂ))^k * a n *
          ((f (densityHeight k p ξ) - (n:ℝ)/k*b (densityHeight k p ξ):ℝ):ℂ))
    have hh : ∀ z : Circle, densityCorrection k R f b W p ((z:ℂ) • (ξ:Base)) =
        (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re := by
      intro z
      rw [densityCorrection,circle_bracket_norm,ite_eq_left hc]
      rw [densityCorrectionRaw_phase_expansion k f b hW p ξ hξ s a he z,phaseSum_shift]
    simp_rw [hh]
    rw [show (∫ z : Circle, (phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z).re ∂circleMeasure) =
      (∫ z : Circle, phaseSum (s.image (fun n => (k:ℤ)+n)) (fun n => A (n-k)) z ∂circleMeasure).re from
      integral_re (compact_continuous_integrable (phaseSum_continuous _ _))]
    have hn : 0 ∉ s.image (fun n => (k:ℤ)+n) := by
      intro hn
      obtain ⟨m,hm,he⟩ := Finset.mem_image.mp hn
      have hm' := (abs_le.mp (hs m hm)).1
      omega
    rw [phaseSum_integral _ hn]
    rfl
  · simp only [densityCorrection,circle_bracket_norm,ite_eq_right hc,integral_zero]

def densityBandwidth (Q : ℕ) (j : ℕ) : ℕ := ∑ i ∈ Finset.range j, Q^(i+1)

lemma densityBandwidth_succ (Q j : ℕ) : densityBandwidth Q (j+1)=Q^(j+1)+densityBandwidth Q j := by
  simp [densityBandwidth,Finset.sum_range_succ,Nat.add_comm]

lemma densityBandwidth_lt {Q : ℕ} (hQ : 2 ≤ Q) (j : ℕ) : densityBandwidth Q j < Q^(j+1) := by
  induction j with
  | zero => simp [densityBandwidth]; omega
  | succ j ih =>
    rw [densityBandwidth_succ]
    have hp : 0 < Q^(j+1) := pow_pos (by omega) _
    calc
      Q^(j+1)+densityBandwidth Q j < Q^(j+1)*2 := by omega
      _ ≤ Q^(j+1)*Q := Nat.mul_le_mul_left _ hQ
      _ = _ := by simp only [pow_succ]

lemma density_bandwidth {Q : ℕ} (hQ : 0 < Q) {R E : ℝ} (hER : E < R)
    {f b : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (htail : ∀ y, E ≤ y → f y=0 ∧ b y=0) (P : ℕ → Finset Sphere) (j : ℕ) :
    PhaseBandwidth (density Q R f b P j) (densityBandwidth Q j) := by
  induction j with
  | zero => exact phaseBandwidth_one
  | succ j ih =>
    rw [densityBandwidth_succ]
    apply phaseBandwidth_add (phaseBandwidth_mono ih (Nat.le_add_left _ _))
    apply phaseBandwidth_sum
    intro p hp
    exact densityCorrection_phase_band ((density_smooth hQ hER hf hb htail P j).differentiable (by simp)) ih R f b p

end PinchedHartogs.BaseConstruction

end

end OAI
