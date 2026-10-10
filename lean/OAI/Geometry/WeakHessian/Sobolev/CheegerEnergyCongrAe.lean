import Mathlib
import OAI.Geometry.WeakHessian.Model

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerEnergy_congr_ae {f g : X → ℝ} (h : f =ᵐ[m] g) :
    cheegerEnergy m f = cheegerEnergy m g := by
  have hm : MemLp f 2 m ↔ MemLp g 2 m := memLp_congr_ae h
  have he : ∀ u : X → ℝ, eLpNorm (fun x => u x - f x) 2 m =
      eLpNorm (fun x => u x - g x) 2 m := by
    intro u
    apply eLpNorm_congr_ae
    filter_upwards [h] with x hx
    simp only [hx]
  simp only [cheegerEnergy, hm, he]

lemma cheegerEnergy_le_liminf {f : X → ℝ} (hf : MemLp f 2 m)
    {fs : ℕ → X → ℝ}
    (hfs : ∀ n, GloballyLipschitz (fs n) ∧ MemLp (fs n) 2 m)
    (hc : Tendsto (fun n => eLpNorm (fun x => fs n x - f x) 2 m) atTop (𝓝 0)) :
    cheegerEnergy m f ≤ liminf (fun n => (2 : ℝ≥0∞)⁻¹ *
      ∫⁻ x, (localSlope (fs n) x)^2 ∂m) atTop := by
  rw [cheegerEnergy, ite_eq_left hf]
  exact sInf_le ⟨fs, hfs, hc, rfl⟩

lemma cheegerEnergy_lt_approx {f : Lp ℝ 2 m} {a : ℝ≥0∞}
    (ha : cheegerEnergy m (f : X → ℝ) < a) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : X → ℝ, GloballyLipschitz g ∧ ∃ hg : MemLp g 2 m,
      dist (hg.toLp g) f < ε ∧
      (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, (localSlope g x)^2 ∂m) < a := by
  rw [cheegerEnergy, ite_eq_left (Lp.memLp f), sInf_lt_iff] at ha
  obtain ⟨b, ⟨fs, hfs, hc, hb⟩, hba⟩ := ha
  have hconv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs
    (fun n => (hfs n).2) (f : X → ℝ) (Lp.memLp f)).mpr hc
  simp only [Lp.toLp_coeFn] at hconv
  have hdist : ∀ᶠ n in atTop, dist ((hfs n).2.toLp (fs n)) f < ε :=
    (tendsto_order.1 (hconv.dist tendsto_const_nhds)).2 ε (by simpa only [dist_self] using hε)
  rw [hb] at hba
  have H := frequently_lt_of_liminf_lt (h := hba)
  obtain ⟨n, hn, hd⟩ := (H.and_eventually hdist).exists
  exact ⟨fs n, (hfs n).1, (hfs n).2, hd, hn⟩

lemma cheegerEnergy_le_of_lip_approximations {f : Lp ℝ 2 m} {a : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → ∃ g : X → ℝ, GloballyLipschitz g ∧
      ∃ hg : MemLp g 2 m, dist (hg.toLp g) f < ε ∧
        (2 : ℝ≥0∞)⁻¹ * (∫⁻ x, (localSlope g x)^2 ∂m) ≤ a) :
    cheegerEnergy m (f : X → ℝ) ≤ a := by
  choose g hg hm hd he using fun n : ℕ => h (1/((n:ℝ)+1)) (by positivity)
  have hconv : Tendsto (fun n => (hm n).toLp (g n)) atTop (𝓝 f) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun n => dist_nonneg) (fun n => (hd n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hm
    (f : X → ℝ) (Lp.memLp f)).mp (by simpa only [Lp.toLp_coeFn] using hconv)
  exact (cheegerEnergy_le_liminf (Lp.memLp f) (fun n => ⟨hg n, hm n⟩) hc).trans
    (liminf_le_of_frequently_le (Eventually.of_forall he).frequently)

lemma lowerSemicontinuous_cheegerEnergy :
    LowerSemicontinuous (fun f : Lp ℝ 2 m => cheegerEnergy m (f : X → ℝ)) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro f
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  apply cheegerEnergy_le_of_lip_approximations
  intro ε hε
  have H := frequently_lt_of_liminf_lt (h := ha)
  obtain ⟨u, hu, hd⟩ := (H.and_eventually
    (Metric.ball_mem_nhds f (half_pos hε))).exists
  obtain ⟨g, hg, hm, hgu, hge⟩ := cheegerEnergy_lt_approx hu (half_pos hε)
  refine ⟨g, hg, hm, ?_, hge.le⟩
  calc
    dist (hm.toLp g) f ≤ dist (hm.toLp g) u + dist u f := dist_triangle _ _ _
    _ < ε/2 + ε/2 := add_lt_add hgu hd
    _ = ε := add_halves ε

end WeakHessian

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

end
end InlinedFile0

end OAI
