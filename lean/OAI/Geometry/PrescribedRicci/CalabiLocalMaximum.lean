import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiCutoffDifferential
import OAI.Geometry.PrescribedRicci.CalabiGradient
import OAI.Geometry.PrescribedRicci.CalabiLower
import OAI.Geometry.PrescribedRicci.CalabiTraceBound

namespace OAI

/-! Calabi Local Maximum. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

lemma flatTrace_nonneg (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) : 0 ≤ g.flatTrace q z :=
  (Complex.nonneg_iff.mp (g.positive q z hz).posSemidef.trace_nonneg).1

lemma compact_cutoff_derivative_bound {L : Set (Coordinates d)} (hL : IsCompact L)
    (χ : Coordinates d → ℝ) (hχ : ContDiff ℝ ∞ χ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z ∈ L, |χ z| ≤ B ∧ ‖holRealDeriv χ z‖ ≤ B ∧
      ‖PotentialKaehler.potentialMatrix (fun y => χ y*χ y) z‖ ≤ B := by
  let size : Coordinates d → ℝ := fun z => |χ z|+‖holRealDeriv χ z‖+
    ‖PotentialKaehler.potentialMatrix (fun y => χ y*χ y) z‖
  have hs : Continuous size := by
    have hd : ContDiff ℝ ∞ (fun z => holRealDeriv χ z) := contDiff_iff_contDiffAt.mpr
      (fun z => contDiffAt_pi.mpr (fun a => contDiffAt_holRealDeriv hχ.contDiffAt a))
    have hdd : ContDiff ℝ ∞ (fun z => PotentialKaehler.potentialMatrix (fun y => χ y*χ y) z) :=
      contDiff_iff_contDiffAt.mpr (fun z => PotentialKaehler.potentialMatrix_smooth (hχ.mul hχ).contDiffAt)
    exact (hχ.continuous.abs.add hd.continuous.norm).add hdd.continuous.norm
  obtain ⟨b,hb⟩ := hL.bddAbove_image hs.continuousOn
  refine ⟨1+max 0 b,by positivity,?_⟩
  intro z hz
  have hh := (hb (mem_image_of_mem _ hz)).trans (le_max_right (0:ℝ) b)
  dsimp [size] at hh
  refine ⟨?_,?_,?_⟩ <;> linarith [abs_nonneg (χ z),norm_nonneg (holRealDeriv χ z),
    norm_nonneg (PotentialKaehler.potentialMatrix (fun y => χ y*χ y) z)]

 

theorem calabi_bound_on_compact (q : Fin A.count) {L : Set (Coordinates d)}
    (hL : IsCompact L) (hLt : L ⊆ (A.chart q).target)
    (χ : Coordinates d → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχL : tsupport χ ⊆ interior L) {M R : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) :
    ∃ P : ℝ, 0 < P ∧ ∀ g : KaehlerMetric A,
      (∀ z ∈ L, ‖g.matrix q z‖ ≤ M ∧ ‖(g.matrix q z)⁻¹‖ ≤ M ∧
        ‖g.curvatureRicci q z‖ ≤ R ∧ ∀ a, ‖holDerivative (g.curvatureRicci q) z a‖ ≤ R) →
      ∀ z ∈ L, χ z = 1 → g.calabiNorm q z ≤ P := by
  obtain ⟨C,hC,hCal⟩ := calabiNorm_lower_bound d M R hM hR
  obtain ⟨B,hB,hcut⟩ := compact_cutoff_derivative_bound hL χ hχ
  let K := 2*(Fintype.card (TensorIndex (Fin d)):ℝ)^4*M^13
  let δ := (1+(Fintype.card (TensorIndex (Fin d)):ℝ)^2*M^5)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let a := cutoffCoefficient d M B C K δ
  have ha : 0 < a := cutoffCoefficient_pos hM hB.le hC.le hK hδ
  let Q := B^2*C+a*((d:ℝ)*R)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨1+B^2*Q+a*((d:ℝ)*M),by positivity,?_⟩
  intro g hbounds z hz hzχ
  let f : Coordinates d → ℝ := fun y => χ y*χ y*g.calabiNorm q y+a*g.flatTrace q y
  have hfs (y : Coordinates d) (hy : y ∈ L) : ContDiffAt ℝ ∞ f y :=
    ((hχ.contDiffAt.mul hχ.contDiffAt).mul (g.calabiNorm_smooth q (hLt hy))).add
      (contDiffAt_const.mul (g.flatTrace_smooth q (hLt hy)))
  obtain ⟨x,hx,hmax⟩ := hL.exists_isMaxOn ⟨z,hz⟩ (fun y hy => (hfs y hy).continuousAt.continuousWithinAt)
  have hzle : g.calabiNorm q z ≤ f z := by
    change _ ≤ χ z*χ z*g.calabiNorm q z+a*g.flatTrace q z
    rw [hzχ]
    have ht := mul_nonneg ha.le (g.flatTrace_nonneg q (hLt hz))
    nlinarith
  have hmaxbound : f x ≤ B^2*Q+a*((d:ℝ)*M) := by
    have ht := g.flatTrace_bound q x (hbounds x hx).1
    by_cases h0 : χ x = 0
    · change χ x*χ x*g.calabiNorm q x+a*g.flatTrace q x ≤ _
      rw [h0]
      have hh := mul_le_mul_of_nonneg_left ht ha.le
      nlinarith [mul_nonneg (sq_nonneg B) hQ]
    · have hn : L ∈ nhds x := mem_interior_iff_mem_nhds.mp (hχL (subset_tsupport _ h0))
      have hlocal : IsLocalMax f x := Filter.eventually_of_mem hn (fun y hy => hmax hy)
      have hnonpos := EllipticKernel.trace_potentialMatrix_nonpos_at_localMax
        (hfs x hx) hlocal (g.matrix q x) (g.positive q x (hLt hx))
      have hb := hbounds x hx
      have hgrad : ‖holRealDeriv (g.calabiNorm q) x‖^2 ≤ K*g.calabiNorm q x*g.calabiEnergy q x :=
        norm_pi_sq_bound (by positivity [g.calabiNorm_nonneg q (hLt hx),g.calabiEnergy_nonneg q (hLt hx)])
          (fun j => g.calabiNorm_gradient_sq_bound q (hLt hx) hM hb.1 hb.2.1 j)
      have hlow := cutoff_test_lower_bound (g.matrix q x) (g.positive q x (hLt hx))
        hχ.contDiffAt (g.calabiNorm_smooth q (hLt hx)) (g.flatTrace_smooth q (hLt hx))
        hM hB.le hC.le hK hδ (g.calabiEnergy_nonneg q (hLt hx)) (g.calabiNorm_nonneg q (hLt hx))
        hb.2.1 (hcut x hx).1 (hcut x hx).2.1 (hcut x hx).2.2 hgrad
        (hCal g q x (hLt hx) hb.1 hb.2.1 hb.2.2.1 hb.2.2.2)
        (g.flatTrace_lower_bound q (hLt hx) hM hb.1 hb.2.1 hb.2.2.1)
      have hS : g.calabiNorm q x ≤ Q := by
        change g.calabiNorm q x-B^2*C-a*((d:ℝ)*R) ≤ localLap (g.matrix q x) f x at hlow
        change localLap (g.matrix q x) f x ≤ 0 at hnonpos
        dsimp [Q]
        linarith
      have hcx : χ x*χ x ≤ B^2 := by
        have hh := (sq_le_sq₀ (abs_nonneg (χ x)) hB.le).mpr (hcut x hx).1
        rw [sq_abs] at hh
        simpa only [pow_two] using hh
      have hh := mul_le_mul hcx hS (g.calabiNorm_nonneg q (hLt hx)) (sq_nonneg B)
      have hhT := mul_le_mul_of_nonneg_left ht ha.le
      change χ x*χ x*g.calabiNorm q x+a*g.flatTrace q x ≤ _
      linarith
  exact (hzle.trans (hmax hz)).trans (hmaxbound.trans (by linarith))

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
