import Mathlib
import OAI.Geometry.PrescribedRicci.CalabiMetricC1
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Uniform Coefficient Oscillation. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
lemma matrix_trace_norm_le (B : Matrix n n ℂ) : ‖B.trace‖ ≤ (Fintype.card n:ℝ)*‖B‖ := by
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun i _ => norm_entry_le_entrywise_sup_norm B (i:=i) (j:=i))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

lemma inverse_difference_bound (H K : Matrix n n ℂ) (hH : H.PosDef) (hK : K.PosDef)
    {M : ℝ} (hM : 0 ≤ M) (hI : ‖H⁻¹‖ ≤ M) (hJ : ‖K⁻¹‖ ≤ M) :
    ‖H⁻¹-K⁻¹‖ ≤ (Fintype.card n:ℝ)^2*M^2*‖H-K‖ := by
  have hHU : IsUnit H := (Matrix.isUnit_iff_isUnit_det H).mpr (isUnit_iff_ne_zero.mpr hH.det_pos.ne')
  have hKU : IsUnit K := (Matrix.isUnit_iff_isUnit_det K).mpr (isUnit_iff_ne_zero.mpr hK.det_pos.ne')
  rw [Matrix.inv_sub_inv ⟨fun _ => hKU,fun _ => hHU⟩]
  have h1 := matrix_norm_mul_le (H⁻¹*(K-H)) K⁻¹
  have h2 := matrix_norm_mul_le H⁻¹ (K-H)
  calc
    _ ≤ (Fintype.card n:ℝ)*((Fintype.card n:ℝ)*M*‖K-H‖)*M :=
      h1.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hI (Nat.cast_nonneg _)) (norm_nonneg _))) (Nat.cast_nonneg _))
        hJ (norm_nonneg _) (by positivity))
    _ = _ := by rw [norm_sub_rev]; ring
end MongeAmpere

namespace EllipticKernel
open MongeAmpere
variable {n : ℕ}

lemma traceBilin_difference_bound (H K : Matrix (Fin n) (Fin n) ℂ) (B : Bilin (EC n)) :
    |traceBilin H B-traceBilin K B| ≤ (n:ℝ)^2*‖H⁻¹-K⁻¹‖*
      ‖PotentialKaehler.hermitianPartMatrix (pullBilin B)‖ := by
  rw [traceBilin_apply,traceBilin_apply,← Complex.sub_re,← Matrix.trace_sub,← Matrix.sub_mul]
  apply (Complex.abs_re_le_norm _).trans
  apply (matrix_trace_norm_le _).trans
  apply (mul_le_mul_of_nonneg_left (matrix_norm_mul_le _ _) (Nat.cast_nonneg _)).trans_eq
  simp only [Fintype.card_fin]; ring
end EllipticKernel

namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] {A : ComplexAtlas d X}

theorem volumePath_metric_lipschitz_on_compact (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) (q : Fin A.count)
    {K : Set (Coordinates d)} (hK : IsCompact K) (hKc : Convex ℝ K) (hKt : K ⊆ (A.chart q).target) :
    ∃ P : ℝ, 0 < P ∧ ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ),
      g.integral φ.value = 0 → ∀ (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
      (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
      ∀ x ∈ K, ∀ y ∈ K,
      ‖(g.deform φ hp).matrix q y-(g.deform φ hp).matrix q x‖ ≤ P*‖y-x‖ ∧
      ‖((g.deform φ hp).matrix q y)⁻¹-((g.deform φ hp).matrix q x)⁻¹‖ ≤ P*‖y-x‖ := by
  obtain ⟨M,hM,hmetric⟩ := g.volumePath_metric_bounds_on_compact line hd q hK hKt
  obtain ⟨P,hP,hder⟩ := g.volumePath_metric_C1_on_compact line hd q hK hKt
  refine ⟨P+(d:ℝ)^2*M^2*P,by positivity,?_⟩
  intro φ hp hm t b ht heq x hx y hy
  let H := (g.deform φ hp).matrix q
  have hdiff : ‖H y-H x‖ ≤ P*‖y-x‖ := by
    apply matrix_norm_le_of_entries (by positivity)
    intro i j
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (s:=K) _ _ hKc hx hy
    · intro z hz
      exact differentiableAt_pi.mp (differentiableAt_pi.mp
        ((((g.deform φ hp).smooth q).contDiffAt ((A.chart q).open_target.mem_nhds (hKt hz))).differentiableAt
          (by simp)) i) j
    · intro z hz
      exact hder φ hp hm t b ht heq z hz i j
  have hi := inverse_difference_bound (H y) (H x)
    ((g.deform φ hp).positive q y (hKt hy)) ((g.deform φ hp).positive q x (hKt hx)) hM.le
    (hmetric φ hp hm t b ht heq y hy).2 (hmetric φ hp hm t b ht heq x hx).2
  simp only [Fintype.card_fin] at hi
  have hi' := hi.trans (mul_le_mul_of_nonneg_left hdiff (by positivity))
  constructor
  · exact hdiff.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (norm_nonneg _))
  · change ‖(H y)⁻¹-(H x)⁻¹‖ ≤ _
    nlinarith only [hi',mul_nonneg hP.le (norm_nonneg (y-x))]
end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
