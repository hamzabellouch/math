import Mathlib
import OAI.Geometry.PrescribedRicci.ArrayWirtinger
import OAI.Geometry.PrescribedRicci.CalabiLower
import OAI.Geometry.PrescribedRicci.CalabiTensorBounds
import OAI.Geometry.PrescribedRicci.CompactPathBounds
import OAI.Geometry.PrescribedRicci.UniformCalabi
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Calabi Metric C1. -/

section

 

noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma real_direction_of_hol_bar (f : Coordinates d → Mat) (z : Coordinates d) (a : Fin d) :
    fderiv ℝ f z (coordinateVector a) = holDerivative f z a+barDerivative f z a := by
  ext i j
  simp only [holDerivative,barDerivative,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring

lemma imaginary_direction_of_hol_bar (f : Coordinates d → Mat) (z : Coordinates d) (a : Fin d) :
    fderiv ℝ f z (Complex.I • coordinateVector a) = Complex.I • (holDerivative f z a-barDerivative f z a) := by
  ext i j
  simp only [holDerivative,barDerivative,Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul]
  ring_nf
  simp

lemma norm_real_linear_map_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : Coordinates d →L[ℝ] F) {B : ℝ} (hB : 0 ≤ B)
    (hre : ∀ a, ‖L (coordinateVector a)‖ ≤ B)
    (him : ∀ a, ‖L (Complex.I • coordinateVector a)‖ ≤ B) :
    ‖L‖ ≤ (2*(d:ℝ))*B := by
  apply L.opNorm_le_bound (by positivity)
  intro v
  have he : v = ∑ j, ((v j).re • coordinateVector j + (v j).im • (Complex.I • coordinateVector j)) := by
    ext k
    simp only [coordinateVector,Finset.sum_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      Complex.real_smul,Pi.single_apply]
    simp [mul_ite,Finset.sum_add_distrib]
  calc
    ‖L v‖ = ‖∑ j, ((v j).re • L (coordinateVector j)+(v j).im • L (Complex.I • coordinateVector j))‖ := by
      conv_lhs => rw [he,map_sum]
      simp only [map_add,map_smul]
    _ ≤ ∑ j : Fin d, (‖(v j).re‖*‖L (coordinateVector j)‖+‖(v j).im‖*‖L (Complex.I • coordinateVector j)‖) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      simpa only [norm_smul] using norm_add_le ((v j).re • L (coordinateVector j)) ((v j).im • L (Complex.I • coordinateVector j))
    _ ≤ ∑ _j : Fin d, (‖v‖*B+‖v‖*B) := by
      apply Finset.sum_le_sum
      intro j _
      exact add_le_add
        (mul_le_mul ((Complex.abs_re_le_norm _).trans (norm_le_pi_norm v j)) (hre j) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul ((Complex.abs_im_le_norm _).trans (norm_le_pi_norm v j)) (him j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma metric_fderiv_bound (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) {M P : ℝ} (hM : 0 ≤ M) (hP : 0 ≤ P)
    (hH : ‖g.matrix q z‖ ≤ M) (hI : ‖(g.matrix q z)⁻¹‖ ≤ M)
    (hCal : g.calabiNorm q z ≤ P) (i j : Fin d) :
    ‖fderiv ℝ (fun y => g.matrix q y i j) z‖ ≤ 4*(d:ℝ)^2*M*(1+M^3*P) := by
  let B := 1+M^3*P
  have hT2 := (g.calabiTensor_sq_bound q hz hM hH hI).trans
    (mul_le_mul_of_nonneg_left hCal (pow_nonneg hM 3))
  have hT : ‖g.calabiTensor q z‖ ≤ B := by
    dsimp [B]
    nlinarith only [hT2,sq_nonneg (‖g.calabiTensor q z‖-1)]
  have hg : DifferentiableAt ℝ (g.matrix q) z :=
    ((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).differentiableAt (by simp)
  have hhol (a : Fin d) : ‖holDerivative (g.matrix q) z a‖ ≤ (d:ℝ)*M*B := by
    rw [← holArray_eq_holDerivative hg,g.metric_hol_connection q hz]
    apply (matrix_norm_mul_le _ _).trans
    simp only [Fintype.card_fin]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg d))
      ((g.chernConnection_norm_le_calabiTensor q z a).trans hT) (norm_nonneg _) (by positivity)
  have hbar (a : Fin d) : ‖barDerivative (g.matrix q) z a‖ ≤ (d:ℝ)*M*B := by
    rw [← barArray_eq_barDerivative hg,barArray_eq_adjoint_hol,
      Matrix.norm_conjTranspose,holArray_eq_holDerivative hg]
    · exact hhol a
    · filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
      exact (g.positive q y hy).isHermitian
  have hB : 0 ≤ 2*(d:ℝ)*M*B := by dsimp [B]; positivity
  have hre (a : Fin d) : ‖fderiv ℝ (fun y => g.matrix q y i j) z (coordinateVector a)‖ ≤ 2*(d:ℝ)*M*B := by
    rw [fderiv_entry hg,real_direction_of_hol_bar]
    exact (norm_entry_le_entrywise_sup_norm _).trans ((norm_add_le _ _).trans (by linarith only [hhol a,hbar a]))
  have him (a : Fin d) : ‖fderiv ℝ (fun y => g.matrix q y i j) z (Complex.I • coordinateVector a)‖ ≤ 2*(d:ℝ)*M*B := by
    rw [fderiv_entry hg,imaginary_direction_of_hol_bar]
    apply (norm_entry_le_entrywise_sup_norm _).trans
    rw [norm_smul,Complex.norm_I,one_mul]
    exact (norm_sub_le _ _).trans (by linarith only [hhol a,hbar a])
  have hh := norm_real_linear_map_bound (fderiv ℝ (fun y => g.matrix q y i j) z) hB hre him
  convert hh using 1
  dsimp only [B]
  ring

variable [T2Space X] [CompactSpace X] [ConnectedSpace X]

theorem volumePath_metric_C1_on_compact (g : KaehlerMetric A)
    (line : SemipositiveAnticanonicalMetric A) (hd : 2 ≤ d) (q : Fin A.count)
    {K : Set (Coordinates d)} (hK : IsCompact K) (hKt : K ⊆ (A.chart q).target) :
    ∃ P : ℝ, 0 < P ∧ ∀ (φ : SmoothRealFunction A) (hp : g.PositivePotential φ),
      g.integral φ.value = 0 → ∀ (t b : ℝ), t ∈ Icc (0:ℝ) 1 →
      (∀ x, (g.logRatio (g.deform φ hp)).value x = t*(prescribedForcing g line).value x+b) →
      ∀ z ∈ K, ∀ i j : Fin d, ‖fderiv ℝ (fun y => (g.deform φ hp).matrix q y i j) z‖ ≤ P := by
  obtain ⟨M,hM,hmetric⟩ := g.volumePath_metric_bounds_on_compact line hd q hK hKt
  obtain ⟨P,hP,hcal⟩ := g.volumePath_calabi_bound_on_compact line hd q hK hKt
  refine ⟨1+4*(d:ℝ)^2*M*(1+M^3*P),by positivity,?_⟩
  intro φ hp hm t b ht heq z hz i j
  have hb := hmetric φ hp hm t b ht heq z hz
  have hh := metric_fderiv_bound (g.deform φ hp) q (hKt hz) hM.le hP.le hb.1 hb.2
    (hcal φ hp hm t b ht heq z hz) i j
  linarith only [hh]
end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
