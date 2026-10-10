import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCoordinateCoercivity
import OAI.Geometry.PrescribedPotential.CircleRadialCalculus
import OAI.Geometry.PrescribedPotential.HolomorphicDirection
import OAI.Geometry.PrescribedPotential.TracePositivity

namespace OAI

/-! Calabi Coordinate Bound. -/

section

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus
variable {n : ℕ}

lemma matrix_mul_elementwise_bound (M N : Matrix (Fin n) (Fin n) ℂ) :
    ‖M*N‖ ≤ n*‖M‖*‖N‖ := by
  apply (Matrix.norm_le_iff (by positivity)).mpr
  intro i j
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖M i k*N k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ‖M‖*‖N‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (Matrix.norm_entry_le_entrywise_sup_norm M)
        (Matrix.norm_entry_le_entrywise_sup_norm N) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

lemma hol_matrix_stencil_bound (v : V n) (T : ConnectionTensor n) :
    ‖∑ i, v i • T i‖ ≤ n*‖v‖*‖T‖ := by
  calc
    _ ≤ ∑ i, ‖v i • T i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖v‖*‖T‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul]
      exact mul_le_mul (norm_le_pi_norm v i) (norm_le_pi_norm T i) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [mul_assoc]

namespace LocalKaehlerField
variable (K : LocalKaehlerField n)
lemma holDerivative_connection {z : V n} (hz : z ∈ K.domain) (i : Fin n) :
    mderiv (-Complex.I) (e i) K.matrix z = K.matrix z*K.connection i z := by
  rw [connection,← mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos)),one_mul]

lemma fderiv_eq_hol_add_star {z : V n} (hz : z ∈ K.domain) (v : V n) :
    fderiv ℝ K.matrix z v = mderiv (-Complex.I) v K.matrix z +
      (mderiv (-Complex.I) v K.matrix z)ᴴ := by
  rw [← mderiv_bar_eq_conjTranspose K.isOpen K.smooth
    (fun y hy => (K.positive y hy).isHermitian) hz v]
  have hd := (K.smooth.contDiffAt (K.isOpen.mem_nhds hz)).differentiableAt (by simp)
  ext i j
  have he : fderiv ℝ K.matrix z v i j = fderiv ℝ (fun y => K.matrix y i j) z v := by
    change fderiv ℝ (fun y a b => K.matrix y a b) z v i j = _
    rw [fderiv_pi (fun a => differentiableAt_pi.mp hd a)]
    simp only [ContinuousLinearMap.pi_apply]
    rw [fderiv_pi (fun b => differentiableAt_pi.mp (differentiableAt_pi.mp hd i) b)]
    rfl
  rw [he]
  change _ = wderiv (-Complex.I) v (fun y => K.matrix y i j) z +
    wderiv Complex.I v (fun y => K.matrix y i j) z
  unfold wderiv
  ring

lemma matrix_fderiv_bound {z : V n} (hz : z ∈ K.domain) :
    ‖fderiv ℝ (fun y i j => K.matrix y i j) z‖ ≤ 2*n^2*‖K.matrix z‖*‖fun i => K.connection i z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have he : fderiv ℝ (fun y i j => K.matrix y i j) z v =
      (fun i j => (mderiv (-Complex.I) v K.matrix z +
        (mderiv (-Complex.I) v K.matrix z)ᴴ) i j) := K.fderiv_eq_hol_add_star hz v
  rw [he]
  change ‖mderiv (-Complex.I) v K.matrix z + (mderiv (-Complex.I) v K.matrix z)ᴴ‖ ≤ _
  have ht : mderiv (-Complex.I) v K.matrix z =
      K.matrix z*(∑ i, v i • K.connection i z) := by
    rw [mderiv_hol_coordinates,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [K.holDerivative_connection hz,Matrix.mul_smul]
  have hb := (matrix_mul_elementwise_bound (K.matrix z) (∑ i, v i • K.connection i z)).trans
    (mul_le_mul_of_nonneg_left (hol_matrix_stencil_bound v (fun i => K.connection i z)) (by positivity))
  rw [← ht] at hb
  calc
    _ ≤ ‖mderiv (-Complex.I) v K.matrix z‖ + ‖(mderiv (-Complex.I) v K.matrix z)ᴴ‖ := norm_add_le _ _
    _ ≤ 2*(n*‖K.matrix z‖*(n*‖v‖*‖fun i => K.connection i z‖)) := by
      rw [Matrix.norm_conjTranspose]
      linarith
    _ = _ := by ring
end LocalKaehlerField

 

theorem calabi_coordinate_connection_uniform {X : Type*} [TopologicalSpace X]
    {L : Set X} (hL : IsCompact L) (G : X → Matrix (Fin n) (Fin n) ℂ)
    (hG : ContinuousOn G L) (hp : ∀ x ∈ L, (G x).PosDef)
    {R H C : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ L, ∀ (K : LocalKaehlerField n) z, z ∈ K.domain →
      ((R:ℂ) • K.matrix z-G x).PosSemidef → ((H:ℂ) • G x-K.matrix z).PosSemidef →
      K.calabiNorm z ≤ C → ‖K.matrix z‖ ≤ B ∧ ‖fun i => K.connection i z‖ ≤ B := by
  obtain ⟨b,hb,hframe⟩ := compact_normalizing_frames hL G hG hp hR hH
  obtain ⟨δ,hδ,hcoercive⟩ := boundedFrame_tensor_coercivity (n := n) b
  let M := (n:ℝ)*b^2
  let T := C/δ+1
  let B := max M T
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨B,hM.trans (le_max_left _ _),?_⟩
  intro x hx K z hz hlow hupp hcal
  obtain ⟨F,hF,hN⟩ := whitening (K.matrix z) (K.positive z hz)
  have hFI : F*F⁻¹=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hF)
  have hIF : F⁻¹*F=1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hF)
  obtain ⟨hf,hfi⟩ := hframe x hx (K.matrix z) F F⁻¹ hlow hupp hFI hN
  have hpair : (F,F⁻¹) ∈ boundedFramePairs b := ⟨hf,hfi,hFI,hIF⟩
  have hcoer : ∀ U : ConnectionTensor n, δ*‖U‖^2 ≤ tensorSquare (tensorTransport F F⁻¹ U) :=
    hcoercive (F,F⁻¹) hpair
  have hc : δ*‖fun i => K.connection i z‖^2 ≤ C :=
    (connection_norm_bound_of_frame (K := K) (z := z) (C := F) (D := F⁻¹)
      (δ := δ) hz hFI hIF hN hδ hcoer).trans hcal
  have hconn : ‖fun i => K.connection i z‖ ≤ T := by
    have hsq : ‖fun i => K.connection i z‖^2 ≤ C/δ :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hc)
    dsimp [T]
    nlinarith only [hsq, sq_nonneg (‖fun i => K.connection i z‖-1)]
  have hm : ‖K.matrix z‖ ≤ M := by
    rw [unnormalize_matrix hFI hN]
    have hh := matrix_mul_elementwise_bound (F⁻¹)ᴴ F⁻¹
    rw [Matrix.norm_conjTranspose] at hh
    have hs := (sq_le_sq₀ (norm_nonneg _) hb).mpr hfi
    dsimp [M]
    nlinarith only [hh,hs,Nat.cast_nonneg (α := ℝ) n]
  exact ⟨hm.trans (le_max_left _ _),hconn.trans (le_max_right _ _)⟩

theorem calabi_coordinate_C1_uniform {X : Type*} [TopologicalSpace X]
    {L : Set X} (hL : IsCompact L) (G : X → Matrix (Fin n) (Fin n) ℂ)
    (hG : ContinuousOn G L) (hp : ∀ x ∈ L, (G x).PosDef)
    {R H C : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ L, ∀ (K : LocalKaehlerField n) z, z ∈ K.domain →
      ((R:ℂ) • K.matrix z-G x).PosSemidef → ((H:ℂ) • G x-K.matrix z).PosSemidef →
      K.calabiNorm z ≤ C → ‖K.matrix z‖ ≤ B ∧
        ‖fderiv ℝ (fun y i j => K.matrix y i j) z‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := calabi_coordinate_connection_uniform hL G hG hp hR hH hC
  refine ⟨max B (2*n^2*B*B),hB.trans (le_max_left _ _),?_⟩
  intro x hx K z hz hl hu hs
  obtain ⟨hm,hc⟩ := hbound x hx K z hz hl hu hs
  refine ⟨hm.trans (le_max_left _ _),?_⟩
  exact (K.matrix_fderiv_bound hz).trans ((mul_le_mul
    (mul_le_mul_of_nonneg_left hm (by positivity)) hc (norm_nonneg _) (by positivity)).trans
      (le_max_right _ _))
end KaehlerCalculus

end
end

end OAI
