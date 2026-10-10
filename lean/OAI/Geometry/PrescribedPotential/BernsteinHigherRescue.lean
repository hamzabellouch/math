import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiCutoffAlgebra
import OAI.Geometry.PrescribedPotential.RealFrameScalar

namespace OAI

/-! Bernstein Higher Rescue. -/

section

 
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

lemma frameLaplace_const_mul {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) {x : E} (hx : x ∈ U) (v : ι → E) (c : ℝ) :
    frameLaplace v (fun y => c*f y) x = c*frameLaplace v f x := by
  rw [frameLaplace_mul hU contDiffOn_const hf hx,frameLaplace_const,frameGradient_const]
  simp

lemma linear_cutoff_uniform {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {S T η : E → ℝ} (hS : ContDiffOn ℝ ∞ S U) (hT : ContDiffOn ℝ ∞ T U)
    (hη : ContDiffOn ℝ ∞ η U) {C R δ : ℝ} (hC : 0 ≤ C) (_hR : 0 ≤ R) (hδ : 0 < δ)
    (hvalues : ∀ x ∈ K, 0 ≤ S x ∧ S x ≤ R ∧ 0 ≤ T x ∧ 0 ≤ η x ∧ η x ≤ 1)
    (hinterior : ∀ x ∈ K, η x ≠ 0 → x ∈ interior K)
    (v : E → ι → E) (Q : E → ℝ)
    (hineq : ∀ x ∈ K, η x ≠ 0 →
      0 ≤ Q x ∧ δ*T x-C ≤ frameLaplace (v x) S x ∧
      Q x-C*(1+T x) ≤ frameLaplace (v x) T x ∧
      -C ≤ frameLaplace (v x) η x ∧
      ‖frameGradient (v x) η x‖^2 ≤ C*η x ∧
      ‖frameGradient (v x) T x‖^2 ≤ 4*T x*Q x) :
    ∀ z ∈ K, η z = 1 → T z ≤ 2*C*(1+(12*C+1)/δ)+((12*C+1)/δ)*R := by
  let A := (12*C+1)/δ
  have hA : 0 ≤ A := div_nonneg (by positivity) hδ.le
  let W : E → ℝ := fun x => η x*T x+A*S x
  have hW : ContDiffOn ℝ ∞ W U := (hη.mul hT).add (contDiffOn_const.mul hS)
  intro z hz hηz
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn ⟨z,hz⟩ (hW.continuousOn.mono hKU)
  obtain ⟨hSx,hSRx,hTx,hηx,hη1x⟩ := hvalues x hx
  have hL : T z ≤ W x := by
    have h := hmax hz
    change η z*T z+A*S z ≤ W x at h
    rw [hηz,one_mul] at h
    exact (le_add_of_nonneg_right (mul_nonneg hA (hvalues z hz).1)).trans h
  have hB : W x ≤ 2*C*(1+A)+A*R := by
    by_cases hn : η x=0
    · dsimp only [W]
      rw [hn,zero_mul,zero_add]
      exact (mul_le_mul_of_nonneg_left hSRx hA).trans (le_add_of_nonneg_left (by positivity))
    have hm : IsLocalMax W x := by
      filter_upwards [mem_interior_iff_mem_nhds.mp (hinterior x hx hn)] with y hy
      exact hmax hy
    have hmaxL := frameLaplace_nonpos_of_localMax (hW.contDiffAt (hU.mem_nhds (hKU hx))) hm (v x)
    change frameLaplace (v x) (fun y => η y*T y+A*S y) x ≤ 0 at hmaxL
    rw [frameLaplace_add hU (hη.mul hT) (contDiffOn_const.mul hS) (hKU hx),
      frameLaplace_mul hU hη hT (hKU hx),frameLaplace_const_mul hU hS (hKU hx)] at hmaxL
    obtain ⟨hQ,hLS,hLT,hLη,hGη,hGT⟩ := hineq x hx hn
    have hcauchy : (inner ℝ (frameGradient (v x) η x) (frameGradient (v x) T x))^2 ≤
        ‖frameGradient (v x) η x‖^2*‖frameGradient (v x) T x‖^2 := by
      simpa only [sq_abs,mul_pow] using
        (sq_le_sq₀ (abs_nonneg (inner ℝ (frameGradient (v x) η x) (frameGradient (v x) T x)))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (abs_real_inner_le_norm (frameGradient (v x) η x) (frameGradient (v x) T x))
    have hcross : (2*inner ℝ (frameGradient (v x) η x) (frameGradient (v x) T x))^2 ≤
        8*(2*C)*η x*T x*Q x := by
      have h := mul_le_mul hGη hGT (sq_nonneg _) (mul_nonneg hC hηx)
      nlinarith only [hcauchy,h]
    have hh : T x ≤ 2*C*(1+A) := by
      have hls : Q x-(2*C)*(1+T x) ≤ frameLaplace (v x) T x := by
        have : 0 ≤ C*(1+T x) := by positivity
        linarith only [hLT,this]
      have hlt : δ*T x-2*C ≤ frameLaplace (v x) S x := by linarith only [hLS,hC]
      have hle : -(2*C) ≤ frameLaplace (v x) η x := by linarith only [hLη,hC]
      have ha : (6*(2*C)+1)/δ = A := by dsimp [A]; congr 1; ring
      simpa only [ha] using CalabiEstimate.cutoff_max_bound hTx hQ hηx hη1x
        (show 0 ≤ 2*C by positivity) hδ hls hlt hle hcross (by simpa only [ha] using hmaxL)
    dsimp only [W]
    exact add_le_add ((mul_le_mul_of_nonneg_right hη1x hTx).trans (by simpa using hh))
      (mul_le_mul_of_nonneg_left hSRx hA)
  exact hL.trans hB
end HigherJet

end
end

end OAI
