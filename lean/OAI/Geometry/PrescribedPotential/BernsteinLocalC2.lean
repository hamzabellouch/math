import Mathlib
import OAI.Geometry.PrescribedPotential.BernsteinProductMaximum
import OAI.Geometry.PrescribedPotential.BernsteinQuarticAlgebra

namespace OAI

/-! Bernstein Local C2. -/

section

 

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace HigherJet
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

def quarticConstant (C B : ℝ) : ℝ := B*C+C+3*B*C+4*C^2+1

lemma quartic_cutoff_uniform {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {S T η : E → ℝ} (hS : ContDiffOn ℝ ∞ S U) (hT : ContDiffOn ℝ ∞ T U)
    (hη : ContDiffOn ℝ ∞ η U) {C R : ℝ} (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hvalues : ∀ x ∈ K, 0 ≤ S x ∧ S x ≤ R ∧ 0 ≤ T x ∧ 0 ≤ η x ∧ η x ≤ 1)
    (hinterior : ∀ x ∈ K, η x ≠ 0 → x ∈ interior K)
    (v : E → ι → E)
    (hineq : ∀ x ∈ K, η x ≠ 0 →
      T x-C ≤ frameLaplace (v x) S x ∧
      -C*(1+T x*Real.sqrt (T x)) ≤ frameLaplace (v x) T x ∧
      -C ≤ frameLaplace (v x) η x ∧
      ‖frameGradient (v x) η x‖^2 ≤ C*η x ∧
      ‖frameGradient (v x) S x‖^2 ≤ C*T x) :
    ∀ z ∈ K, η z = 1 →
      T z ≤ (8*C+1+R)*(2*quarticConstant C (8*C+1+R)+2)^2 := by
  let A := 8*C+1
  let B := A+R
  let D := quarticConstant C B
  have hA : 1 ≤ A := by dsimp [A]; linarith
  have hB : 0 ≤ B := by dsimp [B]; linarith
  have hD : 1 ≤ D := by
    have h : 0 ≤ B*C+C+3*B*C+4*C^2 := by positivity
    dsimp [D,quarticConstant]; linarith
  let W : E → ℝ := fun x => η x*(A+S x)*T x
  have hW : ContDiffOn ℝ ∞ W U := (hη.mul (contDiffOn_const.add hS)).mul hT
  intro z hz hηz
  obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn ⟨z,hz⟩ (hW.continuousOn.mono hKU)
  obtain ⟨hSx,hSRx,hTx,hηx,hη1x⟩ := hvalues x hx
  obtain ⟨hSz,_,hTz,_,_⟩ := hvalues z hz
  have hL : A*T z ≤ W x := by
    have hh := hmax hz
    change η z*(A+S z)*T z ≤ W x at hh
    rw [hηz,one_mul] at hh
    nlinarith only [hh,mul_nonneg hSz hTz]
  have hAB : A+S x ≤ B := by dsimp [B]; linarith
  have hax : 0 < A+S x := by linarith
  by_cases hn : η x=0
  · have he : W x=0 := by dsimp [W]; rw [hn]; ring
    rw [he] at hL
    have : T z ≤ 0 := by nlinarith only [hL,hA,hTz]
    exact this.trans (mul_nonneg (by dsimp [A,B] at hB; exact hB) (sq_nonneg _))
  have hηpos : 0 < η x := lt_of_le_of_ne hηx (Ne.symm hn)
  have hm : IsLocalMax W x := by
    filter_upwards [mem_interior_iff_mem_nhds.mp (hinterior x hx hn)] with y hy
    exact hmax hy
  have hnum := quartic_test_at_max hU hη hS hT (hKU hx) (v x) A hn (ne_of_gt hax) hm
  obtain ⟨hLS,hLT,hLη,hGη,hGS⟩ := hineq x hx hn
  have hcross : (inner ℝ (frameGradient (v x) η x) (frameGradient (v x) S x))^2 ≤
      ‖frameGradient (v x) η x‖^2*‖frameGradient (v x) S x‖^2 := by
    simpa only [sq_abs,mul_pow] using
      (sq_le_sq₀ (abs_nonneg (inner ℝ (frameGradient (v x) η x) (frameGradient (v x) S x)))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
        (abs_real_inner_le_norm (frameGradient (v x) η x) (frameGradient (v x) S x))
  have hb := BernsteinEstimate.quartic_max_reduction hηpos hη1x hTx
    (Real.sqrt_nonneg _) (Real.sq_sqrt hTx) hC (by dsimp only [A]; linarith only [hSx]) hAB
    hLS hLT hLη (sq_nonneg _) (sq_nonneg _) hGη hGS hcross hnum
  have hbound : η x*T x ≤ (2*D+2)^2 :=
    BernsteinEstimate.weighted_quartic_bound hηx hη1x hTx hD hb
  have hWB : W x ≤ B*(2*D+2)^2 := by
    calc
      _ = (A+S x)*(η x*T x) := by dsimp [W]; ring
      _ ≤ B*(2*D+2)^2 := mul_le_mul hAB hbound (mul_nonneg hηx hTx) hB
  change T z ≤ B*(2*D+2)^2
  have hAT : T z ≤ A*T z := le_mul_of_one_le_left hTz hA
  exact hAT.trans (hL.trans hWB)
end HigherJet

end
end

end OAI
