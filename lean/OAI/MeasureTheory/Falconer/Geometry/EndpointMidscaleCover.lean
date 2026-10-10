import OAI.MeasureTheory.Falconer.Recursion.RetainedProfileBounds
import OAI.MeasureTheory.Falconer.Incidence.UpperBlockBracket
import OAI.MeasureTheory.Falconer.Geometry.HalfSlopeGrid

namespace OAI

/-! The square-root cover required by the regular gain follows from an
upper profile chord even when its midpoint lies between selected blocks. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_retained_midscale_cover {N : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    {n : ℕ} (hn : 3 ≤ n) (hlen : blockDepth N B j-blockDepth N B i = 2*n)
    {t A : ℝ} (ht : 0 ≤ t)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      (49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t := by
  have hab := blockDepth_antitone N B hji
  have hmid : blockDepth N B i+n+3 ≤ blockDepth N B j := by omega
  obtain ⟨k,hjk,hki,hlo,hup⟩ := blockDepth_upper_bracket hji
    (show blockDepth N B i ≤ blockDepth N B i+n+3 by omega) hmid
  have hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤
      1/(2:ℝ)^(n+3) := by
    rw [dyadic_relative_mesh _ _ (blockDepth_antitone N B hki)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc := blockClass_retained_endpoint_cover hL B f g K p q hsub Q hQ hi hp₀ hN
    hjk hki (by positivity : 0 < 1/(2:ℝ)^(n+3)) hscale (hprofile k hjk hki)
  have hdist : (blockDepth N B k:ℝ)-(blockDepth N B i:ℝ) ≤ (n:ℝ)+3+B := by
    have hc : blockDepth N B k ≤ blockDepth N B i+n+3+B := hup
    have hc' : (blockDepth N B k:ℝ) ≤ (blockDepth N B i:ℝ)+n+3+B := by exact_mod_cast hc
    linarith only [hc']
  calc
    _ ≤ 49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := hc
    _ ≤ 49*((2:ℝ)^i*(2:ℝ)^(t*((n:ℝ)+3+B)+A)) := by gcongr; norm_num
    _ = (49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t := by
      apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos (by positivity) t))).2
      rw [dyadic_inverse_power_eq]
      calc
        _ = 49*((2:ℝ)^i*((2:ℝ)^(t*((n:ℝ)+3+B)+A)*(2:ℝ)^(-t*(n:ℝ)))) := by ring
        _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 3; ring

end Falconer

end OAI
