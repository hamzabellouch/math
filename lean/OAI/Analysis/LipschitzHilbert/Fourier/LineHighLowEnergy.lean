import OAI.Analysis.LipschitzHilbert.Fourier.LineLowHighSpectrum
import OAI.Analysis.LipschitzHilbert.Fourier.LineKernelCancellation

namespace OAI

/-! Cancellation of the high coefficient and Bernstein for the low input
give the actual high/low commutator its geometric scale factor. -/
noncomputable section
open MeasureTheory
open scoped FourierTransform
namespace LipschitzHilbert.PacketRepresentation

theorem lineSchwartzProduct_energy (b h : SchwartzMap ℝ ℂ) (B : ℝ)
    (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzProduct b h x‖^2)≤B^2*(∫ x, ‖h x‖^2) := by
  rw [←integral_const_mul]
  apply integral_mono
    ((lineSchwartzProduct b h).memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0))
    ((h.memLp 2 volume |>.integrable_norm_pow (by decide : 2≠0)).const_mul _)
  intro x
  simp only [lineSchwartzProduct_apply,norm_mul,mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hb x) 2) (sq_nonneg _)

theorem lineSchwartzCommutator_bounded_energy (m b h : SchwartzMap ℝ ℂ) (A B : ℝ)
    (hm : ∀ eta, ‖m eta‖≤A) (hb : ∀ x, ‖b x‖≤B) :
    (∫ x, ‖lineSchwartzCommutator m b h x‖^2)≤4*A^2*B^2*(∫ x, ‖h x‖^2) := by
  let U := lineSchwartzProduct b (lineSchwartzProjection m 1 (by norm_num) h)
  let V := lineSchwartzProjection m 1 (by norm_num) (lineSchwartzProduct b h)
  have hi (f : SchwartzMap ℝ ℂ) : Integrable (fun x => ‖f x‖^2) :=
    (f.memLp 2 volume).integrable_norm_pow (by decide : 2≠0)
  have hp (x : ℝ) : ‖U x-V x‖^2≤2*‖U x‖^2+2*‖V x‖^2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (U x) (V x)) 2
    nlinarith [sq_nonneg (‖U x‖-‖V x‖)]
  have hu := (lineSchwartzProduct_energy b _ B hb).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProjection_energy m 1 (by norm_num) A hm h) (sq_nonneg B))
  have hv := (lineSchwartzProjection_energy m 1 (by norm_num) A hm _).trans
    (mul_le_mul_of_nonneg_left (lineSchwartzProduct_energy b h B hb) (sq_nonneg A))
  calc
    _ ≤ ∫ x, 2*‖U x‖^2+2*‖V x‖^2 :=
      integral_mono (hi _) (((hi U).const_mul 2).add ((hi V).const_mul 2)) hp
    _ = 2*(∫ x, ‖U x‖^2)+2*(∫ x, ‖V x‖^2) := by
      rw [integral_add ((hi U).const_mul 2) ((hi V).const_mul 2),integral_const_mul,integral_const_mul]
    _ ≤ _ := by dsimp [U,V] at *; nlinarith [hu,hv]

theorem highLowCommutator_energy (m b h : SchwartzMap ℝ ℂ) (W V A L : ℝ)
    (hW : 0<W) (hV : 0<V) (hm : ∀ eta, ‖m eta‖≤A)
    (hLip : ∀ x y, ‖b x-b y‖≤L*|x-y|) :
    let B := lineSchwartzProjection dyadicDifference W hW.ne' b
    let H := lineSchwartzProjection dyadicDifference V hV.ne' h
    (∫ x, ‖lineSchwartzCommutator m B (schwartzDerivative 1 H) x‖^2)≤
      (A*L*(∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖)*
        (26*Real.pi/3)*(W/V))^2*(∫ x, ‖H x‖^2) := by
  intro B H
  let M := ∫ t, |t| *‖(𝓕⁻ dyadicDifference : SchwartzMap ℝ ℂ) t‖
  have hb (x : ℝ) : ‖B x‖≤L*W*M := by
    dsimp [B]
    rw [lineSchwartzProjection_eq_convolution]
    exact dyadicProjection_lipschitz_bound W hW b b.continuous.measurable
      (SchwartzMap.seminorm ℝ 0 0 b) (fun z => b.norm_le_seminorm ℝ z) L hLip x
  have hc := lineSchwartzCommutator_bounded_energy m B (schwartzDerivative 1 H) A (L*W*M) hm hb
  have hd := line_bernstein_energy H ((13/6)/V)
    (fun eta heta => (dyadicProjection_frequency V hV h eta heta).2)
  calc
    _ ≤ 4*A^2*(L*W*M)^2*(∫ x, ‖schwartzDerivative 1 H x‖^2) := hc
    _ ≤ 4*A^2*(L*W*M)^2*((2*Real.pi*((13/6)/V))^2*(∫ x, ‖H x‖^2)) :=
      mul_le_mul_of_nonneg_left hd (by positivity)
    _ = _ := by dsimp [M]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
