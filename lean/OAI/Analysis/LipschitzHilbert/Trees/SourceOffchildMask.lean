import OAI.Analysis.LipschitzHilbert.Trees.SourceResidualPropagation
import OAI.Analysis.LipschitzHilbert.Trees.SourceMaskTail

namespace OAI

/-! A loss below one contains only tops outside their weight dilation.
Their actual sinc masks are exponentially small, so the off-child error
is paid by the exact lost mass. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert

 theorem SlopeBox.one_le_weight_of_radius_le (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ × ℝ) (hr : T.radius z ≤ K) :
    1 ≤ T.weight K D z := by
  have hb : 0 < 1+T.radius z/K := by
    have := T.radius_nonnegative z
    positivity
  have hratio : 1 ≤ 2/(1+T.radius z/K) := by
    apply (le_div_iff₀ hb).mpr
    have := (div_le_one hK).mpr hr
    linarith
  have heq : T.weight K D z = (2/(1+T.radius z/K))^D := by
    rw [Real.div_rpow (by norm_num : (0:ℝ) ≤ 2) hb.le,div_eq_mul_inv,
      ← Real.rpow_neg hb.le]
    rfl
  rw [heq]
  exact Real.one_le_rpow hratio hD

 theorem SlopeBox.radius_large_of_weight_lt_one (T : SlopeBox) {K D : ℝ}
    (hK : 0 < K) (hD : 0 ≤ D) (z : ℝ × ℝ) (hw : T.weight K D z < 1) :
    K < T.radius z := by
  by_contra hr
  exact (not_le_of_gt hw) (T.one_le_weight_of_radius_le hK hD z (le_of_not_gt hr))

namespace AngularGrid
attribute [local instance] Classical.propDecidable Classical.decEq
variable {τ σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem source_offchild_weight_lt_one (g : AngularGrid) (tops : Finset τ)
    (T : τ → SlopeBox) (w cutoff K D : ℝ) (hw : 0 < w) (hK : 0 < K)
    (lower upper : ℕ) (hle : lower ≤ upper) (pathSlope : ℝ) (z : ℝ × ℝ)
    (hdrop : g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight K D z) lower (g.index lower pathSlope) z-
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight K D z) upper (g.index upper pathSlope) z < 1)
    (t : τ)
    (ht : t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cutoff lower (g.index lower pathSlope))
    (hc : t ∉ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cutoff upper (g.index upper pathSlope)) : (T t).weight K D z < 1 := by
  let parent := g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
    cutoff lower (g.index lower pathSlope)
  let child := g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
    cutoff upper (g.index upper pathSlope)
  have hsub : child ⊆ parent := g.cellTops_subset_ancestor tops _ _ cutoff
    (fun t _ => (div_pos hw (T t).length_pos).le) hle pathSlope
  have hsum := Finset.single_le_sum
    (s := parent\child) (f := fun t => (T t).weight K D z)
    (fun t _ => ((T t).weight_pos hK D z).le) (Finset.mem_sdiff.mpr ⟨ht,hc⟩)
  have hpart := Finset.sum_sdiff hsub (f := fun t => (T t).weight K D z)
  change (∑ t ∈ parent\child, (T t).weight K D z)+
    g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight K D z) upper (g.index upper pathSlope) z =
    g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight K D z) lower (g.index lower pathSlope) z at hpart
  linarith

 theorem source_offchild_masked_amplitude_bound (g : AngularGrid) (tops : Finset τ)
    (T : τ → SlopeBox) (w cutoff D L maskExponent : ℝ)
    (hw : 0 < w) (hD : 0 ≤ D) (hL : 2 ≤ L)
    (K : ℕ) (gap : ℕ → ℝ) (bands : Finset σ) (stop : τ → σ → ℕ)
    (value : τ → σ → E)
    (he : ∀ t ∈ tops, ∀ k ∈ bands, g.eligible cutoff (w/(T t).length) (stop t k))
    (phase : ℕ → ℂ) (a : ℝ) (z : ℝ × ℝ) {lower upper : ℕ}
    (hle : lower ≤ upper) (pathSlope B : ℝ)
    (hdrop : g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight (L^(maskExponent+2)) D z) lower (g.index lower pathSlope) z-
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff
      (fun t z => (T t).weight (L^(maskExponent+2)) D z) upper (g.index upper pathSlope) z < 1)
    (hamp : ∀ t ∈ g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cutoff lower (g.index lower pathSlope),
      ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
        cutoff (fun t z => (T t).weight (L^(maskExponent+2)) D z) K gap bands
        (fun _ => t) (stop t) (value t) phase a z lower (g.index lower (T t).slope)‖ ≤
      B*(T t).weight (L^(maskExponent+2)) D z) :
    let weight := fun t z => (T t).weight (L^(maskExponent+2)) D z
    let child := g.cellTops tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cutoff upper (g.index upper pathSlope)
    ‖g.sourcePacketAmplitude tops (fun t => (T t).slope) (fun t => w/(T t).length)
      cutoff weight K gap ((tops ×ˢ bands).filter fun q => q.1 ∉ child) Prod.fst
      (fun q => stop q.1 q.2) (fun q => ((T q.1).mask L maskExponent z : ℂ) • value q.1 q.2)
      phase a z lower (g.index lower pathSlope)‖ ≤
    (B*Real.exp (-L*Real.log L))*(
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff weight
        lower (g.index lower pathSlope) z-
      g.mass tops (fun t => (T t).slope) (fun t => w/(T t).length) cutoff weight
        upper (g.index upper pathSlope) z) := by
  dsimp only
  have hscale : 0 < L^(maskExponent+2) := Real.rpow_pos_of_pos (by linarith) _
  apply g.source_offchild_amplitude_bound tops (fun t => (T t).slope)
    (fun t => w/(T t).length) cutoff (fun t z => (T t).weight (L^(maskExponent+2)) D z)
    (fun t _ => (div_pos hw (T t).length_pos).le) K gap bands stop
    (fun t k => ((T t).mask L maskExponent z : ℂ) • value t k) he phase a z hle pathSlope
    (B*Real.exp (-L*Real.log L))
  intro t ht hc
  have hwt := g.source_offchild_weight_lt_one tops T w cutoff (L^(maskExponent+2)) D
    hw hscale lower upper hle pathSlope z hdrop t ht hc
  have hr := (T t).radius_large_of_weight_lt_one hscale hD z hwt
  have hmask := (T t).mask_tail hL z hr.le
  rw [g.sourcePacketAmplitude_smul_value,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ Real.exp (-L*Real.log L)*(B*(T t).weight (L^(maskExponent+2)) D z) :=
      mul_le_mul hmask (hamp t ht) (norm_nonneg _)
        (Real.exp_pos _).le
    _ = _ := by ring

end AngularGrid
end LipschitzHilbert

end

end OAI
