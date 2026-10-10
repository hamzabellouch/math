import OAI.Geometry.SurfaceImmersion.Whitney.CrosscapStripFrame

namespace OAI

/-! Smooth inverse frames and the exact normal-coordinate immersion criterion. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma curveNormalLinear_invertible {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) : (curveNormalLinear v a).IsInvertible := by
  have hb := curveNormalLinear_bijective hv ha
  exact ⟨ContinuousLinearEquiv.ofBijective (curveNormalLinear v a)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2),rfl⟩

lemma curveNormalLinear_inverse_velocity {v a : Fin 3 → ℝ}
    (hv : v ≠ 0) (ha : ∀ r : ℝ, r • v ≠ a) :
    (curveNormalLinear v a).inverse v = ((0 : Base),1) := by
  apply ((curveNormalLinear_invertible hv ha).inverse_apply_eq).mpr
  simp [curveNormalLinear_apply]

lemma curveNormalLinear_inverse_smooth {v : ℝ → Fin 3 → ℝ}
    (hv : ContDiff ℝ ∞ v) {a : Fin 3 → ℝ} {J : Set ℝ}
    (hn : ∀ t ∈ J, v t ≠ 0) (ha : ∀ t r : ℝ, r • v t ≠ a) :
    ContDiffOn ℝ ∞ (fun t => (curveNormalLinear (v t) a).inverse) J := by
  intro t ht
  exact ((curveNormalLinear_invertible (hn t ht) (ha t)).contDiffAt_map_inverse.comp t
    (curveNormalLinear_smooth hv a).contDiffAt).contDiffWithinAt

lemma normal_coordinates_injective_iff (L : Base →L[ℝ] (Base × ℝ))
    (hL : L (![1,0] : Base) = ((0:Base),1)) :
    Function.Injective L ↔ (L (![0,1] : Base)).1 ≠ 0 := by
  have hsplit : ∀ x : Base, L x = (x 0) • L (![1,0] : Base) + (x 1) • L (![0,1] : Base) := by
    intro x
    have hx : x = (x 0) • (![1,0] : Base) + (x 1) • (![0,1] : Base) := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hx]
    rw [map_add,map_smul,map_smul]
  constructor
  · intro h hz
    have hEq : L (![0,1] : Base) = L (((L (![0,1] : Base)).2) • (![1,0] : Base)) := by
      rw [map_smul,hL]
      apply Prod.ext
      · simpa using hz
      · simp
    have h0 := congrFun (h hEq) 1
    norm_num at h0
  · intro hn x y hxy
    have hd : L (x-y) = 0 := by rw [map_sub,hxy,sub_self]
    rw [hsplit,hL] at hd
    have hfst := congrArg Prod.fst hd
    have h1 : (x-y) 1 = 0 := by
      have hm : (x-y) 1 • (L (![0,1] : Base)).1 = 0 := by simpa using hfst
      exact (smul_eq_zero.mp hm).resolve_right hn
    have hsnd := congrArg Prod.snd hd
    have h0 : (x-y) 0 = 0 := by simpa [h1] using hsnd
    apply sub_eq_zero.mp
    ext i
    fin_cases i
    · exact h0
    · exact h1

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
