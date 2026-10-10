import OAI.MathematicalPhysics.Transonic.Profile.RationalSmooth

namespace OAI

section
noncomputable section
namespace SepticProfile.SonicShooting
open Set Filter SourceFamily ExteriorPolynomial PhysicalExterior
open scoped Topology ContDiff

def ExteriorTail.globalVelocity {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) : ℝ → ℝ :=
  ODEGlue.join B.beginning M.velocity T.v

lemma ExteriorTail.global_near_local {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : y<B.beginning) : T.globalVelocity =ᶠ[𝓝 y] M.velocity :=
  ODEGlue.join_eventually_left hy

lemma ExteriorTail.global_eq_tail {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : B.beginning≤y) : T.globalVelocity y=T.v y :=
  ODEGlue.join_eq_right hy T.start.symm

lemma ExteriorTail.global_range {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0≤y) : |T.globalVelocity y|<1 := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).eq_of_nhds]
    exact B.width.velocity_abs ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩
  · rw [T.global_eq_tail (le_of_not_gt hb)]
    exact T.range y (le_of_not_gt hb)

lemma ExteriorTail.global_below {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0<y) : T.globalVelocity y<y ∧ y*T.globalVelocity y<1 := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).eq_of_nhds]
    exact B.width.velocity_below ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩
  · rw [T.global_eq_tail (le_of_not_gt hb)]
    exact T.below y (le_of_not_gt hb)

lemma ExteriorTail.global_den_ne {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : M.radius<y) : profileDenom ell y (T.globalVelocity y)≠0 := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).eq_of_nhds]
    exact B.width.exterior_den_ne ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩
  · rw [T.global_eq_tail (le_of_not_gt hb)]
    exact T.den_ne y (le_of_not_gt hb)

lemma ExteriorTail.global_derivative {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : M.radius<y) :
    HasDerivAt T.globalVelocity (field ell M.beta (y,T.globalVelocity y)) y := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).eq_of_nhds]
    exact (B.width.exterior_derivative ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩).congr_of_eventuallyEq
      (T.global_near_local hb)
  · let a := (M.radius+B.beginning)/2
    have ha : M.radius<a ∧ a<B.beginning := by dsimp [a];constructor <;> linarith only [B.beginning_bounds.1]
    have hu (t:ℝ) (ht:t∈Icc a B.beginning) :
        HasDerivWithinAt M.velocity (field ell M.beta (t,M.velocity t)) (Icc a B.beginning) t :=
      (B.width.exterior_derivative ⟨ha.1.trans_le ht.1,ht.2.trans B.beginning_bounds.2.1.le⟩).hasDerivWithinAt
    have hd := ODEGlue.hasDerivWithinAt_join_Ici (f:=fun y u => field ell M.beta (y,u)) ha.2.le hu T.derivative T.start.symm y
      (ha.2.le.trans (le_of_not_gt hb))
    exact hd.hasDerivAt (Ici_mem_nhds (ha.2.trans_le (le_of_not_gt hb)))

lemma ExteriorTail.global_smooth {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0≤y) : ContDiffAt ℝ ∞ T.globalVelocity y := by
  by_cases hb : y<B.beginning
  · exact (B.width.velocity_smooth ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩).congr_of_eventuallyEq
      (T.global_near_local hb)
  · have hyr : M.radius<y := B.beginning_bounds.1.trans_le (le_of_not_gt hb)
    have hs := source_solution_smooth (beta:=M.beta) (s:=Ioi M.radius) isOpen_Ioi
      (fun _ ht => T.global_den_ne ht) (fun _ ht => T.global_derivative ht)
    exact (hs y hyr).contDiffAt (Ioi_mem_nhds hyr)

lemma ExteriorTail.global_equation {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0≤y) :
    profileDenom ell y (T.globalVelocity y)*deriv T.globalVelocity y=
      profileNumer ell M.beta y (T.globalVelocity y) := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).deriv_eq,(T.global_near_local hb).eq_of_nhds]
    exact B.width.velocity_equation ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩
  · have hyr : M.radius<y := B.beginning_bounds.1.trans_le (le_of_not_gt hb)
    rw [(T.global_derivative hyr).deriv]
    exact mul_div_cancel₀ _ (T.global_den_ne hyr)

lemma ExteriorTail.global_unique_sonic {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B)
    {y : ℝ} (hy : 0≤y) :
    velocityToU y (T.globalVelocity y)=sonicSpeed ↔ y=M.radius := by
  by_cases hb : y<B.beginning
  · rw [(T.global_near_local hb).eq_of_nhds]
    exact B.width.unique_sonic ⟨hy,hb.le.trans B.beginning_bounds.2.1.le⟩
  · have hyr : M.radius<y := B.beginning_bounds.1.trans_le (le_of_not_gt hb)
    have hyp : 0<y := M.radius_bounds.1.trans hyr
    have hp : 1-y*T.globalVelocity y≠0 := ne_of_gt (sub_pos.mpr (T.global_below hyp).2)
    exact iff_of_false (fun h => T.global_den_ne hyr (denom_zero_of_sonic hp h)) (ne_of_gt hyr)

lemma ExteriorTail.global_sonic_slope {M : MatchedPair} {B : ExteriorBranch M} (T : ExteriorTail B) :
    0<deriv (fun y => velocityToU y (T.globalVelocity y)) M.radius := by
  have he : (fun y => velocityToU y (T.globalVelocity y)) =ᶠ[𝓝 M.radius]
      (fun y => velocityToU y (M.velocity y)) := by
    filter_upwards [T.global_near_local B.beginning_bounds.1] with y hy
    rw [hy]
  rw [he.deriv_eq]
  exact B.width.sonic_slope

end SepticProfile.SonicShooting

end
end

end OAI
