import OAI.Geometry.Immersion.ClosedSurface.SecondForms
import OAI.Geometry.Immersion.ClosedSurface.PhaseGrid
import OAI.Geometry.Immersion.ClosedSurface.ProjectionBounds

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes Set Metric



theorem uniform_gram_neighborhood (R c : ℝ) (hc : 0 < c) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ p q : TangentPair,
      ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ η →
      ‖q‖ ≤ R+1 ∧ c/2 ≤ NormalFrame.gramDet q.1 q.2 := by
  obtain ⟨L,hL⟩ := contDiff_gram_pair.contDiffOn.exists_lipschitzOnWith
    (show (∞ : ℕ∞ω) ≠ 0 by simp) (convex_closedBall (0 : TangentPair) (R+1))
    (isCompact_closedBall _ _)
  let η : ℝ := min 1 (c/(2*((L:ℝ)+1)))
  have hη : 0 < η := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨η,hη,min_le_left _ _,fun p q hp hpD hpq => ?_⟩
  have hq : ‖q‖ ≤ R+1 := by
    calc ‖q‖ ≤ ‖p‖+‖q-p‖ := norm_le_insert' q p
         _ = ‖p‖+‖p-q‖ := by rw [norm_sub_rev q p]
         _ ≤ R+1 := add_le_add hp (hpq.trans (min_le_left _ _))
  have hpK : p ∈ closedBall 0 (R+1) := by
    rw [mem_closedBall,dist_zero_right]
    linarith
  have hqK : q ∈ closedBall 0 (R+1) := by simpa only [mem_closedBall,dist_zero_right] using hq
  have hl : |NormalFrame.gramDet p.1 p.2-NormalFrame.gramDet q.1 q.2| ≤ (L:ℝ)*‖p-q‖ := by
    simpa only [Real.dist_eq,dist_eq_norm,Real.norm_eq_abs] using hL.dist_le_mul p hpK q hqK
  have hηc : (L:ℝ)*η ≤ c/2 := by
    have hmin : η ≤ c/(2*((L:ℝ)+1)) := min_le_right _ _
    have hmul := (le_div_iff₀ (show 0 < 2*((L:ℝ)+1) by positivity)).mp hmin
    nlinarith [hη.le]
  refine ⟨hq,?_⟩
  have hdiff := (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hpq L.coe_nonneg))
  linarith



theorem uniform_normal_projection_stability (R c : ℝ) (hc : 0 < c) :
    ∃ η L D : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ D ∧
      ∀ p q : TangentPair, ‖p‖ ≤ R → c ≤ NormalFrame.gramDet p.1 p.2 →
        ‖p-q‖ ≤ η → ∀ W Z : RVec 4,
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤
          L*‖p-q‖*‖W‖+D*‖W-Z‖ := by
  obtain ⟨η,hη,hη1,hηb⟩ := uniform_gram_neighborhood R c hc
  obtain ⟨L,D,hL,hD,hb⟩ := compact_normal_projection_bounds (R+1) (c/2) (half_pos hc)
  refine ⟨η,L,D,hη,hη1,hL,hD,fun p q hp hpD hpq W Z => ?_⟩
  obtain ⟨hq,hqD⟩ := hηb p q hp hpD hpq
  exact hb p q (by linarith) (by linarith) hq hqD W Z




theorem normal_projection_z4_stability (R c : ℝ) (hc : 0 < c) (A : ℝ) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (p q : TangentPair) (W Z : RVec 4), ‖p‖ ≤ R →
        c ≤ NormalFrame.gramDet p.1 p.2 → ‖p-q‖ ≤ z^4 →
        ‖W‖ ≤ A/z^2 → ‖W-Z‖ ≤ z^4 →
        ‖realNormalPart p.1 p.2 W-realNormalPart q.1 q.2 Z‖ ≤ C*z^2 := by
  obtain ⟨η,L,D,hη,_,hL,hD,hb⟩ := uniform_normal_projection_stability R c hc
  refine ⟨η,L*A+D,hη,by positivity,fun z hz hz1 hzη p q W Z hp hpD hpq hW hWZ => ?_⟩
  have hh := hb p q hp hpD (hpq.trans hzη) W Z
  have hz42 : z^4 ≤ z^2 := pow_le_pow_of_le_one hz.le hz1 (by norm_num : 2 ≤ 4)
  calc
    _ ≤ L*‖p-q‖*‖W‖+D*‖W-Z‖ := hh
    _ ≤ L*z^4*(A/z^2)+D*z^4 := by gcongr
    _ ≤ L*z^4*(A/z^2)+D*z^2 := by gcongr
    _ = (L*A+D)*z^2 := by field_simp [hz.ne']

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set

def firstJetPair (F : RField 4) (p : Base) : TangentPair :=
  (coordDeriv dx F p,coordDeriv dy F p)

def secondJetTriple (F : RField 4) (p : Base) : Fin 3 → RVec 4 :=
  ![coordDeriv dx (coordDeriv dx F) p,
    coordDeriv dx (coordDeriv dy F) p,
    coordDeriv dy (coordDeriv dy F) p]

lemma realSecondTensor_eq_projection (F : RField 4) (p : Base) (i : Fin 3) :
    realSecondTensor F p i =
      realNormalPart (firstJetPair F p).1 (firstJetPair F p).2 (secondJetTriple F p i) := by
  fin_cases i <;> rfl





theorem secondTensor_z4_stability (R c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 → z^4 ≤ η →
      ∀ (F G : RField 4) (p : Base), ‖firstJetPair F p‖ ≤ R →
      c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 →
      ‖firstJetPair F p-firstJetPair G p‖ ≤ z^4 →
      ‖secondJetTriple F p‖ ≤ A/z^2 →
      ‖secondJetTriple F p-secondJetTriple G p‖ ≤ z^4 →
      ‖realSecondTensor F p-realSecondTensor G p‖ ≤ C*z^2 := by
  obtain ⟨η,C,hη,hC,hb⟩ := normal_projection_z4_stability R c hc A hA
  refine ⟨η,C,hη,hC,fun z hz hz1 hzη F G p hp hpD hpq hH hHG => ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply,realSecondTensor_eq_projection]
  exact hb z hz hz1 hzη _ _ _ _ hp hpD hpq
    ((norm_le_pi_norm _ i).trans hH) ((norm_le_pi_norm _ i).trans hHG)

end ClosedSurfaceR4.RealModes

end

end OAI
