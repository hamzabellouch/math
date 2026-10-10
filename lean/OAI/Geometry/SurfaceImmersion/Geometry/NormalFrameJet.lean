import OAI.Geometry.SurfaceImmersion.Atlas.NormalDefectCoordinates

namespace OAI

/-! A regular three-dimensional direction jet induces a regular
normal-defect jet in the transverse two-plane. -/
noncomputable section
open Set Filter Matrix
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

def directionBlock (K : Base →L[ℝ] (Fin 3 → ℝ)) (u : Fin 3 → ℝ) :
    (Base × ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  K.comp (ContinuousLinearMap.fst ℝ Base ℝ) + (ContinuousLinearMap.snd ℝ Base ℝ).smulRight u

lemma directionBlock_apply (K : Base →L[ℝ] (Fin 3 → ℝ)) (u : Fin 3 → ℝ) (z : Base × ℝ) :
    directionBlock K u z = K z.1 + z.2 • u := rfl

lemma normal_frame_jet_bijective {u a : Fin 3 → ℝ} (hu : u ≠ 0)
    (ha : ∀ r : ℝ, r • u ≠ a) (K : Base →L[ℝ] (Fin 3 → ℝ))
    (hK : Function.Bijective (directionBlock K u)) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ Base ℝ).comp
      ((curveNormalLinear u a).inverse.comp K)) := by
  let F := curveNormalLinear u a
  let J := F.inverse
  let P := (ContinuousLinearMap.fst ℝ Base ℝ).comp (J.comp K)
  have hI : F.IsInvertible := curveNormalLinear_invertible hu ha
  have hJu : J u = ((0:Base),1) := curveNormalLinear_inverse_velocity hu ha
  have hJinj : Function.Injective J := by
    intro v w he
    have hh := congrArg F he
    change F (F.inverse v) = F (F.inverse w) at hh
    simpa only [hI.self_apply_inverse] using hh
  have hnormal : ∀ z : Base × ℝ, (J (directionBlock K u z)).1 = P z.1 := by
    intro z
    rw [directionBlock_apply,map_add,map_smul,hJu]
    simp [P]
  change Function.Bijective P
  constructor
  · intro v w he
    have hz : P (v-w) = 0 := by rw [map_sub,he,sub_self]
    let z : Base × ℝ := (v-w,-(J (K (v-w))).2)
    have hzero : directionBlock K u z = 0 := by
      apply hJinj
      rw [map_zero,directionBlock_apply,map_add,map_smul,hJu]
      apply Prod.ext
      · simpa [P,z] using hz
      · simp [z]
    have hzz := hK.1 (hzero.trans (map_zero _).symm)
    have hdiff : v-w = 0 := congrArg Prod.fst hzz
    exact sub_eq_zero.mp hdiff
  · intro v
    obtain ⟨z,hz⟩ := hK.2 (F (v,0))
    refine ⟨z.1,?_⟩
    rw [← hnormal,hz,hI.inverse_apply_self]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
