import OAI.Geometry.SurfaceImmersion.Primitive.BoundaryProfileNormal

namespace OAI

/-! Project the old unit normal into a nearby tangent plane's orthogonal
complement. Compactness gives nonvanishing and uniform closeness to the old normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma compact_exterior_normal_projection {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {A B n : X → Vec} (hA : Continuous A) (hB : Continuous B) (hn : Continuous n)
    (hD : ∀ x, gramDet (A x) (B x) ≠ 0)
    (hunit : ∀ x, n x ⬝ᵥ n x = 1)
    (hAn : ∀ x, A x ⬝ᵥ n x = 0) (hBn : ∀ x, B x ⬝ᵥ n x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ A' B' : Vec,
      ‖A'-A x‖ < δ → ‖B'-B x‖ < δ →
      gramDet A' B' ≠ 0 ∧ realNormalPart A' B' (n x) ≠ 0 ∧
      ‖normalize (realNormalPart A' B' (n x))-n x‖ < ε := by
  let J : X → BoundaryProfile := fun x => ![A x,B x,n x,0,0]
  have hJ : Continuous J := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hn
    · exact continuous_const
    · exact continuous_const
  have hnormal (x : X) : profileNormalPart (J x) = n x :=
    realNormalPart_of_perp _ _ _ (hAn x) (hBn x)
  have hreg (x : X) : J x ∈ regularBoundaryProfiles := by
    refine ⟨hD x,?_⟩
    rw [hnormal]
    intro hz
    have hh := hunit x
    norm_num [hz] at hh
  have hpref (x : X) : profilePreferred (J x) = n x := by
    change normalize (profileNormalPart (J x)) = n x
    rw [hnormal,normalize_of_unit (hunit x)]
  obtain ⟨δ,hδ,hclose⟩ := compact_boundary_profile_stability (isCompact_range hJ)
    (by rintro _ ⟨x,rfl⟩; exact hreg x) ε hε
  refine ⟨δ,hδ,?_⟩
  intro x A' B' hA' hB'
  let H : BoundaryProfile := ![A',B',n x,0,0]
  have herr : ‖H-J x‖ < δ := by
    have hbnd : ‖H-J x‖ ≤ max ‖A'-A x‖ ‖B'-B x‖ := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simp [H,J]
      · simp [H,J]
      · simp [H,J]
    exact hbnd.trans_lt (max_lt hA' hB')
  obtain ⟨hregular,hnear⟩ := hclose (J x) (mem_range_self x) H herr
  have hnnear : ‖profilePreferred H-profilePreferred (J x)‖ < ε := by
    exact ((norm_fst_le (profileGeometry H-profileGeometry (J x)).1).trans
      (norm_fst_le (profileGeometry H-profileGeometry (J x)))).trans_lt hnear
  rw [hpref] at hnnear
  exact ⟨hregular.1,hregular.2,hnnear⟩

lemma normalized_projection_smoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : IsOpen U) {A B n : E → Vec}
    (hA : ContDiffOn ℝ ∞ A U) (hB : ContDiffOn ℝ ∞ B U) (hn : ContDiffOn ℝ ∞ n U)
    (hD : ∀ x ∈ U, gramDet (A x) (B x) ≠ 0)
    (hp : ∀ x ∈ U, realNormalPart (A x) (B x) (n x) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => normalize (realNormalPart (A x) (B x) (n x))) U := by
  intro x hx
  exact (normalize_smoothAt
    (contDiffAt_realNormalPart (hA.contDiffAt (hU.mem_nhds hx))
      (hB.contDiffAt (hU.mem_nhds hx)) (hn.contDiffAt (hU.mem_nhds hx)) (hD x hx))
    (hp x hx)).contDiffWithinAt

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
