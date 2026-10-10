import OAI.MeasureTheory.Falconer.Geometry.TwoProjectionPiecePair
import OAI.MeasureTheory.Falconer.Angular.PublishedIntegerCaps

namespace OAI

/-! # Integer cap availability in the first auxiliary space -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m h : ℕ} {μ : ProbabilityMeasure (Space d)} {s δ ε : ℝ}
  {f : TwoProjectionFrame μ m (h+1) s}

namespace TwoProjectionPieces

theorem first_integer_caps (p : TwoProjectionPieces f ε)
    (hpublished : PublishedRadialMoment) (hh : 1 ≤ h)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hδs : s = (h:ℝ)+δ)
    (Γ : ℕ → Set (Space m × Space m)) (hΓ : ∀ N, MeasurableSet (Γ N))
    (hΓsub : ∀ N, Γ N ⊆
      ((p.left : Measure (Space d)).map f.first).support ×ˢ
        ((p.right : Measure (Space d)).map f.first).support) :
    CapAvailable (p.left.map f.first) (p.right.map f.first) Γ (h:ℝ) := by
  subst s
  let ν₁ := p.left.map f.first
  let ν₂ := p.right.map f.first
  have hK₁ : IsCompact (ν₁ : Measure (Space m)).support :=
    (compact_projected_support _ p.left_support_compact f.first).2
  have hK₂ : IsCompact (ν₂ : Measure (Space m)).support :=
    (compact_projected_support _ p.right_support_compact f.first).2
  have hfrost := p.projected_frostman (f.second.comp f.first) f.second_frostman
  have hmap₁ : (ν₁ : Measure (Space m)).map f.second =
      (p.left : Measure (Space d)).map (f.second.comp f.first) :=
    Measure.map_map f.second.continuous.measurable f.first.continuous.measurable
  have hmap₂ : (ν₂ : Measure (Space m)).map f.second =
      (p.right : Measure (Space d)).map (f.second.comp f.first) :=
    Measure.map_map f.second.continuous.measurable f.first.continuous.measurable
  have hsep : Disjoint ((ν₁ : Measure (Space m)).map f.second).support
      ((ν₂ : Measure (Space m)).map f.second).support := by
    rw [hmap₁,hmap₂]
    apply projected_supports_disjoint _ _ p.left_support_compact p.right_support_compact
    intro x hx y hy he
    have hlow := (p.geometry x (p.left_support hx) y (p.right_support hy)).2.2.1
    have hz : (f.second.comp f.first) (radialDirection x y) = 0 := by
      simp only [radialDirection,map_smul,map_sub,he,sub_self,smul_zero]
    rw [hz,norm_zero] at hlow
    exact (not_le_of_gt p.lower_pos) hlow
  have hcap := integer_caps_of_published_radial hpublished h hh
    (ν₁.map f.second) (ν₂.map f.second) hδ hδ1
    (compact_projected_support _ hK₁ f.second).2
    (compact_projected_support _ hK₂ f.second).2 hsep
    (by
      change FrostmanBallBound ((ν₁ : Measure (Space m)).map f.second) _ _
      rw [hmap₁]
      exact hfrost.1)
    (by
      change FrostmanBallBound ((ν₂ : Measure (Space m)).map f.second) _ _
      rw [hmap₂]
      exact hfrost.2)
    (fun _ => univ) (fun _ => MeasurableSet.univ)
  apply CapAvailable.pullback f.second ν₁ ν₂
    (by linarith [p.lower_pos] : 0 < p.lower/4) f.second_contractive (Nat.cast_nonneg h)
    hΓ (fun _ _ _ => mem_univ _) _ hcap
  intro N z hz
  exact p.second_direction_lower z.1 (hΓsub N hz).1 z.2 (hΓsub N hz).2

end TwoProjectionPieces
end Falconer

end OAI
