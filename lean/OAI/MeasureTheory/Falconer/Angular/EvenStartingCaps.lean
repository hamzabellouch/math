import OAI.MeasureTheory.Falconer.Estimates.ProjectedPair
import OAI.MeasureTheory.Falconer.Angular.PublishedIntegerCaps
import OAI.MeasureTheory.Falconer.Angular.CapTransport

namespace OAI

/-! # The original-pair starting cap estimate in even dimensions -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

namespace ProjectedStartingPair
variable {d m : ℕ} {ζ : ProbabilityMeasure (Space d)} {s ε : ℝ}

def relation (p : ProjectedStartingPair ζ m s ε) : Set (Space d × Space d) :=
  (p.left : Measure (Space d)).support ×ˢ (p.right : Measure (Space d)).support

theorem relation_measurable (p : ProjectedStartingPair ζ m s ε) :
    MeasurableSet p.relation :=
  Measure.isClosed_support.measurableSet.prod Measure.isClosed_support.measurableSet

theorem relation_mass (p : ProjectedStartingPair ζ m s ε) :
    ((p.left : Measure (Space d)).prod (p.right : Measure (Space d))) p.relation = 1 := by
  rw [relation,Measure.prod_prod]
  have hμ : (p.left : Measure (Space d)) (p.left : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  have hν : (p.right : Measure (Space d)) (p.right : Measure (Space d)).support = 1 :=
    (mem_ae_iff_prob_eq_one Measure.isClosed_support.measurableSet).mp Measure.support_mem_ae
  rw [hμ,hν,mul_one]

theorem projected_disjoint (p : ProjectedStartingPair ζ m s ε) :
    Disjoint ((p.left : Measure (Space d)).map p.projection).support
      ((p.right : Measure (Space d)).map p.projection).support := by
  apply projected_supports_disjoint _ _ p.left_compact p.right_compact
  intro x hx y hy he
  have hlow := (p.geometry x hx y hy).2.2.1
  have hz : p.projection (radialDirection x y) = 0 := by
    simp only [radialDirection,map_smul,map_sub,he,sub_self,smul_zero]
  rw [hz,norm_zero] at hlow
  exact (not_le_of_gt p.lower_pos) hlow

theorem integer_available (hpublished : PublishedRadialMoment)
    {h : ℕ} (hh : 1 ≤ h) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε) :
    CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  have hcap := integer_caps_of_published_radial hpublished h hh
    (p.left.map p.projection) (p.right.map p.projection) hδ hδ1
    (compact_projected_support _ p.left_compact p.projection).2
    (compact_projected_support _ p.right_compact p.projection).2
    p.projected_disjoint p.projected_left_frostman p.projected_right_frostman
    (fun _ => univ) (fun _ => MeasurableSet.univ)
  apply CapAvailable.pullback p.projection p.left p.right p.lower_pos p.contractive
    (Nat.cast_nonneg h) (fun _ => p.relation_measurable) (fun _ _ _ => mem_univ _) _ hcap
  intro N z hz
  exact ⟨(p.geometry z.1 hz.1 z.2 hz.2).2.2.1,
    (p.geometry z.1 hz.1 z.2 hz.2).2.2.2.1⟩

end ProjectedStartingPair

theorem exists_even_starting_caps (hpublished : PublishedRadialMoment)
    {d h : ℕ} (hh : 1 ≤ h) (ζ : ProbabilityMeasure (Space d))
    {s C ε : ℝ} (hs : (h:ℝ) < s)
    (hfrost : FrostmanBallBound (ζ : Measure (Space d)) s C) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ p : ProjectedStartingPair ζ (h+1) ((h:ℝ)+δ) ε,
        CapAvailable p.left p.right (fun _ => p.relation) (h:ℝ) := by
  let δ := min (s-(h:ℝ)) 1 / 2
  have hδ : 0 < δ := div_pos (lt_min (sub_pos.mpr hs) zero_lt_one) (by norm_num)
  have hδ1 : δ < 1 := by dsimp [δ]; have := min_le_right (s-(h:ℝ)) 1; linarith
  have hδs : (h:ℝ)+δ < s := by
    have hmin := min_le_left (s-(h:ℝ)) 1
    dsimp [δ]
    linarith
  have hu : 0 < (h:ℝ)+δ := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hδ
  have hum : (h:ℝ)+δ < (h+1:ℕ) := by push_cast; linarith
  obtain ⟨p⟩ := exists_projected_starting_pair ζ hu hδs hum hfrost hε
  exact ⟨δ,hδ,hδ1,p,p.integer_available hpublished hh hδ hδ1⟩

end Falconer

end OAI
