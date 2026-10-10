import OAI.MeasureTheory.Falconer.Radial.PublishedRadialMoment
import OAI.MeasureTheory.Falconer.Radial.RadialMomentParameters

namespace OAI

/-! # Integer cap availability from the precise published radial moment -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem integer_caps_of_published_radial (hpublished : PublishedRadialMoment)
    (h : ℕ) (hh : 1 ≤ h) (μ ν : ProbabilityMeasure (Space (h+1)))
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (hμK : IsCompact (μ : Measure (Space (h+1))).support)
    (hνK : IsCompact (ν : Measure (Space (h+1))).support)
    (hsep : Disjoint (μ : Measure (Space (h+1))).support (ν : Measure (Space (h+1))).support)
    (hμfrost : FrostmanBallBound (μ : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (hνfrost : FrostmanBallBound (ν : Measure (Space (h+1))) ((h:ℝ)+δ) C)
    (Γ : ℕ → Set (Space (h+1) × Space (h+1))) (hΓ : ∀ N, MeasurableSet (Γ N)) :
    CapAvailable μ ν Γ (h:ℝ) := by
  have hh' : (1:ℝ) ≤ h := by exact_mod_cast hh
  obtain ⟨hs,_,ht0,ht,_,hp,_,_⟩ := radial_moment_parameters hh' hδ hδ1
  have hsrc : (h:ℝ)+δ/2 < (h:ℝ)+δ := by linarith only [hδ]
  have hpin : (h:ℝ)-δ/4 < (h:ℝ)+δ := by linarith only [hδ]
  have hμs := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hμfrost
  have hνs := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1)))
    (show 0 < (h:ℝ)+δ/2 by linarith only [hh',hs]) hsrc hνfrost
  have hμt := rieszEnergyOn_lt_top_of_frostman (μ : Measure (Space (h+1))) ht0 hpin hμfrost
  have hνt := rieszEnergyOn_lt_top_of_frostman (ν : Measure (Space (h+1))) ht0 hpin hνfrost
  have hμν := hpublished h hh μ ν δ hδ hδ1 hμK hνK hsep hμs hνt
  have hνμ := hpublished h hh ν μ δ hδ hδ1 hνK hμK hsep.symm hνs hμt
  apply capAvailable_of_radial_moments μ ν (surfaceMeasure (h+1)) hνμ.1 hμν.1 hp
    (show 0 < (((h+1:ℕ):ℝ)*(2:ℝ)^(h+1)) by positivity) _
    (ENNReal.add_lt_top.mpr ⟨hνμ.2,hμν.2⟩).ne Γ hΓ
  intro w hw r hr _
  simpa only [Real.rpow_natCast] using surfaceMeasure_ball_bound h w hw hr.le

end Falconer

end OAI
