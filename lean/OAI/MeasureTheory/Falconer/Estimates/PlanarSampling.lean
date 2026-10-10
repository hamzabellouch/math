import OAI.MeasureTheory.Falconer.Incidence.IncidenceSamples
import OAI.MeasureTheory.Falconer.Incidence.SampledFurstenberg

namespace OAI

/-!
# Original labels, slope coordinates and prescribed strip covers

These adapters connect the two uniform sampling stages to the exact finite
Furstenberg obstruction. Every strip list remains indexed by its original
direction label, including when slope coordinates coincide.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

noncomputable def slopePoint (m : ℝ) : Space 2 := WithLp.toLp 2 ![m,0]

@[simp] theorem slopePoint_zero (m : ℝ) : slopePoint m 0 = m := rfl
@[simp] theorem slopePoint_one (m : ℝ) : slopePoint m 1 = 0 := rfl

theorem continuous_slopePoint : Continuous slopePoint := by
  change Continuous (fun m : ℝ => WithLp.toLp 2 ![m,0])
  apply (PiLp.continuous_toLp 2 _).comp
  fun_prop

theorem slopePoint_dist (s t : ℝ) : dist (slopePoint s) (slopePoint t) = |s-t| := by
  have hh := EuclideanSpace.dist_sq_eq (slopePoint s) (slopePoint t)
  simp only [Fin.sum_univ_two, slopePoint_zero, slopePoint_one, Real.dist_eq, sq_abs] at hh
  nlinarith [dist_nonneg (x := slopePoint s) (y := slopePoint t), abs_nonneg (s-t), sq_abs (s-t)]

theorem slopePoint_ball_mass_le {W : Type*} [MeasurableSpace W]
    (ν : ProbabilityMeasure W) (m : W → ℝ) {δ b K : ℝ}
    (hb : ∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ K*r^b)
    (c : Space 2) (r : ℝ) (hr : δ ≤ r) :
    (ν : Measure W).real {w | dist (slopePoint (m w)) c ≤ r} ≤ K*r^b := by
  apply le_trans (measureReal_mono (μ := (ν : Measure W)) ?_) (hb (c 0) r hr)
  intro w hw
  exact (show |m w-c 0| ≤ dist (slopePoint (m w)) c by
    simpa only [slopePoint_zero, Real.dist_eq] using
      PiLp.dist_apply_le (slopePoint (m w)) c 0).trans hw

noncomputable def incidentLabels {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (ω : Fin n → W) (x : X) : Finset (Fin n) :=
  Finset.univ.filter (fun i => E x (ω i))

theorem empirical_incidence_eq_card {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (ω : Fin n → W) (x : X) :
    iidAverage (fun w => if E x w then (1 : ℝ) else 0) ω =
      (n : ℝ)⁻¹ * ((incidentLabels E ω x).card : ℝ) := by
  change (n : ℝ)⁻¹ * iidCount {w | E x w} ω = _
  rw [iidCount_eq_card_filter]
  rfl

theorem empirical_incidence_card_lower {X W : Type*} (E : X → W → Prop)
    {n : ℕ} (hn : 0 < n) (ω : Fin n → W) (x : X) {I : ℝ}
    (hI : I ≤ iidAverage (fun w => if E x w then (1 : ℝ) else 0) ω) :
    I * (n : ℝ) ≤ ((incidentLabels E ω x).card : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [empirical_incidence_eq_card] at hI
  have hh := mul_le_mul_of_nonneg_left hI hnR.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hnR.ne', one_mul, mul_one, mul_comm] using hh

noncomputable def stripLineCandidates (δ m : ℝ) (A : Finset ℝ) (L : ℕ) :
    Finset (Space 2) := A.biUnion (fun a => roundedStripCandidates δ m a L)

theorem stripLineCandidates_card_le (δ m : ℝ) (A : Finset ℝ) (L : ℕ) :
    (stripLineCandidates δ m A L).card ≤ A.card * (2*L+1) := by
  calc
    _ ≤ ∑ a ∈ A, (roundedStripCandidates δ m a L).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, (2*L+1) := Finset.sum_le_sum (fun a _ => roundedStripCandidates_card_le δ m a L)
    _ = _ := by simp

theorem roundedIncidentLine_mem_stripLineCandidates {δ C m : ℝ}
    (hδ : 0 < δ) (A : Finset ℝ) (L : ℕ) (hL : C+2 ≤ (L : ℝ))
    (x : Space 2) (hx : |x 0| ≤ 1)
    (hcover : ∃ a ∈ A, |x 1-m*x 0-a| ≤ C*δ) :
    roundedIncidentLine δ x m ∈ stripLineCandidates δ m A L := by
  obtain ⟨a, ha, hb⟩ := hcover
  exact Finset.mem_biUnion.mpr ⟨a, ha, roundedIncidentLine_mem_candidates hδ x hx hb L hL⟩

end Falconer

end OAI
