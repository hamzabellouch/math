import OAI.NumberTheory.Jacobsthal.Analysis.RawCompactPlacement

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Filter Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.TransitionKernels
open NumberTheoryLean.FirstHitKernels

noncomputable def genuineMarkedVisitEvent (a : ℕ) (v H : ℝ) : Set (RawEvenMarkedHitTrace a) :=
  {z | rawEvenHitAnchor a z ∈ regenerationSet ∧ z ∈ evenHitIncreasing a ∧
    z ∈ rawEvenPhysicalHitEvent a v H}

lemma genuineMarkedVisitEvent_measurable (a : ℕ) (v H : ℝ) : MeasurableSet (genuineMarkedVisitEvent a v H) :=
  (regenerationSet_measurable.preimage (rawEvenHitAnchor_measurable a)).inter
    ((evenHitIncreasing_measurable a).inter (rawEvenPhysicalHitEvent_measurable a v H))

lemma rawEvenHit_ae_genuine (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    ∀ᵐ z ∂rawEvenMarkedHitKernel a v H h, z ∈ genuineMarkedVisitEvent a v H := by
  filter_upwards [rawEvenHit_anchor_regenerates a v H h,rawEvenHit_increasing a v H h,
    rawEvenHit_ae_physical a v H h] with z hz0 hz1 hz2
  exact ⟨hz0,hz1,hz2⟩

theorem genuineMarkedVisit_mass (a : ℕ) (v H : ℝ) (h : RawHistory a) :
    rawEvenMarkedHitKernel a v H h (genuineMarkedVisitEvent a v H)=rawEvenMarkedHitKernel a v H h univ :=
  (ae_mem_iff_measure_eq (genuineMarkedVisitEvent_measurable a v H).nullMeasurableSet).mp
    (rawEvenHit_ae_genuine a v H h)

theorem genuineMarkedVisit_exponential (S : ℝ) : ∃ eta C eta0 B : ℝ,
    0 < eta ∧ 0 < C ∧ 0 < eta0 ∧ 0 ≤ B ∧ ∀ (a : ℕ) (h : RawHistory a) (s : EvenState),
      rawLast a h=(Sum.inl s,0) → s.1 ≤ S → ∀ v H : ℝ, 0 ≤ H →
        1-rawEvenMarkedHitKernel a v H h (genuineMarkedVisitEvent a v H) ≤
          ENNReal.ofReal (C*Real.exp (-eta*H)+B*Real.exp (-eta0*v)) := by
  obtain ⟨eta,C,eta0,B,heta,hC,heta0,hB,h⟩ := rawEvenMarkedHit_exponential S
  refine ⟨eta,C,eta0,B,heta,hC,heta0,hB,?_⟩
  intro a past s hs hS v H hH
  rw [genuineMarkedVisit_mass]
  exact h a past s hs hS v H hH

theorem moving_genuine_marked_visit {eps : ℝ} (heps : 0 < eps) :
    ∃ rho : ℝ, 10 < rho ∧ ∀ K : ℝ, 0 < K →
      ∀ᶠ w : ℝ in atTop, 3 ≤ w ∧ ∀ r : ℝ, w ≤ r → ∀ (a : ℕ) (h : RawHistory a) (s : EvenState),
        rawLast a h=(Sum.inl s,0) → 199/100 ≤ s.1 → s.1 ≤ 23/10 →
        1-rawEvenMarkedHitKernel a (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10)) h
          (genuineMarkedVisitEvent a (Real.log (r/(rho*K*(Real.log w)^2))) (Real.log (rho/10))) ≤
          ENNReal.ofReal eps := by
  obtain ⟨rho,hrho,hMoving⟩ := moving_raw_even_marked_hit heps
  refine ⟨rho,hrho,?_⟩
  intro K hK
  filter_upwards [hMoving K hK] with w hw
  refine ⟨hw.1,?_⟩
  intro r hr a h s hs hs0 hs1
  rw [genuineMarkedVisit_mass]
  exact hw.2 r hr a h s hs hs0 hs1

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
