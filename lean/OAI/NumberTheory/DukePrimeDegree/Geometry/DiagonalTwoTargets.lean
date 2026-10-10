import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTimeSelection

namespace OAI

/-!
# Diagonal orbit control for both shearing target sets

The same large measurable set controls visits to the compact-return good
set and the small-leaf-ball good set. Together with the common-time lemma
this supplies the two-target recurrence step of EKL Lemmas 4.5 and 4.6.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_diagonal_two_target_control
    (d : ℕ) (j : Fin (d + 1)) (μ : Measure (X (d + 1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (G H : Set (X (d + 1))) (hG : MeasurableSet G) (hH : MeasurableSet H)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Set (X (d + 1)), MeasurableSet Z ∧
      μ Zᶜ ≤ ENNReal.ofReal (2 * μ.real Gᶜ / ε) + ENNReal.ofReal (2 * μ.real Hᶜ / ε) ∧
      ∀ z ∈ Z, ∀ T : ℝ, 1 ≤ T →
        volume.real (Ioc 0 T ∩
          {t | rightAction z (rootCanonicalFlow d j (-2 * t)) ∉ G}) ≤ ε * T ∧
        volume.real (Ioc 0 T ∩
          {t | rightAction z (rootCanonicalFlow d j (-2 * t)) ∉ H}) ≤ ε * T := by
  obtain ⟨ZG, hZG, hmG, htG⟩ :=
    exists_diagonal_return_good_set d j μ hA Gᶜ hG.compl ε hε
  obtain ⟨ZH, hZH, hmH, htH⟩ :=
    exists_diagonal_return_good_set d j μ hA Hᶜ hH.compl ε hε
  refine ⟨ZG ∩ ZH, hZG.inter hZH, ?_, ?_⟩
  · rw [compl_inter]
    exact (measure_union_le _ _).trans (add_le_add hmG hmH)
  · intro z hz T hT
    exact ⟨htG z hz.1 T hT, htH z hz.2 T hT⟩

theorem common_diagonal_two_scale_time
    (d : ℕ) (j : Fin (d + 1)) (G H : Set (X (d + 1)))
    (z : Fin 2 → X (d + 1)) (T ε : ℝ) (hT : 1 ≤ T) (hε : 36 * ε < 1)
    (θ η : Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hcontrol : ∀ k, ∀ S : ℝ, 1 ≤ S →
      volume.real (Ioc 0 S ∩
        {t | rightAction (z k) (rootCanonicalFlow d j (-2 * t)) ∉ G}) ≤ ε * S ∧
      volume.real (Ioc 0 S ∩
        {t | rightAction (z k) (rootCanonicalFlow d j (-2 * t)) ∉ H}) ≤ ε * S) :
    ∃ τ ∈ Ioc 0 T,
      (∀ k, rightAction (z k) (rootCanonicalFlow d j (-2 * τ)) ∈ G) ∧
      ∀ k q, rightAction (z k)
        (rootCanonicalFlow d j (-(θ q + (2 - η q) * τ))) ∈ H := by
  obtain ⟨τ, hτ, hG, hH⟩ := exists_common_two_scale_time
    (fun t x => rightAction x (rootCanonicalFlow d j (-2 * t))) G H z T ε
    (by linarith) hε θ η hθlo hθhi hη
    (fun k => (hcontrol k T hT).1)
    (fun k => (hcontrol k (4 * T) (by linarith)).2)
  refine ⟨τ, hτ, hG, ?_⟩
  intro k q
  have he : -2 * ((θ q + (2 - η q) * τ) / 2) = -(θ q + (2 - η q) * τ) := by ring
  simpa only [he] using hH k q

end DukePrimeDegree

end

end OAI
