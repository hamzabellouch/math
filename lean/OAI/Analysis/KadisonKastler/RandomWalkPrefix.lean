import OAI.Analysis.KadisonKastler.RandomWalkIdentityBoundary
import OAI.Analysis.KadisonKastler.CountableQuasiSelection

namespace OAI

/-! Inserting prescribed countable roots and first increments is nonsingular. -/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkPrepend (g : G) (ω : ℕ → G) (n : ℕ) : G := Nat.casesOn n g ω

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
theorem randomWalkPrepend_measurable :
    Measurable (fun p : G × (ℕ → G) => randomWalkPrepend G p.1 p.2) := by
  apply Measurable.of_eval
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem randomWalkPrepend_law :
    (randomWalkPathLaw G).map (fun p => randomWalkPrepend G p.1 p.2) =
      Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G) := by
  let ν := Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)
  let T : (ℕ → G) → G × (ℕ → G) := fun ω => (ω 0, fun n => ω (n + 1))
  have hm : Measurable T := (measurable_pi_apply 0).prodMk
    (Measurable.of_eval (fun n => measurable_pi_apply (n + 1)))
  change ((symmetricRandomWalkLaw G).prod ν).map _ = ν
  rw [← iid_first_increment_tail_law (symmetricRandomWalkLaw G),
    Measure.map_map (randomWalkPrepend_measurable G) hm]
  have he : (fun p => randomWalkPrepend G p.1 p.2) ∘ T = id := by
    funext ω n
    cases n <;> rfl
  rw [he, Measure.map_id]

theorem randomWalkRoot_quasi (g : G) :
    Measure.QuasiMeasurePreserving (fun ω : ℕ → G => (g, ω))
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) (randomWalkPathLaw G) := by
  refine ⟨measurable_const.prodMk measurable_id, ?_⟩
  rw [← Measure.dirac_prod]
  exact Measure.AbsolutelyContinuous.prod
    (absolutelyContinuous_symmetricRandomWalkLaw (Measure.dirac g))
    (Measure.AbsolutelyContinuous.refl _)

theorem randomWalkPrepend_quasi (g : G) :
    Measure.QuasiMeasurePreserving (randomWalkPrepend G g)
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))
      (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) := by
  have hp : Measure.QuasiMeasurePreserving
      (fun p : RandomWalkPath G => randomWalkPrepend G p.1 p.2)
      (randomWalkPathLaw G) (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G)) :=
    ⟨randomWalkPrepend_measurable G, (randomWalkPrepend_law G).symm ▸ Measure.AbsolutelyContinuous.refl _⟩
  exact hp.comp (randomWalkRoot_quasi G g)

end

end KadisonKastler

end OAI
