import OAI.Analysis.KadisonKastler.CountableRandomWalkLaw
import OAI.Analysis.KadisonKastler.NonsingularBoundary
import Mathlib.Probability.ProductMeasure

namespace OAI

/-! # The nonsingular action on rooted random-walk paths

The root is separated from the sequence of increments. Left translation
changes only the root, and commutes with advancing the random walk.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory

variable (G : Type*) [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

abbrev RandomWalkPath := G × (ℕ → G)

def randomWalkPathLaw : Measure (RandomWalkPath G) :=
  (symmetricRandomWalkLaw G).prod (Measure.infinitePi (fun _ : ℕ => symmetricRandomWalkLaw G))

instance randomWalkPathLaw_probability : IsProbabilityMeasure (randomWalkPathLaw G) := by
  unfold randomWalkPathLaw
  infer_instance

def randomWalkPathAction : NonsingularAction G (RandomWalkPath G) (randomWalkPathLaw G) where
  toPerm := {
    toFun := fun g => Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)
    map_one' := by ext x <;> simp
    map_mul' := by intro g h; ext x <;> simp [mul_assoc] }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (symmetricRandomWalkLaw_quasi (fun x => g * x))
    (Measure.QuasiMeasurePreserving.id _)

@[simp]
theorem randomWalkPathAction_apply (g : G) (x : RandomWalkPath G) :
    (randomWalkPathAction G).toPerm g x = (g * x.1, x.2) := rfl

def randomWalkAdvance (x : RandomWalkPath G) : RandomWalkPath G :=
  (x.1 * x.2 0, fun n => x.2 (n + 1))

theorem randomWalkAdvance_measurable : Measurable (randomWalkAdvance G) := by
  apply Measurable.prodMk
  · exact (measurable_of_countable (fun p : G × G => p.1 * p.2)).comp
      (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
  · exact Measurable.of_eval (fun n => (measurable_pi_apply (n + 1)).comp measurable_snd)

theorem randomWalkAdvance_action (g : G) (x : RandomWalkPath G) :
    randomWalkAdvance G ((randomWalkPathAction G).toPerm g x) =
      (randomWalkPathAction G).toPerm g (randomWalkAdvance G x) := by
  apply Prod.ext
  · exact mul_assoc g x.1 (x.2 0)
  · rfl

theorem randomWalkAdvance_iterate_action (g : G) (n : ℕ) (x : RandomWalkPath G) :
    (randomWalkAdvance G)^[n] ((randomWalkPathAction G).toPerm g x) =
      (randomWalkPathAction G).toPerm g ((randomWalkAdvance G)^[n] x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact randomWalkAdvance_action G g _

def randomWalkPosition (n : ℕ) (x : RandomWalkPath G) : G :=
  ((randomWalkAdvance G)^[n] x).1

theorem randomWalkPosition_action (g : G) (n : ℕ) (x : RandomWalkPath G) :
    randomWalkPosition G n ((randomWalkPathAction G).toPerm g x) =
      g * randomWalkPosition G n x := by
  unfold randomWalkPosition
  rw [randomWalkAdvance_iterate_action]
  rfl

end

end KadisonKastler

end OAI
