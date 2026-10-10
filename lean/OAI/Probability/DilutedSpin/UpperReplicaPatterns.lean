import OAI.Probability.DilutedSpin.ClippedModelFacts
import OAI.Probability.DilutedSpin.FiniteTowerPi
import OAI.Probability.DilutedSpin.TopologyDecay

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def qLaw (x : ℝ) : FiniteLaw Spin where
  weight := q x
  nonneg s := (q_pos x s).le
  total := q_sum x

noncomputable def averagedFactor (f : Spin → ℝ) (x : ℝ) : ℝ :=
  ∑ s : Spin,q x s*f s

/-- The finite law of spin patterns induced by one fresh message label on
all replica leaves. The message label, including its root, is shared across
leaves; only the final spin draws are conditionally independent. -/
noncomputable def freshPatternLaw {Z : Type} [Fintype Z] {n : ℕ}
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) : FiniteLaw (Fin n → Spin) :=
  (Q.bind (fun z => FiniteLaw.pi (fun a : Fin n => qLaw (x z a)))).map Prod.snd

lemma freshPatternFeature {Z : Type} [Fintype Z] {n : ℕ}
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (R : ℝ) (f : Spin → ℝ) :
    patternFeature R (freshPatternLaw Q x) f =
      Q.expect (fun z => ∏ a : Fin n,averagedFactor (factorCut R f) (x z a)) := by
  unfold patternFeature freshPatternLaw
  rw [FiniteLaw.expect_map,FiniteLaw.expect_bind]
  apply FiniteLaw.expect_congr
  intro z
  exact FiniteLaw.expect_pi_product _ _

/-- Empirical pattern law of the old spin array at independently drawn sites. -/
noncomputable def oldPatternLaw {N n : ℕ} [NeZero N]
    (s : Fin N → Fin n → Spin) : FiniteLaw (Fin n → Spin) :=
  (FiniteLaw.uniform : FiniteLaw (Fin N)).map s

lemma oldPatternFeature {N n : ℕ} [NeZero N]
    (s : Fin N → Fin n → Spin) (R : ℝ) (f : Spin → ℝ) :
    patternFeature R (oldPatternLaw s) f =
      (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun i => ∏ a : Fin n,factorCut R f (s i a)) := by
  exact FiniteLaw.expect_map _ _ _

lemma mixedPatternMoment {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (R : ℝ) (old : Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (oldCoord : Fin p → Bool) :
    replicaInsertionMoment M R (fun l : Fin p => if oldCoord l then oldPatternLaw old else freshPatternLaw Q x) =
      ∫ z : InteractionSample p,(-z.2.2.1)^n *
        (∏ l : Fin p, if oldCoord l then
          (FiniteLaw.uniform : FiniteLaw (Fin N)).expect (fun i => ∏ a : Fin n,factorCut R (z.2.2.2 l) (old i a))
        else Q.expect (fun w => ∏ a : Fin n,averagedFactor (factorCut R (z.2.2.2 l)) (x w a)))
      ∂M.disorder.toMeasure := by
  unfold replicaInsertionMoment
  apply integral_congr_ae
  filter_upwards [] with z
  congr 1
  have he : (fun s : Fin p → Fin n → Spin => ∏ a : Fin n,∏ l : Fin p,factorCut R (z.2.2.2 l) (s l a)) =
      (fun s => ∏ l : Fin p,∏ a : Fin n,factorCut R (z.2.2.2 l) (s l a)) :=
    funext (fun _ => Finset.prod_comm)
  rw [he]
  rw [FiniteLaw.expect_pi_product (fun l : Fin p => if oldCoord l then oldPatternLaw old else freshPatternLaw Q x)
    (fun l (s : Fin n → Spin) => ∏ a : Fin n,factorCut R (z.2.2.2 l) (s a))]
  apply Finset.prod_congr rfl
  intro l _
  cases oldCoord l
  · simp only [Bool.false_eq_true,↓reduceIte]
    exact freshPatternFeature Q x R (z.2.2.2 l)
  · simp only [↓reduceIte]
    exact oldPatternFeature old R (z.2.2.2 l)

end DilutedSpinGlass

end

end OAI
