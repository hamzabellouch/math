import OAI.Probability.DilutedSpin.CavityGapFubini
import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.PhysicalFieldOrder

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory KernelTower
open scoped NNReal BigOperators
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {N q : ℕ} [NeZero N]

lemma finiteTrial_pressure_le (M : Model (q+1)) (hM : Admissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) :
    pressure M N ≤ functional M r (finiteTrialLaw r Q U x) m := by
  let ζ := finiteTrialLaw r Q U x
  let μ := Measure.pi (fun _ : Fin N => M.field.toMeasure)
  let S : ℝ → ℝ := fun h => ∫ k,trialDisorderAt M m ζ k h ∂poissonMeasure (M.alpha*(q+1))
  let E := ∫ z,trialLog r ζ m (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure
  have hp : ∀ d,0 < m d := fun d => (hm.2 d).1
  have hS : Integrable S M.field.toMeasure :=
    (trialDisorderAt_joint_integrable M m hp ζ hM.interaction_integrable hM.field_integrable _).integral_prod_right
  have hF := (centeredDisorderAt_joint_integrable (N := N) M hM.interaction_integrable
    hM.field_integrable (M.alpha*N)).integral_prod_right
  have hiS (s : Fin N) : Integrable (fun h : Fin N → ℝ => S (h s)) μ :=
    integrable_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) (i := s) hS
  have hb (h : Fin N → ℝ) :
      (∫ k,centeredDisorderAt M k h ∂poissonMeasure (M.alpha*N))+(M.alpha:ℝ)*N*q*E ≤ ∑ s,S (h s) := by
    have he := finiteTrial_upper_fixedField M hM a r Q U x m hm h
    simpa only [FiniteLaw.expect_sub,FiniteLaw.expect_const,FiniteLaw.expect_uniform,
      centeredDisorderAt,indexAverage,trialDisorderAt,S,E,ζ] using he
  have hi := integral_mono (hF.add (integrable_const ((M.alpha:ℝ)*N*q*E)))
    (integrable_finsetSum Finset.univ (fun s _ => hiS s)) hb
  simp only [Pi.add_apply] at hi
  rw [integral_add hF (integrable_const _),integral_const,probReal_univ,one_smul,
    centeredPressure_field_order M hM.interaction_integrable hM.field_integrable,
    integral_finsetSum _ (fun s _ => hiS s)] at hi
  dsimp only [μ] at hi
  simp only [integral_comp_eval (μ := fun _ : Fin N => M.field.toMeasure) hS.aestronglyMeasurable,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hi
  dsimp only [S] at hi
  rw [trialPoisson_field_order M m hp ζ hM.interaction_integrable hM.field_integrable] at hi
  have hN : (0:ℝ)<N := by exact_mod_cast NeZero.pos N
  unfold functional
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
  change pressure M N ≤ Real.log 2+(∫ k,trialSiteDisorder M m ζ k ∂poissonMeasure (M.alpha*(q+1)))-
    (M.alpha:ℝ)*q*E
  nlinarith

end DilutedSpinGlass.PrescribedTree

end

end OAI
