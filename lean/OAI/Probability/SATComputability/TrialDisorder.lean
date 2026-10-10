import OAI.Probability.SATComputability.DisorderEnumeration
import OAI.Probability.SATComputability.SATVariational

namespace OAI

namespace FixedClauseThreshold.Computability

open DilutedSpinGlass _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Nat.Partrec FiniteArithmetic
open scoped BigOperators NNReal Classical

local instance trialDisorderRatPrimcodable : Primcodable ℚ :=
  PeriodicLattice.RecursiveArithmetic.ratPrimcodable

theorem integral_sat_packet (a : ℝ≥0) (β : ℝ) (k : ℕ)
    (f : (Fin k → InteractionSample 3) → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂Measure.pi (fun _ : Fin k => (satModel a β).disorder.toMeasure)) =
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin 3 → Bool)).expect
        (fun J => f (fun i => satSample β (J i))) := by
  change (∫ θ, f θ ∂Measure.pi (fun _ : Fin k =>
    Measure.map (satSample β) signLaw.toMeasure)) = _
  rw [← Measure.pi_map_pi (μ := fun _ : Fin k => signLaw.toMeasure)
    (f := fun _ J => satSample β J) (fun _ => (measurable_of_countable _).aemeasurable)]
  rw [integral_map
    (φ := fun J : Fin k → Fin 3 → Bool => fun i => satSample β (J i))
    (Measurable.of_eval (fun i => (measurable_of_countable (satSample β)).comp
      (measurable_pi_apply i))).aemeasurable hf.aestronglyMeasurable]
  have he : signLaw.toMeasure = finiteUniform (Fin 3 → Bool) := rfl
  rw [he, finiteUniform_pi, integral_finiteUniform]
  simp only [FiniteLaw.expect, FiniteLaw.uniform, smul_eq_mul, ← Finset.mul_sum]

theorem integral_sat_edge (a : ℝ≥0) (β : ℝ) (f : InteractionSample 3 → ℝ) (hf : Measurable f) :
    (∫ θ, f θ ∂(satModel a β).disorder.toMeasure) =
      (FiniteLaw.uniform : FiniteLaw (Fin 3 → Bool)).expect (fun J => f (satSample β J)) := by
  change (∫ θ, f θ ∂Measure.map (satSample β) signLaw.toMeasure) = _
  rw [integral_map (measurable_of_countable _).aemeasurable
    hf.aestronglyMeasurable, signLaw_integral]

noncomputable def packetSiteValue (β : ℚ) (root : Code) (ms : List ℚ) (k : ℕ) : ℝ :=
  expressionValue (averagedSiteExpression β root ms k)

noncomputable def packetEdgeValue (β : ℚ) (root : Code) (ms : List ℚ) : ℝ :=
  expressionValue (averagedEdgeExpression β root ms)

theorem packet_functional (a : ℝ≥0) (β : ℚ) (root : Code) (ms : List ℚ)
    (hm : ∀ i : Fin ms.length, 0 < ms.get i) :
    functional (satModel a β) ms.length
      (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
      (fun i => (ms.get i : ℝ)) =
    Real.log 2 + (∫ k, packetSiteValue β root ms k ∂poissonMeasure (a*3)) -
      (a : ℝ)*2*packetEdgeValue β root ms := by
  let ζ := rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root)
  let m : Fin ms.length → ℝ := fun i => ms.get i
  have hp : ∀ i, 0 < m i := fun i => by
    dsimp only [m]
    exact_mod_cast hm i
  have hs (k : ℕ) : (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂(satModel a β).field.toMeasure
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) =
      packetSiteValue β root ms k := by
    change (∫ θ : Fin k → InteractionSample 3,
      ∫ h, trialLog ms.length ζ m (siteLog θ h) ∂Measure.dirac 0
      ∂Measure.pi (fun _ => (satModel a β).disorder.toMeasure)) = _
    simp only [integral_dirac]
    have hf : Measurable (fun θ : Fin k → InteractionSample 3 =>
        trialLog ms.length ζ m (siteLog θ 0)) := by
      simpa only [Function.comp_def, id_eq] using
        ((trial_site_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))).measurable
    rw [integral_sat_packet a (β : ℝ) k _ hf]
    exact (averagedSiteExpression_value β root ms k).symm
  have he : (∫ θ : InteractionSample 3,
      trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))
      ∂(satModel a β).disorder.toMeasure) = packetEdgeValue β root ms := by
    have hf : Measurable (fun θ : InteractionSample 3 =>
        trialLog ms.length ζ m (fun x => Real.log (edge θ.1 x))) := by
      simpa only [Function.comp_def] using
        ((trial_edge_lipschitz ms.length m hp ζ).continuous.comp
          (continuous_fst (X := Interaction 3) (Y := ℝ × ℝ × (Fin 3 → Bool → ℝ)))).measurable
    rw [integral_sat_edge a (β : ℝ) _ hf]
    exact (averagedEdgeExpression_value β root ms).symm
  unfold functional
  congr 2
  apply integral_congr_ae
  exact ae_of_all _ hs

theorem packetSiteValue_bound {β : ℚ} (hβ : 0 ≤ β) (root : Code) (ms : List ℚ)
    (hm : ∀ i : Fin ms.length, 0 < ms.get i) (k : ℕ) :
    |packetSiteValue β root ms k| ≤ (β : ℝ)*(k : ℝ) := by
  rw [packetSiteValue, averagedSiteExpression_value]
  apply FiniteLaw.abs_expect_le
  intro J
  have hp : ∀ i : Fin ms.length, (0 : ℝ) < ms.get i := fun i => by exact_mod_cast hm i
  have hb := trial_site_bound ms.length (fun i => (ms.get i : ℝ)) hp
    (rationalTreeValue (ms.length+1) (decodeTree (ms.length+1) root))
    (fun j => satSample (β : ℝ) (J j)) 0
  apply hb.trans
  simp only [abs_zero, zero_add, satSample]
  calc
    _ ≤ ∑ _j : Fin k, (β : ℝ) := Finset.sum_le_sum (fun j _ =>
      satInteraction_norm_le (by exact_mod_cast hβ) (J j))
    _ = _ := by simp [mul_comm]

end FixedClauseThreshold.Computability

end OAI
