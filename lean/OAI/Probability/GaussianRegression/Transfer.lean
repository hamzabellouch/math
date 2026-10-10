import OAI.Probability.GaussianRegression.Observation
import OAI.Probability.GaussianRegression.Caps
import OAI.Probability.GaussianRegression.Execution

namespace OAI

/-!
Prefix integration and transfer between almost-everywhere equal transitions.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamTransfer
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurePreserving_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν]
    {t T : ℕ} (ht : t ≤ T) :
    MeasurePreserving (fun x : Fin T → E => fun i : Fin t => x (Fin.castLE ht i))
      (Measure.pi (fun _ => ν)) (Measure.pi (fun _ => ν)) := by
  refine ⟨by fun_prop, ?_⟩
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (by fun_prop)]
  exact lintegral_pi_prefix ν ht f hf

lemma sphere_sample_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E)
    {T : ℕ} (i : Fin T) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × (Fin T → E) => (z.2 i, ⟪z.1.val,z.2 i⟫))
      ((sphereLaw (E := E)).prod (Measure.pi (fun _ => stdGaussian E)))
      ((stdGaussian E).prod volume) := by
  exact (sphere_observation_quasi hd).comp
    ((MeasurePreserving.id (sphereLaw (E := E))).prod
      (measurePreserving_eval (fun _ : Fin T => stdGaussian E) i)).quasiMeasurePreserving

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] in
lemma streamRoute_congr {J : Type*} (δ δ' : ℕ → J → (E × ℝ) → J)
    (n k : ℕ) (j : J) (A : Fin k → E) (b : Fin k → ℝ)
    (h : ∀ t j i, δ t j (A i,b i) = δ' t j (A i,b i)) :
    streamRoute δ n k j (A,b) = streamRoute δ' n k j (A,b) := by
  induction k generalizing n j with
  | zero => rfl
  | succ k ih =>
    rw [streamRoute, streamRoute, h]
    exact ih (n+1) _ (Fin.tail A) (Fin.tail b) (fun t j i => h t j i.succ)

lemma prefix_route_cap_bound [Nontrivial E]
    {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]
    {δ : ℕ → J → (E × ℝ) → J} (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) {k T : ℕ} (hk : k ≤ T) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin T => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j
        ((fun i => z.2 (Fin.castLE hk i)),fun i => ⟪z.1.val,z.2 (Fin.castLE hk i)⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ (T/q+1) := by
  have hp := (MeasurePreserving.id (sphereLaw (E := E))).prod
    (measurePreserving_pi_prefix (stdGaussian E) hk)
  have hs : MeasurableSet
      {z : (Metric.sphere (0 : E) 1) × (Fin k → E) |
        dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  apply (le_of_eq (hp.measure_preimage hs.nullMeasurableSet)).trans
  apply (route_cap_bound hδ y hε ha hq hqa k j).trans
  apply mul_le_mul' le_rfl
  exact pow_le_pow_right₀ (one_le_streamFactor (by omega : 0 < q))
    (Nat.add_le_add_right (Nat.div_le_div_right hk) 1)

end StreamTransfer

end NoiselessRegression

end

end OAI
