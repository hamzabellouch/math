import OAI.Probability.GaussianReplacement.StreamBlock
import OAI.Probability.GaussianRegression.Caps
import OAI.Probability.GaussianRegression.Execution

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
universe u
namespace NoiselessRegression
open InnerProductSpace
open scoped Pointwise

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [borelSpaceE : BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
omit borelSpaceE in
lemma continuation_le_one_no_borel {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih => exact (lintegral_mono (fun x => ih _ _)).trans_eq (by simp)

end StreamAux

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

section StreamCaps
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end StreamCaps

section ObservationAC
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma projectionLaw_absolutelyContinuous {ν : Measure E} [IsFiniteMeasure ν]
    {a m n : ℕ} {C : ℝ≥0∞} (hν : PolynomialMass ν a C) (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hsupport : ν.support ⊆ Metric.closedBall 0 1) (hn : 1 ≤ n) (hmargin : n+m ≤ a) :
    projectionLaw ν m ≪ matrixLabelReference (E := E) m := by
  let ν' := C⁻¹ • ν
  have hCi : C⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hC
  let : IsFiniteMeasure ν' := ⟨by simp only [ν', Measure.smul_apply, smul_eq_mul]; finiteness⟩
  have hlocal : HasLocalMassBound ν' (a : ℝ) := by
    intro z _ r hr
    have hh := mul_le_mul' (le_rfl : C⁻¹ ≤ C⁻¹) (hν z r hr)
    simpa only [ν', Measure.smul_apply, smul_eq_mul, ← mul_assoc,
      ENNReal.inv_mul_cancel hC hCt, one_mul, Real.rpow_natCast] using hh
  have hs : ν'.support ⊆ Metric.closedBall 0 1 :=
    (Measure.smul_absolutelyContinuous.support_mono).trans hsupport
  have hbound (S : Set ((Fin m → E) × (Fin m → ℝ))) :=
    projectionLaw_set_bound hlocal hs m n hn (by exact_mod_cast hmargin) S
  have he : projectionLaw ν' m = C⁻¹ • projectionLaw ν m := by
    exact projectionLaw_smul ν m C⁻¹
  intro S hS
  have h := hbound S
  rw [hS, ENNReal.zero_rpow_of_pos (by
    have : (1 : ℝ) < n+1 := by exact_mod_cast (by omega : 1 < n+1)
    exact sub_pos.mpr ((div_lt_one (by positivity)).mpr this)), mul_zero, he,
    Measure.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp (le_antisymm h bot_le)).resolve_left (ENNReal.inv_ne_zero.mpr hCt)

lemma sphere_observation_quasi [Nontrivial E] (hd : 3 ≤ Module.finrank ℝ E) :
    Measure.QuasiMeasurePreserving
      (fun z : (Metric.sphere (0 : E) 1) × E => (z.2, ⟪z.1.val,z.2⟫))
      ((sphereLaw (E := E)).prod (stdGaussian E)) ((stdGaussian E).prod volume) := by
  have hac : projectionLaw (ambientSphereLaw (E := E)) 1 ≪ matrixLabelReference (E := E) 1 := by
    apply projectionLaw_absolutelyContinuous (a := 2) (n := 1)
      (C := ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E))
    · intro z r hr
      exact ambientSphereLaw_closedBall z hr 2 (by omega)
    · positivity
    · exact ENNReal.ofReal_ne_top
    · exact ambientSphereLaw_support.trans Metric.sphere_subset_closedBall
    · omega
    · omega
  have hp : Measure.QuasiMeasurePreserving
      (fun z : (Fin 1 → E) × E => (z.1, fun j => ⟪z.2,z.1 j⟫))
      ((Measure.pi (fun _ : Fin 1 => stdGaussian E)).prod (ambientSphereLaw (E := E)))
      (matrixLabelReference (E := E) 1) := ⟨by fun_prop, hac⟩
  have h1 := ((measurePreserving_funUnique (stdGaussian E) (Fin 1)).symm
      (MeasurableEquiv.funUnique (Fin 1) E)).prod
    (measurable_subtype_coe.measurePreserving (sphereLaw (E := E)))
  have h2 := (measurePreserving_funUnique (stdGaussian E) (Fin 1)).prod
    (volume_preserving_funUnique (Fin 1) ℝ)
  have h3 := h2.quasiMeasurePreserving.comp (hp.comp (h1.quasiMeasurePreserving.comp
    Measure.measurePreserving_swap.quasiMeasurePreserving))
  convert h3 using 1
  ext z <;> simp [MeasurableEquiv.funUnique]

end ObservationAC

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
