import OAI.Probability.ProjectionMoments.AllRadii

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma continuation_mass_bound_ceil [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ ((k+q-1)/q)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q),pow_zero,mul_one,continuation] using hlocal n j
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q+q-1)/q) ≠ ∞ :=
        ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
      have hb := blockValue_mass_bound μ
        (fun b => measurable_continuation hδ hw (n+q) (k-q) b)
        (fun b s => continuation_le_one hw1 (n+q) (k-q) b s)
        (fun b => ih (k-q) hki (n+q) b) hC1 hC1t hd ha
        (by omega : q ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+q ≤ a) (measurable_streamRoute hδ n q j)
      have he : continuation δ w n k j =
          blockValue (fun b => continuation δ w (n+q) (k-q) b) (streamRoute δ n q j) := by
        funext s
        simpa [Nat.add_sub_of_le hk] using continuation_unroll hδ n q (k-q) j s
      rw [he]
      have hdiv : (k+q-1)/q = (k-q+q-1)/q+1 := by
        have he : k+q-1 = q+(k-q+q-1) := by omega
        rw [he,Nat.add_div_left _ hq0]
      convert hb using 1
      rw [hden, ← streamFactor, hdiv, pow_succ]
      ring
    · have hkm : k ≤ q := by omega
      have hb := blockValue_mass_bound μ
        (fun b => hw (n+k) b) (fun b s => hw1 (n+k) b s) (hlocal (n+k)) hC hCt hd ha
        (by omega : k ≤ Module.finrank ℝ E) (by omega : 1 ≤ q-1)
        (by omega : q-1+k ≤ a) (measurable_streamRoute hδ n k j)
      have he : continuation δ w n k j = blockValue (w (n+k)) (streamRoute δ n k j) := by
        funext s
        simpa [continuation] using continuation_unroll hδ n k 0 j s
      rw [he]
      convert hb using 1
      have hdiv : (k+q-1)/q = 1 := by
        have he : k+q-1 = q+(k-1) := by omega
        rw [he,Nat.add_div_left _ hq0,Nat.div_eq_of_lt (by omega : k-1 < q)]
      rw [hden, ← streamFactor,hdiv,pow_one]
      exact mul_comm _ _

variable [Nontrivial E] [Nonempty J]

lemma continuation_cap_integral_bound_ceil {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  apply ambient_mass_bound
  apply continuation_mass_bound_ceil _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass (y n j) hε a ha)
    (Module.finrank_pos (R := ℝ) (M := E)) (by omega) hq hqa

lemma route_cap_bound_ceil {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ Module.finrank ℝ E - 1)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  let w : ℕ → J → E → ℝ≥0∞ := fun _ j => capWeight (y j) ε
  have hV := measurable_continuation (w := w) hδ (fun _ j => measurable_capWeight (y j) ε) 0 k j
  have he (s : E) : continuation δ w 0 k j s =
      ∫⁻ A : Fin k → E, capWeight (y (streamRoute δ 0 k j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian E) := by
    simpa [w, blockValue, continuation] using continuation_unroll (w := w) hδ 0 k 0 j s
  let S : Set ((Metric.sphere (0 : E) 1) × (Fin k → E)) :=
    {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact measurable_subtype_coe.comp measurable_fst |>.dist
      ((measurable_of_finite y).comp ((measurable_streamRoute hδ 0 k j).comp (by fun_prop)))
  change ((sphereLaw (E := E)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := E)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : Metric.sphere (0 : E) 1,
      (∫⁻ A, S.indicator (fun _ => (1 : ℝ≥0∞)) (s,A) ∂Measure.pi (fun _ => stdGaussian E)) =
        continuation δ w 0 k j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (y (streamRoute δ 0 k j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  exact continuation_cap_integral_bound_ceil hδ (fun _ => y) hε ha hq hqa 0 k j

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

instance taggedMeasurableSingletonClass : MeasurableSingletonClass (TaggedState M T) :=
  ⟨fun _ => trivial⟩

lemma card_taggedState (M T : ℕ) : Fintype.card (TaggedState M T) = (T+2)*2^M := by
  simp only [TaggedState, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, State]
  ring

def decodeTagged : TaggedState M T → RunStatus M
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.val,j)

def taggedStep (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (t : ℕ) : TaggedState M T → (Vector d × ℝ) → TaggedState M T
  | .inr done, _ => .inr done
  | .inl j, obs =>
    if ht : t ≤ T then
      let a := τ t j obs
      if a.1 then .inr (⟨t,by omega⟩,a.2) else .inl a.2
    else .inl j

lemma measurable_taggedStep {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (t : ℕ) (j : TaggedState M T) :
    Measurable (taggedStep (T := T) τ t j) := by
  classical
  cases j with
  | inr done => exact measurable_const
  | inl j =>
    unfold taggedStep
    split_ifs with ht
    · exact (measurable_of_finite (fun a : Bool × State M =>
        if a.1 then Sum.inr ((⟨t,by omega⟩ : Fin (T+1)),a.2) else Sum.inl a.2)).comp (hτ t j)
    · exact measurable_const

def taggedOutput (L : Learner d M T Ω) (ω : Ω) : TaggedState M T → UnitSphere d
  | .inl j => L.output T ω j
  | .inr (t,j) => L.output t ω j

lemma decode_taggedStart (a : Bool × State M) :
    decodeTagged (taggedStart (T := T) a) = if a.1 then .inr (0,a.2) else .inl a.2 := by
  simp only [taggedStart]; split_ifs <;> rfl

lemma run_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T)
    {n : ℕ} (hn : n ≤ T) :
    L.run s ω x n = decodeTagged (streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j))
      0 n (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE hn i)),fun i => ⟪s.val,x (Fin.castLE hn i)⟫)) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [fin_prefix_snoc hn x, fin_prefix_snoc hn (fun i => ⟪s.val,x i⟫),streamRoute_snoc]
    rw [run,ih (by omega)]
    generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 n
      (taggedStart (L.initialChoice ω))
      ((fun i => x (Fin.castLE (by omega : n ≤ T) i)),fun i => ⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫) = j
    cases j with
    | inr done => rfl
    | inl j =>
      simp only [decodeTagged, taggedStep, Nat.zero_add,dite_eq_left (by omega : n < T),
        dite_eq_left (by omega : n+1 ≤ T),real_inner_comm]
      split_ifs <;> rfl

lemma estimate_eq_taggedRoute (L : Learner d M T Ω) (s : UnitSphere d) (ω : Ω) (x : Samples d T) :
    L.estimate s ω x = L.taggedOutput ω (streamRoute
      (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T (taggedStart (L.initialChoice ω))
      (x,fun i => ⟪s.val,x i⟫)) := by
  unfold estimate terminal
  rw [L.run_eq_taggedRoute s ω x le_rfl]
  have hi : (fun i : Fin T => x (Fin.castLE le_rfl i)) = x := by funext i; exact congrArg x (Fin.ext rfl)
  have hb : (fun i : Fin T => ⟪s.val,x (Fin.castLE le_rfl i)⟫) = (fun i => ⟪s.val,x i⟫) := by funext i; rfl
  rw [hi,hb]
  generalize streamRoute (taggedStep (T := T) (fun t j => L.transition t ω j)) 0 T
    (taggedStart (L.initialChoice ω)) (x,fun i => ⟪s.val,x i⟫) = j
  cases j with
  | inl j => rfl
  | inr done => rfl

lemma taggedStep_congr {τ τ' : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ)
    (h : ∀ a, τ t a obs = τ' t a obs) :
    taggedStep τ t j obs = taggedStep τ' t j obs := by
  cases j with
  | inr done => rfl
  | inl j => simp only [taggedStep,h]

lemma frozen_success_bound_tagged (L : Learner d M T Ω) (ω : Ω) (hd : 3 ≤ d)
    (htrans : ∀ t j, AEMeasurable (L.transition t ω j) (observationReference d))
    {ε : ℝ} (hε : 0 < ε) {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let τ : ℕ → State M → (Vector d × ℝ) → Bool × State M := fun t j => (htrans t j).mk _
  have hτ (t : ℕ) (j : State M) : Measurable (τ t j) := (htrans t j).measurable_mk
  let μ := (uniformSphere d).prod (sampleLaw d T)
  have hgood : ∀ᵐ z ∂μ, ∀ t j (i : Fin T),
      L.transition t ω j (z.2 i,⟪z.1.val,z.2 i⟫) = τ t j (z.2 i,⟪z.1.val,z.2 i⟫) := by
    simp only [ae_all_iff]
    intro t j i
    exact (sphere_sample_observation_quasi (by simpa using hd) i).ae (htrans t j).ae_eq_mk
  let S := {z : UnitSphere d × Samples d T | dist z.1.val
    (L.taggedOutput ω (streamRoute (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω))
      (z.2,fun i => ⟪z.1.val,z.2 i⟫))).val ≤ ε}
  have hmono : {z : UnitSphere d × Samples d T | angularError z.1 (L.estimate z.1 ω z.2) ≤ ε}
      ≤ᵐ[μ] S := by
    filter_upwards [hgood] with z hz
    intro hs
    have he := streamRoute_congr (taggedStep (T := T) (fun t j => L.transition t ω j))
      (taggedStep (T := T) τ) 0 T (taggedStart (L.initialChoice ω)) z.2
      (fun i => ⟪z.1.val,z.2 i⟫) (fun t j i => taggedStep_congr t j _ (fun a => hz t a i))
    have hc : dist z.1.val (L.estimate z.1 ω z.2).val ≤ ε := by
      apply le_trans _ hs
      simpa only [angularError,dist_comm] using chord_le_arccos (L.estimate z.1 ω z.2) z.1
    change dist z.1.val _ ≤ ε
    rw [L.estimate_eq_taggedRoute,he] at hc
    exact hc
  apply (measure_mono_ae hmono).trans
  simpa only [S,μ,uniformSphere,sphereLaw,sampleLaw,finrank_euclideanSpace_fin] using
    route_cap_bound_ceil (measurable_taggedStep hτ) (fun j => (L.taggedOutput ω j).val)
      hε (by simpa using ha) hq hqa T (taggedStart (L.initialChoice ω))

lemma streaming_success_bound_tagged [MeasurableSpace Ω]
    (L : Learner d M T Ω) (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (hL : L.Admissible ρ) (hd : 3 ≤ d) {ε : ℝ} (hε : 0 < ε)
    {a q : ℕ} (ha : 2*a ≤ d-1) (hq : 2 ≤ q) (hqa : 2*q ≤ a) :
    L.uniformSuccess ρ ε ≤
      (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
        streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q) := by
  let : NeZero d := ⟨by omega⟩
  let : SigmaFinite (observationReference d) := by unfold observationReference; infer_instance
  have hω : ∀ᵐ ω ∂ρ, ∀ t j,
      AEMeasurable (L.transition t ω j) (observationReference d) := by
    simp only [ae_all_iff]
    intro t j
    exact ae_fiber_aemeasurable (hL.transition t j).prod_swap
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  let S := {z : UnitSphere d × (Ω × Samples d T) |
    angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε}
  have hS : NullMeasurableSet S ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    L.angularSuccess_nullMeasurable ρ ε hL
  have he := hp.measure_preimage hS
  have hb := prod_null_set_bound (hS.preimage hp.quasiMeasurePreserving)
    (c := (ENNReal.ofReal ((3 : ℝ)*4^d) * ENNReal.ofReal (ε^a)) *
      streamFactor (E := Vector d) (J := TaggedState M T) q ^ ((T+q-1)/q))
    (by
      filter_upwards [hω] with ω hω
      exact L.frozen_success_bound_tagged ω hd hω hε ha hq hqa)
  simpa only [he,measure_univ,mul_one,S,uniformSuccess] using hb

end Learner
end NoiselessRegression

end

end OAI
