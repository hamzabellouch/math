import OAI.Probability.ProjectionMoments.Realization

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

lemma capWeight_mass_mixed (y : E) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (a : ℕ) {b : ℝ} (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ)) :
    PolynomialMass ((ambientSphereLaw (E := E)).withDensity (capWeight y ε)) a
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) := by
  change PolynomialMass ((ambientSphereLaw (E := E)).withDensity ((Metric.closedBall y ε).indicator 1)) a _
  rw [withDensity_indicator_one Metric.isClosed_closedBall.measurableSet]
  intro z r hr
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet]
  by_cases h : r ≤ ε
  · apply (measure_mono Set.inter_subset_left).trans
    apply (ambientSphereLaw_closedBall z hr (Module.finrank ℝ E-1) le_rfl).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hpow : r^(Module.finrank ℝ E-1) ≤ r^((a:ℝ)+b) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hr (h.trans hε1) hab
    apply hpow.trans
    rw [Real.rpow_add hr,Real.rpow_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hr.le h hb) (pow_nonneg hr.le _)
  · apply (measure_mono Set.inter_subset_right).trans
    apply (ambientSphereLaw_closedBall y hε (Module.finrank ℝ E-1) le_rfl).trans
    rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
    apply mul_le_mul' le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hpow : ε^(Module.finrank ℝ E-1) ≤ ε^((a:ℝ)+b) := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hε hε1 hab
    apply hpow.trans
    rw [Real.rpow_add hε,Real.rpow_natCast,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le (le_of_not_ge h) a) (Real.rpow_nonneg hε.le _)

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

lemma continuation_mixed_integral_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : ℕ → J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    (∫⁻ s, continuation δ (fun n j => capWeight (y n j) ε) n k j s ∂ambientSphereLaw) ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
        streamFactor (E := E) (J := J) q ^ ((k+q-1)/q) := by
  have ha : a ≤ Module.finrank ℝ E := by
    have : (a:ℝ) ≤ (Module.finrank ℝ E:ℝ) := by
      have hh : ((Module.finrank ℝ E-1:ℕ):ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast Nat.sub_le (Module.finrank ℝ E) 1
      linarith
    exact_mod_cast this
  apply ambient_mass_bound
  apply continuation_mass_bound_ceil _ hδ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity)) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    (fun n j => capWeight_mass_mixed (y n j) hε hε1 a hb hab)
    (Module.finrank_pos (R := ℝ) (M := E)) ha hq hqa

lemma route_mixed_bound {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (y : J → E)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (Module.finrank ℝ E-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (k : ℕ) (j : J) :
    ((sphereLaw (E := E)).prod (Measure.pi (fun _ : Fin k => stdGaussian E)))
      {z | dist z.1.val (y (streamRoute δ 0 k j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε} ≤
      (ENNReal.ofReal ((3 : ℝ)*4^Module.finrank ℝ E) * ENNReal.ofReal (ε^b)) *
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
  exact continuation_mixed_integral_bound hδ (fun _ => y) hε hε1 hb hab hq hqa 0 k j

end

namespace Learner

section
variable {d M : ℕ}

def haltShift {k : ℕ} : TaggedState M k → TaggedState M (k+1)
  | .inl j => .inl j
  | .inr (t,j) => .inr (t.succ,j)

def haltRoute (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M) (n : ℕ) :
    (k : ℕ) → State M → ((Fin k → Vector d) × (Fin k → ℝ)) → TaggedState M k
  | 0, j, _ => .inl j
  | k+1, j, X =>
    let a := τ (n+1) j (X.1 0,X.2 0)
    if a.1 then .inr (⟨1,by omega⟩,a.2)
    else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))

lemma measurable_haltRoute {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (n k : ℕ) (j : State M) :
    Measurable (haltRoute τ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    let h : (Bool × State M) → ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) → TaggedState M (k+1) :=
      fun a X => if a.1 then .inr (⟨1,by omega⟩,a.2)
        else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))
    change Measurable (fun X => h (τ (n+1) j (X.1 0,X.2 0)) X)
    apply measurable_select (J := Bool × State M) _ ((hτ (n+1) j).comp (by fun_prop))
    intro a
    dsimp [h]
    split_ifs
    · exact measurable_const
    · exact (measurable_of_finite haltShift).comp ((ih (n+1) a.2).comp (by
        change Measurable (fun X : ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) =>
          ((fun i : Fin k => X.1 i.succ),(fun i : Fin k => X.2 i.succ)))
        fun_prop))

def haltChild (w : ℕ → State M → Vector d → ℝ≥0∞)
    (v : State M → Vector d → ℝ≥0∞) (n : ℕ) {k : ℕ} : TaggedState M k → Vector d → ℝ≥0∞
  | .inl j => v j
  | .inr (t,j) => w (n+t) j

def stoppedContinuation (τ : ℕ → State M → (Vector d × ℝ) → Bool × State M)
    (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : ℕ → State M → Vector d → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, let a := τ (n+1) j (x,⟪s,x⟫)
      if a.1 then w (n+1) a.2 s else stoppedContinuation τ w (n+1) k a.2 s ∂stdGaussian (Vector d)

lemma measurable_stoppedContinuation {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : State M) :
    Measurable (stoppedContinuation τ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    change Measurable (fun z : Vector d × Vector d =>
      if (τ (n+1) j (z.1,⟪z.2,z.1⟫)).1 then w (n+1) (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2
      else stoppedContinuation τ w (n+1) k (τ (n+1) j (z.1,⟪z.2,z.1⟫)).2 z.2)
    apply measurable_select (J := Bool × State M) (h := fun a (z : Vector d × Vector d) =>
      if a.1 then w (n+1) a.2 z.2 else stoppedContinuation τ w (n+1) k a.2 z.2) _
      ((hτ (n+1) j).comp (by fun_prop))
    intro a
    split_ifs
    · exact (hw (n+1) a.2).comp measurable_snd
    · exact (ih (n+1) a.2).comp measurable_snd

lemma stoppedContinuation_le_one
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih =>
    change (∫⁻ x, (if (τ (n+1) j (x,⟪s,x⟫)).1 then w (n+1) (τ (n+1) j (x,⟪s,x⟫)).2 s else stoppedContinuation τ w (n+1) k (τ (n+1) j (x,⟪s,x⟫)).2 s) ∂stdGaussian (Vector d)) ≤ 1
    apply (lintegral_mono (g := fun _ => (1:ℝ≥0∞)) (fun x => ?_)).trans_eq (by simp)
    split_ifs
    · exact hw _ _ _
    · exact ih _ _

lemma stoppedContinuation_unroll
    {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (n m k : ℕ) (j : State M) (s : Vector d) :
    stoppedContinuation τ w n (m+k) j s =
      blockValue (haltChild w (stoppedContinuation τ w (n+m) k) n) (haltRoute τ n m j) s := by
  induction m generalizing n j with
  | zero => simp [blockValue,haltRoute,haltChild]
  | succ m ih =>
    rw [Nat.succ_add,stoppedContinuation]
    unfold blockValue
    have hf : Measurable (fun X : Fin (m+1) → Vector d =>
        haltChild w (stoppedContinuation τ w (n+(m+1)) k) n
          (haltRoute τ n (m+1) j (X,fun i => ⟪s,X i⟫)) s) :=
      (measurable_of_finite (fun a => haltChild w (stoppedContinuation τ w (n+(m+1)) k) n a s)).comp
        ((measurable_haltRoute hτ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    have htail (X : Fin m → Vector d) : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x X : Fin (m+1) → Vector d) i⟫) = (fun i => ⟪s,X i⟫) := by funext i; rfl
    simp only [haltRoute,Fin.cons_zero,Fin.tail_cons,htail]
    split_ifs with h
    · simp [haltChild]
    · rw [ih]
      unfold blockValue
      apply lintegral_congr
      intro X
      have h1 : n+(m+1) = n+1+m := by omega
      rw [h1]
      generalize haltRoute τ (n+1) m (τ (n+1) j (x,⟪s,x⟫)).2 (X,fun i => ⟪s,X i⟫) = a
      cases a with
      | inl j => rfl
      | inr done =>
        simp only [haltShift,haltChild,Fin.val_succ]
        rw [show n+1+done.1.val = n+(done.1.val+1) by omega]

lemma stoppedContinuation_mass_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (n k : ℕ) (j : State M) :
    PolynomialMass (ambientSphereLaw.withDensity (stoppedContinuation τ w n k j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((k+q-1)/q)) := by
  let : NeZero d := ⟨by omega⟩
  let K := streamFactor (E := Vector d) (J := TaggedState M q) q
  have hK1 : 1 ≤ K := one_le_streamFactor (by omega)
  have hK0 : K ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt : K ≠ ∞ := streamFactor_ne_top _
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
  have hq0 : 0 < q := by omega
  change PolynomialMass _ a (C*K^_)
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk0 : k = 0
    · subst k
      simpa only [Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q),pow_zero,mul_one,stoppedContinuation] using hlocal n j
    let m := min k q
    have hm0 : 0 < m := by dsimp [m]; omega
    have hm : m ≤ q := min_le_right _ _
    have hmk : m ≤ k := min_le_left _ _
    have hki : k-m < k := by omega
    let C' := C*K^((k-m+q-1)/q)
    have hC' : C' ≠ 0 := mul_ne_zero hC (pow_ne_zero _ hK0)
    have hC't : C' ≠ ∞ := ENNReal.mul_ne_top hCt (ENNReal.pow_ne_top hKt)
    have hCC' : C ≤ C' := le_mul_of_one_le_right' (one_le_pow₀ hK1)
    let f := haltChild w (stoppedContinuation τ w (n+m) (k-m)) n (k := m)
    have hf (a : TaggedState M m) : Measurable (f a) := by
      cases a with
      | inl j => exact measurable_stoppedContinuation hτ hw _ _ _
      | inr done => exact hw _ _
    have hf1 (a : TaggedState M m) (s : Vector d) : f a s ≤ 1 := by
      cases a with
      | inl j => exact stoppedContinuation_le_one hw1 _ _ _ _
      | inr done => exact hw1 _ _ _
    have hflocal (a' : TaggedState M m) : PolynomialMass (ambientSphereLaw.withDensity (f a')) a C' := by
      cases a' with
      | inl j => exact ih (k-m) hki (n+m) j
      | inr done =>
        intro z r hr
        exact (hlocal (n+done.1) done.2 z r hr).trans (mul_le_mul' hCC' le_rfl)
    have hb := blockValue_mass_bound ambientSphereLaw hf hf1 hflocal hC' hC't
      (by simpa using hd) (by simpa using ha) (by simpa using (show m ≤ d by omega))
      (by omega : 1 ≤ q-1) (by omega : q-1+m ≤ a) (measurable_haltRoute hτ n m j)
    have he : stoppedContinuation τ w n k j = blockValue f (haltRoute τ n m j) := by
      funext s
      simpa [f,Nat.add_sub_of_le hmk] using stoppedContinuation_unroll hτ n m (k-m) j s
    rw [he]
    intro z r hr
    apply (hb z r hr).trans
    apply mul_le_mul' _ le_rfl
    have hdiv : (k+q-1)/q = (k-m+q-1)/q+1 := by
      by_cases hqk : q ≤ k
      · have hme : m = q := min_eq_right hqk
        rw [hme]
        have he : k+q-1 = q+(k-q+q-1) := by omega
        rw [he,Nat.add_div_left _ hq0]
      · have hme : m = k := min_eq_left (by omega)
        rw [hme,Nat.sub_self,Nat.zero_add,Nat.div_eq_of_lt (by omega : q-1 < q)]
        have he : k+q-1 = q+(k-1) := by omega
        rw [he,Nat.add_div_left _ hq0,Nat.div_eq_of_lt (by omega : k-1 < q)]
    rw [hden]
    have hcard : (Fintype.card (TaggedState M m):ℝ≥0∞)^(1/(q:ℝ)) ≤
        (Fintype.card (TaggedState M q):ℝ≥0∞)^(1/(q:ℝ)) := by
      apply ENNReal.rpow_le_rpow _ (by positivity)
      exact_mod_cast (show Fintype.card (TaggedState M m) ≤ Fintype.card (TaggedState M q) by
        rw [card_taggedState,card_taggedState]
        exact Nat.mul_le_mul_right _ (Nat.add_le_add_right hm 2))
    calc
      _ ≤ K*C' := mul_le_mul' (mul_le_mul' le_rfl hcard) le_rfl
      _ = _ := by rw [hdiv,pow_succ]; dsimp [C']; ring

end

variable {d M T : ℕ}

def taggedWeight (w : ℕ → State M → Vector d → ℝ≥0∞) (n : ℕ) : TaggedState M T → Vector d → ℝ≥0∞
  | .inl j => w n j
  | .inr (t,j) => w t j

lemma measurable_taggedWeight {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hw : ∀ n j, Measurable (w n j)) (n : ℕ) (j : TaggedState M T) :
    Measurable (taggedWeight w n j) := by cases j <;> exact hw _ _

lemma continuation_tagged_eq {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by
  induction k generalizing n j with
  | zero => cases j <;> rfl
  | succ k ih =>
    cases j with
    | inl j =>
      simp only [continuation,stoppedContinuation]
      apply lintegral_congr
      intro x
      rw [ih (n+1) (by omega)]
      simp only [taggedStep,dite_eq_left (by omega : n+1 ≤ T)]
      split_ifs <;> rfl
    | inr done =>
      simp only [continuation,taggedStep]
      simp only [ih (n+1) (by omega),lintegral_const,measure_univ,mul_one]

lemma tagged_continuation_mass {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (hτ : ∀ t j, Measurable (τ t j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (ambientSphereLaw.withDensity (w n j)) a C)
    (hd : 1 ≤ d) (ha : a ≤ d) (hq : 2 ≤ q) (hqa : 2*q ≤ a)
    (j : TaggedState M T) :
    PolynomialMass (ambientSphereLaw.withDensity
      (continuation (taggedStep τ) (taggedWeight w) 0 T j)) a
      (C * streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q)) := by
  have he := fun s => continuation_tagged_eq (τ := τ) (w := w) 0 T (by omega) j s
  cases j with
  | inl j =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inl j) = stoppedContinuation τ w 0 T j :=
      funext he
    rw [he']
    exact stoppedContinuation_mass_bound hτ hw hw1 hC hCt hlocal hd ha hq hqa 0 T j
  | inr done =>
    have he' : continuation (taggedStep (T := T) τ) (taggedWeight w) 0 T (.inr done) = w done.1 done.2 :=
      funext he
    rw [he']
    intro z r hr
    apply (hlocal _ _ z r hr).trans
    apply mul_le_mul' _ le_rfl
    exact le_mul_of_one_le_right' (one_le_pow₀ (one_le_streamFactor (by omega)))

variable [NeZero d]

lemma stopped_route_mixed_bound {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (y : ℕ → State M → Vector d)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {a q : ℕ} {b : ℝ}
    (hb : 0 ≤ b) (hab : (a:ℝ)+b ≤ (d-1:ℕ))
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (j : TaggedState M T) :
    ((uniformSphere d).prod (sampleLaw d T))
      {z | dist z.1.val
        (match streamRoute (taggedStep (T := T) τ) 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫) with
        | .inl a => y T a
        | .inr (t,a) => y t a) ≤ ε} ≤
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) *
        streamFactor (E := Vector d) (J := TaggedState M q) q ^ ((T+q-1)/q) := by
  let w : ℕ → State M → Vector d → ℝ≥0∞ := fun n j => capWeight (y n j) ε
  let δ := taggedStep (T := T) τ
  let w' : ℕ → TaggedState M T → Vector d → ℝ≥0∞ := taggedWeight w
  let yy : TaggedState M T → Vector d := fun a => match a with
    | .inl a => y T a
    | .inr (t,a) => y t a
  have hw' (n : ℕ) (a : TaggedState M T) : Measurable (w' n a) :=
    measurable_taggedWeight (fun n j => measurable_capWeight _ _) n a
  have hδ := measurable_taggedStep (T := T) hτ
  have hV := measurable_continuation hδ hw' 0 T j
  have he (s : Vector d) : continuation δ w' 0 T j s =
      ∫⁻ A : Fin T → Vector d, capWeight (yy (streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫))) ε s
        ∂Measure.pi (fun _ => stdGaussian (Vector d)) := by
    have hu := continuation_unroll (w := w') hδ 0 T 0 j s
    simp only [Nat.add_zero,continuation] at hu
    rw [hu]
    unfold blockValue
    apply lintegral_congr
    intro A
    cases streamRoute δ 0 T j (A,fun i => ⟪s,A i⟫) <;> simp [w',w,yy,taggedWeight]
  let S : Set (UnitSphere d × Samples d T) :=
    {z | dist z.1.val (yy (streamRoute δ 0 T j (z.2,fun i => ⟪z.1.val,z.2 i⟫))) ≤ ε}
  have hS : MeasurableSet S := by
    apply measurableSet_le _ measurable_const
    exact (measurable_subtype_coe.comp measurable_fst).dist
      ((measurable_of_finite yy).comp ((measurable_streamRoute hδ 0 T j).comp (by fun_prop)))
  change ((sphereLaw (E := Vector d)).prod _) S ≤ _
  rw [← one_mul (((sphereLaw (E := Vector d)).prod _) S), ← lintegral_indicator_const hS 1,
    lintegral_prod _ (measurable_const.indicator hS).aemeasurable]
  have hf : ∀ s : UnitSphere d,
      (∫⁻ A, S.indicator (fun _ => (1:ℝ≥0∞)) (s,A) ∂sampleLaw d T) = continuation δ w' 0 T j s.val := by
    intro s
    rw [he]
    apply lintegral_congr
    intro A
    classical
    change (if dist s.val (yy (streamRoute δ 0 T j (A,fun i => ⟪s.val,A i⟫))) ≤ ε then 1 else 0) = _
    unfold capWeight
    rw [Set.indicator_apply]
    rfl
  simp_rw [hf]
  rw [← lintegral_map hV measurable_subtype_coe]
  apply ambient_mass_bound (a := a)
  have ha : a ≤ d := by
    have hdn : ((d-1:ℕ):ℝ) ≤ (d:ℝ) := by exact_mod_cast Nat.sub_le d 1
    have : (a:ℝ) ≤ d := by linarith
    exact_mod_cast this
  have hl (n : ℕ) (j : State M) : PolynomialMass (ambientSphereLaw.withDensity (w n j)) a
      (ENNReal.ofReal ((3:ℝ)*4^d)*ENNReal.ofReal (ε^b)) := by
    simpa only [finrank_euclideanSpace_fin] using capWeight_mass_mixed (y n j) hε hε1 a hb (by simpa using hab)
  exact tagged_continuation_mass hτ (fun n j => measurable_capWeight _ _)
    (fun n j s => capWeight_le_one _ _ _)
    (mul_ne_zero (by positivity) (by positivity))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    hl
    (Nat.pos_of_ne_zero (NeZero.ne d)) ha hq hqa j

end Learner
end NoiselessRegression

end

end OAI
