import OAI.Probability.PosteriorReplicas.Regression.ProjectionBlocks

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
noncomputable section
universe u
namespace PosteriorRegression
open scoped Topology
open InnerProductSpace
open scoped Pointwise
section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_cons (ν : Measure E) [SigmaFinite ν] {n : ℕ}
    (f : (Fin (n+1) → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ v, f v ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, ∫⁻ v : Fin n → E, f (Fin.cons x v) ∂Measure.pi (fun _ => ν) ∂ν := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) (0 : Fin (n+1))).symm
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f, lintegral_prod]
  · congr 1
    ext x
    congr 1
    ext v
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    simp
  · exact (hf.comp hp.measurable).aemeasurable

def streamRoute (δ : ℕ → J → (E × ℝ) → J) (n : ℕ) :
    (k : ℕ) → J → ((Fin k → E) × (Fin k → ℝ)) → J
  | 0, j, _ => j
  | k+1, j, x => streamRoute δ (n+1) k (δ (n+1) j (x.1 0, x.2 0)) (Fin.tail x.1, Fin.tail x.2)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma measurable_streamRoute {δ : ℕ → J → (E × ℝ) → J}
    (hδ : ∀ n j, Measurable (δ n j)) (n k : ℕ) (j : J) :
    Measurable (streamRoute δ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) => streamRoute δ (n+1) k (δ (n+1) j (x.1 0,x.2 0)) (Fin.tail x.1,Fin.tail x.2))
    have ht : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        (Fin.tail x.1, Fin.tail x.2)) := by
      change Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        ((fun i : Fin k => x.1 i.succ), (fun i : Fin k => x.2 i.succ)))
      fun_prop
    have hd : Measurable (fun x : (Fin (k+1) → E) × (Fin (k+1) → ℝ) =>
        δ (n+1) j (x.1 0,x.2 0)) := (hδ (n+1) j).comp (by fun_prop)
    exact measurable_select (fun a => (ih (n+1) a).comp ht) hd

def continuation (δ : ℕ → J → (E × ℝ) → J) (w : ℕ → J → E → ℝ≥0∞)
    (n : ℕ) : ℕ → J → E → ℝ≥0∞
  | 0, j, s => w n j s
  | k+1, j, s => ∫⁻ x, continuation δ w (n+1) k (δ (n+1) j (x, ⟪s,x⟫)) s ∂stdGaussian E

lemma measurable_continuation {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j)) (n k : ℕ) (j : J) :
    Measurable (continuation δ w n k j) := by
  induction k generalizing n j with
  | zero => exact hw n j
  | succ k ih =>
    apply Measurable.lintegral_prod_left
    exact measurable_select (fun a => (ih (n+1) a).comp measurable_snd)
      ((hδ (n+1) j).comp (by fun_prop))

omit [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [BorelSpace E] in
lemma continuation_le_one {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hw : ∀ n j s, w n j s ≤ 1) (n k : ℕ) (j : J) (s : E) :
    continuation δ w n k j s ≤ 1 := by
  induction k generalizing n j with
  | zero => exact hw n j s
  | succ k ih => exact (lintegral_mono (fun x => ih _ _)).trans_eq (by simp)

lemma continuation_unroll {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j))
    (n m k : ℕ) (j : J) (s : E) :
    continuation δ w n (m+k) j s =
      blockValue (fun a => continuation δ w (n+m) k a) (streamRoute δ n m j) s := by
  induction m generalizing n j with
  | zero =>
    simp [blockValue, streamRoute]
  | succ m ih =>
    rw [Nat.succ_add, continuation]
    simp_rw [ih]
    unfold blockValue
    have hf : Measurable (fun A : Fin (m+1) → E =>
        continuation δ w (n+(m+1)) k (streamRoute δ n (m+1) j (A,fun i => ⟪s,A i⟫)) s) := by
      exact (measurable_of_finite (fun a => continuation δ w (n+(m+1)) k a s)).comp
        ((measurable_streamRoute hδ n (m+1) j).comp (by fun_prop))
    rw [lintegral_pi_cons _ _ hf]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro A
    have he : Fin.tail (fun i : Fin (m+1) => ⟪s,(Fin.cons x A : Fin (m+1) → E) i⟫) = (fun i => ⟪s,A i⟫) := by
      ext i
      simp [Fin.tail]
    simp [streamRoute, he, Nat.add_left_comm, Nat.add_comm]

def streamFactor (q : ℕ) : ℝ≥0∞ :=
  (32768 : ℝ≥0∞)^Module.finrank ℝ E * (Fintype.card J : ℝ≥0∞)^(1/(q : ℝ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamFactor_ne_top (q : ℕ) : streamFactor (E := E) (J := J) q ≠ ∞ := by
  exact ENNReal.mul_ne_top (by simp) (ENNReal.rpow_ne_top_of_nonneg (by positivity) (by simp))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma one_le_streamFactor [Nonempty J] {q : ℕ} (hq : 0 < q) :
    1 ≤ streamFactor (E := E) (J := J) q := by
  apply one_le_mul (one_le_pow₀ (by norm_num))
  exact ENNReal.one_le_rpow (by exact_mod_cast Fintype.card_pos (α := J)) (by positivity)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma PolynomialMass.mono {μ : Measure E} {a : ℕ} {C D : ℝ≥0∞}
    (h : PolynomialMass μ a C) (hCD : C ≤ D) : PolynomialMass μ a D :=
  fun z r hr => (h z r hr).trans (mul_le_mul' hCD le_rfl)

lemma continuation_mass_bound [Nonempty J] (μ : Measure E) [IsFiniteMeasure μ]
    {δ : ℕ → J → (E × ℝ) → J} {w : ℕ → J → E → ℝ≥0∞}
    (hδ : ∀ n j, Measurable (δ n j)) (hw : ∀ n j, Measurable (w n j))
    (hw1 : ∀ n j s, w n j s ≤ 1)
    {a q : ℕ} {C : ℝ≥0∞} (hC : C ≠ 0) (hCt : C ≠ ∞)
    (hlocal : ∀ n j, PolynomialMass (μ.withDensity (w n j)) a C)
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E)
    (hq : 2 ≤ q) (hqa : 2*q ≤ a) (n k : ℕ) (j : J) :
    PolynomialMass (μ.withDensity (continuation δ w n k j)) a
      (C * streamFactor (E := E) (J := J) q ^ (k/q+1)) := by
  have hden : ((q-1 : ℕ) : ℝ)+1 = (q : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
    ring
  have hq0 : 0 < q := by omega
  have hK1 := one_le_streamFactor (E := E) (J := J) hq0
  have hK0 : streamFactor (E := E) (J := J) q ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hK1)
  have hKt := streamFactor_ne_top (E := E) (J := J) q
  induction k using Nat.strong_induction_on generalizing n j with
  | h k ih =>
    by_cases hk : q ≤ k
    · have hki : k-q < k := by omega
      have hC1 : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ 0 :=
        mul_ne_zero hC (pow_ne_zero _ hK0)
      have hC1t : C * streamFactor (E := E) (J := J) q ^ ((k-q)/q+1) ≠ ∞ :=
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
      have hdiv : k/q = (k-q)/q+1 := by
        conv_lhs => rw [← Nat.add_sub_of_le hk]
        exact Nat.add_div_left _ hq0
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
      rw [hden, ← streamFactor, Nat.div_eq_of_lt (by omega : k < q)]
      simp [mul_comm]

lemma fin_tail_snoc {X : Type*} {k : ℕ} (A : Fin (k+1) → X) (x : X) :
    Fin.tail (Fin.snoc A x : Fin (k+2) → X) =
      (Fin.snoc (Fin.tail A : Fin k → X) x : Fin (k+1) → X) := by
  rw [← Fin.cons_self_tail A, ← Fin.cons_snoc_eq_snoc_cons, Fin.tail_cons, Fin.tail_cons]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] in
lemma streamRoute_snoc (δ : ℕ → J → (E × ℝ) → J) (n k : ℕ) (j : J)
    (A : Fin k → E) (b : Fin k → ℝ) (x : E) (y : ℝ) :
    streamRoute δ n (k+1) j (Fin.snoc A x, Fin.snoc b y) =
      δ (n+k+1) (streamRoute δ n k j (A,b)) (x,y) := by
  induction k generalizing n j with
  | zero => simp [streamRoute, Fin.snoc_zero]
  | succ k ih =>
    rw [streamRoute]
    simp only [Fin.snoc_apply_zero, fin_tail_snoc]
    rw [ih, streamRoute]
    congr 1; omega

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
lemma lintegral_pi_prefix (ν : Measure E) [IsProbabilityMeasure ν] {t T : ℕ} (ht : t ≤ T)
    (f : (Fin t → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin T → E, f (fun i => x (Fin.castLE ht i)) ∂Measure.pi (fun _ => ν)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ => ν) := by
  induction T with
  | zero =>
    have : t = 0 := by omega
    subst t
    rfl
  | succ T ih =>
    by_cases h : t ≤ T
    · have he (x : Fin T → E) (y : E) :
          (fun i : Fin t => (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE ht i)) =
            (fun i : Fin t => x (Fin.castLE h i)) := by
        ext i
        change (Fin.snoc x y : Fin (T+1) → E) (Fin.castLE h i).castSucc = _
        exact Fin.snoc_castSucc _ _ _
      rw [lintegral_pi_snoc ν (fun x : Fin (T+1) → E => f (fun i => x (Fin.castLE ht i)))
        (hf.comp (by fun_prop))]
      simp_rw [he, lintegral_const, measure_univ, mul_one]
      exact ih h
    · have he : t = T+1 := by omega
      subst t
      rfl

end StreamAux

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

end PosteriorRegression
end

end OAI
