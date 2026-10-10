import OAI.Probability.Ising.Basic

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- The four functions theorem preserves log-supermodularity under marginalization. -/
lemma jointWeight_logSupermodular {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a a' b b' : Spins n) :
    jointWeight G h I J F τ a b * jointWeight G h I J F τ a' b' ≤
      jointWeight G h I J F τ (a ⊓ a') (b ⊓ b') *
      jointWeight G h I J F τ (a ⊔ a') (b ⊔ b') := by
  classical
  unfold jointWeight constrainedSum
  apply four_functions_theorem_univ
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ
    dsimp only [Pi.zero_apply]
    split_ifs
    · exact (weight_pos G h σ).le
    · exact le_rfl
  · intro σ ρ
    dsimp only
    by_cases hσ : AgreesOn I σ a ∧ AgreesOn J σ b ∧ AgreesOn F σ τ
    · by_cases hρ : AgreesOn I ρ a' ∧ AgreesOn J ρ b' ∧ AgreesOn F ρ τ
      · have hmin : AgreesOn I (σ ⊓ ρ) (a ⊓ a') ∧
            AgreesOn J (σ ⊓ ρ) (b ⊓ b') ∧ AgreesOn F (σ ⊓ ρ) τ := by
          exact ⟨agreesOn_inf hσ.1 hρ.1, agreesOn_inf hσ.2.1 hρ.2.1,
            by simpa using agreesOn_inf hσ.2.2 hρ.2.2⟩
        have hmax : AgreesOn I (σ ⊔ ρ) (a ⊔ a') ∧
            AgreesOn J (σ ⊔ ρ) (b ⊔ b') ∧ AgreesOn F (σ ⊔ ρ) τ := by
          exact ⟨agreesOn_sup hσ.1 hρ.1, agreesOn_sup hσ.2.1 hρ.2.1,
            by simpa using agreesOn_sup hσ.2.2 hρ.2.2⟩
        simpa only [ite_eq_left hσ, ite_eq_left hρ, ite_eq_left hmin, ite_eq_left hmax] using
          weight_logSupermodular G h σ ρ
      · simp only [ite_eq_right hρ, mul_zero]
        apply mul_nonneg <;> split_ifs <;> first | exact (weight_pos G h _).le | exact le_rfl
    · simp only [ite_eq_right hσ, zero_mul]
      apply mul_nonneg <;> split_ifs <;> first | exact (weight_pos G h _).le | exact le_rfl

/-- The extreme-rectangle bound does not require the four configurations to be ordered. -/
lemma extreme_rectangle {A B : Type*} [PartialOrder A] [BoundedOrder A]
    [PartialOrder B] [BoundedOrder B] (f : A → B → ℝ)
    (hrect : ∀ u v s t, u ≤ v → s ≤ t → f u t + f v s ≤ f u s + f v t)
    (a a' : A) (b b' : B) :
    |f a b + f a' b' - f a b' - f a' b| ≤
      f ⊤ ⊤ + f ⊥ ⊥ - f ⊤ ⊥ - f ⊥ ⊤ := by
  apply abs_le.mpr
  constructor
  · have h₁ := hrect ⊥ a' ⊥ b' bot_le bot_le
    have h₂ := hrect a ⊤ b ⊤ le_top le_top
    have h₃ := hrect a' ⊤ ⊥ b le_top bot_le
    have h₄ := hrect ⊥ a b' ⊤ bot_le le_top
    linarith
  · have h₁ := hrect ⊥ a' ⊥ b bot_le bot_le
    have h₂ := hrect a ⊤ b' ⊤ le_top le_top
    have h₃ := hrect a' ⊤ ⊥ b' le_top bot_le
    have h₄ := hrect ⊥ a b ⊤ bot_le le_top
    linarith

/-- The extreme-rectangle bound for the arbitrary-field Ising marginal with common pins. -/
lemma marginal_extreme_rectangle {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a a' b b' : Spins n) :
    |Real.log (jointWeight G h I J F τ a b) +
        Real.log (jointWeight G h I J F τ a' b') -
        Real.log (jointWeight G h I J F τ a b') -
        Real.log (jointWeight G h I J F τ a' b)| ≤
      Real.log (jointWeight G h I J F τ ⊤ ⊤) +
        Real.log (jointWeight G h I J F τ ⊥ ⊥) -
        Real.log (jointWeight G h I J F τ ⊤ ⊥) -
        Real.log (jointWeight G h I J F τ ⊥ ⊤) := by
  apply extreme_rectangle (fun u v => Real.log (jointWeight G h I J F τ u v)) _ a a' b b'
  intro u v s t huv hst
  have H := jointWeight_logSupermodular G h I J F τ u v t s
  rw [inf_eq_left.mpr huv, sup_eq_right.mpr huv,
    inf_eq_right.mpr hst, sup_eq_left.mpr hst] at H
  have hp := jointWeight_pos G h I J F hIJ hIF hJF τ
  have HL := Real.log_le_log (mul_pos (hp u t) (hp v s)) H
  simpa only [Real.log_mul (hp u t).ne' (hp v s).ne',
    Real.log_mul (hp u s).ne' (hp v t).ne'] using HL

/-- A general normalization lemma. Rectangle control on unnormalized positive
weights bounds the ACTUAL normalized pointwise ratio, not merely its odds. -/
lemma normalized_ratio_of_rectangles {A B : Type*} [Fintype A]
    (p : A → B → ℝ) (hp : ∀ a b, 0 < p a b) (L : ℝ)
    (hrect : ∀ a a' b b',
      |Real.log (p a b) + Real.log (p a' b') - Real.log (p a b') -
        Real.log (p a' b)| ≤ L) (a : A) (b b' : B) :
    Real.exp (-L) ≤ (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ∧
      (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') ≤ Real.exp L := by
  classical
  have : Nonempty A := ⟨a⟩
  have hsum : ∀ c, 0 < ∑ x, p x c := fun c =>
    Finset.sum_pos (fun x _ => hp x c) Finset.univ_nonempty
  have hu : p a b * (∑ x, p x b') ≤ (Real.exp L * p a b') * ∑ x, p x b := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have H := (abs_le.mp (hrect a x b b')).2
    have H' : Real.log (p a b) + Real.log (p x b') ≤
        L + Real.log (p a b') + Real.log (p x b) := by linarith
    have H'' := Real.exp_le_exp.mpr H'
    simpa only [Real.exp_add, Real.exp_log (hp a b), Real.exp_log (hp x b'),
      Real.exp_log (hp a b'), Real.exp_log (hp x b)] using H''
  have hl : (Real.exp (-L) * p a b') * (∑ x, p x b) ≤ p a b * ∑ x, p x b' := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x _
    have H := (abs_le.mp (hrect a x b b')).1
    have H' : -L + Real.log (p a b') + Real.log (p x b) ≤
        Real.log (p a b) + Real.log (p x b') := by linarith
    have H'' := Real.exp_le_exp.mpr H'
    simpa only [Real.exp_add, Real.exp_log (hp a b), Real.exp_log (hp x b'),
      Real.exp_log (hp a b'), Real.exp_log (hp x b)] using H''
  have heq : (p a b / ∑ x, p x b) / (p a b' / ∑ x, p x b') =
      (p a b * ∑ x, p x b') / (p a b' * ∑ x, p x b) := by
    field_simp
  rw [heq]
  constructor
  · apply (le_div_iff₀ (mul_pos (hp a b') (hsum b))).mpr
    simpa only [mul_assoc] using hl
  · apply (div_le_iff₀ (mul_pos (hp a b') (hsum b))).mpr
    simpa only [mul_assoc] using hu

def restrictSpin {n : ℕ} (I : Finset (Fin n)) (σ : Spins n) : I → Bool := fun v => σ v.val

def extendSpin {n : ℕ} (I : Finset (Fin n)) (a : I → Bool) : Spins n :=
  fun v => if hv : v ∈ I then a ⟨v, hv⟩ else false

@[simp] lemma restrict_extend {n : ℕ} (I : Finset (Fin n)) (a : I → Bool) :
    restrictSpin I (extendSpin I a) = a := by
  funext v
  simp [restrictSpin, extendSpin, v.property]

lemma agreesOn_iff_restrict_eq {n : ℕ} (I : Finset (Fin n)) (σ a : Spins n) :
    AgreesOn I σ a ↔ restrictSpin I σ = restrictSpin I a := by
  constructor
  · intro H
    funext v
    exact H v.val v.property
  · intro H v hv
    exact congrFun H ⟨v, hv⟩

lemma jointWeight_extend_restrict {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ a b : Spins n) :
    jointWeight G h I J F τ (extendSpin I (restrictSpin I a)) b =
      jointWeight G h I J F τ a b := by
  simp only [jointWeight, constrainedSum, agreesOn_iff_restrict_eq, restrict_extend]

lemma sum_jointWeight_eq_denominator {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ b : Spins n) :
    (∑ a : I → Bool, jointWeight G h I J F τ (extendSpin I a) b) =
      constrainedSum G h (fun σ => AgreesOn J σ b ∧ AgreesOn F σ τ) := by
  classical
  unfold jointWeight constrainedSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  by_cases hσ : AgreesOn J σ b ∧ AgreesOn F σ τ
  · simp only [hσ, and_true, ite_true]
    simp only [agreesOn_iff_restrict_eq, restrict_extend]
    simp
  · simp only [hσ, and_false, ite_false, Finset.sum_const_zero]

noncomputable def extremeLogOdds {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n)) (τ : Spins n) : ℝ :=
  Real.log (jointWeight G h I J F τ ⊤ ⊤) +
    Real.log (jointWeight G h I J F τ ⊥ ⊥) -
    Real.log (jointWeight G h I J F τ ⊤ ⊥) -
    Real.log (jointWeight G h I J F τ ⊥ ⊤)

/-- The normalized conditional probability ratio is bounded by the extreme log odds. -/
lemma conditional_ratio_extreme {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ a b b' : Spins n) :
    Real.exp (-extremeLogOdds G h I J F τ) ≤
        conditionalProb G h I J F a b τ / conditionalProb G h I J F a b' τ ∧
      conditionalProb G h I J F a b τ / conditionalProb G h I J F a b' τ ≤
        Real.exp (extremeLogOdds G h I J F τ) := by
  have H := normalized_ratio_of_rectangles
    (fun (α : I → Bool) β => jointWeight G h I J F τ (extendSpin I α) β)
    (fun α β => jointWeight_pos G h I J F hIJ hIF hJF τ (extendSpin I α) β)
    (extremeLogOdds G h I J F τ)
    (fun α α' β β' => marginal_extreme_rectangle G h I J F hIJ hIF hJF τ
      (extendSpin I α) (extendSpin I α') β β')
    (restrictSpin I a) b b'
  simp only [sum_jointWeight_eq_denominator, jointWeight_extend_restrict] at H
  simpa only [jointWeight, conditionalProb] using H

lemma conditionalProb_pos {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (a b τ : Spins n) : 0 < conditionalProb G h I J F a b τ := by
  apply div_pos (jointWeight_pos G h I J F hIJ hIF hJF τ a b)
  apply constrainedSum_pos G h _ (fun v => if v ∈ J then b v else τ v)
  constructor
  · intro v hv
    simp [hv]
  · intro v hv
    have hvJ : v ∉ J := fun hvJ => Finset.disjoint_left.mp hJF hvJ hv
    simp [hvJ]

lemma positive_average {B : Type*} [Fintype B] (p μ : B → ℝ)
    (hp : ∀ b, 0 < p b) (hμ : ∀ b, 0 ≤ μ b) (hμsum : ∑ b, μ b = 1) :
    0 < ∑ b, μ b * p b := by
  classical
  have hex : ∃ b, 0 < μ b := by
    by_contra hn
    push Not at hn
    have hz : ∀ b, μ b = 0 := fun b => le_antisymm (hn b) (hμ b)
    simp [hz] at hμsum
  obtain ⟨b, hb⟩ := hex
  exact lt_of_lt_of_le (mul_pos hb (hp b))
    (Finset.single_le_sum (fun c _ => mul_nonneg (hμ c) (hp c).le) (Finset.mem_univ b))

/-- Multiplicative pointwise control survives arbitrary mixtures on both
sides. The proof uses the original constants without a second loss. -/
lemma mixture_ratio_of_pointwise {B : Type*} [Fintype B]
    (p : B → ℝ) (hp : ∀ b, 0 < p b) (L U : ℝ)
    (hbound : ∀ b b', L ≤ p b / p b' ∧ p b / p b' ≤ U)
    (μ ν : B → ℝ) (hμ : ∀ b, 0 ≤ μ b) (hν : ∀ b, 0 ≤ ν b)
    (hμsum : ∑ b, μ b = 1) (hνsum : ∑ b, ν b = 1) :
    L ≤ (∑ b, μ b * p b) / (∑ b, ν b * p b) ∧
      (∑ b, μ b * p b) / (∑ b, ν b * p b) ≤ U := by
  have havg := positive_average p ν hp hν hνsum
  have honeL : ∀ b, L * (∑ c, ν c * p c) ≤ p b := by
    intro b
    calc
      L * (∑ c, ν c * p c) = ∑ c, ν c * (L * p c) := by
        simp only [Finset.mul_sum]; congr 1; ext c; ring
      _ ≤ ∑ c, ν c * p b := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (hp c)).mp (hbound b c).1) (hν c)
      _ = p b := by rw [← Finset.sum_mul, hνsum, one_mul]
  have honeU : ∀ b, p b ≤ U * (∑ c, ν c * p c) := by
    intro b
    calc
      p b = ∑ c, ν c * p b := by rw [← Finset.sum_mul, hνsum, one_mul]
      _ ≤ ∑ c, ν c * (U * p c) := Finset.sum_le_sum fun c _ =>
        mul_le_mul_of_nonneg_left ((div_le_iff₀ (hp c)).mp (hbound b c).2) (hν c)
      _ = U * (∑ c, ν c * p c) := by
        simp only [Finset.mul_sum]; congr 1; ext c; ring
  constructor
  · apply (le_div_iff₀ havg).mpr
    calc
      _ = ∑ b, μ b * (L * ∑ c, ν c * p c) := by
        rw [← Finset.sum_mul, hμsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (honeL b) (hμ b)
  · apply (div_le_iff₀ havg).mpr
    calc
      _ ≤ ∑ b, μ b * (U * ∑ c, ν c * p c) :=
        Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (honeU b) (hμ b)
      _ = _ := by rw [← Finset.sum_mul, hμsum, one_mul]

lemma mixture_ratio_extreme {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (a τ : Spins n) (mix mix' : Spins n → ℝ)
    (hmix : ∀ b, 0 ≤ mix b) (hmix' : ∀ b, 0 ≤ mix' b)
    (hmixsum : ∑ b, mix b = 1) (hmix'sum : ∑ b, mix' b = 1) :
    Real.exp (-extremeLogOdds G h I J F τ) ≤
        mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ∧
      mixtureProb G h I J F a τ mix / mixtureProb G h I J F a τ mix' ≤
        Real.exp (extremeLogOdds G h I J F τ) :=
  mixture_ratio_of_pointwise
    (fun b => conditionalProb G h I J F a b τ)
    (fun b => conditionalProb_pos G h I J F hIJ hIF hJF a b τ) _ _
    (fun b b' => conditional_ratio_extreme G h I J F hIJ hIF hJF τ a b b')
    mix mix' hmix hmix' hmixsum hmix'sum

lemma extremeLogOdds_nonneg {n m : ℕ} (G : FiniteGraph n m)
    (h : Fin n → ℝ) (I J F : Finset (Fin n))
    (hIJ : Disjoint I J) (hIF : Disjoint I F) (hJF : Disjoint J F)
    (τ : Spins n) : 0 ≤ extremeLogOdds G h I J F τ := by
  exact (abs_nonneg _).trans
    (marginal_extreme_rectangle G h I J F hIJ hIF hJF τ ⊤ ⊥ ⊤ ⊥)

end BufferedIsing

end OAI
