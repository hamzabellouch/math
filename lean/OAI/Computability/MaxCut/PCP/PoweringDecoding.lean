import Mathlib
import OAI.Computability.MaxCut.PCP.PreprocessingRegularSoundness

namespace OAI

/-! Modal decoding is an actual maximum of finite empirical letter masses.
Its reciprocal-alphabet lower bound is derived from their total mass one. -/

namespace MaxCutGames.Foundations.PCP.PoweringDecoding

open scoped BigOperators

variable {Ω A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype A] [Nonempty A]

noncomputable def mass (opinion : Ω → A) (a : A) : ℝ := by
  classical
  exact Finset.univ.expect (fun ω => if opinion ω = a then 1 else 0)

omit [Nonempty A] in
theorem mass_sum (opinion : Ω → A) : (∑ a, mass opinion a) = 1 := by
  classical
  calc
    (∑ a, mass opinion a) =
        (Finset.univ : Finset Ω).expect
          (fun ω => ∑ a : A, if opinion ω = a then (1 : ℝ) else 0) :=
      (Finset.expect_sum_comm (Finset.univ : Finset Ω) (Finset.univ : Finset A)
        (fun ω a => if opinion ω = a then (1 : ℝ) else 0)).symm
    _ = (Finset.univ : Finset Ω).expect (fun _ => (1 : ℝ)) := by
      apply Finset.expect_congr rfl
      intro ω _
      simp
    _ = 1 := Finset.expect_const Finset.univ_nonempty 1

omit [Nonempty Ω] in
theorem exists_mode (opinion : Ω → A) :
    ∃ a : A, ∀ b : A, mass opinion b ≤ mass opinion a := by
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset A)
    (mass opinion) Finset.univ_nonempty
  exact ⟨a, fun b => ha b (Finset.mem_univ b)⟩

noncomputable def mode (opinion : Ω → A) : A := Classical.choose (exists_mode opinion)

omit [Nonempty Ω] in
theorem mode_max (opinion : Ω → A) (b : A) :
    mass opinion b ≤ mass opinion (mode opinion) :=
  Classical.choose_spec (exists_mode opinion) b

theorem mode_mass_lower (opinion : Ω → A) :
    1 / (Fintype.card A : ℝ) ≤ mass opinion (mode opinion) := by
  have hk : 0 < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (1 : ℝ) ≤ mass opinion (mode opinion) * (Fintype.card A : ℝ) := by
    calc
      (1 : ℝ) = ∑ a : A, mass opinion a := (mass_sum opinion).symm
      _ ≤ ∑ _a : A, mass opinion (mode opinion) :=
        Finset.sum_le_sum (fun a _ => mode_max opinion a)
      _ = mass opinion (mode opinion) * (Fintype.card A : ℝ) := by simp [mul_comm]
  exact (div_le_iff₀ hk).2 hsum

theorem exists_letter_mass_lower (opinion : Ω → A) :
    ∃ a : A, 1 / (Fintype.card A : ℝ) ≤ mass opinion a :=
  ⟨mode opinion, mode_mass_lower opinion⟩

end MaxCutGames.Foundations.PCP.PoweringDecoding

/-! Actual indicator counting and the second-moment rejection estimate.
The hypotheses describe event inclusion and moment bounds, while the
Cauchy--Schwarz conclusion and all positivity properties are proved here. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PoweringMoment

open scoped BigOperators

def bit (p : Prop) : ℝ := by
  classical
  exact if p then 1 else 0

def hits {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) : ℝ :=
  ∑ i, bit (E i ω)

def mean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ := Finset.univ.expect f

theorem bit_nonneg (p : Prop) : 0 ≤ bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_sq (p : Prop) : bit p ^ 2 = bit p := by
  classical
  by_cases hp : p <;> simp [bit, hp]

theorem bit_mul (p q : Prop) : bit p * bit q = bit (p ∧ q) := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [bit, hp, hq]

theorem bit_mono {p q : Prop} (hpq : p → q) : bit p ≤ bit q := by
  classical
  by_cases hp : p
  · simp [bit, hp, hpq hp]
  · have hz : bit p = 0 := by simp [bit, hp]
    rw [hz]
    exact bit_nonneg q

theorem hits_nonneg {I Ω : Type*} [Fintype I] (E : I → Ω → Prop) (ω : Ω) :
    0 ≤ hits E ω := Finset.sum_nonneg (fun i _ => bit_nonneg (E i ω))

theorem mean_nonneg {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) :
    0 ≤ mean f := Finset.expect_nonneg (fun ω _ => hf ω)

theorem mean_hits {I Ω : Type*} [Fintype I] [Fintype Ω] (E : I → Ω → Prop) :
    mean (hits E) = ∑ i, mean (fun ω => bit (E i ω)) := by
  exact Finset.expect_sum_comm _ _ _

theorem second_moment_eq {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E : I → Ω → Prop) :
    mean (fun ω => hits E ω ^ 2) =
      ∑ i, ∑ j, mean (fun ω => bit (E i ω ∧ E j ω)) := by
  simp only [hits, pow_two, Finset.sum_mul, Finset.mul_sum, bit_mul,
    mean, Finset.expect_sum_comm]
  exact Finset.sum_comm

theorem mean_witness_sq_le {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω) :
    mean (hits W) ^ 2 ≤
      mean (fun ω => bit (reject ω)) * mean (fun ω => hits E ω ^ 2) := by
  classical
  have hNH (ω : Ω) : hits W ω ≤ hits E ω :=
    Finset.sum_le_sum (fun i _ => bit_mono (hWE i ω))
  have hzero (ω : Ω) (hr : ¬ reject ω) : hits W ω = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hw : ¬ W i ω := fun h => hr (hWR i ω h)
    simp [bit, hw]
  have hsupport (ω : Ω) : bit (reject ω) * hits W ω = hits W ω := by
    by_cases hr : reject ω
    · simp [bit, hr]
    · rw [hzero ω hr]
      simp
  have hCS := Finset.expect_mul_sq_le_sq_mul_sq Finset.univ
    (fun ω => bit (reject ω)) (hits W)
  have hsquares : mean (fun ω => hits W ω ^ 2) ≤ mean (fun ω => hits E ω ^ 2) := by
    apply Finset.expect_le_expect
    intro ω _
    simpa only [pow_two] using
      (mul_le_mul (hNH ω) (hNH ω) (hits_nonneg W ω) (hits_nonneg E ω))
  calc
    _ ≤ mean (fun ω => bit (reject ω)) * mean (fun ω => hits W ω ^ 2) := by
      simpa only [mean, hsupport, bit_sq] using hCS
    _ ≤ _ := mul_le_mul_of_nonneg_left hsquares
      (mean_nonneg _ (fun ω => bit_nonneg (reject ω)))

theorem rejection_lower_bound {I Ω : Type*} [Fintype I] [Fintype Ω]
    (E W : I → Ω → Prop) (reject : Ω → Prop)
    (hWE : ∀ i ω, W i ω → E i ω)
    (hWR : ∀ i ω, W i ω → reject ω)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hfirst : a ≤ mean (hits W))
    (hsecond : mean (fun ω => hits E ω ^ 2) ≤ b) :
    a ^ 2 / b ≤ mean (fun ω => bit (reject ω)) := by
  have hN : 0 ≤ mean (hits W) := mean_nonneg _ (hits_nonneg W)
  have hρ : 0 ≤ mean (fun ω => bit (reject ω)) :=
    mean_nonneg _ (fun ω => bit_nonneg (reject ω))
  have haSq : a ^ 2 ≤ mean (hits W) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hfirst hfirst ha.le hN
  have hCS := mean_witness_sq_le E W reject hWE hWR
  apply (div_le_iff₀ hb).2
  exact haSq.trans (hCS.trans (mul_le_mul_of_nonneg_left hsecond hρ))

end MaxCutGames.Foundations.PCP.PoweringMoment
end

/-! Actual finite walk averages and their operator representations.
All changes of probability coordinates come from explicit equivalences. -/

namespace MaxCutGames.Foundations.PCP.PoweringReturn

open PoweringWalks SpectralReturn
open PoweringMoment (bit)

variable {V D : Type*}

def portConsEquiv (D : Type*) (n : Nat) :
    (D × (Fin n → D)) ≃ (Fin (n + 1) → D) where
  toFun z := Fin.cases z.1 z.2
  invFun r := (r 0, fun j => r j.succ)
  left_inv z := by
    apply Prod.ext
    · rfl
    · funext j
      rfl
  right_inv r := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j

theorem mean_word_cons_head [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun d : D => mean (fun r : Fin n → D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : D × (Fin n → D) => F (Fin.cases z.1 z.2)) :=
      (mean_equiv (portConsEquiv D n) F).symm
    _ = _ := mean_prod _

theorem mean_word_cons_tail [Fintype D] (n : Nat)
    (F : (Fin (n + 1) → D) → ℝ) :
    mean F = mean (fun r : Fin n → D => mean (fun d : D => F (Fin.cases d r))) := by
  calc
    mean F = mean (fun z : (Fin n → D) × D => F (Fin.cases z.2 z.1)) :=
      (mean_equiv ((Equiv.prodComm (Fin n → D) D).trans (portConsEquiv D n)) F).symm
    _ = _ := mean_prod _

theorem iterateOperator_succ_right [Fintype D] (G : PortGraph V D)
    (n : Nat) (f : V → ℝ) :
    iterateOperator G n (averagingOperator G f) = iterateOperator G (n + 1) f := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (averagingOperator G) ih

theorem mean_wordEnd [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (v : V) (f : V → ℝ),
      mean (fun r : Fin n → D => f (wordEnd G n v r)) = iterateOperator G n f v := by
  intro n
  induction n with
  | zero =>
    intro v f
    change mean (fun _ : Fin 0 → D => f v) = f v
    exact mean_const _
  | succ n ih =>
    intro v f
    rw [mean_word_cons_head]
    change mean (fun d : D => mean (fun r : Fin n → D =>
      f (wordEnd G n (next G v d) r))) = _
    calc
      _ = mean (fun d : D => iterateOperator G n f (next G v d)) := by
        congr 1
        funext d
        exact ih (next G v d) f
      _ = iterateOperator G (n + 1) f v := rfl

/-- Conditional endpoint factorization at an arbitrary fixed pivot dart. -/
theorem mean_pivot_endpoints [Fintype D] [Nonempty D] (G : PortGraph V D) :
    ∀ (n : Nat) (k : Fin (n + 1)) (e : Edge V D) (φ ψ : V → ℝ),
      mean (fun r : Fin n → D =>
        φ (leftFromPivot G n k e.1 r) * ψ (rightFromPivot G n k e r)) =
        iterateOperator G k.val φ e.1 *
          iterateOperator G (n - k.val) ψ (next G e.1 e.2) := by
  intro n
  induction n with
  | zero =>
    intro k e φ ψ
    have hk : k = 0 := Fin.eq_zero k
    subst k
    change mean (fun _ : Fin 0 → D => φ e.1 * ψ (next G e.1 e.2)) =
      φ e.1 * ψ (next G e.1 e.2)
    exact mean_const _
  | succ n ih =>
    intro k e φ ψ
    refine Fin.cases ?_ (fun j => ?_) k
    · change mean (fun r : Fin (n + 1) → D =>
        φ e.1 * ψ (wordEnd G (n + 1) (next G e.1 e.2) r)) =
          φ e.1 * iterateOperator G (n + 1) ψ (next G e.1 e.2)
      rw [mean_mul_left, mean_wordEnd]
    · simp only [Fin.val_succ, Nat.add_sub_add_right]
      rw [mean_word_cons_tail]
      change mean (fun r : Fin n → D => mean (fun d : D =>
        φ (next G (leftFromPivot G n j e.1 r) d) *
          ψ (rightFromPivot G n j e r))) =
        iterateOperator G (j.val + 1) φ e.1 *
          iterateOperator G (n - j.val) ψ (next G e.1 e.2)
      calc
        _ = mean (fun r : Fin n → D =>
            averagingOperator G φ (leftFromPivot G n j e.1 r) *
              ψ (rightFromPivot G n j e r)) := by
          congr 1
          funext r
          rw [mean_mul_right]
          rfl
        _ = iterateOperator G j.val (averagingOperator G φ) e.1 *
            iterateOperator G (n - j.val) ψ (next G e.1 e.2) :=
          ih j e (averagingOperator G φ) ψ
        _ = _ := by rw [iterateOperator_succ_right]

/-- The pivot and both endpoint opinions are averaged over actual walks. -/
theorem mean_edge_endpoints [Fintype V] [Fintype D] [Nonempty D]
    (G : PortGraph V D) (n : Nat) (k : Fin (n + 1)) (φ ψ : Edge V D → V → ℝ) :
    mean (fun w : Walk V D (n + 1) =>
      φ (edgeAt G n w k) w.1 * ψ (edgeAt G n w k) (endpoint G w)) =
      mean (fun e : Edge V D =>
        iterateOperator G k.val (φ e) e.1 *
          iterateOperator G (n - k.val) (ψ e) (next G e.1 e.2)) := by
  let F : Edge V D × (Fin n → D) → ℝ := fun z =>
    φ z.1 (leftFromPivot G n k z.1.1 z.2) *
      ψ z.1 (rightFromPivot G n k z.1 z.2)
  calc
    _ = mean (fun w => F (pivotEquiv G n k w)) := by
      congr 1
      funext w
      dsimp [F]
      rw [leftFromPivot_actual, rightFromPivot_actual, pivotEquiv_fst]
    _ = mean F := mean_equiv (pivotEquiv G n k) F
    _ = mean (fun e : Edge V D => mean (fun r : Fin n → D =>
        φ e (leftFromPivot G n k e.1 r) * ψ e (rightFromPivot G n k e r))) := mean_prod F
    _ = _ := by
      congr 1
      funext e
      exact mean_pivot_endpoints G n k e (φ e) (ψ e)

theorem bit_bool (b : Bool) : bit (b = true) = (if b then 1 else 0 : ℝ) := by
  cases b <;> simp [bit]

theorem mean_edge_bit [Fintype D] (bad : V × D → Bool) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true)) = edgeProfile bad v := by
  simp only [bit_bool, mean, edgeProfile]

theorem mean_marked_bit [Fintype D] (G : PortGraph V D)
    (bad : V × D → Bool) (f : V → ℝ) (v : V) :
    mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
      markedStep G bad f v := by
  change mean (fun d : D => bit (bad (v, d) = true) * f (next G v d)) =
    mean (fun d : D => if bad (v, d) then f (next G v d) else 0)
  congr 1
  funext d
  cases bad (v, d) <;> simp [bit]

theorem edgeAt_zero (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1)) :
    edgeAt G n w 0 = (w.1, w.2 0) := by
  cases n <;> rfl

theorem word_first_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (v : V) :
    mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) 0) = true)) =
      edgeProfile bad v := by
  rw [mean_word_cons_head]
  simp_rw [edgeAt_zero]
  change mean (fun d : D => mean (fun _ : Fin n → D => bit (bad (v, d) = true))) = _
  calc
    _ = mean (fun d : D => bit (bad (v, d) = true)) := by simp only [mean_const]
    _ = edgeProfile bad v := mean_edge_bit bad v

theorem word_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (k : Fin (n + 1)),
      mean (fun p : Fin (n + 1) → D => bit (bad (edgeAt G n (v, p) k) = true)) =
        iterateOperator G k.val (edgeProfile bad) v := by
  intro n
  induction n with
  | zero =>
    intro v k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    exact word_first_hit_mean G bad 0 v
  | succ n ih =>
    intro v k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact word_first_hit_mean G bad (n + 1) v
    · rw [mean_word_cons_head]
      change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (next G v d, p) j) = true))) =
          averagingOperator G (iterateOperator G j.val (edgeProfile bad)) v
      calc
        _ = mean (fun d : D => iterateOperator G j.val (edgeProfile bad) (next G v d)) := by
          congr 1
          funext d
          exact ih (next G v d) j
        _ = _ := rfl

theorem word_pair_hit_mean [Fintype D] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) :
    ∀ (n : Nat) (v : V) (i j : Fin (n + 1)), i < j →
      mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true)) =
        iterateOperator G i.val (markedStep G bad
          (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) v := by
  intro n
  induction n with
  | zero =>
    intro v i j hij
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst i
    subst j
    exact ((lt_irrefl _) hij).elim
  | succ n ih =>
    intro v i
    refine Fin.cases ?_ (fun a => ?_) i
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact ((lt_irrefl _) hij).elim
      · intro _hij
        simp only [Fin.val_zero, Fin.val_succ, Nat.sub_zero, Nat.add_sub_cancel]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (v, d) = true) * bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          markedStep G bad (iterateOperator G b.val (edgeProfile bad)) v
        calc
          _ = mean (fun d : D => bit (bad (v, d) = true) *
              iterateOperator G b.val (edgeProfile bad) (next G v d)) := by
            congr 1
            funext d
            rw [mean_mul_left, word_hit_mean]
          _ = _ := mean_marked_bit G bad _ v
    · intro j
      refine Fin.cases ?_ (fun b => ?_) j
      · intro hij
        exact (Nat.not_lt_zero _ hij).elim
      · intro hij
        have hab : a < b := Nat.lt_of_succ_lt_succ hij
        simp only [Fin.val_succ, Nat.add_sub_add_right]
        rw [mean_word_cons_head]
        change mean (fun d : D => mean (fun p : Fin (n + 1) → D =>
          bit (bad (edgeAt G n (next G v d, p) a) = true) *
            bit (bad (edgeAt G n (next G v d, p) b) = true))) =
          averagingOperator G (iterateOperator G a.val (markedStep G bad
            (iterateOperator G (b.val - a.val - 1) (edgeProfile bad)))) v
        calc
          _ = mean (fun d : D => iterateOperator G a.val (markedStep G bad
              (iterateOperator G (b.val - a.val - 1) (edgeProfile bad))) (next G v d)) := by
            congr 1
            funext d
            exact ih (next G v d) a b hab
          _ = _ := rfl

theorem hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat) (k : Fin (n + 1)) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w k) = true)) =
      edgeDensity bad := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) k) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w k) = true))
    _ = mean (iterateOperator G k.val (edgeProfile bad)) := by
      congr 1
      funext v
      exact word_hit_mean G bad n v k
    _ = mean (edgeProfile bad) := mean_iterate G k.val _
    _ = _ := rfl

theorem pair_hit_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) => bit (bad (edgeAt G n w i) = true) *
      bit (bad (edgeAt G n w j) = true)) = returnMass G bad (j.val - i.val - 1) := by
  calc
    _ = mean (fun v : V => mean (fun p : Fin (n + 1) → D =>
        bit (bad (edgeAt G n (v, p) i) = true) *
          bit (bad (edgeAt G n (v, p) j) = true))) :=
      mean_prod (A := V) (B := Fin (n + 1) → D)
        (fun w => bit (bad (edgeAt G n w i) = true) *
          bit (bad (edgeAt G n w j) = true))
    _ = mean (iterateOperator G i.val (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad)))) := by
      congr 1
      funext v
      exact word_pair_hit_mean G bad n v i j hij
    _ = mean (markedStep G bad
        (iterateOperator G (j.val - i.val - 1) (edgeProfile bad))) := mean_iterate G i.val _
    _ = _ := rfl

theorem pair_event_mean [Fintype V] [Fintype D] [Nonempty V] [Nonempty D]
    (G : PortGraph V D) (bad : V × D → Bool) (n : Nat)
    (i j : Fin (n + 1)) (hij : i < j) :
    mean (fun w : Walk V D (n + 1) =>
      bit (bad (edgeAt G n w i) = true ∧ bad (edgeAt G n w j) = true)) =
        returnMass G bad (j.val - i.val - 1) := by
  simpa only [PoweringMoment.bit_mul] using pair_hit_mean G bad n i j hij

end MaxCutGames.Foundations.PCP.PoweringReturn

/-! Actual local-label opinions, modal decoding at the reference length, and
its proved persistence at nearby lazy-walk lengths. -/

noncomputable section

namespace MaxCutGames.Foundations.PCP.PoweringOpinions

open PoweringWalks PoweringLabels SpectralReturn
open PoweringMoment (bit)

variable {V D A : Type*}

/-- Outside the full-radius neighborhood a fixed fallback makes the opinion
function total. Actual tested path vertices will be certified inside it. -/
def opinionAt (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : A := by
  classical
  exact if h : ∃ n, n ≤ t ∧ ∃ p : Fin n → D, wordEnd G n v p = u then
    decode (selectors v) (labels v) ⟨u, h⟩ else fallback

theorem opinionAt_eq_decode (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors labels fallback u.val v = decode (selectors v) (labels v) u := by
  classical
  simp [opinionAt, u.property]
  rfl

def honestLabels (G : PortGraph V D) (t : Nat) (assignment : V → A) :
    V → PaddedLabel D t A := fun v => encode G t v (fun u => assignment u.val)

theorem opinionAt_honest (G : PortGraph V D) (t : Nat)
    (selectors : ∀ v, AddressSelector G t v) (assignment : V → A)
    (fallback : A) (v : V) (u : Ball G t v) :
    opinionAt G t selectors (honestLabels G t assignment) fallback u.val v =
      assignment u.val := by
  rw [opinionAt_eq_decode]
  exact congrFun (decode_encode (selectors v) (fun u => assignment u.val)) u

variable [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]

def sampleOpinion (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) (p : Fin N → D) : A :=
  opinionAt G t selectors labels fallback u (wordEnd G N u p)

def decoded (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) : A :=
  PoweringDecoding.mode (sampleOpinion G t N selectors labels fallback u)

def matchFn (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) : ℝ :=
  bit (opinionAt G t selectors labels fallback u v = decoded G t N selectors labels fallback u)

omit [Nonempty D] in
theorem matchFn_mem_Icc (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u v : V) :
    matchFn G t N selectors labels fallback u v ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  constructor
  · exact PoweringMoment.bit_nonneg _
  · unfold matchFn bit
    split <;> simp

/-- The reference-length modal lower bound is proved from actual port samples. -/
theorem decoded_modal_baseline (G : PortGraph V D) (t N : Nat)
    (selectors : ∀ v, AddressSelector G t v) (labels : V → PaddedLabel D t A)
    (fallback : A) (u : V) :
    1 / (Fintype.card A : ℝ) ≤
      iterateOperator G N (matchFn G t N selectors labels fallback u) u := by
  have h := PoweringDecoding.mode_mass_lower (sampleOpinion G t N selectors labels fallback u)
  change 1 / (Fintype.card A : ℝ) ≤ mean (fun p : Fin N → D =>
    matchFn G t N selectors labels fallback u (wordEnd G N u p)) at h
  rwa [PoweringReturn.mean_wordEnd] at h

/-- Actual decoded letters retain positive mass throughout the middle window. -/
theorem decoded_modal_near (G : PortGraph V D) (t M m : Nat)
    (selectors : ∀ v, AddressSelector (lazyGraph G) t v)
    (labels : V → PaddedLabel (Bool × D) t A) (fallback : A)
    (hM : 1 ≤ M)
    (hlo : (4 * Fintype.card A * M) ^ 2 - M ≤ m)
    (hhi : m ≤ (4 * Fintype.card A * M) ^ 2 + M) (u : V) :
    1 / (2 * (Fintype.card A : ℝ)) ≤
      iterateOperator (lazyGraph G) m
        (matchFn (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
          selectors labels fallback u) u := by
  exact PoweringLazy.lazy_endpoint_modal_transfer G (Fintype.card A) M m
    Fintype.card_pos hM hlo hhi _
    (matchFn_mem_Icc (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u) u
    (decoded_modal_baseline (lazyGraph G) t ((4 * Fintype.card A * M) ^ 2)
      selectors labels fallback u)

end MaxCutGames.Foundations.PCP.PoweringOpinions
end

/-!
# Full-radius access to the endpoints of each actual walk edge

The tail of each traversed edge is reachable from the walk's start. Its head
is reachable from the walk's end by reversing the remaining suffix with the
actual arrival ports. These facts supply values in the two neighborhood-ball
types used by the endpoint label decoders.
-/

namespace MaxCutGames.Foundations.PCP.PoweringReach

open PoweringWalks PoweringLabels

variable {V D : Type*}

def ReachLE (G : PortGraph V D) (t : Nat) (u v : V) : Prop :=
  ∃ l, l ≤ t ∧ ∃ p : Fin l → D, wordEnd G l u p = v

theorem reach_refl (G : PortGraph V D) (t : Nat) (u : V) : ReachLE G t u u :=
  ⟨0, Nat.zero_le t, Fin.elim0, rfl⟩

theorem reach_mono {G : PortGraph V D} {s t : Nat} {u v : V}
    (hst : s ≤ t) (h : ReachLE G s u v) : ReachLE G t u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  exact ⟨l, hl.trans hst, p, hp⟩

theorem reach_prepend (G : PortGraph V D) {t : Nat} (u : V) (d : D) {v : V}
    (h : ReachLE G t (next G u d) v) : ReachLE G (t + 1) u v := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨l + 1, Nat.succ_le_succ hl,
    (fun i : Fin (l + 1) => Fin.cases d p i), ?_⟩
  simpa only [wordEnd, Fin.cases_zero, Fin.cases_succ] using hp

/-- Reversal records each arrival port, not the original outgoing port. -/
def reversePorts (G : PortGraph V D) : V → List D → List D
  | _, [] => []
  | v, d :: ds => reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]

theorem reversePorts_length (G : PortGraph V D) (v : V) (ds : List D) :
    (reversePorts G v ds).length = ds.length := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih => simp [reversePorts, ih]

theorem walkEnd_reversePorts (G : PortGraph V D) (v : V) (ds : List D) :
    walkEnd G (walkEnd G v ds) (reversePorts G v ds) = v := by
  induction ds generalizing v with
  | nil => rfl
  | cons d ds ih =>
    change walkEnd G (walkEnd G (next G v d) ds)
      (reversePorts G (next G v d) ds ++ [(G.rot (v, d)).2]) = v
    rw [walkEnd_append, ih]
    change (G.rot (G.rot (v, d))).1 = v
    exact congrArg Prod.fst (G.rot_involutive (v, d))

theorem wordEnd_eq_walkEnd_ofFn (G : PortGraph V D) :
    ∀ n v (p : Fin n → D), wordEnd G n v p = walkEnd G v (List.ofFn p) := by
  intro n
  induction n with
  | zero => intro v p; rfl
  | succ n ih =>
    intro v p
    rw [List.ofFn_succ, walkEnd_cons]
    exact ih (next G v (p 0)) (fun j => p j.succ)

theorem reach_reverse {G : PortGraph V D} {t : Nat} {u v : V}
    (h : ReachLE G t u v) : ReachLE G t v u := by
  obtain ⟨l, hl, p, hp⟩ := h
  refine ⟨(reversePorts G u (List.ofFn p)).length, ?_,
    (reversePorts G u (List.ofFn p)).get, ?_⟩
  · simpa only [reversePorts_length, List.length_ofFn] using hl
  · rw [wordEnd_eq_walkEnd_ofFn, List.ofFn_get]
    have hlist : walkEnd G u (List.ofFn p) = v := by
      rw [← wordEnd_eq_walkEnd_ofFn]
      exact hp
    rw [← hlist, walkEnd_reversePorts]

/-- The actual prefix places each traversed edge's tail in the start ball. -/
theorem tail_reach (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) w.1 (edgeAt G n w k).1 := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 w.1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact reach_refl G (n + 2) w.1
    · exact reach_prepend G w.1 (w.2 0) (ih (advanceTail G w) j)

/-- The suffix proceeds from the traversed edge's head to the walk endpoint. -/
theorem head_reach_endpoint (G : PortGraph V D) :
    ∀ (n : Nat) (w : Walk V D (n + 1)) (k : Fin (n + 1)),
      ReachLE G (n + 1) (G.rot (edgeAt G n w k)).1 (endpoint G w) := by
  intro n
  induction n with
  | zero =>
    intro w k
    exact reach_refl G 1 (G.rot (w.1, w.2 0)).1
  | succ n ih =>
    intro w k
    refine Fin.cases ?_ (fun j => ?_) k
    · exact ⟨n + 1, Nat.le_succ (n + 1), (fun j => w.2 j.succ), rfl⟩
    · exact reach_mono (Nat.le_succ (n + 1)) (ih (advanceTail G w) j)

def tailFromStart (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) w.1 :=
  ⟨(edgeAt G n w k).1, tail_reach G n w k⟩

def headFromEnd (G : PortGraph V D) (n : Nat) (w : Walk V D (n + 1))
    (k : Fin (n + 1)) : Ball G (n + 1) (endpoint G w) :=
  ⟨(G.rot (edgeAt G n w k)).1, reach_reverse (head_reach_endpoint G n w k)⟩

@[simp] theorem tailFromStart_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (tailFromStart G n w k).val = (edgeAt G n w k).1 := rfl

@[simp] theorem headFromEnd_val (G : PortGraph V D) (n : Nat)
    (w : Walk V D (n + 1)) (k : Fin (n + 1)) :
    (headFromEnd G n w k).val = (G.rot (edgeAt G n w k)).1 := rfl

end MaxCutGames.Foundations.PCP.PoweringReach

/-!
# The actual constraint-graph powering test

Every recorded port walk gives two directed darts. Reversal flips an
orientation bit while preserving the recorded walk. The common vertex
alphabet is the full-radius padded local-label alphabet. The test checks the
actual base constraint at every traversed edge using the two endpoint labels.

Honest local encodings give perfect completeness. A decoded bad edge together
with the two matching local opinions forces rejection of the actual test.
Neither conclusion is assumed as a rejection-inclusion or distribution law.
-/

namespace MaxCutGames.Foundations.PCP.PoweringTest

open PoweringWalks PoweringLabels PoweringReach PoweringOpinions

variable {V D A : Type*}

/-- The base port predicates packaged as a constraint graph. -/
def baseGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b) :
    ConstraintGraph V (Edge V D) A where
  reverse := G.rot
  reverse_involutive := G.rot_involutive
  tail := Prod.fst
  accepts := accepts
  reverse_accepts := reverse_accepts

/-- Check all base constraints along the recorded walk. The reach certificates
select genuine vertices in the two full-radius neighborhood balls. -/
def pathAccepts (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) : Bool :=
  decide (∀ k : Fin (n + 1),
    accepts (edgeAt G n w k)
      (decode (selectors w.1) a (tailFromStart G n w k))
      (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true)

theorem pathAccepts_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (w : Walk V D (n + 1)) (a b : PaddedLabel D (n + 1) A) :
    pathAccepts G accepts n selectors w a b = true ↔
      ∀ k : Fin (n + 1),
        accepts (edgeAt G n w k)
          (decode (selectors w.1) a (tailFromStart G n w k))
          (decode (selectors (endpoint G w)) b (headFromEnd G n w k)) = true := by
  simp [pathAccepts]

abbrev Dart (V D : Type*) (n : Nat) := Bool × Walk V D (n + 1)

/-- Reversal preserves the recorded walk and changes its direction flag. -/
def reverseDart (V D : Type*) (n : Nat) : Dart V D n ≃ Dart V D n where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨b, w⟩
    cases b <;> rfl

theorem reverseDart_involutive (V D : Type*) (n : Nat) :
    Function.Involutive (reverseDart V D n) := by
  rintro ⟨b, w⟩
  cases b <;> rfl

/-- An actual powered constraint graph, with a common raw alphabet at all
vertices. Its reversal law is witnessed by the orientation bit. -/
def poweredGraph (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v) :
    ConstraintGraph V (Dart V D n) (PaddedLabel D (n + 1) A) where
  reverse := reverseDart V D n
  reverse_involutive := reverseDart_involutive V D n
  tail d := if d.1 then endpoint G d.2 else d.2.1
  accepts d a b := if d.1 then pathAccepts G accepts n selectors d.2 b a
    else pathAccepts G accepts n selectors d.2 a b
  reverse_accepts := by
    rintro ⟨direction, w⟩ a b
    cases direction <;> rfl

@[simp] theorem poweredGraph_tail_false (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (false, w) = w.1 := rfl

@[simp] theorem poweredGraph_tail_true (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).tail (true, w) = endpoint G w := rfl

/-- Both directed copies evaluate the same original-start/original-end path
test. Uniformly doubling the darts therefore introduces no change of event. -/
theorem poweredGraph_edgeSatisfied (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A)
    (direction : Bool) (w : Walk V D (n + 1)) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) =
      pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) := by
  cases direction <;> rfl

/-- The actual directed-dart rejection average is exactly the recorded-walk
rejection average. Only the orientation-bit average is removed, so the vertex
type and the walk type are allowed to be empty. -/
theorem rejection_mean_eq_path_mean [Fintype V] [Fintype D]
    (G : PortGraph V D) (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) :
    SpectralReturn.mean (fun d : Dart V D n => PoweringMoment.bit
      ((poweredGraph G accepts n selectors).edgeSatisfied labels d = false)) =
      SpectralReturn.mean (fun w : Walk V D (n + 1) => PoweringMoment.bit
        (pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false)) := by
  rw [SpectralReturn.mean_prod]
  simp only [poweredGraph_edgeSatisfied, SpectralReturn.mean_const]

theorem pathAccepts_honest (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true)
    (w : Walk V D (n + 1)) :
    pathAccepts G accepts n selectors w
      (honestLabels G (n + 1) assignment w.1)
      (honestLabels G (n + 1) assignment (endpoint G w)) = true := by
  apply (pathAccepts_eq_true_iff G accepts n selectors w _ _).2
  intro k
  simpa only [honestLabels, decode_encode, tailFromStart_val, headFromEnd_val] using
    satisfies (edgeAt G n w k)

/-- Perfect completeness for the actual powered graph and its common alphabet. -/
theorem perfect_completeness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (assignment : V → A)
    (satisfies : ∀ e, accepts e (assignment e.1) (assignment (G.rot e).1) = true) :
    ∀ d, (poweredGraph G accepts n selectors).edgeSatisfied
      (honestLabels G (n + 1) assignment) d = true := by
  rintro ⟨direction, w⟩
  rw [poweredGraph_edgeSatisfied]
  exact pathAccepts_honest G accepts n selectors assignment satisfies w

theorem preserves_satisfiability (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (n : Nat) (selectors : ∀ v, AddressSelector G (n + 1) v)
    (h : (baseGraph G accepts reverse_accepts).Satisfiable) :
    (poweredGraph G accepts n selectors).Satisfiable := by
  obtain ⟨assignment, satisfies⟩ := h
  refine ⟨honestLabels G (n + 1) assignment, ?_⟩
  apply perfect_completeness G accepts n selectors assignment
  intro e
  exact satisfies e

/-- Badness is computed from the actual base predicate and the decoded labels. -/
def decodedBad (G : PortGraph V D) (accepts : Edge V D → A → A → Bool)
    (assignment : V → A) (e : Edge V D) : Bool :=
  !(accepts e (assignment e.1) (assignment (G.rot e).1))

theorem decodedBad_eq_true_iff (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment e = true ↔
      accepts e (assignment e.1) (assignment (G.rot e).1) = false := by
  simp [decodedBad]

/-- The base reversal law makes the decoded bad-edge event rotor-invariant. -/
theorem decodedBad_rot (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool)
    (reverse_accepts : ∀ e a b, accepts (G.rot e) b a = accepts e a b)
    (assignment : V → A) (e : Edge V D) :
    decodedBad G accepts assignment (G.rot e) = decodedBad G accepts assignment e := by
  have h := congrArg Bool.not
    (reverse_accepts e (assignment e.1) (assignment (G.rot e).1))
  simpa only [decodedBad, G.rot_involutive e] using h

/-- A bad decoded edge with matching opinions at its two true endpoints. -/
noncomputable def witness (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1)) : Prop :=
  decodedBad G accepts assignment (edgeAt G n w k) = true ∧
    opinionAt G (n + 1) selectors labels fallback (edgeAt G n w k).1 w.1 =
      assignment (edgeAt G n w k).1 ∧
    opinionAt G (n + 1) selectors labels fallback
      (G.rot (edgeAt G n w k)).1 (endpoint G w) =
        assignment (G.rot (edgeAt G n w k)).1

theorem witness_bad (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    decodedBad G accepts assignment (edgeAt G n w k) = true := h.1

/-- The witness forces failure of the actual kth checked path constraint.
The opinion/decode identities use the genuine reach certificates. -/
theorem witness_implies_path_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k) :
    pathAccepts G accepts n selectors w (labels w.1) (labels (endpoint G w)) = false := by
  obtain ⟨hBad, hTail, hHead⟩ := h
  have hTailDecode :
      decode (selectors w.1) (labels w.1) (tailFromStart G n w k) =
        assignment (edgeAt G n w k).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback w.1
      (tailFromStart G n w k)).symm.trans hTail
  have hHeadDecode :
      decode (selectors (endpoint G w)) (labels (endpoint G w))
          (headFromEnd G n w k) = assignment (G.rot (edgeAt G n w k)).1 :=
    (opinionAt_eq_decode G (n + 1) selectors labels fallback (endpoint G w)
      (headFromEnd G n w k)).symm.trans hHead
  have hFalse := (decodedBad_eq_true_iff G accepts assignment (edgeAt G n w k)).1 hBad
  cases hPath : pathAccepts G accepts n selectors w
      (labels w.1) (labels (endpoint G w)) with
  | false => rfl
  | true =>
      have hChecked := (pathAccepts_eq_true_iff G accepts n selectors w _ _).1 hPath k
      rw [hTailDecode, hHeadDecode, hFalse] at hChecked
      exact False.elim (Bool.noConfusion hChecked)

/-- Rejection inclusion for the actual powered graph, derived from its test. -/
theorem witness_implies_rejection (G : PortGraph V D)
    (accepts : Edge V D → A → A → Bool) (n : Nat)
    (selectors : ∀ v, AddressSelector G (n + 1) v)
    (labels : V → PaddedLabel D (n + 1) A) (fallback : A)
    (assignment : V → A) (w : Walk V D (n + 1)) (k : Fin (n + 1))
    (h : witness G accepts n selectors labels fallback assignment w k)
    (direction : Bool) :
    (poweredGraph G accepts n selectors).edgeSatisfied labels (direction, w) = false := by
  rw [poweredGraph_edgeSatisfied]
  exact witness_implies_path_rejection G accepts n selectors labels fallback assignment w k h

end MaxCutGames.Foundations.PCP.PoweringTest

end OAI
