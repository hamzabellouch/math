import Mathlib

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem355.LiftingProbability

theorem sum_comp_of_constant_fibres {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (M : ℕ)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = y)).card = M)
    (p : Y → ℝ) :
    (∑ x, p (f x)) = (M : ℝ) * ∑ y, p y := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ f (fun x => p (f x)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  calc
    (∑ x ∈ Finset.univ.filter (fun x => f x = y), p (f x)) =
        ∑ _x ∈ Finset.univ.filter (fun x => f x = y), p y := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = (M : ℝ) * p y := by simp [hf]

theorem sum_uniform_lift {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (M : ℕ) (hM : 0 < M)
    (hf : ∀ y, (Finset.univ.filter (fun x => f x = y)).card = M)
    (p : Y → ℝ) (hp : ∑ y, p y = 1) :
    (∑ x, p (f x) / (M : ℝ)) = 1 := by
  classical
  rw [← Finset.sum_div, sum_comp_of_constant_fibres f M hf p, hp, mul_one]
  exact div_self (by exact_mod_cast Nat.ne_of_gt hM)

abbrev TripleIn {B : Type*} (V : Finset B) (b : Fin 3 → B) : Prop :=
  ∀ i, b i ∈ V

theorem card_triples {B : Type*} [Fintype B] [DecidableEq B] (V : Finset B) :
    (Finset.univ.filter (TripleIn V)).card = V.card ^ 3 := by
  classical
  calc
    (Finset.univ.filter (TripleIn V)).card = Fintype.card {b : Fin 3 → B // TripleIn V b} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card (Fin 3 → V) := by
      exact Fintype.card_congr (Equiv.subtypePiEquivPi
        (β := fun _ : Fin 3 => B) (p := fun _ b => b ∈ V))
    _ = V.card ^ 3 := by simp

def inclusionMass {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ := by
  classical
  exact ∑ ω, if TripleIn (V ω) b then w ω else 0

 theorem inclusionMass_nonneg {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ inclusionMass w V b := by
  classical
  unfold inclusionMass
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all

theorem sum_inclusionMass {Ω B : Type*} [Fintype Ω] [Fintype B]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ)
    (hV : ∀ ω, (V ω).card = s) (hw : ∑ ω, w ω = 1) :
    (∑ b : Fin 3 → B, inclusionMass w V b) = (s : ℝ) ^ 3 := by
  classical
  simp only [inclusionMass]
  rw [Finset.sum_comm]
  calc
    (∑ ω, ∑ b : Fin 3 → B, if TripleIn (V ω) b then w ω else 0) =
        ∑ ω, (s : ℝ) ^ 3 * w ω := by
      apply Finset.sum_congr rfl
      intro ω hω
      rw [← Finset.sum_filter]
      simp [card_triples, hV]
    _ = (s : ℝ) ^ 3 := by rw [← Finset.mul_sum, hw, mul_one]

def mainMass {A : Type*} (O : Finset A) (a : A) : ℝ := by
  classical
  exact if a ∈ O then 1 / (O.card : ℝ) else 0

theorem mainMass_nonneg {A : Type*} (O : Finset A) (a : A) : 0 ≤ mainMass O a := by
  classical
  unfold mainMass
  split_ifs <;> positivity

theorem sum_mainMass {A : Type*} [Fintype A] (O : Finset A) (hO : O.Nonempty) :
    (∑ a, mainMass O a) = 1 := by
  classical
  unfold mainMass
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  have hc : (O.card : ℝ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hO
  exact mul_one_div_cancel hc

def auxiliaryMass {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ) (b : Fin 3 → B) : ℝ :=
  inclusionMass w V b / (s : ℝ) ^ 3

theorem auxiliaryMass_nonneg {Ω B : Type*} [Fintype Ω]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ) (hw : ∀ ω, 0 ≤ w ω) (b : Fin 3 → B) :
    0 ≤ auxiliaryMass w V s b :=
  div_nonneg (inclusionMass_nonneg w V hw b) (pow_nonneg (Nat.cast_nonneg _) _)

theorem sum_auxiliaryMass {Ω B : Type*} [Fintype Ω] [Fintype B]
    (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ) (hs : 0 < s)
    (hV : ∀ ω, (V ω).card = s) (hw : ∑ ω, w ω = 1) :
    (∑ b : Fin 3 → B, auxiliaryMass w V s b) = 1 := by
  classical
  unfold auxiliaryMass
  rw [← Finset.sum_div, sum_inclusionMass w V s hV hw]
  exact div_self (pow_ne_zero _ (by exact_mod_cast Nat.ne_of_gt hs))

def residueMass {A Ω B : Type*} [Fintype Ω]
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s : ℕ)
    (r : A × (Fin 3 → B)) : ℝ :=
  mainMass O r.1 * auxiliaryMass w V s r.2

theorem sum_residueMass {A Ω B : Type*} [Fintype A] [Fintype Ω] [Fintype B]
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s : ℕ) (hs : 0 < s) (hV : ∀ ω, (V ω).card = s) (hw : ∑ ω, w ω = 1) :
    (∑ r, residueMass O w V s r) = 1 := by
  classical
  simp only [residueMass, Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, sum_auxiliaryMass w V s hs hV hw, mul_one]
  exact sum_mainMass O hO

def liftedMass {X A Ω B : Type*} [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ) (x : X) : ℝ :=
  residueMass O w V s (f x, g x) / (M : ℝ)

theorem liftedMass_nonneg {X A Ω B : Type*} [Fintype Ω]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (w : Ω → ℝ) (V : Ω → Finset B) (s M : ℕ)
    (hw : ∀ ω, 0 ≤ w ω) (x : X) :
    0 ≤ liftedMass f g O w V s M x :=
  div_nonneg (mul_nonneg (mainMass_nonneg O (f x))
    (auxiliaryMass_nonneg w V s hw (g x))) (Nat.cast_nonneg _)

theorem sum_liftedMass {X A Ω B : Type*} [Fintype X] [Fintype A] [Fintype Ω]
    [Fintype B] [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s M : ℕ) (hs : 0 < s) (hM : 0 < M)
    (hV : ∀ ω, (V ω).card = s) (hw : ∑ ω, w ω = 1)
    (hf : ∀ r : A × (Fin 3 → B),
      (Finset.univ.filter (fun x => (f x, g x) = r)).card = M) :
    (∑ x, liftedMass f g O w V s M x) = 1 := by
  classical
  exact sum_uniform_lift (fun x => (f x, g x)) M hM hf
    (residueMass O w V s) (sum_residueMass O hO w V s hs hV hw)

def auxiliaryWeight {Ω B : Type*} [Fintype Ω]
    (q s : ℕ) (w : Ω → ℝ) (V : Ω → Finset B) (b : Fin 3 → B) : ℝ :=
  (((q : ℝ) ^ 3) / (s : ℝ)) ^ 3 * inclusionMass w V b

theorem lifting_normalization (h q L s o : ℝ) (z : ℝ)
    (hh : h ≠ 0) (hq : q ≠ 0) (hL : L ≠ 0) (hs : s ≠ 0) (ho : o ≠ 0) :
    (1 / o) * (z / s ^ 3) / L ^ 9 =
      h ^ 9 / ((L * (h * q)) ^ 9 * o) * ((q ^ 3 / s) ^ 3 * z) := by
  field_simp

theorem liftedMass_eq_weight {X A Ω B : Type*} [Fintype Ω] [DecidableEq A]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L) (x : X) :
    liftedMass f g O w V s (L ^ 9) x =
      if f x ∈ O then
        (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * (O.card : ℝ)) *
          auxiliaryWeight q s w V (g x)
      else 0 := by
  classical
  unfold liftedMass residueMass mainMass auxiliaryMass auxiliaryWeight
  split_ifs with hx
  · simp only [Nat.cast_pow, Nat.cast_mul]
    apply lifting_normalization
    · exact_mod_cast Nat.ne_of_gt hh
    · exact_mod_cast Nat.ne_of_gt hq
    · exact_mod_cast Nat.ne_of_gt hL
    · exact_mod_cast Nat.ne_of_gt hs
    · exact_mod_cast Finset.card_ne_zero.mpr hO
  · simp

theorem exact_lifting_identity {X A Ω B : Type*} [Fintype Ω] [DecidableEq A]
    (f : X → A) (g : X → (Fin 3 → B))
    (O : Finset A) (hO : O.Nonempty) (w : Ω → ℝ) (V : Ω → Finset B)
    (s h q L : ℕ) (hs : 0 < s) (hh : 0 < h) (hq : 0 < q) (hL : 0 < L)
    (E : Finset X) :
    (∑ x ∈ E, liftedMass f g O w V s (L ^ 9) x) =
      (h : ℝ) ^ 9 / ((L * (h * q) : ℕ) ^ 9 * (O.card : ℝ)) *
        ∑ x ∈ E.filter (fun x => f x ∈ O), auxiliaryWeight q s w V (g x) := by
  classical
  simp_rw [liftedMass_eq_weight f g O hO w V s h q L hs hh hq hL]
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

def conditionalColumnMass {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) : ℝ := by
  classical
  exact if f x = a ∧ g x ∈ V then 1 / ((s : ℝ) * (L : ℝ) ^ 3) else 0

theorem conditionalColumnMass_nonneg {X A B : Type*}
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ) (x : X) :
    0 ≤ conditionalColumnMass f g a V s L x := by
  classical
  unfold conditionalColumnMass
  split_ifs <;> positivity

theorem sum_conditionalColumnMass {X A B : Type*} [Fintype X] [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (a : A) (V : Finset B) (s L : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hV : V.card = s)
    (hf : ∀ r : A × B, (Finset.univ.filter (fun x => (f x, g x) = r)).card = L ^ 3) :
    (∑ x, conditionalColumnMass f g a V s L x) = 1 := by
  classical
  have hVne : V.Nonempty := Finset.card_pos.mp (by omega)
  let p : A × B → ℝ := fun r => (if r.1 = a then 1 else 0) * mainMass V r.2
  have hp : (∑ r, p r) = 1 := by
    dsimp [p]
    rw [Fintype.sum_prod_type]
    change (∑ x : A, ∑ y : B, ((if x = a then 1 else 0) : ℝ) * mainMass V y) = 1
    simp_rw [← Finset.mul_sum]
    simp_rw [sum_mainMass V hVne]
    simp only [mul_one]
    simp
  have hnormal := sum_uniform_lift (fun x => (f x, g x)) (L ^ 3)
    (pow_pos hL _) hf p hp
  calc
    (∑ x, conditionalColumnMass f g a V s L x) =
        ∑ x, p (f x, g x) / ((L ^ 3 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [p]
      by_cases hfa : f x = a <;> by_cases hgv : g x ∈ V <;>
        simp [conditionalColumnMass, mainMass, hfa, hgv, hV, div_eq_mul_inv, mul_inv_rev,
          mul_comm]
    _ = 1 := hnormal

theorem product_conditionalColumnMass {X A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : X → A) (g : X → B) (a : Fin 3 → A) (V : Finset B) (s L : ℕ)
    (x : Fin 3 → X) :
    (∏ i, conditionalColumnMass f g (a i) V s L (x i)) =
      if (fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i)) then
        1 / ((s : ℝ) ^ 3 * (L : ℝ) ^ 9) else 0 := by
  classical
  have hp : (∀ i, f (x i) = a i ∧ g (x i) ∈ V) ↔
      (fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i)) := by
    simp only [TripleIn, funext_iff, forall_and]
  by_cases hall : ∀ i, f (x i) = a i ∧ g (x i) ∈ V
  · calc
      (∏ i, conditionalColumnMass f g (a i) V s L (x i)) =
          ∏ _i : Fin 3, (1 : ℝ) / ((s : ℝ) * (L : ℝ) ^ 3) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [conditionalColumnMass, hall i]
      _ = _ := by simp [hp.mp hall, mul_pow, ← pow_mul]
  · obtain ⟨i, hi⟩ := not_forall.mp hall
    have hz : conditionalColumnMass f g (a i) V s L (x i) = 0 := by
      simp [conditionalColumnMass, hi]
    have hzero : (∏ i, conditionalColumnMass f g (a i) V s L (x i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    have hnot : ¬ ((fun i => f (x i)) = a ∧ TripleIn V (fun i => g (x i))) :=
      fun h => hall (hp.mpr h)
    rw [hzero]
    simp [hnot]

theorem sum_independent_indicators {Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
    (ρ : Θ → ℝ) (w : Ω → ℝ) (P : Θ → Prop) (Q : Ω → Prop)
    [DecidablePred P] [DecidablePred Q] (K : ℝ) :
    (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
      (∑ θ, if P θ then ρ θ else 0) * (∑ ω, if Q ω then w ω else 0) * K := by
  classical
  calc
    (∑ θ, ρ θ * ∑ ω, w ω * (if P θ ∧ Q ω then K else 0)) =
        ∑ θ, (if P θ then ρ θ else 0) * ((∑ ω, if Q ω then w ω else 0) * K) := by
      apply Finset.sum_congr rfl
      intro θ hθ
      by_cases hP : P θ
      · simp only [hP, true_and, ite_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro ω hω
        by_cases hQ : Q ω <;> simp [hQ]
      · simp [hP]
    _ = _ := by rw [← Finset.sum_mul, mul_assoc]

def pushforwardMass {Θ A : Type*} [Fintype Θ]
    (ρ : Θ → ℝ) (F : Θ → A) (a : A) : ℝ := by
  classical
  exact ∑ θ, if a = F θ then ρ θ else 0

theorem averaged_columns_eq_liftedMass
    {X A B Θ Ω : Type*} [Fintype Θ] [Fintype Ω]
    (f : X → A) (g : X → B) (F : Θ → (Fin 3 → A))
    (ρ : Θ → ℝ) (w : Ω → ℝ) (V : Ω → Finset B)
    (O : Finset (Fin 3 → A)) (s L : ℕ)
    (hpush : ∀ a, pushforwardMass ρ F a = mainMass O a)
    (x : Fin 3 → X) :
    (∑ θ, ρ θ * ∑ ω, w ω *
      ∏ i, conditionalColumnMass f g (F θ i) (V ω) s L (x i)) =
      liftedMass (fun x i => f (x i)) (fun x i => g (x i))
        O w V s (L ^ 9) x := by
  classical
  simp_rw [product_conditionalColumnMass]
  rw [sum_independent_indicators]
  have hmain : (∑ θ, if (fun i => f (x i)) = F θ then ρ θ else 0) =
      mainMass O (fun i => f (x i)) := by
    calc
      (∑ θ, if (fun i => f (x i)) = F θ then ρ θ else 0) =
          pushforwardMass ρ F (fun i => f (x i)) := by
        unfold pushforwardMass
        apply Finset.sum_congr rfl
        intro θ hθ
        by_cases h : (fun i => f (x i)) = F θ <;> simp [h]
      _ = _ := hpush _
  rw [hmain]
  unfold liftedMass residueMass auxiliaryMass inclusionMass
  simp only [Nat.cast_pow, div_eq_mul_inv, mul_inv_rev]
  ring

end Problem355.LiftingProbability

end

end OAI
