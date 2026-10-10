import OAI.Probability.SATVariance.WeightedRewards

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def extendWord.{u_1} {α : Type u_1} [Nonempty α] {M : ℕ} (w : Fin M → α) (i : ℕ) : α :=
  if h : i < M then w ⟨i,h⟩ else Classical.choice ‹Nonempty α›

lemma extendWord_fin.{u_1} {α : Type u_1} [Nonempty α] {M : ℕ} (w : Fin M → α) (i : Fin M) :
    extendWord w i = w i := by simp [extendWord, i.isLt]

def wordCount.{u_1} {α : Type u_1} {M : ℕ} (p : α → Prop) (w : Fin M → α) : ℝ :=
  ∑ i, if p (w i) then 1 else 0

def hitProbability.{u_1} {α : Type u_1} [Fintype α] (p : α → Prop) : ℝ :=
  favg (fun x => if p x then 1 else 0)

lemma wordCount_nonneg.{u_1} {α : Type u_1} {M : ℕ} (p : α → Prop) (w : Fin M → α) :
    0 ≤ wordCount p w := Finset.sum_nonneg fun _ _ => by split <;> norm_num

lemma hitProbability_nonneg.{u_1} {α : Type u_1} [Fintype α] (p : α → Prop) :
    0 ≤ hitProbability p := favg_nonneg fun _ => by split <;> norm_num

lemma wordCount_cons.{u_1} {α : Type u_1} {M : ℕ} (p : α → Prop) (x : α) (w : Fin M → α) :
    wordCount p (Fin.cons x w) = (if p x then 1 else 0)+wordCount p w := by
  rw [wordCount, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

lemma wordCount_zero.{u_1} {α : Type u_1} (p : α → Prop) (w : Fin 0 → α) : wordCount p w = 0 := by
  simp [wordCount]

lemma exp_hit_avg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p : α → Prop) :
    favg (fun x => Real.exp (if p x then 1 else 0)) =
      1+(Real.exp 1-1)*hitProbability p := by
  have he (x : α) : Real.exp (if p x then 1 else 0) =
      1+(Real.exp 1-1)*(if p x then 1 else 0) := by split <;> simp
  simp only [he, favg_add, favg_const, favg_mul, hitProbability]

lemma subhit_exp_avg.{u_1} {α : Type u_1} [Fintype α] (p q : α → Prop) (hqp : ∀ x, q x → p x) :
    favg (fun x => (if q x then 1 else 0)*Real.exp (if p x then 1 else 0)) =
      Real.exp 1*hitProbability q := by
  have he (x : α) : (if q x then 1 else 0)*Real.exp (if p x then 1 else 0) =
      Real.exp 1*(if q x then 1 else 0) := by
    by_cases hq : q x
    · simp [hq, hqp x hq]
    · simp [hq]
  simp only [he, favg_mul, hitProbability]

lemma exp_wordCount_avg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p : α → Prop) (M : ℕ) :
    favg (fun w : Fin M → α => Real.exp (wordCount p w)) =
      (1+(Real.exp 1-1)*hitProbability p)^M := by
  induction M with
  | zero => simp only [wordCount_zero, Real.exp_zero, favg_const, pow_zero]
  | succ M ih =>
    rw [favg_cons, favg_comm]
    simp_rw [wordCount_cons, Real.exp_add, favg_mul, ih]
    have he (x : α) : Real.exp (if p x then 1 else 0) *
        (1+(Real.exp 1-1)*hitProbability p)^M =
        (1+(Real.exp 1-1)*hitProbability p)^M * Real.exp (if p x then 1 else 0) := mul_comm _ _
    simp only [he, favg_mul, exp_hit_avg, pow_succ]

lemma exp_wordCount_bound.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p : α → Prop) (M : ℕ) :
    favg (fun w : Fin M → α => Real.exp (wordCount p w)) ≤
      Real.exp (M*(Real.exp 1-1)*hitProbability p) := by
  rw [exp_wordCount_avg]
  have he : 1+(Real.exp 1-1)*hitProbability p ≤
      Real.exp ((Real.exp 1-1)*hitProbability p) := by
    simpa only [add_comm] using Real.add_one_le_exp ((Real.exp 1-1)*hitProbability p)
  have hp : 0 ≤ 1+(Real.exp 1-1)*hitProbability p := by
    have he1 := Real.exp_one_gt_d9
    nlinarith [hitProbability_nonneg p]
  have hh := pow_le_pow_left₀ hp he M
  rw [← Real.exp_nat_mul] at hh
  simpa only [mul_assoc] using hh

lemma wordCount_avg.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p : α → Prop) (M : ℕ) :
    favg (fun w : Fin M → α => wordCount p w) = M*hitProbability p := by
  induction M with
  | zero => simp only [wordCount_zero, favg_const, Nat.cast_zero, zero_mul]
  | succ M ih =>
    rw [favg_cons]
    simp only [wordCount_cons, favg_add, favg_const]
    change hitProbability p+favg (fun w : Fin M → α => wordCount p w) = _
    rw [ih, Nat.cast_add, Nat.cast_one]
    ring

lemma subcount_exp_bound.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p q : α → Prop)
    (hqp : ∀ x, q x → p x) (M : ℕ) :
    favg (fun w : Fin M → α => wordCount q w * Real.exp (wordCount p w)) ≤
      M*Real.exp 1*hitProbability q*(1+(Real.exp 1-1)*hitProbability p)^M := by
  let A := 1+(Real.exp 1-1)*hitProbability p
  have hA : 1 ≤ A := by
    dsimp only [A]
    nlinarith [Real.exp_one_gt_d9, hitProbability_nonneg p]
  have hq := hitProbability_nonneg q
  induction M with
  | zero => simp only [wordCount_zero, zero_mul, favg_const, Nat.cast_zero, le_refl]
  | succ M ih =>
    rw [favg_cons]
    have hex (w : Fin M → α) (x : α) :
        wordCount q (Fin.cons x w)*Real.exp (wordCount p (Fin.cons x w)) =
        Real.exp (wordCount p w)*((if q x then 1 else 0)*Real.exp (if p x then 1 else 0)) +
        (wordCount q w*Real.exp (wordCount p w))*Real.exp (if p x then 1 else 0) := by
      rw [wordCount_cons, wordCount_cons, Real.exp_add]
      ring
    simp only [hex, favg_add, favg_mul, subhit_exp_avg p q hqp, exp_hit_avg]
    have he (w : Fin M → α) :
        Real.exp (wordCount p w)*(Real.exp 1*hitProbability q) =
        (Real.exp 1*hitProbability q)*Real.exp (wordCount p w) := mul_comm _ _
    have he' (w : Fin M → α) :
        wordCount q w*Real.exp (wordCount p w)*(1+(Real.exp 1-1)*hitProbability p) =
        A*(wordCount q w*Real.exp (wordCount p w)) := mul_comm _ _
    simp only [he, he', favg_mul, exp_wordCount_avg]
    change Real.exp 1*hitProbability q*A^M + A*favg (fun w : Fin M → α => wordCount q w*Real.exp (wordCount p w)) ≤ _
    have hmul := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ A)
    have hpow : 0 ≤ Real.exp 1*hitProbability q*A^M := by positivity
    have hextra := mul_le_mul_of_nonneg_right hA hpow
    rw [Nat.cast_add, Nat.cast_one, pow_succ]
    change _ ≤ (↑M+1)*Real.exp 1*hitProbability q*(A^M*A)
    nlinarith

lemma wordCount_factorial_second.{u_1} {α : Type u_1} [Fintype α] [Nonempty α]
    (p : α → Prop) (M : ℕ) :
    favg (fun w : Fin M → α => wordCount p w*(wordCount p w-1)) =
      (M : ℝ)*(M-1)*(hitProbability p)^2 := by
  induction M with
  | zero => simp only [wordCount_zero, zero_mul, favg_const, Nat.cast_zero]
  | succ M ih =>
    rw [favg_cons]
    have he (w : Fin M → α) (x : α) :
        wordCount p (Fin.cons x w)*(wordCount p (Fin.cons x w)-1) =
        wordCount p w*(wordCount p w-1)+(2*wordCount p w)*(if p x then 1 else 0) := by
      rw [wordCount_cons]
      split <;> ring
    simp only [he, favg_add, favg_const, favg_mul]
    change favg (fun w : Fin M → α => wordCount p w*(wordCount p w-1)) +
      favg (fun w : Fin M → α => (2*wordCount p w)*hitProbability p) = _
    have he' (w : Fin M → α) : (2*wordCount p w)*hitProbability p =
        (2*hitProbability p)*wordCount p w := by ring
    simp only [he', favg_mul, wordCount_avg, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma one_add_cube_le_exp {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^3 ≤ 6*Real.exp 1*Real.exp x := by
  have hh := Real.pow_div_factorial_le_exp (1+x) (by linarith) 3
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hh
  rw [Real.exp_add] at hh
  linarith

lemma one_add_sq_le_exp {x : ℝ} (hx : 0 ≤ x) :
    (1+x)^2 ≤ 2*Real.exp 1*Real.exp x := by
  have hh := Real.pow_div_factorial_le_exp (1+x) (by linarith) 2
  norm_num only [Nat.factorial, Nat.cast_ofNat] at hh
  rw [Real.exp_add] at hh
  linarith

lemma wordCount_cube_bound.{u_1} {α : Type u_1} [Fintype α] [Nonempty α]
    (p : α → Prop) (M : ℕ) {A : ℝ} (hA : M*hitProbability p ≤ A) :
    favg (fun w : Fin M → α => (1+wordCount p w)^3) ≤
      6*Real.exp 1*Real.exp ((Real.exp 1-1)*A) := by
  have hh := favg_mono (fun w : Fin M → α => one_add_cube_le_exp (wordCount_nonneg p w))
  rw [favg_mul] at hh
  have he := exp_wordCount_bound p M
  have ha : Real.exp (M*(Real.exp 1-1)*hitProbability p) ≤ Real.exp ((Real.exp 1-1)*A) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_one_gt_d9]
  exact hh.trans (mul_le_mul_of_nonneg_left (he.trans ha) (by positivity))

lemma subcount_sq_bound.{u_1} {α : Type u_1} [Fintype α] [Nonempty α] (p q : α → Prop)
    (hqp : ∀ x, q x → p x) (M : ℕ) {A : ℝ} (hA : M*hitProbability p ≤ A) :
    favg (fun w : Fin M → α => wordCount q w*(1+wordCount p w)^2) ≤
      2*(Real.exp 1)^2*M*hitProbability q*Real.exp ((Real.exp 1-1)*A) := by
  have hh := favg_mono (fun w : Fin M → α =>
    mul_le_mul_of_nonneg_left (one_add_sq_le_exp (wordCount_nonneg p w)) (wordCount_nonneg q w))
  have hew (w : Fin M → α) : wordCount q w*(2*Real.exp 1*Real.exp (wordCount p w)) =
      (2*Real.exp 1)*(wordCount q w*Real.exp (wordCount p w)) := by ring
  simp only [hew, favg_mul] at hh
  have hs := subcount_exp_bound p q hqp M
  rw [← exp_wordCount_avg p M] at hs
  have he := exp_wordCount_bound p M
  have ha : Real.exp (M*(Real.exp 1-1)*hitProbability p) ≤ Real.exp ((Real.exp 1-1)*A) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.exp_one_gt_d9]
  have hq := hitProbability_nonneg q
  have hf := mul_le_mul_of_nonneg_left (he.trans ha)
    (show 0 ≤ M*Real.exp 1*hitProbability q by positivity)
  have hg := mul_le_mul_of_nonneg_left (hs.trans hf) (show 0 ≤ 2*Real.exp 1 by positivity)
  nlinarith

lemma wordCount_factorial_second_bound.{u_1} {α : Type u_1} [Fintype α] [Nonempty α]
    (p : α → Prop) (M : ℕ) :
    favg (fun w : Fin M → α => wordCount p w*(wordCount p w-1)) ≤
      (M : ℝ)^2*(hitProbability p)^2 := by
  rw [wordCount_factorial_second]
  nlinarith [sq_nonneg (hitProbability p), Nat.cast_nonneg (α := ℝ) M]

def rootIncident {u k : ℕ} (p : RootData u k) : Prop := rootSize p.1 ≠ 0

def rootCollision {u k : ℕ} (p : RootData u k) : Prop := 2 ≤ rootSize p.1

lemma wordCount_incident {u k M : ℕ} (ps : Fin M → RootData u k) :
    wordCount rootIncident ps = (incidentSet ps).card := by
  simp only [wordCount, rootIncident, incidentSet]
  norm_cast
  exact Finset.sum_boole _ _

lemma wordCount_collision {u k M : ℕ} (ps : Fin M → RootData u k) :
    wordCount rootCollision ps = (collisionSet ps).card := by
  simp only [wordCount, rootCollision, collisionSet]
  norm_cast
  exact Finset.sum_boole _ _

lemma rootRewards_square_poly {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) (ps : Fin M → RootData u (r+1)) :
    favg (fun z : Fin M → RefreshNoise u (r+1) =>
      (dataRewards (forcedReward a) Finset.univ (fun i => refreshData a (ps i) (z i)))^2) ≤
      8*(lifetimeC (r+1)+1)^2*durationLog (r+1) M*(1+wordCount rootIncident ps)^3 +
      2*M*(lifetimeC (r+1)+1)*(wordCount rootCollision ps*(1+wordCount rootIncident ps)^2) +
      (M : ℝ)^2*(wordCount rootCollision ps*(wordCount rootCollision ps-1)) := by
  let hne (t : RootType (r+1)) : Nonempty (Clause u ((r+1)-rootSize t)) := clause_nonempty _ _ (by omega)
  let : Nonempty (RootData u (r+1)) := ⟨⟨fun _ => none, Classical.choice (hne _)⟩⟩
  have hh := rootRewards_square_conditioned (M := M) hr hru a (extendWord ps)
  simp only [extendWord_fin] at hh
  let Z := (incidentSet ps).card
  let V : ℝ := (collisionSet ps).card
  let Q := deletionQ (r+1) (max 1 Z)
  let C := lifetimeC (r+1)+1
  have hV : 0 ≤ V := Nat.cast_nonneg _
  have hlog : 0 ≤ durationLog (r+1) M := le_trans (by norm_num) (durationLog_one_le _ _)
  have hq := deletionQ_poly_bound (Z := Z) hr
  have hq2 := deletionQ_sq_poly_bound (Z := Z) hr
  change Q ≤ C*(1+(Z : ℝ))^2 at hq
  change Q^2 ≤ C^2*(1+(Z : ℝ))^3 at hq2
  have hfirst := mul_le_mul_of_nonneg_left hq2 (show 0 ≤ 8*durationLog (r+1) M by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hq (show 0 ≤ 2*M*V by positivity)
  rw [wordCount_incident, wordCount_collision]
  change _ ≤ 8*C^2*durationLog (r+1) M*(1+(Z : ℝ))^3 +
    2*M*C*(V*(1+(Z : ℝ))^2)+(M : ℝ)^2*(V*(V-1))
  change _ ≤ 8*Q^2*durationLog (r+1) M+2*M*Q*V+(M : ℝ)^2*V*(V-1) at hh
  nlinarith

def deletionMomentC (k : ℕ) (A D : ℝ) : ℝ :=
  48*Real.exp 1*(lifetimeC k+1)^2*Real.exp ((Real.exp 1-1)*A) +
  4*(Real.exp 1)^2*(lifetimeC k+1)*D*Real.exp ((Real.exp 1-1)*A)+D^2

lemma deletionMomentC_nonneg {r : ℕ} (hr : 2 ≤ r) (A D : ℝ) (hD : 0 ≤ D) :
    0 ≤ deletionMomentC (r+1) A D := by
  have hc : 0 ≤ lifetimeC (r+1)+1 := by linarith [lifetimeC_pos (by omega : 1 ≤ r)]
  unfold deletionMomentC
  positivity

lemma rootRewards_square_avg {u r M : ℕ} (hr : 2 ≤ r) (hru : r+1 ≤ u)
    (a : Assignment (r+1)) {A D : ℝ}
    (hA : M*hitProbability (rootIncident (u := u) (k := r+1)) ≤ A)
    (hD : (M : ℝ)^2*hitProbability (rootCollision (u := u) (k := r+1)) ≤ D) :
    favg (fun ps : Fin M → RootData u (r+1) => (dataRewards (forcedReward a) Finset.univ ps)^2) ≤
      deletionMomentC (r+1) A D*durationLog (r+1) M := by
  let hne (t : RootType (r+1)) : Nonempty (Clause u ((r+1)-rootSize t)) := clause_nonempty _ _ (by omega)
  let : Nonempty (RootData u (r+1)) := ⟨⟨fun _ => none, Classical.choice (hne _)⟩⟩
  let C := lifetimeC (r+1)+1
  let h := durationLog (r+1) M
  let E := Real.exp ((Real.exp 1-1)*A)
  let q := hitProbability (rootCollision (u := u) (k := r+1))
  have hC : 0 ≤ C := by dsimp [C]; linarith [lifetimeC_pos (by omega : 1 ≤ r)]
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hq : 0 ≤ q := hitProbability_nonneg _
  have hh : 1 ≤ h := durationLog_one_le _ _
  have hD0 : 0 ≤ D := le_trans (mul_nonneg (sq_nonneg (M : ℝ)) hq) hD
  have hstat := favg_pointwise_refresh (refreshData a) (favg_refreshData hru a) M
    (fun ps : Fin M → RootData u (r+1) => (dataRewards (forcedReward a) Finset.univ ps)^2)
  have hpoly := favg_mono (fun ps : Fin M → RootData u (r+1) => rootRewards_square_poly hr hru a ps)
  rw [hstat] at hpoly
  simp only [favg_add, favg_mul] at hpoly
  have h3 := wordCount_cube_bound (rootIncident (u := u) (k := r+1)) M hA
  have h2 := subcount_sq_bound (rootIncident (u := u) (k := r+1)) rootCollision
    (fun _ hc => by unfold rootIncident rootCollision at *; omega) M hA
  have hf := wordCount_factorial_second_bound (rootCollision (u := u) (k := r+1)) M
  have h3' := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 8*C^2*h by positivity)
  have h2' := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 2*M*C by positivity)
  have hf' := mul_le_mul_of_nonneg_left hf (sq_nonneg (M : ℝ))
  have hD' := mul_le_mul_of_nonneg_left hD (show 0 ≤ 4*(Real.exp 1)^2*C*E by positivity)
  have hDsq := pow_le_pow_left₀ (show 0 ≤ (M : ℝ)^2*q by positivity) hD 2
  have hstretch := mul_le_mul_of_nonneg_right hh
    (show 0 ≤ 4*(Real.exp 1)^2*C*D*E+D^2 by positivity)
  change _ ≤ (48*Real.exp 1*C^2*E+4*(Real.exp 1)^2*C*D*E+D^2)*h
  change _ ≤ 8*C^2*h*favg (fun ps : Fin M → RootData u (r+1) => (1+wordCount rootIncident ps)^3) +
    2*M*C*favg (fun ps : Fin M → RootData u (r+1) => wordCount rootCollision ps*(1+wordCount rootIncident ps)^2)+
    (M : ℝ)^2*favg (fun ps : Fin M → RootData u (r+1) => wordCount rootCollision ps*(wordCount rootCollision ps-1)) at hpoly
  dsimp only [E, q] at hDsq hD' hstretch
  dsimp only [C, h, E] at hpoly ⊢
  nlinarith

end RandomKSAT

end

end OAI
