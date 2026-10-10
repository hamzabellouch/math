import OAI.Dynamics.SmoothObstruction.WordEntropy
import OAI.Dynamics.SmoothObstruction.PairLaw

namespace OAI

section

open scoped Classical
open Finset

namespace SmoothObstruction.FiniteLaw
open Finset FiniteEntropy
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

lemma expect_push_sum (P : Law α) (f : α → β) (g : β → ℝ) :
    (∑ b,(push P f).mass b*g b)=∑ a,P.mass a*g (f a) := by
  classical
  simp only [push,sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  simp only [ite_mul,zero_mul,sum_ite_eq,mem_univ,ite_true]

/-- The finite push mass, independent of the choice of equality decision procedure. -/
lemma push_mass_canonical [DecidableEq β] (P : Law α) (f : α → β) :
    (push P f).mass=FiniteEntropy.pushMass P.mass f := by
  funext b
  change (∑ a,if f a=b then P.mass a else 0)=_
  unfold FiniteEntropy.pushMass
  apply sum_congr rfl
  intro a _
  split_ifs <;> rfl

lemma mass_le_push (P : Law α) (f : α → β) (a : α) :
    P.mass a≤(push P f).mass (f a) := by
  classical
  change P.mass a≤∑ x,if f x=f a then P.mass x else 0
  have hh := single_le_sum (s:=univ) (f:=fun x => if f x=f a then P.mass x else 0)
    (fun x _ => by split_ifs; exact P.nonneg x; exact le_rfl) (mem_univ a)
  simpa only [ite_true] using hh

/-- The conditioning cost is the actual entropy of the mixing variable;
zero cell masses contribute zero. -/
lemma entropy_mixture_upper (P : Law α) (Q : α → Law β) :
    entropy (mixture P Q)≤entropy P+∑ a,P.mass a*entropy (Q a) := by
  let p : α × β → ℝ := fun z => P.mass z.1*(Q z.1).mass z.2
  have hp : ∀ z,0≤p z := fun z => mul_nonneg (P.nonneg z.1) ((Q z.1).nonneg z.2)
  have hproj : pushMass p Prod.snd=(mixture P Q).mass := by
    classical
    funext b
    simp only [pushMass,Fintype.sum_prod_type,p,mixture]
    simp only [sum_ite_eq',mem_univ,ite_true]
  have hh := FiniteEntropy.entropy_push_le hp Prod.snd
  rw [hproj] at hh
  have hj := FiniteEntropy.entropy_joint P.mass (fun a => (Q a).mass) (fun a => (Q a).total)
  exact hh.trans_eq hj

lemma entropy_card (P : Law α) : entropy P≤Real.log (Fintype.card α) :=
  FiniteEntropy.entropy_le_log_card P.nonneg P.total

/-- Entropy of a finite vector is bounded by the sum of its entry entropies.
The proof works directly for any finite index type, including the empty case. -/
lemma entropy_vector_le {J : Type*} [Fintype J] [DecidableEq J] (P : Law (J → α)) :
    entropy P≤∑ j,entropy (push P (fun w => w j)) := by
  classical
  let q (j : J) := push P (fun w => w j)
  have hsum : (∑ w : J → α,∏ j,(q j).mass (w j))=1 := by
    have hh := prod_univ_sum (fun _ : J => (univ : Finset α)) (fun j a => (q j).mass a)
    simpa only [Fintype.piFinset_univ,(q _).total,prod_const_one] using hh.symm
  have hpoint (w : J → α) : Real.negMulLog (P.mass w)≤
      (∑ j,-P.mass w*Real.log ((q j).mass (w j)))+
        (∏ j,(q j).mass (w j))-P.mass w := by
    rcases (P.nonneg w).eq_or_lt with hz|hp
    · rw [←hz]
      simp only [Real.negMulLog_zero,neg_zero,zero_mul,sum_const_zero,zero_add,sub_zero]
      exact prod_nonneg (fun j _ => (q j).nonneg _)
    · have hqp (j : J) : 0<(q j).mass (w j) := hp.trans_le (mass_le_push P _ w)
      have hh := FiniteEntropy.negMulLog_le_cross hp.le (prod_pos (s:=univ) (fun j _ => hqp j))
      rw [Real.log_prod (fun j _ => (hqp j).ne'),mul_sum] at hh
      exact hh
  have he (j : J) : (∑ w,P.mass w*(-Real.log ((q j).mass (w j))))=entropy (q j) := by
    rw [←expect_push_sum P (fun w => w j) (fun a => -Real.log ((q j).mass a))]
    simp only [entropy,natEntropy,Real.negMulLog_def,mul_neg,neg_mul,q]
  have hs := sum_le_sum (fun w (_ : w∈univ) => hpoint w)
  rw [sum_sub_distrib,sum_add_distrib,sum_comm,hsum,P.total,add_sub_cancel_right] at hs
  simp only [neg_mul,←mul_neg,he] at hs
  exact hs

/-- Finite-vector entropy after conditioning on a finite cell partition.
No product assertion after mixing a shared entry index is used. -/
theorem conditional_entry_sum {J : Type*} [Fintype J] [DecidableEq J]
    (P : Law α) (Q : α → Law (J → β)) :
    entropy (mixture P Q)-Real.log (Fintype.card α)≤
      ∑ a,P.mass a*∑ j,entropy (push (Q a) (fun w => w j)) := by
  have h1 := entropy_mixture_upper P Q
  have h2 := entropy_card P
  have h3 := sum_le_sum (fun a (_ : a∈univ) =>
    mul_le_mul_of_nonneg_left (entropy_vector_le (Q a)) (P.nonneg a))
  linarith

end SmoothObstruction.FiniteLaw

namespace SmoothObstruction.BinaryCharacter

/-- The real-valued character of the two-element field. -/
def sign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

@[simp] lemma sign_zero : sign 0 = 1 := by simp [sign]
@[simp] lemma sign_one : sign 1 = -1 := by norm_num [sign]
lemma eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a
lemma sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    rcases eq_zero_or_one b with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 : ZMod 2) + 1 = 0 by decide, sign_zero, sign_one]
    norm_num
@[simp] lemma sign_neg (a : ZMod 2) : sign (-a) = sign a := by
  rcases eq_zero_or_one a with rfl | rfl <;>
    simp [show -(1 : ZMod 2) = 1 by decide]
lemma sign_sub (a b : ZMod 2) : sign (a - b) = sign a * sign b := by
  rw [sub_eq_add_neg, sign_add, sign_neg]
@[simp] lemma sign_sq (a : ZMod 2) : sign a ^ 2 = 1 := by
  unfold sign
  split_ifs <;> norm_num
lemma one_of_ne_zero {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  exact (eq_zero_or_one a).resolve_left ha

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

/-- Character cancellation: translation by any point where a functional is
one changes every summand's sign. No probabilistic estimate is assumed. -/
lemma sum_sign_eq_zero {f : V →ₗ[ZMod 2] ZMod 2}
    (hf : ∃ v, f v ≠ 0) : ∑ v, sign (f v) = 0 := by
  classical
  obtain ⟨w, hw⟩ := hf
  have hw' := one_of_ne_zero hw
  have hsum := Equiv.sum_comp (Equiv.addRight w) (fun v => sign (f v))
  change (∑ v, sign (f (v + w))) = ∑ v, sign (f v) at hsum
  simp only [map_add, sign_add, hw', sign_one, mul_neg_one,
    sum_neg_distrib] at hsum
  linarith

/-- Exact row orthogonality for the full binary bilinear character matrix. -/
lemma row_orthogonality [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (u w : V) :
    ∑ v, sign (B u v) * sign (B w v) = if u = w then (Fintype.card V : ℝ) else 0 := by
  classical
  by_cases huw : u = w
  · subst w
    simp [← sq]
  · rw [ite_eq_right huw]
    have he : ∃ v, B (u - w) v ≠ 0 := by
      by_contra h
      push Not at h
      exact sub_ne_zero.mpr huw (hB.1 (u - w) h)
    convert sum_sign_eq_zero he using 1
    apply sum_congr rfl
    intro v _
    simp [LinearMap.map_sub, sign_sub]

lemma column_orthogonality [DecidableEq V] (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (v w : V) :
    ∑ u, sign (B u v) * sign (B u w) = if v = w then (Fintype.card V : ℝ) else 0 := by
  exact row_orthogonality B.flip hB.flip v w

/-- The finite Parseval identity, useful also for nonuniform light laws. -/
lemma parseval (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (q : V → ℝ) :
    ∑ u, (∑ v, sign (B u v) * q v) ^ 2 = (Fintype.card V : ℝ) * ∑ v, q v ^ 2 := by
  classical
  have hexpand (u : V) : (∑ v, sign (B u v) * q v) ^ 2 =
      ∑ v, ∑ w, q v * q w * (sign (B u v) * sign (B u w)) := by
    rw [sq, sum_mul]
    apply sum_congr rfl
    intro v _
    rw [mul_sum]
    apply sum_congr rfl
    intro w _
    ring
  simp_rw [hexpand]
  rw [sum_comm]
  calc
    _ = ∑ v, ∑ w, q v * q w * (∑ u, sign (B u v) * sign (B u w)) := by
      apply sum_congr rfl
      intro v _
      rw [sum_comm]
      apply sum_congr rfl
      intro w _
      rw [mul_sum]
    _ = _ := by
      simp only [column_orthogonality B hB]
      simp [mul_ite, mul_comm, sq, mul_sum]

/-- Squared spectral estimate with the exact matrix size, obtained from
Parseval and the finite Cauchy--Schwarz inequality. -/
theorem bilinear_sq_le (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (p q : V → ℝ) :
    (∑ u, ∑ v, p u * sign (B u v) * q v) ^ 2 ≤
      (Fintype.card V : ℝ) * (∑ u, p u ^ 2) * (∑ v, q v ^ 2) := by
  classical
  have h := sum_mul_sq_le_sq_mul_sq univ p (fun u => ∑ v, sign (B u v) * q v)
  rw [parseval B hB] at h
  calc
    _ = (∑ u, p u * ∑ v, sign (B u v) * q v) ^ 2 := by
      simp only [mul_sum, mul_assoc]
    _ ≤ _ := h
    _ = _ := by ring

lemma sign_indicator (a : ZMod 2) :
    (if a = 0 then (1 : ℝ) else 0) = (1 + sign a) / 2 := by
  unfold sign
  split_ifs <;> norm_num

section Nonzero
variable [DecidableEq V]

noncomputable def extendZero (p : {v : V // v ≠ 0} → ℝ) (v : V) : ℝ :=
  if h : v ≠ 0 then p ⟨v, h⟩ else 0

omit [Module (ZMod 2) V] [Fintype V] in
@[simp] lemma extendZero_zero (p : {v : V // v ≠ 0} → ℝ) : extendZero p 0 = 0 := by
  simp [extendZero]
omit [Module (ZMod 2) V] [Fintype V] in
@[simp] lemma extendZero_coe (p : {v : V // v ≠ 0} → ℝ) (v : {v : V // v ≠ 0}) :
    extendZero p v = p v := by simp [extendZero, v.property]

omit [Module (ZMod 2) V] in
lemma sum_remove_zero (f : V → ℝ) (hf : f 0 = 0) :
    ∑ v, f v = ∑ v : {v : V // v ≠ 0}, f v := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0, hf, zero_add]

/-- Restricting the character matrix to nonzero indices retains the full
space spectral bound, including its diagonal entries. -/
lemma nonzero_bilinear_sq_le (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (p q : {v : V // v ≠ 0} → ℝ) :
    (∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0}, p u * sign (B u v) * q v) ^ 2 ≤
      (Fintype.card V : ℝ) * (∑ u, p u ^ 2) * (∑ v, q v ^ 2) := by
  have h := bilinear_sq_le B hB (extendZero p) (extendZero q)
  have hleft : (∑ u, ∑ v, extendZero p u * sign (B u v) * extendZero q v) =
      ∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0}, p u * sign (B u v) * q v := by
    rw [sum_remove_zero _ (by simp)]
    apply sum_congr rfl
    intro u _
    rw [sum_remove_zero _ (by simp)]
    simp
  have hp : (∑ u, (extendZero p u) ^ 2) = ∑ u, p u ^ 2 := by
    rw [sum_remove_zero _ (by simp)]
    simp
  have hq : (∑ u, (extendZero q u) ^ 2) = ∑ u, q u ^ 2 := by
    rw [sum_remove_zero _ (by simp)]
    simp
  simpa only [hleft, hp, hq] using h

end Nonzero
end SmoothObstruction.BinaryCharacter

namespace SmoothObstruction.GraphBound
open BinaryCharacter

variable {α : Type*} [Fintype α]

noncomputable def light (τ : ℝ) (p : α → ℝ) (i : α) : ℝ :=
  if p i ≤ τ then p i else 0

omit [Fintype α] in
lemma light_nonneg {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (i : α) :
    0 ≤ light τ p i := by unfold light; split_ifs; exact hp i; exact le_rfl
omit [Fintype α] in
lemma light_le {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i) (i : α) :
    light τ p i ≤ p i := by unfold light; split_ifs; exact le_rfl; exact hp i
omit [Fintype α] in
lemma light_le_threshold {τ : ℝ} (hτ : 0 ≤ τ) (p : α → ℝ) (i : α) :
    light τ p i ≤ τ := by unfold light; split_ifs with h; exact h; exact hτ

lemma sum_light_le_one {τ : ℝ} {p : α → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i, p i = 1) : ∑ i, light τ p i ≤ 1 := by
  calc
    _ ≤ ∑ i, p i := sum_le_sum (fun i _ => light_le hp i)
    _ = 1 := hsum

lemma sum_light_sq_le {τ : ℝ} (hτ : 0 ≤ τ) {p : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∑ i, light τ p i ^ 2 ≤ τ := by
  calc
    _ ≤ ∑ i, τ * light τ p i := sum_le_sum (fun i _ => by
      nlinarith [light_nonneg (τ := τ) hp i, light_le_threshold hτ p i])
    _ = τ * ∑ i, light τ p i := by rw [mul_sum]
    _ ≤ τ * 1 := mul_le_mul_of_nonneg_left (sum_light_le_one hp hsum) hτ
    _ = τ := mul_one _

/-- Pointwise removal of all pairs with a heavy coordinate. -/
lemma remove_heavy_pointwise {τ p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (_ht : 0 ≤ t) (ht' : t ≤ 1) :
    p * q * t ≤ (if p ≤ τ then p else 0) * (if q ≤ τ then q else 0) * t +
      (p - if p ≤ τ then p else 0) * q + p * (q - if q ≤ τ then q else 0) := by
  split_ifs <;> nlinarith [mul_nonneg hp hq, mul_nonneg (mul_nonneg hp hq) _ht,
    mul_nonneg (mul_nonneg hp hq) (sub_nonneg.mpr ht')]

noncomputable def passing {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (e : α → V) (p q : α → ℝ) : ℝ :=
  ∑ u, ∑ v, p u * q v * if B (e u) (e v) = 0 then 1 else 0

/-- Exactly the independent law (not a conditioned or resampled law). -/
theorem passing_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (e : α → V) {p q : α → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    {τ β : ℝ}
    (hlight : ∑ u, ∑ v, light τ p u * sign (B (e u) (e v)) * light τ q v ≤ β) :
    passing B e p q ≤ (∑ u, (p u - light τ p u)) +
      (∑ v, (q v - light τ q v)) + (1 + β) / 2 := by
  have heq : passing B e (light τ p) (light τ q) =
      ((∑ u, light τ p u) * (∑ v, light τ q v) +
        ∑ u, ∑ v, light τ p u * sign (B (e u) (e v)) * light τ q v) / 2 := by
    unfold passing
    calc
      _ = ∑ u, ∑ v, (light τ p u * light τ q v +
          light τ p u * sign (B (e u) (e v)) * light τ q v) / 2 := by
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        rw [sign_indicator]
        ring
      _ = _ := by
        simp only [← sum_div, sum_add_distrib, ← mul_sum, ← sum_mul]
  have hmass : (∑ u, light τ p u) * (∑ v, light τ q v) ≤ 1 := by
    exact (mul_le_mul (sum_light_le_one hp hpsum) (sum_light_le_one hq hqsum)
      (sum_nonneg (fun i _ => light_nonneg hq i)) zero_le_one).trans_eq (mul_one 1)
  have hll : passing B e (light τ p) (light τ q) ≤ (1 + β) / 2 := by
    rw [heq]
    linarith
  have hpoint := fun (u v : α) => remove_heavy_pointwise (τ := τ) (hp u) (hq v)
    (show (0 : ℝ) ≤ if B (e u) (e v) = 0 then 1 else 0 by split_ifs <;> norm_num)
    (show (if B (e u) (e v) = 0 then (1 : ℝ) else 0) ≤ 1 by split_ifs <;> norm_num)
  have hsum := sum_le_sum (s := univ) (fun u _ =>
    sum_le_sum (s := univ) (fun v _ => hpoint u v))
  change passing B e p q ≤ ∑ u, ∑ v,
    ((light τ p u * light τ q v * if B (e u) (e v) = 0 then 1 else 0) +
      (p u - light τ p u) * q v + p u * (q v - light τ q v)) at hsum
  simp only [sum_add_distrib, ← mul_sum, hqsum, mul_one, ← sum_mul, hpsum, one_mul] at hsum
  change passing B e p q ≤ passing B e (light τ p) (light τ q) +
    (∑ u, (p u - light τ p u)) + (∑ v, (q v - light τ q v)) at hsum
  linarith

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V]

lemma light_spectral_bound (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    {p q : {v : V // v ≠ 0} → ℝ} (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1) {τ : ℝ} (hτ : 0 ≤ τ) :
    |∑ u : {v : V // v ≠ 0}, ∑ v : {v : V // v ≠ 0},
      light τ p u * sign (B u v) * light τ q v| ≤ Real.sqrt (Fintype.card V) * τ := by
  have h := nonzero_bilinear_sq_le B hB (light τ p) (light τ q)
  have hm : (Fintype.card V : ℝ) * (∑ u, light τ p u ^ 2) * (∑ v, light τ q v ^ 2) ≤
      (Fintype.card V : ℝ) * τ ^ 2 := by
    calc
      _ ≤ (Fintype.card V : ℝ) * τ * τ := by
        gcongr
        · exact sum_light_sq_le hτ hp hpsum
        · exact sum_light_sq_le hτ hq hqsum
      _ = _ := by ring
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hτ)).mp
  rw [sq_abs, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact h.trans hm

end SmoothObstruction.GraphBound

namespace SmoothObstruction.GraphEntropy
open FiniteEntropy GraphBound BinaryCharacter

lemma spectral_small {L : ℝ} (hL : 1 ≤ L)
    (hlog : 1000 * Real.log 2 ≤ Real.log L) :
    Real.sqrt (L + 1) * Real.exp (-(4 / 5 : ℝ) * Real.log L) ≤ 1 / 50 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : -(3 / 5 : ℝ) * Real.log L ≤ -(14 * Real.log 2) := by linarith
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_nonneg _))
    (by norm_num : (0 : ℝ) ≤ 1 / 50)).mp
  rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ L + 1), sq (Real.exp _), ← Real.exp_add]
  calc
    _ ≤ 2 * L * Real.exp (-(4 / 5 : ℝ) * Real.log L + -(4 / 5 : ℝ) * Real.log L) := by
      gcongr
      linarith
    _ = 2 * Real.exp (-(3 / 5 : ℝ) * Real.log L) := by
      conv_lhs => rw [mul_assoc, show L = Real.exp (Real.log L) from
        (Real.exp_log (by linarith : 0 < L)).symm]
      rw [← Real.exp_add, Real.log_exp]
      congr 2
      ring
    _ ≤ 2 * Real.exp (-(14 * Real.log 2)) := by gcongr
    _ = 2 / (2 : ℝ) ^ 14 := by
      rw [Real.exp_neg, show (14 : ℝ) * Real.log 2 = (14 : ℕ) * Real.log 2 by norm_num,
        Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    _ ≤ (1 / 50 : ℝ) ^ 2 := by norm_num

variable {α ξ : Type*} [Fintype α] [Nonempty α] [Fintype ξ]

lemma average_heavy_le (w : ξ → ℝ) (p : ξ → α → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hp : ∀ x i, 0 ≤ p x i) (hp1 : ∀ x, ∑ i, p x i = 1)
    (hH : (99 / 100 : ℝ) * Real.log (Fintype.card α) ≤ ∑ x, w x * natEntropy (p x))
    (hlog : 1000 * Real.log 2 ≤ Real.log (Fintype.card α)) :
    ∑ x, w x * heavyMass (4 / 5) (p x) ≤ 11 / 200 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogpos : 0 < Real.log (Fintype.card α) := by linarith
  have hsum := sum_le_sum (s := univ) (fun x _ =>
    mul_le_mul_of_nonneg_left (entropy_le_heavy (hp x) (hp1 x) (4 / 5)) (hw x))
  have hrhs : (∑ x, w x * (Real.log 2 + (1 - (1 - (4 / 5 : ℝ)) *
      heavyMass (4 / 5) (p x)) * Real.log (Fintype.card α))) =
      Real.log 2 + (1 - (1 / 5 : ℝ) * (∑ x, w x * heavyMass (4 / 5) (p x))) *
        Real.log (Fintype.card α) := by
    calc
      _ = ∑ x, (w x * Real.log 2 + w x * Real.log (Fintype.card α) -
          (w x * heavyMass (4 / 5) (p x)) * ((1 / 5 : ℝ) * Real.log (Fintype.card α))) := by
        apply sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [sum_sub_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← sum_mul, hw1]
        ring
  rw [hrhs] at hsum
  have hh : (1 / 5 : ℝ) * (∑ x, w x * heavyMass (4 / 5) (p x)) *
      Real.log (Fintype.card α) ≤ (11 / 1000 : ℝ) * Real.log (Fintype.card α) := by
    linarith
  have h := (mul_le_mul_iff_left₀ hlogpos).mp hh
  linarith

omit [Nonempty α] in
lemma tail_eq_heavy {p : α → ℝ} :
    (∑ i, (p i - light (Real.exp (-(4 / 5 : ℝ) * Real.log (Fintype.card α))) p i)) =
      heavyMass (4 / 5) p := by
  apply sum_congr rfl
  intro i _
  unfold light
  split_ifs with h h' h'
  · linarith
  · simp
  · simp
  · simp_all only [not_le]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The independent graph-test bound needed in the actual cell experiment.
This retains diagonal pairs and uses the original (not renormalized) input laws.
The finite index includes both the cell and the coordinate of the label list. -/
theorem graph_independent_finite (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (w : ξ → ℝ) (p q : ξ → {v : V // v ≠ 0} → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw1 : ∑ x, w x = 1)
    (hp : ∀ x i, 0 ≤ p x i) (hq : ∀ x i, 0 ≤ q x i)
    (hp1 : ∀ x, ∑ i, p x i = 1) (hq1 : ∀ x, ∑ i, q x i = 1)
    (hHp : (99 / 100 : ℝ) * Real.log (Fintype.card {v : V // v ≠ 0}) ≤
      ∑ x, w x * natEntropy (p x))
    (hHq : (99 / 100 : ℝ) * Real.log (Fintype.card {v : V // v ≠ 0}) ≤
      ∑ x, w x * natEntropy (q x))
    (hlog : 1000 * Real.log 2 ≤ Real.log (Fintype.card {v : V // v ≠ 0})) :
    ∑ x, w x * passing B Subtype.val (p x) (q x) ≤ 31 / 50 := by
  have : Nonempty {v : V // v ≠ 0} := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact ⟨⟨v, hv⟩⟩
  let L : ℝ := Fintype.card {v : V // v ≠ 0}
  let τ := Real.exp (-(4 / 5 : ℝ) * Real.log L)
  have hL : 1 ≤ L := by
    dsimp [L]
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ‹Nonempty {v : V // v ≠ 0}›))
  have hcard : (Fintype.card V : ℝ) = L + 1 := by
    have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : V))
    simp only [Fintype.card_option] at h
    dsimp [L]
    exact_mod_cast h.symm
  have hτ : 0 ≤ τ := Real.exp_nonneg _
  have hβ : Real.sqrt (Fintype.card V) * τ ≤ 1 / 50 := by
    rw [hcard]
    exact spectral_small hL hlog
  have hsingle (x : ξ) : passing B Subtype.val (p x) (q x) ≤
      heavyMass (4 / 5) (p x) + heavyMass (4 / 5) (q x) + 51 / 100 := by
    have hs := light_spectral_bound B hB (hp x) (hq x) (hp1 x) (hq1 x) hτ
    have hh := passing_le B Subtype.val (hp x) (hq x) (hp1 x) (hq1 x)
      ((le_abs_self _).trans (hs.trans hβ))
    rw [tail_eq_heavy, tail_eq_heavy] at hh
    norm_num at hh ⊢
    exact hh
  have havg := sum_le_sum (s := univ) (fun x _ => mul_le_mul_of_nonneg_left (hsingle x) (hw x))
  simp only [mul_add, sum_add_distrib, ← sum_mul, hw1, one_mul] at havg
  have hpH := average_heavy_le w p hw hw1 hp hp1 hHp hlog
  have hqH := average_heavy_le w q hw hw1 hq hq1 hHq hlog
  linarith

end SmoothObstruction.GraphEntropy

namespace SmoothObstruction.IndependentUpper
open Finset FiniteLaw FiniteEntropy
variable {C J V : Type*} [Fintype C] [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]

/-- The independent upper bound of source section 7 from the entropies of
actual whole lists and the finite cell cost. Independence is used only
conditional on the FULL index (cell,entry), never after mixing entries. -/
theorem list_graph_upper (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (P : Law C) (U W : C → Law (J → {v : V // v≠0}))
    (hU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (mixture P U))
    (hW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (mixture P W))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤Real.log (Fintype.card {v : V // v≠0})) :
    (∑ c,P.mass c*∑ j,GraphBound.passing B Subtype.val
      (push (U c) (fun w => w j)).mass (push (W c) (fun w => w j)).mass)/Fintype.card J≤31/50 := by
  let w : C × J → ℝ := fun z => P.mass z.1/Fintype.card J
  let p : C × J → {v : V // v≠0} → ℝ := fun z => (push (U z.1) (fun a => a z.2)).mass
  let q : C × J → {v : V // v≠0} → ℝ := fun z => (push (W z.1) (fun a => a z.2)).mass
  have hJ : (0:ℝ)<Fintype.card J := by exact_mod_cast Fintype.card_pos
  have hw : ∀ z,0≤w z := fun z => div_nonneg (P.nonneg z.1) hJ.le
  have hw1 : ∑ z,w z=1 := by
    simp only [w,Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul,
      mul_div_cancel₀ _ hJ.ne',P.total]
  have hweight (F : C × J → ℝ) :
      (∑ z,w z*F z)=(∑ c,P.mass c*∑ j,F (c,j))/Fintype.card J := by
    simp only [w,Fintype.sum_prod_type,div_mul_eq_mul_div,←sum_div,mul_sum]
  have hp : (99/100:ℝ)*Real.log (Fintype.card {v : V // v≠0})≤
      ∑ z,w z*natEntropy (p z) := by
    rw [hweight,le_div_iff₀ hJ]
    have hh := conditional_entry_sum P U
    change _≤∑ c,P.mass c*∑ j,entropy (push (U c) (fun a => a j))
    calc
      _ = (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) -
          (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) := by ring
      _ ≤ entropy (mixture P U)-Real.log (Fintype.card C) := sub_le_sub hU hC
      _ ≤ _ := by simpa only [entropy,push_mass_canonical] using hh
  have hq : (99/100:ℝ)*Real.log (Fintype.card {v : V // v≠0})≤
      ∑ z,w z*natEntropy (q z) := by
    rw [hweight,le_div_iff₀ hJ]
    have hh := conditional_entry_sum P W
    change _≤∑ c,P.mass c*∑ j,entropy (push (W c) (fun a => a j))
    calc
      _ = (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) -
          (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}) := by ring
      _ ≤ entropy (mixture P W)-Real.log (Fintype.card C) := sub_le_sub hW hC
      _ ≤ _ := by simpa only [entropy,push_mass_canonical] using hh
  have hh := GraphEntropy.graph_independent_finite B hB w p q hw hw1
    (fun z => (push (U z.1) (fun a => a z.2)).nonneg)
    (fun z => (push (W z.1) (fun a => a z.2)).nonneg)
    (fun z => (push (U z.1) (fun a => a z.2)).total)
    (fun z => (push (W z.1) (fun a => a z.2)).total) hp hq hlog
  rw [hweight] at hh
  exact hh
end SmoothObstruction.IndependentUpper

namespace SmoothObstruction.PairLaw
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C A B : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A] [Nonempty A]
  [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B] [Nonempty B]

/-- Exact original-law finite observation formula for the weighted same-cell
pair experiment. Zero-mass cells vanish without renormalizing the experiment. -/
theorem rectangle_conditional (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (U : X → A) (hU : Measurable U)
    (V : X → B) (hV : Measurable V) (a : A) (b : B) :
    (law μ P).real ((U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}))=
      ∑ c,(observed μ P hP).mass c*
        (conditionalObserved μ U hU P hP c).mass a*
        (conditionalObserved μ V hV P hP c).mass b := by
  let := law_probability μ P hP
  let E := (U ⁻¹' {a}) ×ˢ (V ⁻¹' {b})
  have hfin (c : C) : ((μ (P ⁻¹' {c}))⁻¹ • (cell μ P c).prod (cell μ P c)) E≠∞ := by
    apply ne_top_of_le_ne_top (measure_ne_top (law μ P) E)
    rw [law,Measure.finsetSum_apply]
    exact Finset.single_le_sum
      (f := fun cellIndex : C =>
        ((μ (P ⁻¹' {cellIndex}))⁻¹ • (cell μ P cellIndex).prod (cell μ P cellIndex)) E)
      (fun _ _ => bot_le) (mem_univ c)
  change ((law μ P) E).toReal=_
  rw [law,Measure.finsetSum_apply,ENNReal.toReal_sum (fun c _ => hfin c)]
  apply sum_congr rfl
  intro c _
  simp only [Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  rw [show E=(U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}) from rfl,Measure.prod_prod,
    ENNReal.toReal_mul,cell,Measure.restrict_apply (hU (measurableSet_singleton a)),
    Measure.restrict_apply (hV (measurableSet_singleton b))]
  have hEU : (U ⁻¹' {a}) ∩ (P ⁻¹' {c})={x | P x=c ∧ U x=a} := by
    ext x; simp only [mem_inter_iff,Set.mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
  have hEV : (V ⁻¹' {b}) ∩ (P ⁻¹' {c})={x | P x=c ∧ V x=b} := by
    ext x; simp only [mem_inter_iff,Set.mem_preimage,mem_singleton_iff,mem_ofPred_eq,and_comm]
  rw [hEU,hEV]
  change ((observed μ P hP).mass c)⁻¹*
    (μ.real {x | P x=c ∧ U x=a}*μ.real {x | P x=c ∧ V x=b})=_
  rw [←conditionalObserved_mass μ U hU P hP,←conditionalObserved_mass μ V hV P hP]
  by_cases hz : (observed μ P hP).mass c=0
  · simp only [hz,inv_zero,zero_mul]
  · field_simp

/-- The full pair label law, not merely a product assertion for individual
entries. It determines the single statistic used on both sides of the final
contradiction. -/
theorem observed_pair (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P) (U : X → A) (hU : Measurable U)
    (V : X → B) (hV : Measurable V) :
    letI := law_probability μ P hP
    ∀ a b,(observed (law μ P) (fun z : X × X => (U z.1,V z.2))
      ((hU.comp measurable_fst).prodMk (hV.comp measurable_snd))).mass (a,b)=
      ∑ c,(observed μ P hP).mass c*
        (conditionalObserved μ U hU P hP c).mass a*
        (conditionalObserved μ V hV P hP c).mass b := by
  intro a b
  change (law μ P).real {z : X × X | (U z.1,V z.2)=(a,b)}=_
  have he : {z : X × X | (U z.1,V z.2)=(a,b)}=(U ⁻¹' {a}) ×ˢ (V ⁻¹' {b}) := by
    ext z; simp only [Set.mem_ofPred_eq,Prod.mk.injEq,mem_prod,Set.mem_preimage,mem_singleton_iff]
  rw [he]
  exact rectangle_conditional μ P hP U hU V hV a b
end SmoothObstruction.PairLaw

namespace SmoothObstruction.PairUpper
open MeasureTheory Set Finset FiniteLaw
open scoped ENNReal
variable {X C J V : Type*} [MeasurableSpace X]
  [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
  [Fintype J] [DecidableEq J] [Nonempty J]
  [AddCommGroup V] [Module (ZMod 2) V] [Fintype V] [DecidableEq V] [Nontrivial V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

instance nonzeroNonempty : Nonempty {v : V // v≠0} := by
  obtain ⟨v,hv⟩ := exists_ne (0:V)
  exact ⟨⟨v,hv⟩⟩

noncomputable def statistic (B : LinearMap.BilinForm (ZMod 2) V)
    (u v : J → {v : V // v≠0}) : ℝ :=
  (∑ j,if B (u j) (v j)=0 then (1:ℝ) else 0)/Fintype.card J

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Nontrivial V] [Nonempty J] in
lemma product_push_expect {α β γ δ : Type*} [Fintype α] [Fintype β]
    [Fintype γ] [Fintype δ] (P : Law α) (Q : Law β)
    (f : α → γ) (h : β → δ) (g : γ → δ → ℝ) :
    (∑ a,∑ b,P.mass a*Q.mass b*g (f a) (h b))=
      ∑ c,∑ d,(push P f).mass c*(push Q h).mass d*g c d := by
  simp only [mul_assoc,←mul_sum]
  simp only [expect_push_sum]

omit [MeasurableSpace V] [MeasurableSingletonClass V] [Nonempty J] [Nontrivial V] in
lemma product_statistic (B : LinearMap.BilinForm (ZMod 2) V)
    (P Q : Law (J → {v : V // v≠0})) :
    (∑ u,∑ v,P.mass u*Q.mass v*statistic B u v)=
    (∑ j,GraphBound.passing B Subtype.val
      (push P (fun u => u j)).mass (push Q (fun v => v j)).mass)/Fintype.card J := by
  simp only [statistic,←mul_div_assoc,←sum_div,mul_sum]
  congr 1
  conv_lhs => enter [2,u]; rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  simpa only [GraphBound.passing, push_mass_canonical] using
    product_push_expect P Q (fun u => u j) (fun v => v j)
      (fun u v => if B u v=0 then 1 else 0)

omit [Nonempty J] in
/-- The passing statistic on the original pair law. This identifies exactly
its finite expectation with source (7.2), using the full conditional lists. -/
theorem expectation_formula (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) :
    letI := PairLaw.law_probability μ P hP
    (∑ uv,(observed (PairLaw.law μ P) (fun z : X × X => (U z.1,W z.2))
      ((hU.comp measurable_fst).prodMk (hW.comp measurable_snd))).mass uv*
      statistic B uv.1 uv.2)=
    (∑ c,(observed μ P hP).mass c*∑ j,GraphBound.passing B Subtype.val
      (push (conditionalObserved μ U hU P hP c) (fun u => u j)).mass
      (push (conditionalObserved μ W hW P hP c) (fun v => v j)).mass)/Fintype.card J := by
  let := PairLaw.law_probability μ P hP
  have hm := PairLaw.observed_pair μ P hP U hU W hW
  simp only [Fintype.sum_prod_type,hm,sum_mul]
  conv_lhs => enter [2,u]; rw [sum_comm]
  rw [sum_comm]
  have hp (c : C) := product_statistic B (conditionalObserved μ U hU P hP c)
    (conditionalObserved μ W hW P hP c)
  simp only [mul_assoc,←mul_sum] at hp
  simp only [mul_assoc,←mul_sum,hp,←mul_div_assoc,←sum_div]

/-- Section 7's .62 upper bound for the actual same-cell measure. The two
entropy hypotheses refer to the original input probability, not the retained
or renormalized measure. -/
theorem expectation_upper (μ : Measure X) [IsProbabilityMeasure μ]
    (P : X → C) (hP : Measurable P)
    (U W : X → J → {v : V // v≠0}) (hU : Measurable U) (hW : Measurable W)
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.Nondegenerate)
    (hentU : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ U hU))
    (hentW : (249/250:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0})≤
      entropy (observed μ W hW))
    (hC : Real.log (Fintype.card C)≤
      (3/500:ℝ)*Fintype.card J*Real.log (Fintype.card {v : V // v≠0}))
    (hlog : 1000*Real.log 2≤Real.log (Fintype.card {v : V // v≠0})) :
    letI := PairLaw.law_probability μ P hP
    (∑ uv,(observed (PairLaw.law μ P) (fun z : X × X => (U z.1,W z.2))
      ((hU.comp measurable_fst).prodMk (hW.comp measurable_snd))).mass uv*
      statistic B uv.1 uv.2)≤31/50 := by
  let := PairLaw.law_probability μ P hP
  exact (expectation_formula μ P hP U W hU hW B).trans_le (by
    rw [observed_mixture μ U hU P hP] at hentU
    rw [observed_mixture μ W hW P hP] at hentW
    exact IndependentUpper.list_graph_upper B hB (observed μ P hP)
      (conditionalObserved μ U hU P hP) (conditionalObserved μ W hW P hP)
      hentU hentW hC hlog)
end SmoothObstruction.PairUpper

end

end OAI
