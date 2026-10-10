import Mathlib

namespace OAI

section

open Finset

namespace SmoothObstruction.SymplecticSampling

lemma bit_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  exact h a

lemma bit_one {a : ZMod 2} (h : a ≠ 0) : a = 1 := (bit_cases a).resolve_left h

lemma bit_neg (a : ZMod 2) : -a = a := by
  rcases bit_cases a with rfl | rfl <;> decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

lemma add_self (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 by decide, zero_smul]

lemma alt_symm {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt) (x y : V) :
    B x y = B y x := by
  rw [← hB.neg_eq x y, bit_neg]

lemma transvection_preserves {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (v x y : V) :
    B (LinearEquiv.transvection (hB v) x) (LinearEquiv.transvection (hB v) y) = B x y := by
  simp only [LinearEquiv.transvection.apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB v, mul_zero, add_zero]
  rw [← alt_symm hB x v]
  rcases bit_cases (B v x) with hx | hx <;>
    rcases bit_cases (B v y) with hy | hy <;>
    simp [hx, hy, alt_symm hB x v, add_assoc,
      show (1 : ZMod 2) + 1 = 0 by decide]

lemma transvection_moves {B : LinearMap.BilinForm (ZMod 2) V} (hB : B.IsAlt)
    {v w : V} (hvw : B v w = 1) :
    LinearEquiv.transvection (hB (v + w)) v = w := by
  rw [LinearEquiv.transvection.apply, map_add, LinearMap.add_apply, hB v,
    alt_symm hB w v, hvw, zero_add, one_smul, ← add_assoc, add_self, zero_add]

lemma exists_pairing_one {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.Nondegenerate) {v : V} (hv : v ≠ 0) : ∃ w, B v w = 1 := by
  have h : ¬ ∀ w, B v w = 0 := fun h => hv (hB.1 v h)
  obtain ⟨w, hw⟩ := not_forall.mp h
  exact ⟨w, bit_one hw⟩

lemma common_pairing_one {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.Nondegenerate) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ z, B v z = 1 ∧ B w z = 1 := by
  obtain ⟨a, ha⟩ := exists_pairing_one hB hv
  obtain ⟨b, hb⟩ := exists_pairing_one hB hw
  rcases bit_cases (B w a) with hwa | hwa
  · rcases bit_cases (B v b) with hvb | hvb
    · exact ⟨a + b, by simp [ha, hvb], by simp [hwa, hb]⟩
    · exact ⟨b, hvb, hb⟩
  · exact ⟨a, ha, hwa⟩

/-- Explicit symplectic transitivity in characteristic two, using at most two
transvections. This proves the uniform one-label marginal input to the actual
sequential word sampling, without assuming a symplectic-basis theorem. -/
theorem symplectic_transitive {B : LinearMap.BilinForm (ZMod 2) V}
    (hB : B.IsAlt) (hnd : B.Nondegenerate) {v w : V} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ e : V ≃ₗ[ZMod 2] V, e v = w ∧ ∀ x y, B (e x) (e y) = B x y := by
  obtain ⟨z, hvz, hwz⟩ := common_pairing_one hnd hv hw
  let e₁ := LinearEquiv.transvection (hB (v + z))
  let e₂ := LinearEquiv.transvection (hB (z + w))
  refine ⟨e₁.trans e₂, ?_, ?_⟩
  · change e₂ (e₁ v) = w
    rw [show e₁ v = z from transvection_moves hB hvz]
    exact transvection_moves hB ((alt_symm hB z w).trans hwz)
  · intro x y
    exact (transvection_preserves hB (z + w) (e₁ x) (e₁ y)).trans
      (transvection_preserves hB (v + z) x y)

section Cardinality
variable [Fintype V] [DecidableEq V]
noncomputable local instance {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Fintype f.ker := Fintype.ofFinite _

noncomputable def nonzeroKerEquiv {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    {u : f.ker // u ≠ 0} ≃ {v : V // v ≠ 0 ∧ f v = 0} where
  toFun u := ⟨u.val.val, by
    constructor
    · intro h
      exact u.property (Subtype.ext h)
    · exact u.val.property⟩
  invFun v := ⟨⟨v.val, v.property.2⟩, by
    intro h
    exact v.property.1 (congrArg Subtype.val h)⟩
  left_inv u := rfl
  right_inv v := rfl

lemma card_nonzero_ker {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    Fintype.card f.ker = Fintype.card {v : V // v ≠ 0 ∧ f v = 0} + 1 := by
  have h := Fintype.card_congr (Equiv.optionSubtypeNe (0 : f.ker))
  rw [Fintype.card_option, Fintype.card_congr (nonzeroKerEquiv f)] at h
  exact h.symm

/-- At most k linear equations remove at most k binary dimensions, even when
they are dependent. The zero vector is then removed exactly once. -/
theorem common_kernel_lower {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2)) :
    2 ^ (Module.finrank (ZMod 2) V - k) ≤
      Fintype.card {v : V // v ≠ 0 ∧ f v = 0} + 1 := by
  have hr := f.finrank_range_add_finrank_ker
  have hk : Module.finrank (ZMod 2) f.range ≤ k := by
    simpa using (Submodule.finrank_le f.range)
  have hdim : Module.finrank (ZMod 2) V - k ≤ Module.finrank (ZMod 2) f.ker := by omega
  calc
    _ ≤ 2 ^ Module.finrank (ZMod 2) f.ker := Nat.pow_le_pow_right (by decide) hdim
    _ = Fintype.card f.ker := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ = _ := card_nonzero_ker f

/-- The quantitative bound actually used in source (word-choices), with the
original nonzero alphabet and dependent equations allowed. -/
theorem common_kernel_choices {k : ℕ} (f : V →ₗ[ZMod 2] (Fin k → ZMod 2))
    (hk : 1 ≤ k) (hd : k + 1 ≤ Module.finrank (ZMod 2) V) :
    Fintype.card {v : V // v ≠ 0} ≤
      2 ^ (2 * k) * Fintype.card {v : V // v ≠ 0 ∧ f v = 0} := by
  let d := Module.finrank (ZMod 2) V
  let c := Fintype.card {v : V // v ≠ 0 ∧ f v = 0}
  have hlo : 2 ^ (d - k) ≤ c + 1 := common_kernel_lower f
  have hexp : d - k = (d - k - 1) + 1 := by dsimp [d]; omega
  have hpow : 2 ^ (d - k - 1) ≤ c := by
    rw [hexp, pow_succ] at hlo
    have hn : 1 ≤ 2 ^ (d - k - 1) := Nat.one_le_pow _ _ (by decide)
    omega
  have hdim : d ≤ 2 * k + (d - k - 1) := by dsimp [d]; omega
  have hfull : Fintype.card V ≤ 2 ^ (2 * k) * c := calc
    _ = 2 ^ d := by rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    _ ≤ 2 ^ (2 * k + (d - k - 1)) := Nat.pow_le_pow_right (by decide) hdim
    _ = 2 ^ (2 * k) * 2 ^ (d - k - 1) := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ hpow
  exact (Fintype.card_subtype_le _).trans hfull

variable (B : LinearMap.BilinForm (ZMod 2) V)

/-- The exact nonzero choices, not an independent-equations approximation. -/
noncomputable def allowed {k : ℕ} (u : Fin k → V) : Finset {v : V // v ≠ 0} :=
  univ.filter (fun v => ∀ j, B (u j) v.val = 0)

noncomputable def equationMap {k : ℕ} (u : Fin k → V) : V →ₗ[ZMod 2] (Fin k → ZMod 2) :=
  LinearMap.pi (fun j => B (u j))

lemma mem_allowed {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) :
    v ∈ allowed B u ↔ ∀ j, B (u j) v.val = 0 := by
  classical
  simp [allowed]

lemma allowed_card {k : ℕ} (u : Fin k → V) :
    (allowed B u).card = Fintype.card {v : V // v ≠ 0 ∧ equationMap B u v = 0} := by
  classical
  let e : {v // v ∈ allowed B u} ≃ {v : V // v ≠ 0 ∧ equationMap B u v = 0} :=
    { toFun := fun v => ⟨v.val.val, v.val.property, by
        ext j
        exact (mem_allowed B u v.val).mp v.property j⟩
      invFun := fun v => ⟨⟨v.val, v.property.1⟩, (mem_allowed B u _).mpr (fun j =>
        congrFun v.property.2 j)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_coe _).symm.trans (Fintype.card_congr e)

lemma allowed_nonempty {k : ℕ} (u : Fin k → V)
    (hd : k + 1 ≤ Module.finrank (ZMod 2) V) : (allowed B u).Nonempty := by
  have h := common_kernel_lower (equationMap B u)
  rw [← allowed_card B u] at h
  have hpow : 2 ≤ 2 ^ (Module.finrank (ZMod 2) V - k) := by
    simpa using Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤
      Module.finrank (ZMod 2) V - k by omega)
  exact card_pos.mp (by omega)

/-- Uniform sampling among all allowed nonzero labels. -/
noncomputable def kernel {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) : ℝ :=
  if v ∈ allowed B u then ((allowed B u).card : ℝ)⁻¹ else 0

lemma kernel_nonneg {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0}) :
    0 ≤ kernel B u v := by
  unfold kernel
  split_ifs <;> positivity

lemma kernel_sum {k : ℕ} (u : Fin k → V)
    (hd : k + 1 ≤ Module.finrank (ZMod 2) V) : ∑ v, kernel B u v = 1 := by
  classical
  have hc : ((allowed B u).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Finset.card_ne_zero.mpr (allowed_nonempty B u hd))
  simp only [kernel, sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
  exact mul_inv_cancel₀ hc

lemma kernel_upper {k : ℕ} (u : Fin k → V) (v : {v : V // v ≠ 0})
    (hk : 1 ≤ k) (hd : k + 1 ≤ Module.finrank (ZMod 2) V) :
    kernel B u v ≤ (2 : ℝ) ^ (2 * k) / Fintype.card {v : V // v ≠ 0} := by
  have hN : 0 < (Fintype.card {v : V // v ≠ 0} : ℝ) := by
    have : Nonempty {v : V // v ≠ 0} := (allowed_nonempty B u hd).nonempty
    exact_mod_cast Fintype.card_pos
  have hc : 0 < ((allowed B u).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (allowed_nonempty B u hd)
  have hb : (Fintype.card {v : V // v ≠ 0} : ℝ) ≤
      (2 : ℝ) ^ (2 * k) * (allowed B u).card := by
    have h := common_kernel_choices (equationMap B u) hk hd
    rw [← allowed_card B u] at h
    exact_mod_cast h
  unfold kernel
  split_ifs
  · apply (le_div_iff₀ hN).mpr
    apply (inv_mul_le_iff₀ hc).mpr
    simpa only [mul_comm] using hb
  · positivity

noncomputable def nonzeroEquiv (e : V ≃ₗ[ZMod 2] V) :
    {v : V // v ≠ 0} ≃ {v : V // v ≠ 0} where
  toFun v := ⟨e v.val, fun h => v.property (e.injective (h.trans e.map_zero.symm))⟩
  invFun v := ⟨e.symm v.val, fun h => v.property (e.symm.injective (h.trans e.symm.map_zero.symm))⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.val)
  right_inv v := Subtype.ext (e.apply_symm_apply v.val)

lemma allowed_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) (v : {v : V // v ≠ 0}) :
    nonzeroEquiv e v ∈ allowed B (e ∘ u) ↔ v ∈ allowed B u := by
  simp only [mem_allowed, nonzeroEquiv, Equiv.coe_fn_mk, Function.comp_apply, he]

lemma allowed_card_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) :
    (allowed B (e ∘ u)).card = (allowed B u).card := by
  classical
  have h := Fintype.card_congr ((nonzeroEquiv e).subtypeEquiv
    (fun v => (allowed_equivariant B u e he v).symm))
  simpa only [Fintype.card_coe] using h.symm

lemma kernel_equivariant {k : ℕ} (u : Fin k → V) (e : V ≃ₗ[ZMod 2] V)
    (he : ∀ x y, B (e x) (e y) = B x y) (v : {v : V // v ≠ 0}) :
    kernel B (e ∘ u) (nonzeroEquiv e v) = kernel B u v := by
  simp only [kernel, allowed_equivariant B u e he, allowed_card_equivariant B u e he]

end Cardinality

end SmoothObstruction.SymplecticSampling

namespace SmoothObstruction.SequentialLaw

variable {A : Type*}

/-- A finite left-to-right sampling law. The kernel at time k may depend on
all k preceding labels; no independence inside a group is assumed. -/
def weight (K : (k : ℕ) → (Fin k → A) → A → ℝ) : (n : ℕ) → (Fin n → A) → ℝ
  | 0, _ => 1
  | n + 1, w => weight K n (Fin.init w) * K n (Fin.init w) (w (Fin.last n))

@[simp] lemma weight_zero (K : (k : ℕ) → (Fin k → A) → A → ℝ) (w : Fin 0 → A) :
    weight K 0 w = 1 := rfl

@[simp] lemma weight_snoc (K : (k : ℕ) → (Fin k → A) → A → ℝ)
    {n : ℕ} (w : Fin n → A) (a : A) :
    weight K (n + 1) (Fin.snoc w a) = weight K n w * K n w a := by
  simp [weight]

lemma weight_nonneg {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w a, 0 ≤ K k w a) : ∀ n w, 0 ≤ weight K n w
  | 0, _ => by simp
  | n + 1, w => mul_nonneg (weight_nonneg hK n _) (hK n _ _)

variable [Fintype A]

omit [Fintype A] in
lemma snoc_equiv_apply {n : ℕ} (p : A × (Fin n → A)) :
    (Fin.snocEquiv (fun _ : Fin (n + 1) => A)) p = Fin.snoc p.2 p.1 := rfl

lemma sum_weight {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w, ∑ a, K k w a = 1) : ∀ n, ∑ w, weight K n w = 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp]
    simp only [snoc_equiv_apply, weight_snoc, Fintype.sum_prod_type]
    rw [sum_comm]
    simp only [← mul_sum, hK, mul_one]
    exact ih

variable [DecidableEq A]

def mark (m : Option A) (a : A) : ℝ :=
  match m with
  | none => 1
  | some b => if a = b then 1 else 0

def test {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) : ℝ :=
  ∏ i, mark (m i) (w i)

omit [Fintype A] in
lemma mark_nonneg (m : Option A) (a : A) : 0 ≤ mark m a := by
  cases m with
  | none => norm_num [mark]
  | some b => change 0 ≤ (if _ = b then (1 : ℝ) else 0); split_ifs <;> norm_num

omit [Fintype A] in
lemma test_nonneg {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) : 0 ≤ test m w :=
  prod_nonneg (fun i _ => mark_nonneg (m i) (w i))

omit [Fintype A] in
@[simp] lemma test_snoc {n : ℕ} (m : Fin (n + 1) → Option A) (w : Fin n → A) (a : A) :
    test m (Fin.snoc w a) = test (Fin.init m) w * mark (m (Fin.last n)) a := by
  unfold test
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rfl

lemma sum_test_succ (K : (k : ℕ) → (Fin k → A) → A → ℝ)
    {n : ℕ} (m : Fin (n + 1) → Option A) :
    (∑ w, weight K (n + 1) w * test m w) =
      ∑ w, (weight K n w * test (Fin.init m) w) *
        (∑ a, K n w a * mark (m (Fin.last n)) a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => A)).sum_comp]
  simp only [snoc_equiv_apply, weight_snoc, test_snoc, Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  ring

/-- Any list of specified coordinates has probability at most the product
of the pointwise conditional upper bounds. Unspecified labels are integrated
out, exactly as in (word-raw-sublist). -/
theorem cylinder_bound {K : (k : ℕ) → (Fin k → A) → A → ℝ} {ζ : ℝ}
    (h0 : ∀ k w a, 0 ≤ K k w a) (h1 : ∀ k w, ∑ a, K k w a = 1)
    (hζ : 0 ≤ ζ) (hK : ∀ k w a, K k w a ≤ ζ) :
    ∀ n (m : Fin n → Option A), (∑ w, weight K n w * test m w) ≤
      ∏ i, (if (m i).isSome then ζ else 1) := by
  intro n
  induction n with
  | zero => intro m; simp [test]
  | succ n ih =>
    intro m
    rw [sum_test_succ, Fin.prod_univ_castSucc]
    have hstep (w : Fin n → A) : (∑ a, K n w a * mark (m (Fin.last n)) a) ≤
        if (m (Fin.last n)).isSome then ζ else 1 := by
      cases hm : m (Fin.last n) with
      | none => simp [mark, h1]
      | some a => simpa [mark] using hK n w a
    calc
      _ ≤ ∑ w, (weight K n w * test (Fin.init m) w) *
          (if (m (Fin.last n)).isSome then ζ else 1) :=
        sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hstep w)
          (mul_nonneg (weight_nonneg h0 n w) (test_nonneg _ _)))
      _ = (∑ w, weight K n w * test (Fin.init m) w) *
          (if (m (Fin.last n)).isSome then ζ else 1) := by rw [sum_mul]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right (ih (Fin.init m))
        split_ifs <;> positivity

omit [Fintype A] [DecidableEq A] in
lemma weight_equivariant (K : (k : ℕ) → (Fin k → A) → A → ℝ) (e : A ≃ A)
    (hK : ∀ k w a, K k (e ∘ w) (e a) = K k w a) :
    ∀ n w, weight K n (e ∘ w) = weight K n w := by
  intro n
  induction n with
  | zero => intro w; rfl
  | succ n ih =>
    intro w
    simp only [weight]
    have hi : Fin.init (e ∘ w) = e ∘ Fin.init w := rfl
    rw [hi, ih, Function.comp_apply, hK]

lemma test_eq_indicator {n : ℕ} (m : Fin n → Option A) (w : Fin n → A) :
    test m w = if ∀ i a, m i = some a → w i = a then 1 else 0 := by
  classical
  have hm (i : Fin n) : mark (m i) (w i) =
      if ∀ a, m i = some a → w i = a then 1 else 0 := by
    cases h : m i <;> simp [mark]
  simp only [test, hm, Finset.prod_boole, Finset.mem_univ, forall_const]

lemma test_upper_pow {K : (k : ℕ) → (Fin k → A) → A → ℝ} {ζ : ℝ}
    (h0 : ∀ k w a, 0 ≤ K k w a) (h1 : ∀ k w, ∑ a, K k w a = 1)
    (hζ : 0 ≤ ζ) (hK : ∀ k w a, K k w a ≤ ζ)
    (n : ℕ) (m : Fin n → Option A) :
    (∑ w, weight K n w * test m w) ≤
      ζ ^ (univ.filter (fun i => (m i).isSome)).card := by
  simpa only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one]
    using cylinder_bound h0 h1 hζ hK n m

/-- The unconditioned one-coordinate law; the complete path is summed out. -/
def marginal (K : (k : ℕ) → (Fin k → A) → A → ℝ) {n : ℕ} (i : Fin n) (a : A) : ℝ :=
  ∑ w, if w i = a then weight K n w else 0

lemma sum_marginal {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (hK : ∀ k w, ∑ a, K k w a = 1) {n : ℕ} (i : Fin n) :
    ∑ a, marginal K i a = 1 := by
  unfold marginal
  rw [sum_comm]
  simp only [sum_ite_eq, mem_univ, ite_true]
  exact sum_weight hK n

lemma marginal_equivariant (K : (k : ℕ) → (Fin k → A) → A → ℝ) (e : A ≃ A)
    (hK : ∀ k w a, K k (e ∘ w) (e a) = K k w a) {n : ℕ} (i : Fin n) (a : A) :
    marginal K i (e a) = marginal K i a := by
  unfold marginal
  let E : (Fin n → A) ≃ (Fin n → A) := Equiv.piCongrRight (fun _ => e)
  rw [← E.sum_comp]
  apply sum_congr rfl
  intro w _
  change (if e (w i) = e a then weight K n (e ∘ w) else 0) = _
  simp only [e.injective.eq_iff, weight_equivariant K e hK]

/-- Equivariance under a transitive collection of label permutations gives
exactly uniform marginals, despite arbitrary dependencies between positions. -/
theorem uniform_marginal [Nonempty A]
    {K : (k : ℕ) → (Fin k → A) → A → ℝ}
    (h1 : ∀ k w, ∑ a, K k w a = 1)
    (htrans : ∀ a b : A, ∃ e : A ≃ A, e a = b ∧
      ∀ k w x, K k (e ∘ w) (e x) = K k w x)
    {n : ℕ} (i : Fin n) (a : A) : marginal K i a = 1 / Fintype.card A := by
  have heq (b : A) : marginal K i b = marginal K i a := by
    obtain ⟨e, hab, he⟩ := htrans a b
    rw [← hab]
    exact marginal_equivariant K e he i a
  have hsum := sum_marginal h1 i
  simp_rw [heq] at hsum
  simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
  have hc : (Fintype.card A : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  exact (eq_div_iff hc).mpr (by simpa only [mul_comm] using hsum)

end SmoothObstruction.SequentialLaw

namespace SmoothObstruction.GroupSampler
open Finset SymplecticSampling SequentialLaw

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [Fintype V] [DecidableEq V]
variable (B : LinearMap.BilinForm (ZMod 2) V) {K : ℕ}

/-- At time t, at most K earlier positions are constrained. None represents
an absent constraint, whose equation is identically zero. -/
def previous (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (j : Fin K) : V :=
  (back t j).elim 0 (fun r => (w r).val)

noncomputable def step (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0}) : ℝ :=
  kernel B (previous back t w) a

lemma step_sum (back : (t : ℕ) → Fin K → Option (Fin t))
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V) (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) :
    ∑ a, step B back t w a = 1 := kernel_sum B _ hd

omit [Fintype V] [DecidableEq V] in
lemma previous_equivariant (back : (t : ℕ) → Fin K → Option (Fin t))
    (e : V ≃ₗ[ZMod 2] V) (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) :
    previous back t (nonzeroEquiv e ∘ w) = e ∘ previous back t w := by
  funext j
  cases h : back t j <;> simp [previous, h, nonzeroEquiv]

lemma step_equivariant (back : (t : ℕ) → Fin K → Option (Fin t))
    (e : V ≃ₗ[ZMod 2] V) (he : ∀ x y, B (e x) (e y) = B x y)
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0}) :
    step B back t (nonzeroEquiv e ∘ w) (nonzeroEquiv e a) = step B back t w a := by
  unfold step
  rw [previous_equivariant, kernel_equivariant B _ e he]

/-- The actual sequential sampling has exactly uniform one-position laws.
This is not a product law inside a group. -/
theorem uniform_position (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (back : (t : ℕ) → Fin K → Option (Fin t))
    (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    {n : ℕ} (i : Fin n) (a : {v : V // v ≠ 0}) :
    marginal (step B back) i a = 1 / Fintype.card {v : V // v ≠ 0} := by
  let : Nonempty {v : V // v ≠ 0} := ⟨a⟩
  apply uniform_marginal (step_sum B back hd)
  intro v w
  obtain ⟨e, he, hpres⟩ := symplectic_transitive hB hnd v.property w.property
  exact ⟨nonzeroEquiv e, Subtype.ext he, step_equivariant B back e hpres⟩

/-- All sublist probabilities have the source bound, even though prior
constraints can be linearly dependent and unobserved labels are integrated out. -/
theorem raw_sublist (back : (t : ℕ) → Fin K → Option (Fin t))
    (hK : 1 ≤ K) (hd : K + 1 ≤ Module.finrank (ZMod 2) V)
    (n : ℕ) (m : Fin n → Option {v : V // v ≠ 0}) :
    (∑ w, weight (step B back) n w * test m w) ≤
      ((2 : ℝ) ^ (2 * K) / Fintype.card {v : V // v ≠ 0}) ^
        (univ.filter (fun i => (m i).isSome)).card := by
  apply test_upper_pow
  · intro t w a; exact kernel_nonneg B _ _
  · exact step_sum B back hd
  · positivity
  · intro t w a; exact kernel_upper B _ _ hK hd

lemma step_positive_constraint (back : (t : ℕ) → Fin K → Option (Fin t))
    (t : ℕ) (w : Fin t → {v : V // v ≠ 0}) (a : {v : V // v ≠ 0})
    (h : 0 < step B back t w a) {j : Fin K} {r : Fin t} (hr : back t j = some r) :
    B (w r).val a.val = 0 := by
  have hm : a ∈ allowed B (previous back t w) := by
    by_contra hc
    simp [step, kernel, hc] at h
  have he := (mem_allowed B _ _).mp hm j
  simpa [previous, hr] using he

/-- Positively weighted paths satisfy every prescribed relation. -/
theorem supported_constraints (back : (t : ℕ) → Fin K → Option (Fin t)) :
    ∀ n (w : Fin n → {v : V // v ≠ 0}), 0 < weight (step B back) n w →
      ∀ (t : Fin n) (j : Fin K) (r : Fin t.val), back t.val j = some r →
        B (w ⟨r.val, lt_trans r.isLt t.isLt⟩).val (w t).val = 0 := by
  intro n
  induction n with
  | zero => intro w h t; exact Fin.elim0 t
  | succ n ih =>
    intro w hw t j r hr
    have hp : 0 < weight (step B back) n (Fin.init w) ∧
        0 < step B back n (Fin.init w) (w (Fin.last n)) := by
      rcases mul_pos_iff.mp hw with h | h
      · exact h
      · exact False.elim ((not_lt_of_ge (kernel_nonneg B _ _)) h.2)
    by_cases ht : t.val < n
    · exact ih (Fin.init w) hp.1 ⟨t.val, ht⟩ j r hr
    · have teq : t = Fin.last n := Fin.ext (by simp; omega)
      subst t
      exact step_positive_constraint B back n (Fin.init w) (w (Fin.last n)) hp.2 hr

end SmoothObstruction.GroupSampler

end

end OAI
