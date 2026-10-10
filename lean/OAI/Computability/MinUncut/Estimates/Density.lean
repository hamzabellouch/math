import Mathlib
import OAI.Computability.MinUncut.Estimates.F2

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
namespace MinUncut.OuterSmoothness

lemma expect_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] (f : ∀ i, A i → ℝ) :
    (𝔼 x : ∀ i, A i, ∏ i, f i (x i)) = ∏ i, 𝔼 a, f i a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

lemma expect_pair {B C : Type*} [Fintype B] [Fintype C] (f : B × C → ℝ) :
    (𝔼 p, f p) = 𝔼 b, 𝔼 c, f (b,c) := by
  rw [← Finset.univ_product_univ, Finset.expect_product]

structure Density (A : Type*) [Fintype A] where
  val : A → ℝ
  nonneg : ∀ a, 0 ≤ val a
  mean_one : (𝔼 a, val a) = 1

namespace Density
variable {A : Type*} [Fintype A]
instance : CoeFun (Density A) (fun _ => A → ℝ) := ⟨val⟩

lemma pointwise_le_card (p : Density A) (a : A) : p a ≤ Fintype.card A := by
  have h := p.mean_one
  rw [Fintype.expect_eq_sum_div_card] at h
  have hc : (Fintype.card A : ℝ) ≠ 0 := by
    have : Nonempty A := ⟨a⟩
    positivity
  have hs : ∑ a, p a = Fintype.card A := by simpa using (div_eq_iff hc).mp h
  rw [← hs]
  exact Finset.single_le_sum (fun a _ => p.nonneg a) (Finset.mem_univ a)

def tvUniform (p : Density A) : ℝ := (𝔼 a, |p a - 1|) / 2

lemma tvUniform_le_sqrt [Nonempty A] (p : Density A) :
    p.tvUniform ≤ Real.sqrt (𝔼 a, (p a - 1)^2) / 2 := by
  have h := Finset.expect_mul_sq_le_sq_mul_sq (Finset.univ : Finset A)
    (fun a => |p a - 1|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Fintype.expect_const, sq_abs] at h
  have hp : 0 ≤ 𝔼 a, (p a - 1)^2 := Finset.expect_nonneg (fun _ _ => sq_nonneg _)
  have hg : (𝔼 a, |p a - 1|) ≤ Real.sqrt (𝔼 a, (p a - 1)^2) := by
    refine (sq_le_sq₀ (Finset.expect_nonneg (fun _ _ => abs_nonneg _))
      (Real.sqrt_nonneg _)).mp ?_
    rwa [Real.sq_sqrt hp]
  exact div_le_div_of_nonneg_right hg (by norm_num)

def ofMap {B : Type*} [Fintype B] [Nonempty B] [DecidableEq A] (f : B → A) : Density A where
  val a := (Fintype.card A : ℝ) * 𝔼 b, if f b = a then 1 else 0
  nonneg a := mul_nonneg (Nat.cast_nonneg _) (Finset.expect_nonneg (fun _ _ => by positivity))
  mean_one := by
    have : Nonempty A := ⟨f (Classical.choice (inferInstance : Nonempty B))⟩
    have hc : (Fintype.card A : ℝ) ≠ 0 := by positivity
    rw [← Finset.mul_expect, Finset.expect_comm]
    simp only [Fintype.expect_eq_sum_div_card]
    simp [hc]

lemma expect_ofMap {B : Type*} [Fintype B] [Nonempty B] [DecidableEq A]
    (f : B → A) (g : A → ℝ) :
    (𝔼 a, ofMap f a * g a) = 𝔼 b, g (f b) := by
  have : Nonempty A := ⟨f (Classical.choice (inferInstance : Nonempty B))⟩
  have hc : (Fintype.card A : ℝ) ≠ 0 := by positivity
  simp only [ofMap]
  simp_rw [mul_assoc, Finset.expect_mul, Finset.mul_expect]
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro b _
  rw [Fintype.expect_eq_sum_div_card]
  simp [mul_ite, hc]

lemma ofMap_eq_of_invariant {B : Type*} [Fintype B] [Nonempty B]
    [DecidableEq A] {f : B → A} (h : ∀ a a', ofMap f a = ofMap f a') (a : A) :
    ofMap f a = 1 := by
  have : Nonempty A := ⟨a⟩
  calc ofMap f a = 𝔼 a', ofMap f a := (Fintype.expect_const _).symm
       _ = 𝔼 a', ofMap f a' := Finset.expect_congr rfl (fun a' _ => h a a')
       _ = 1 := (ofMap f).mean_one

lemma ofMap_surjective_hom {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [Fintype G] [Fintype H] [DecidableEq H] (f : G →+ H)
    (hf : Function.Surjective f) (y : H) : ofMap f y = 1 := by
  apply ofMap_eq_of_invariant
  intro a a'
  obtain ⟨x, hx⟩ := hf (a' - a)
  unfold ofMap
  dsimp only
  congr 1
  apply Fintype.expect_equiv (Equiv.addLeft x)
  intro z
  change (if f z = a then (1 : ℝ) else 0) = (if f (x+z) = a' then 1 else 0)
  rw [map_add, hx]
  have ht : a' - a + f z = a' + (f z - a) := by abel
  have heq : a' - a + f z = a' ↔ f z = a := by rw [ht]; simp [sub_eq_zero]
  simp only [heq]

lemma ofMap_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B C : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Nonempty (B i)]
    [∀ i, Fintype (C i)] [∀ i, DecidableEq (C i)] (f : ∀ i, B i → C i)
    (c : ∀ i, C i) :
    ofMap (fun b : ∀ i, B i => fun i => f i (b i)) c = ∏ i, ofMap (f i) (c i) := by
  have heq (b : ∀ i, B i) :
      (if (fun i => f i (b i)) = c then (1 : ℝ) else 0) =
        ∏ i, if f i (b i) = c i then (1 : ℝ) else 0 := by
    rw [Finset.prod_boole]
    simp [funext_iff]
  simp only [ofMap, heq]
  rw [expect_prod (fun i b => if f i b = c i then (1 : ℝ) else 0), Fintype.card_pi, Nat.cast_prod, Finset.prod_mul_distrib]

lemma ofMap_fst {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : B → A) (a : A) : ofMap (fun p : B × C => f p.1) a = ofMap f a := by
  change (Fintype.card A : ℝ) * (𝔼 p : B × C, if f p.1 = a then 1 else 0) = _
  rw [expect_pair]
  congr 1
  apply Finset.expect_congr rfl
  intro b _
  exact Fintype.expect_const (ι := C) (if f b = a then (1 : ℝ) else 0)

lemma ofMap_snd {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : C → A) (a : A) : ofMap (fun p : B × C => f p.2) a = ofMap f a := by
  change (Fintype.card A : ℝ) * (𝔼 p : B × C, if f p.2 = a then 1 else 0) = _
  rw [expect_pair]
  congr 1
  exact Fintype.expect_const (ι := B) (𝔼 c : C, if f c = a then (1 : ℝ) else 0)

lemma ofMap_family {B C : Type*} [Fintype B] [Fintype C] [Nonempty B] [Nonempty C]
    [DecidableEq A] (f : B → C → A) (a : A) :
    ofMap (fun p : B × C => f p.1 p.2) a = 𝔼 b, ofMap (f b) a := by
  simp only [ofMap, expect_pair, Finset.mul_expect]

lemma ofMap_uniform_shift {G B C : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    [Fintype B] [Nonempty B] [Fintype C] [DecidableEq C]
    (f : B → C) (offset : B → G) (y : G) (c : C) :
    ofMap (fun p : G × B => (p.1 + offset p.2, f p.2)) (y,c) = ofMap f c := by
  have hc : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hsplit (g : G) (b : B) :
      (if (g + offset b, f b) = (y,c) then (1 : ℝ) else 0) =
        (if g = y - offset b then (1 : ℝ) else 0) * (if f b = c then 1 else 0) := by
    simp only [Prod.mk.injEq, ← eq_sub_iff_add_eq]
    split_ifs <;> simp_all
  simp only [ofMap, expect_pair, hsplit]
  rw [Finset.expect_comm]
  simp_rw [← Finset.expect_mul]
  have hind (b : B) : (𝔼 g : G, if g = y - offset b then (1 : ℝ) else 0) =
      (Fintype.card G : ℝ)⁻¹ := by simp
  simp only [hind, ← Finset.mul_expect, Fintype.card_prod, Nat.cast_mul]
  field_simp

end Density

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)]

def hiddenDensity (p : ∀ i, Density (A i)) (H : Finset ι) : Density (∀ i, A i) where
  val x := ∏ i, if i ∈ H then p i (x i) else 1
  nonneg x := Finset.prod_nonneg (fun _ _ => by split_ifs; exact (p _).nonneg _; norm_num)
  mean_one := by
    rw [expect_prod (fun i a => if i ∈ H then p i a else 1)]
    apply Finset.prod_eq_one
    intro i _
    by_cases hi : i ∈ H <;> simp [hi, Density.mean_one]

lemma hiddenDensity_eq_prod (p : ∀ i, Density (A i)) (H : Finset ι) (x : ∀ i, A i) :
    hiddenDensity p H x = ∏ i ∈ H, p i (x i) := by
  simp [hiddenDensity]

lemma hiddenDensity_cross_disjoint (p : ∀ i, Density (A i))
    {H K : Finset ι} (hHK : Disjoint H K) :
    (𝔼 x, hiddenDensity p H x * hiddenDensity p K x) = 1 := by
  simp only [hiddenDensity]
  simp_rw [← Finset.prod_mul_distrib]
  rw [expect_prod (fun i a => (if i ∈ H then p i a else 1) *
    (if i ∈ K then p i a else 1))]
  apply Finset.prod_eq_one
  intro i _
  have hnot : ¬ (i ∈ H ∧ i ∈ K) := by
    intro hi
    exact Finset.disjoint_left.mp hHK hi.1 hi.2
  by_cases hi : i ∈ H <;> by_cases hk : i ∈ K
  · exact (hnot ⟨hi, hk⟩).elim
  all_goals simp [hi, hk, Density.mean_one]

lemma hiddenDensity_le (p : ∀ i, Density (A i)) {b : ℝ} (_hb : 0 ≤ b)
    (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ b) (H : Finset ι) (x : ∀ i, A i) :
    hiddenDensity p H x ≤ b ^ H.card := by
  rw [hiddenDensity_eq_prod, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun i _ => (p i).nonneg _) (fun i _ =>
    ((p i).pointwise_le_card _).trans (hcard i))

def mixture {S : Type*} [Fintype S] [Nonempty S] (H : S → Finset ι)
    (p : ∀ i, Density (A i)) : Density (∀ i, A i) where
  val x := 𝔼 s, hiddenDensity p (H s) x
  nonneg x := Finset.expect_nonneg (fun s _ => (hiddenDensity p (H s)).nonneg x)
  mean_one := by
    rw [Finset.expect_comm]
    simp [Density.mean_one]

lemma mixture_variance {S : Type*} [Fintype S] [Nonempty S]
    (H : S → Finset ι) (p : ∀ i, Density (A i)) :
    (𝔼 x, (mixture H p x - 1)^2) =
      (𝔼 s, 𝔼 t, 𝔼 x, hiddenDensity p (H s) x * hiddenDensity p (H t) x) - 1 := by
  have hs (x) : (mixture H p x - 1)^2 =
      (𝔼 s, 𝔼 t, hiddenDensity p (H s) x * hiddenDensity p (H t) x) -
        2 * mixture H p x + 1 := by
    simp only [mixture, ← Finset.mul_expect, ← Finset.expect_mul]
    ring
  simp_rw [hs]
  rw [Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    (mixture H p).mean_one, Fintype.expect_const, Finset.expect_comm]
  conv_lhs => arg 1; arg 1; arg 2; ext s; rw [Finset.expect_comm]
  ring

abbrev FixedSets (ι : Type*) [Fintype ι] (k : ℕ) := {H : Finset ι // H.card = k}

omit [DecidableEq ι] in
lemma fixedSets_nonempty {k : ℕ} (hk : k ≤ Fintype.card ι) : Nonempty (FixedSets ι k) := by
  obtain ⟨H, _, hH⟩ := Finset.exists_subset_card_eq (s := Finset.univ) hk
  exact ⟨⟨H, hH⟩⟩

def fixedSetsEquiv (e : ι ≃ ι) (k : ℕ) : FixedSets ι k ≃ FixedSets ι k where
  toFun H := ⟨H.val.map e.toEmbedding, by simpa using H.property⟩
  invFun H := ⟨H.val.map e.symm.toEmbedding, by simpa using H.property⟩
  left_inv H := by apply Subtype.ext; ext i; simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv H := by apply Subtype.ext; ext i; simp only [Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma membership_probability_eq {k : ℕ} (i j : ι) :
    (𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) =
    (𝔼 H : FixedSets ι k, if j ∈ H.val then (1 : ℝ) else 0) := by
  apply Fintype.expect_equiv (fixedSetsEquiv (Equiv.swap i j) k)
  intro H
  simp [fixedSetsEquiv, Finset.mem_map_equiv]

lemma membership_probability [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι) (i : ι) :
    (𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) =
      (k : ℝ) / Fintype.card ι := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hsum : (∑ j : ι, 𝔼 H : FixedSets ι k, if j ∈ H.val then (1 : ℝ) else 0) = k := by
    rw [← Finset.expect_sum_comm]
    have hx (H : FixedSets ι k) : (∑ j : ι, if j ∈ H.val then (1 : ℝ) else 0) = k := by
      simp [H.property]
    simp_rw [hx]
    exact Fintype.expect_const _
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  calc
    (𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) =
        (∑ j : ι, 𝔼 H : FixedSets ι k, if i ∈ H.val then (1 : ℝ) else 0) /
          Fintype.card ι := by simp [hc]
    _ = (∑ j : ι, 𝔼 H : FixedSets ι k, if j ∈ H.val then (1 : ℝ) else 0) /
          Fintype.card ι := by
      congr 1
      exact Finset.sum_congr rfl (fun j _ => membership_probability_eq i j)
    _ = _ := by rw [hsum]

omit [Fintype ι] in
lemma overlap_union_bound (H K : Finset ι) :
    (if ¬Disjoint H K then (1 : ℝ) else 0) ≤
      ∑ i ∈ H, if i ∈ K then (1 : ℝ) else 0 := by
  by_cases h : Disjoint H K
  · simp only [h, not_true_eq_false, ite_false]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  · simp only [h, not_false_eq_true, ite_true]
    obtain ⟨i, hi, hik⟩ := Finset.not_disjoint_iff.mp h
    have hh := Finset.single_le_sum (s := H)
      (f := fun i => if i ∈ K then (1 : ℝ) else 0) (fun _ _ => by positivity) hi
    simpa [hik] using hh

lemma fixedSet_overlap_probability [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι) :
    (𝔼 H : FixedSets ι k, 𝔼 K : FixedSets ι k,
      if ¬Disjoint H.val K.val then (1 : ℝ) else 0) ≤
      (k : ℝ)^2 / Fintype.card ι := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hfix (H : FixedSets ι k) :
      (𝔼 K : FixedSets ι k, if ¬Disjoint H.val K.val then (1 : ℝ) else 0) ≤
        (k : ℝ)^2 / Fintype.card ι := by
    calc
      _ ≤ 𝔼 K : FixedSets ι k, ∑ i ∈ H.val, if i ∈ K.val then (1 : ℝ) else 0 :=
        Finset.expect_le_expect (fun K _ => overlap_union_bound _ _)
      _ = ∑ i ∈ H.val, (k : ℝ) / Fintype.card ι := by
        rw [Finset.expect_sum_comm]
        simp_rw [membership_probability hk]
      _ = _ := by simp [H.property, sq, mul_div_assoc]
  calc
    _ ≤ 𝔼 _H : FixedSets ι k, (k : ℝ)^2 / Fintype.card ι :=
      Finset.expect_le_expect (fun H _ => hfix H)
    _ = _ := Fintype.expect_const _

lemma mixture_tv_bound [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    (p : ∀ i, Density (A i)) {b : ℝ} (hb : 1 ≤ b)
    (hcard : ∀ i, (Fintype.card (A i) : ℝ) ≤ b) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    (mixture (fun H : FixedSets ι k => H.val) p).tvUniform ≤
      Real.sqrt ((b ^ (2*k) - 1) * (k : ℝ)^2 / Fintype.card ι) / 2 := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have hb0 : 0 ≤ b := le_trans (by norm_num) hb
  have hconstant : 0 ≤ b^(2*k) - 1 := sub_nonneg.mpr (one_le_pow₀ hb)
  let d := mixture (fun H : FixedSets ι k => H.val) p
  have hcross (H K : FixedSets ι k) :
      (𝔼 x, hiddenDensity p H.val x * hiddenDensity p K.val x) ≤
        1 + (b^(2*k)-1) * (if ¬Disjoint H.val K.val then 1 else 0) := by
    by_cases h : Disjoint H.val K.val
    · simp [hiddenDensity_cross_disjoint p h, h]
    · simp only [h, not_false_eq_true, ite_true, mul_one, add_sub_cancel]
      have hprod (x : ∀ i, A i) : hiddenDensity p H.val x * hiddenDensity p K.val x ≤ b^(2*k) := by
        have hH := hiddenDensity_le p hb0 hcard H.val x
        have hK := hiddenDensity_le p hb0 hcard K.val x
        rw [H.property] at hH
        rw [K.property] at hK
        calc _ ≤ b^k * b^k := mul_le_mul hH hK ((hiddenDensity p K.val).nonneg x) (pow_nonneg hb0 _)
             _ = _ := by rw [← pow_add]; congr 1; omega
      calc _ ≤ 𝔼 _x : ∀ i, A i, b^(2*k) := Finset.expect_le_expect (fun x _ => hprod x)
           _ = _ := Fintype.expect_const _
  have hvar : (𝔼 x, (d x - 1)^2) ≤ (b^(2*k)-1) * (k : ℝ)^2 / Fintype.card ι := by
    rw [mixture_variance]
    have havg := Finset.expect_le_expect (s := Finset.univ)
      (fun H _ => Finset.expect_le_expect (s := Finset.univ) (fun K _ => hcross H K))
    simp_rw [Finset.expect_add_distrib, Fintype.expect_const, ← Finset.mul_expect] at havg
    have hh := mul_le_mul_of_nonneg_left (fixedSet_overlap_probability hk) hconstant
    rw [← mul_div_assoc] at hh
    linarith
  exact (Density.tvUniform_le_sqrt d).trans
    (div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hvar) (by norm_num))

namespace JointForms
abbrev F₂ := ZMod 2
abbrev Triple := Fin 3 → F₂

local instance dualFintype {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V] :
    Fintype (Module.Dual F₂ V) := by
  classical
  exact Fintype.ofInjective (fun f : Module.Dual F₂ V => (f : V → F₂)) DFunLike.coe_injective
local instance densityDualDecidableEq {V : Type*} [AddCommGroup V] [Module F₂ V] : DecidableEq (Module.Dual F₂ V) := Classical.decEq _

abbrev Block (r d : ℕ) := Fin d → Module.Dual F₂ (Fin r → F₂)
abbrev HiddenRaw (d : ℕ) := Fin 3 × (Fin d → F₂)
abbrev FullRaw (d : ℕ) := Fin d → Module.Dual F₂ Triple
abbrev Raw (d : ℕ) := HiddenRaw d × FullRaw d

def fullPull {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) : FullRaw d →ₗ[F₂] Block r d :=
  LinearMap.pi (fun l => T.dualMap.comp (LinearMap.proj l))

lemma fullPull_surjective {r d : ℕ} {T : (Fin r → F₂) →ₗ[F₂] Triple}
    (hT : Function.Injective T) : Function.Surjective (fullPull (d := d) T) := by
  intro b
  choose w hw using fun l => LinearMap.dualMap_surjective_of_injective hT (b l)
  exact ⟨w, funext hw⟩

def hiddenPull {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) (q : HiddenRaw d) : Block r d :=
  fun l => q.2 l • ((LinearMap.proj q.1).comp T)

def hiddenLaw {r d : ℕ} (T : (Fin r → F₂) →ₗ[F₂] Triple) : Density (Block r d) :=
  Density.ofMap (hiddenPull T)

lemma fullPull_uniform {r d : ℕ} {T : (Fin r → F₂) →ₗ[F₂] Triple}
    (hT : Function.Injective T) (b : Block r d) : Density.ofMap (fullPull T) b = 1 :=
  Density.ofMap_surjective_hom (fullPull T).toAddMonoidHom (fullPull_surjective hT) b

lemma card_block (r d : ℕ) : Fintype.card (Block r d) = 2^(r*d) := by
  rw [Fintype.card_fun, Module.card_eq_pow_finrank (K := F₂),
    Subspace.dual_finrank_eq, Module.finrank_fin_fun]
  simp [F₂, ZMod.card, ← pow_mul]

variable {r : ι → ℕ} {d : ℕ}

def output (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (H : Finset ι)
    (w : ι → Raw d) : ∀ i, Block (r i) d :=
  fun i => if i ∈ H then hiddenPull (T i) (w i).1 else fullPull (T i) (w i).2

lemma output_density (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple)
    (hT : ∀ i, Function.Injective (T i)) (H : Finset ι) (b : ∀ i, Block (r i) d) :
    Density.ofMap (output T H) b = hiddenDensity (fun i => hiddenLaw (T i)) H b := by
  rw [show output T H = (fun w : ι → Raw d => fun i =>
    (fun q : Raw d => if i ∈ H then hiddenPull (T i) q.1 else fullPull (T i) q.2) (w i)) from rfl,
    Density.ofMap_pi (fun i (q : Raw d) => if i ∈ H then hiddenPull (T i) q.1 else fullPull (T i) q.2) b]
  change (∏ i, _) = ∏ i, _
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ H
  · simp only [hi, ite_true]
    exact Density.ofMap_fst _ _
  · simp only [hi, ite_false]
    rw [Density.ofMap_snd]
    exact fullPull_uniform (hT i) _

def offset (o : ι → Triple) (H : Finset ι) (w : ι → Raw d) : Fin d → F₂ :=
  fun l => ∑ i, if i ∈ H then (w i).1.2 l * o i (w i).1.1 else (w i).2 l (o i)

def affineOutput (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (o : ι → Triple) {k : ℕ}
    (sample : (Fin d → F₂) × (FixedSets ι k × (ι → Raw d))) :
      (Fin d → F₂) × (∀ i, Block (r i) d) :=
  (sample.1 + offset o sample.2.1.val sample.2.2, output T sample.2.1.val sample.2.2)

lemma joint_density {k : ℕ} (hk : k ≤ Fintype.card ι)
    (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple) (hT : ∀ i, Function.Injective (T i))
    (o : ι → Triple) (c : Fin d → F₂) (b : ∀ i, Block (r i) d) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    Density.ofMap (affineOutput T o (k := k)) (c,b) =
      mixture (fun H : FixedSets ι k => H.val) (fun i => hiddenLaw (T i)) b := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  rw [show affineOutput T o (k := k) = (fun sample : (Fin d → F₂) × (FixedSets ι k × (ι → Raw d)) =>
      (sample.1 + (fun p : FixedSets ι k × (ι → Raw d) => offset o p.1.val p.2) sample.2,
        (fun p : FixedSets ι k × (ι → Raw d) => output T p.1.val p.2) sample.2)) from rfl,
    Density.ofMap_uniform_shift (fun p : FixedSets ι k × (ι → Raw d) => output T p.1.val p.2)
      (fun p : FixedSets ι k × (ι → Raw d) => offset o p.1.val p.2) c b,
    Density.ofMap_family (fun (H : FixedSets ι k) (w : ι → Raw d) => output T H.val w) b]
  apply Finset.expect_congr rfl
  intro H _
  exact output_density T hT H.val b

theorem joint_smoothness [Nonempty ι] {k : ℕ} (hk : k ≤ Fintype.card ι)
    (hr : ∀ i, r i ≤ 2) (T : ∀ i, (Fin (r i) → F₂) →ₗ[F₂] Triple)
    (hT : ∀ i, Function.Injective (T i)) (o : ι → Triple) :
    letI : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
    (Density.ofMap (affineOutput T o (d := d) (k := k))).tvUniform ≤
      Real.sqrt (((2 : ℝ)^(4*d*k)-1) * (k : ℝ)^2 / Fintype.card ι) / 2 := by
  let : Nonempty (FixedSets ι k) := fixedSets_nonempty hk
  have heq : (Density.ofMap (affineOutput T o (d := d) (k := k))).tvUniform =
      (mixture (fun H : FixedSets ι k => H.val) (fun i => hiddenLaw (d := d) (T i))).tvUniform := by
    unfold Density.tvUniform
    rw [expect_pair]
    simp_rw [joint_density hk T hT o]
    exact congrArg (fun x : ℝ => x / 2) (Fintype.expect_const _)
  rw [heq]
  have hcard (i : ι) : (Fintype.card (Block (r i) d) : ℝ) ≤ (2 : ℝ)^(2*d) := by
    rw [card_block, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right d (hr i))
  have h := mixture_tv_bound hk (fun i => hiddenLaw (d := d) (T i))
    (one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)) hcard
  have hexp : 2*d*(2*k) = 4*d*k := by ring
  simpa only [← pow_mul, hexp] using h

end JointForms
end MinUncut.OuterSmoothness

namespace MinUncut.BinaryFourier
variable {W : Type*} [AddCommGroup W] [Module F₂ W] [Fintype W]
local instance densityFourierDecidableEq : DecidableEq W := Classical.decEq W
attribute [local instance] dualFintype

lemma coefficient_sum {ι : Type*} (s : Finset ι) (f : ι → W → ℝ)
    (α : Module.Dual F₂ W) : coefficient (fun w => ∑ i ∈ s, f i w) α =
      ∑ i ∈ s, coefficient (f i) α := by
  simp only [coefficient, Finset.sum_mul]
  rw [Finset.expect_sum_comm]

lemma coefficient_character (α β : Module.Dual F₂ W) :
    coefficient (character α) β = if α = β then 1 else 0 := by
  by_cases h : α = β <;> simpa [coefficient, h] using character_orthogonality α β

lemma coefficient_scale (a : ℝ) (f : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (fun w => a * f w) α = a * coefficient f α := by
  simp only [coefficient, mul_assoc, Finset.mul_expect]

lemma coefficient_sub (f g : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (fun w => f w - g w) α = coefficient f α - coefficient g α := by
  simp only [coefficient, sub_mul, Finset.expect_sub_distrib]

lemma fourth_moment (f : W → ℝ) :
    (𝔼 a, 𝔼 b, 𝔼 c, f a * f b * f c * f (a+b+c)) =
      ∑ α : Module.Dual F₂ W, coefficient f α ^ 4 := by
  have hexp (a b c : W) : f a * f b * f c * f (a+b+c) =
      ∑ α : Module.Dual F₂ W, coefficient f α *
        ((f a * character α a) * (f b * character α b) * (f c * character α c)) := by
    rw [← inversion f (a+b+c), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    rw [character_add, character_add]
    ring
  simp only [hexp, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  simp_rw [← Finset.mul_expect, ← Finset.expect_mul]
  rw [← Fintype.expect_mul_expect]
  change coefficient f α * (coefficient f α * coefficient f α * coefficient f α) = _
  ring

def largeSpectrum (f : W → ℝ) (u : ℝ) : Finset (Module.Dual F₂ W) :=
  Finset.univ.filter (fun α => u ≤ |coefficient f α|)

def largePart (f : W → ℝ) (u : ℝ) (w : W) : ℝ :=
  ∑ α ∈ largeSpectrum f u, coefficient f α * character α w

def remainder (f : W → ℝ) (u : ℝ) (w : W) : ℝ := f w - largePart f u w

lemma coefficient_largePart (f : W → ℝ) (u : ℝ) (β : Module.Dual F₂ W) :
    coefficient (largePart f u) β = if u ≤ |coefficient f β| then coefficient f β else 0 := by
  classical
  unfold largePart
  rw [coefficient_sum]
  simp_rw [coefficient_scale, coefficient_character]
  simp [largeSpectrum]

lemma coefficient_remainder (f : W → ℝ) (u : ℝ) (β : Module.Dual F₂ W) :
    coefficient (remainder f u) β = if |coefficient f β| < u then coefficient f β else 0 := by
  unfold remainder
  rw [coefficient_sub, coefficient_largePart]
  split_ifs <;> simp_all
  linarith

omit [Module F₂ W] in
lemma energy_le_of_bounded (f : W → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hf : ∀ w, |f w| ≤ M) : (𝔼 w, f w ^ 2) ≤ M^2 := by
  calc _ ≤ 𝔼 _w : W, M^2 := Finset.expect_le_expect (fun w _ => by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hM).mpr (hf w))
       _ = _ := Fintype.expect_const _

lemma largeSpectrum_card (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) : (largeSpectrum f u).card ≤ M^2 / u^2 := by
  have he := energy_le_of_bounded f hM hf
  have hs : (largeSpectrum f u).card * u^2 ≤ ∑ α : Module.Dual F₂ W, coefficient f α ^ 2 := by
    calc _ = ∑ _α ∈ largeSpectrum f u, u^2 := by simp
         _ ≤ ∑ α ∈ largeSpectrum f u, coefficient f α ^ 2 := by
           apply Finset.sum_le_sum
           intro α hα
           have h := (Finset.mem_filter.mp hα).2
           nlinarith [sq_abs (coefficient f α)]
         _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  rw [parseval] at hs
  exact (le_div_iff₀ (sq_pos_of_pos hu)).mpr (hs.trans he)

lemma remainder_fourth_bound (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) :
    (∑ α : Module.Dual F₂ W, coefficient (remainder f u) α ^ 4) ≤ u^2 * M^2 := by
  have he := energy_le_of_bounded f hM hf
  calc _ ≤ ∑ α : Module.Dual F₂ W, u^2 * coefficient f α ^ 2 := by
         apply Finset.sum_le_sum
         intro α _
         rw [coefficient_remainder]
         split_ifs with hα
         · have hs : coefficient f α ^2 ≤ u^2 := by
             simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hu.le).mpr hα.le
           nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (coefficient f α))]
         · simp only [zero_pow (by omega : 4 ≠ 0)]
           exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
       _ = u^2 * (𝔼 w, f w^2) := by rw [← Finset.mul_sum, parseval]
       _ ≤ _ := mul_le_mul_of_nonneg_left he (sq_nonneg u)

lemma remainder_abs_bound (f : W → ℝ) {M u : ℝ} (hM : 0 ≤ M) (hu : 0 < u)
    (hf : ∀ w, |f w| ≤ M) (w : W) : |remainder f u w| ≤ M + M^2 / u := by
  have he := energy_le_of_bounded f hM hf
  have hs : (∑ α ∈ largeSpectrum f u, |coefficient f α|) ≤ M^2/u := by
    calc _ ≤ ∑ α ∈ largeSpectrum f u, coefficient f α ^2/u := by
           apply Finset.sum_le_sum
           intro α hα
           have h := (Finset.mem_filter.mp hα).2
           apply (le_div_iff₀ hu).mpr
           nlinarith [mul_nonneg (abs_nonneg (coefficient f α)) (sub_nonneg.mpr h),
             sq_abs (coefficient f α)]
         _ = (∑ α ∈ largeSpectrum f u, coefficient f α ^2)/u := by rw [Finset.sum_div]
         _ ≤ M^2/u := by
           apply div_le_div_of_nonneg_right _ hu.le
           exact (Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)).trans
             ((parseval f).le.trans he)
  calc |remainder f u w| ≤ |f w| + |largePart f u w| := by
         simpa only [remainder, sub_zero, zero_sub, abs_neg] using abs_sub_le (f w) 0 (largePart f u w)
       _ ≤ M + ∑ α ∈ largeSpectrum f u, |coefficient f α| := by
         apply add_le_add (hf w)
         unfold largePart
         exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp [abs_mul])
       _ ≤ _ := add_le_add_right hs M

variable {V : Type*} [AddCommGroup V] [Module F₂ V] [Fintype V]
local instance densityProjectedDecidableEq : DecidableEq V := Classical.decEq V

omit [Fintype V] in
lemma coefficient_projected_sum (S : Finset (Module.Dual F₂ V))
    (a : Module.Dual F₂ V → ℝ) (π : W →ₗ[F₂] V) (β : Module.Dual F₂ W) :
    coefficient (fun w => ∑ α ∈ S, a α * character α (π w)) β =
      ∑ α ∈ S, if α.comp π = β then a α else 0 := by
  classical
  rw [coefficient_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [coefficient_scale]
  change a α * coefficient (character (α.comp π)) β = _
  rw [coefficient_character]
  split_ifs <;> simp

lemma coefficient_pullback (f : V → ℝ) (π : W →ₗ[F₂] V) (β : Module.Dual F₂ W) :
    coefficient (fun w => f (π w)) β =
      ∑ α : Module.Dual F₂ V, if α.comp π = β then coefficient f α else 0 := by
  classical
  have h : (fun w => f (π w)) = (fun w => ∑ α : Module.Dual F₂ V,
      coefficient f α * character α (π w)) := by
    funext w
    exact (inversion f (π w)).symm
  rw [h, coefficient_projected_sum]

lemma coefficient_largePart_pullback (f : V → ℝ) (u : ℝ) (π : W →ₗ[F₂] V)
    (β : Module.Dual F₂ W) :
    coefficient (fun w => largePart f u (π w)) β =
      ∑ α ∈ largeSpectrum f u, if α.comp π = β then coefficient f α else 0 :=
  coefficient_projected_sum _ _ _ _

lemma large_preimage_of_nonzero (f : V → ℝ) (u : ℝ) (π : W →ₗ[F₂] V)
    (β : Module.Dual F₂ W) (hb : coefficient (fun w => largePart f u (π w)) β ≠ 0) :
    ∃ α : Module.Dual F₂ V, u ≤ |coefficient f α| ∧ α.comp π = β := by
  classical
  by_contra hn
  push Not at hn
  apply hb
  rw [coefficient_largePart_pullback]
  apply Finset.sum_eq_zero
  intro α hα
  exact ite_eq_right (hn α (Finset.mem_filter.mp hα).2)

lemma extract_matched_odd (f : V → ℝ) (g : W → ℝ) (π : W →ₗ[F₂] V)
    (oneV : V) (oneW : W) (hπ : π oneW = oneV)
    (β : Module.Dual F₂ W) {u θ : ℝ} (hθ : 0 < θ)
    (hodd : β oneW = 1) (hβ : θ ≤ |coefficient g β|)
    (hclose : |coefficient g β - coefficient (fun w => f (π w)) β| < θ/4)
    (hrem : |coefficient (fun w => remainder f u (π w)) β| < θ/4) :
    ∃ α : Module.Dual F₂ V, u ≤ |coefficient f α| ∧ α.comp π = β ∧ α oneV = 1 := by
  have hnonzero : coefficient (fun w => largePart f u (π w)) β ≠ 0 := by
    intro hz
    have hr : coefficient (fun w => remainder f u (π w)) β =
        coefficient (fun w => f (π w)) β := by
      unfold remainder
      rw [coefficient_sub, hz, sub_zero]
    rw [hr] at hrem
    have ht := abs_add_le (coefficient g β - coefficient (fun w => f (π w)) β)
      (coefficient (fun w => f (π w)) β)
    rw [sub_add_cancel] at ht
    linarith
  obtain ⟨α, ha, hab⟩ := large_preimage_of_nonzero f u π β hnonzero
  refine ⟨α, ha, hab, ?_⟩
  have he := congrArg (fun γ : Module.Dual F₂ W => γ oneW) hab
  simpa only [LinearMap.comp_apply, hπ, hodd] using he

end MinUncut.BinaryFourier

namespace MinUncut.OuterSmoothness.Density
variable {A : Type*} [Fintype A]

lemma abs_expect_le (f : A → ℝ) : |𝔼 a, f a| ≤ 𝔼 a, |f a| := by
  simp only [Fintype.expect_eq_sum_div_card, abs_div, abs_of_nonneg (Nat.cast_nonneg (Fintype.card A) : (0 : ℝ) ≤ _)]
  exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg _)

lemma expect_difference (p : Density A) (g : A → ℝ) {M : ℝ}
    (_hM : 0 ≤ M) (hg : ∀ a, |g a| ≤ M) :
    |(𝔼 a, p a * g a) - (𝔼 a, g a)| ≤ 2 * p.tvUniform * M := by
  have heq : (𝔼 a, p a * g a) - (𝔼 a, g a) = 𝔼 a, (p a - 1) * g a := by
    simp only [sub_mul, one_mul, Finset.expect_sub_distrib]
  rw [heq]
  calc _ ≤ 𝔼 a, |(p a - 1) * g a| := abs_expect_le _
       _ ≤ 𝔼 a, |p a - 1| * M := by
         apply Finset.expect_le_expect
         intro a _
         rw [abs_mul]
         exact mul_le_mul_of_nonneg_left (hg a) (abs_nonneg _)
       _ = _ := by rw [← Finset.expect_mul]; unfold tvUniform; ring

end MinUncut.OuterSmoothness.Density

end

end OAI
