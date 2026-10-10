import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.TargetEvent

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
namespace SharpLogRamsey.HighRankCoverage
open scoped BigOperators
open Finset Classical FiniteRowProcess
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
def rowSpan (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    Submodule K V := W ⊔ ⨆ i, A (z i)

omit [Fintype Ω] [FiniteDimensional K V] in
lemma le_rowSpan (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    W ≤ rowSpan A W z := le_sup_left

omit [Fintype Ω] [FiniteDimensional K V] in
lemma rowSpan_eq (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    rowSpan A W z = W ↔ ∀ i, A (z i) ≤ W := by
  simp only [rowSpan, sup_eq_left, iSup_le_iff]

omit [Fintype Ω] in
lemma rowSpan_rank (A : Ω → Submodule K V) {m : ℕ} (W : Submodule K V) (z : Fin m → Ω) :
    Module.finrank K (rowSpan A W z) ≤ Module.finrank K W ↔ ∀ i, A (z i) ≤ W := by
  constructor
  · intro h
    apply (rowSpan_eq A W z).mp
    symm
    apply Submodule.eq_of_le_of_finrank_eq (le_rowSpan A W z)
    exact le_antisymm (Submodule.finrank_mono (le_rowSpan A W z)) h
  · intro h
    rw [(rowSpan_eq A W z).mpr h]

omit [Fintype Ω] [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma indicator_all {ι : Type*} [Fintype ι] (P : ι → Prop)
    [DecidablePred P] [Decidable (∀ i, P i)] :
    (if ∀ i, P i then (1:ℝ) else 0) = ∏ i, if P i then 1 else 0 := by
  by_cases h : ∀ i, P i
  · simp [h]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [ite_eq_right (by intro hh; exact hi (hh i))]
    symm
    apply prod_eq_zero (mem_univ i)
    simp [hi]

theorem stagnation_mass (w : Ω → ℝ) (A : Ω → Submodule K V)
    (m : ℕ) (W : Submodule K V) :
    (∑ z : Fin m → Ω, weight w z *
      (if Module.finrank K (rowSpan A W z) ≤ Module.finrank K W then 1 else 0)) =
      (∑ a, w a * (if A a ≤ W then 1 else 0))^m := by
  simp_rw [rowSpan_rank]
  have hh (z : Fin m → Ω) :
      (if ∀ i, A (z i) ≤ W then (1:ℝ) else 0) =
        ∏ i, if A (z i) ≤ W then 1 else 0 := by
      simpa only using (indicator_all (fun i : Fin m => A (z i) ≤ W))
  simp_rw [hh, weight, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (_ : Fin m) (a : Ω) => w a * (if A a ≤ W then 1 else 0))]
  simp

theorem span_growth (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a) (ht : ∑ a, w a = 1)
    (A : Ω → Submodule K V) (r m : ℕ) (p : ℝ) (hp : p ≤ 1)
    (hescape : ∀ W : Submodule K V, Module.finrank K W < r →
      p ≤ ∑ a, w a * (if ¬ A a ≤ W then 1 else 0))
    (W : Submodule K V) :
    expected (weight w : (Fin m → Ω) → ℝ) (rowSpan A) r W
      (fun U => if Module.finrank K U < r then 1 else 0) ≤ r*(1-p)^m := by
  apply rank_reached (weight w) (weight_nonneg w hw) (weight_total w ht m)
    (rowSpan A) (fun U => Module.finrank K U) r ((1-p)^m) (pow_nonneg (by linarith) _)
  · intro U z
    exact Submodule.finrank_mono (le_rowSpan A U z)
  · intro U hU
    rw [stagnation_mass]
    have hs : (∑ a, w a * (if A a ≤ U then 1 else 0)) +
        (∑ a, w a * (if ¬ A a ≤ U then 1 else 0)) = 1 := by
      rw [← sum_add_distrib]
      convert ht using 1
      apply sum_congr rfl
      intro a _
      by_cases ha : A a ≤ U <;> simp [ha]
    have h0 : 0 ≤ ∑ a, w a * (if A a ≤ U then 1 else 0) := by
      apply sum_nonneg
      intro a _
      split_ifs
      · simpa only [mul_one] using hw a
      · simp
    apply pow_le_pow_left₀ h0
    linarith [hescape U hU]
  · omega

noncomputable def projectiveSubmoduleEquiv (W : Submodule K V) :
    Projectivization K W ≃ {a : Projectivization K V // a.submodule ≤ W} := by
  let f : Projectivization K W → {a : Projectivization K V // a.submodule ≤ W} :=
    fun a => ⟨Projectivization.map W.subtype W.injective_subtype a, by
      induction a using Projectivization.ind with
      | h v hv =>
        rw [Projectivization.map_mk, Projectivization.submodule_mk,
          Submodule.span_singleton_le_iff_mem]
        exact v.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    exact Projectivization.map_injective W.subtype W.injective_subtype
      (congrArg Subtype.val h)
  · rintro ⟨a, ha⟩
    have hmem : a.rep ∈ W := ha (by
      rw [Projectivization.submodule_eq]
      exact Submodule.mem_span_singleton_self _)
    let v : W := ⟨a.rep, hmem⟩
    have hv : v ≠ 0 := fun h => a.rep_nonzero (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K v hv, ?_⟩
    apply Subtype.ext
    exact a.mk_rep

variable [Finite K] [Fintype (Projectivization K V)]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma projective_card (W : Submodule K V) :
    (univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card =
      ∑ i ∈ range (Module.finrank K W), Nat.card K^i := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [Fintype Ω] [Fintype (Projectivization K V)] [Field K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma small_span_card (r : ℕ) (hr : 2 ≤ r) (W : Submodule K V)
    (hW : Module.finrank K W < r) :
    ((univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card : ℝ) ≤
      2*(Nat.card K:ℝ)^(r-2) := by
  rw [projective_card, Nat.cast_sum]
  push_cast
  calc
    _ ≤ ∑ i ∈ range ((r-2)+1), (Nat.card K:ℝ)^i := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply range_mono
        omega
      · intro _ _ _; positivity
    _ ≤ _ := geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)) _

omit [Finite K] [FiniteDimensional K V] in
lemma marginal_mass (w : Ω → ℝ) (b : Ω → Projectivization K V) (W : Submodule K V) :
    (∑ a, w a * (if (b a).submodule ≤ W then 1 else 0)) =
      ∑ y ∈ univ.filter (fun y : Projectivization K V => y.submodule ≤ W),
        ∑ a ∈ univ.filter (fun a => b a = y), w a := by
  rw [sum_fiberwise_eq_sum_filter univ
    (univ.filter (fun y : Projectivization K V => y.submodule ≤ W)) b w]
  simp [sum_filter, mul_ite]

omit [Finite K] [FiniteDimensional K V] in
lemma marginal_cap (w : Ω → ℝ) (b : Ω → Projectivization K V) (M : ℝ)
    (hM : ∀ y, (∑ a ∈ univ.filter (fun a => b a = y), w a) ≤ M) (W : Submodule K V) :
    (∑ a, w a * (if (b a).submodule ≤ W then 1 else 0)) ≤
      M * (univ.filter (fun y : Projectivization K V => y.submodule ≤ W)).card := by
  rw [marginal_mass]
  calc
    _ ≤ ∑ _y ∈ univ.filter (fun y : Projectivization K V => y.submodule ≤ W), M := by
      apply sum_le_sum
      intro y _
      exact hM y
    _ = _ := by simp [mul_comm]

omit [Fintype Ω] [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
def hitSpace (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Ω) : Submodule K V :=
  if a z y.rep = 0 then (b z).submodule else ⊥

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma escape_mass (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (W : Submodule K V) :
    (∑ z, w z * (if a z y.rep = 0 then 1 else 0)) -
      (∑ z, w z * (if (b z).submodule ≤ W then 1 else 0)) ≤
        ∑ z, w z * (if ¬ hitSpace a b y z ≤ W then 1 else 0) := by
  rw [sub_le_iff_le_add, ← sum_add_distrib]
  apply sum_le_sum
  intro z _
  by_cases hz : a z y.rep = 0 <;>
    by_cases hb : (b z).submodule ≤ W <;>
    simp [hitSpace, hz, hb, hw z]

theorem projective_span_growth (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z) (ht : ∑ z, w z = 1)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (r m : ℕ) (hr : 2 ≤ r) (H M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z = u), w z) ≤ M)
    (hH : H ≤ ∑ z, w z * (if a z y.rep = 0 then 1 else 0))
    (hH1 : H ≤ 1) :
    expected (weight w : (Fin m → Ω) → ℝ) (rowSpan (hitSpace a b y)) r y.submodule
      (fun U => if Module.finrank K U < r then 1 else 0) ≤
        r*(1-(H-2*M*(Nat.card K:ℝ)^(r-2)))^m := by
  apply span_growth w hw ht (hitSpace a b y) r m _
  · have hnonneg : 0 ≤ 2*M*(Nat.card K:ℝ)^(r-2) := by positivity
    linarith
  · intro W hW
    have hcap := (marginal_cap w b M hM W).trans
      (mul_le_mul_of_nonneg_left (small_span_card r hr W hW) hM0)
    have hesc := escape_mass w hw a b y W
    linarith

end
end SharpLogRamsey.HighRankCoverage

namespace SharpLogRamsey.HighRankGrowth
open scoped BigOperators
open Finset Classical FiniteRowProcess HighRankCoverage HighRankDecoder
noncomputable section
variable {Ω K V : Type*} [Fintype Ω] [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

omit [Fintype Ω] [FiniteDimensional K V] in
lemma run_span_le (A : Ω → Submodule K V) (m n : ℕ)
    (z : Fin n → Fin m → Ω) (W U : Submodule K V)
    (hW : W ≤ U) (hA : ∀ i j, A (z i j) ≤ U) :
    run (rowSpan A) n z W ≤ U := by
  induction n generalizing W with
  | zero => exact hW
  | succ n ih =>
    apply ih (fun i => z i.succ) (rowSpan A W (z 0))
    · apply sup_le hW
      exact iSup_le (hA 0)
    · intro i j
      exact hA i.succ j

omit [Fintype Ω] [FiniteDimensional K V] in
lemma run_le_full {h r m : ℕ} (e : Fin r × Fin m ↪ Fin h)
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) :
    run (rowSpan (HighRankCoverage.hitSpace a b y)) r
      (fun i j => z (e (i,j))) y.submodule ≤ hitSpan a b y z := by
  apply run_span_le
  · exact center_le a b y z
  · intro i j
    unfold HighRankCoverage.hitSpace
    split_ifs with hi
    · exact hit_le a b y z (e (i,j)) hi
    · exact bot_le

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] in
lemma block_mean (w : Ω → ℝ) (ht : ∑ x, w x = 1) {h r m : ℕ}
    (e : Fin r × Fin m ↪ Fin h) (f : (Fin r → Fin m → Ω) → ℝ) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z*f (fun i j => z (e (i,j)))) =
      ∑ z : Fin r → Fin m → Ω, weight (weight w : (Fin m → Ω) → ℝ) z*f z := by
  have H := ProductLaw.marginal w ht e (fun z => f (fun i j => z (i,j)))
  trans ∑ z : Fin r × Fin m → Ω, ProductLaw.weight w z*f (fun i j => z (i,j))
  · convert H using 1 <;> congr!
  rw [← (Equiv.curry (Fin r) (Fin m) Ω).symm.sum_comp]
  apply sum_congr rfl
  intro z _
  congr 1
  simp only [ProductLaw.weight, weight, Fintype.prod_prod_type, Equiv.curry_symm_apply, Function.uncurry]

variable [Finite K] [Fintype (Projectivization K V)]

theorem raw_row_span_growth (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z = 1) (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V)
    (h r m : ℕ) (e : Fin r × Fin m ↪ Fin h) (hr : 2 ≤ r)
    (H M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ u, (∑ z ∈ univ.filter (fun z => b z = u), w z) ≤ M)
    (hH : H ≤ ∑ z, w z * (if a z y.rep = 0 then 1 else 0)) (hH1 : H ≤ 1) :
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
      (if Module.finrank K (hitSpan a b y z) < r then 1 else 0)) ≤
        r*(1-(H-2*M*(Nat.card K:ℝ)^(r-2)))^m := by
  let f (z : Fin r → Fin m → Ω) : ℝ :=
    if Module.finrank K (run (rowSpan (HighRankCoverage.hitSpace a b y)) r z y.submodule : Submodule K V) < r
      then 1 else 0
  calc
    _ ≤ ∑ z : Fin h → Ω, ProductLaw.weight w z*f (fun i j => z (e (i,j))) := by
      apply sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (ProductLaw.nonneg w hw z)
      dsimp [f]
      split_ifs with hfull hpart hpart
      · rfl
      · exact False.elim (hpart ((Submodule.finrank_mono (run_le_full e a b y z)).trans_lt hfull))
      · norm_num
      · rfl
    _ = _ := block_mean w ht e f
    _ ≤ _ := projective_span_growth w hw ht a b y r m hr H M hM0 hM hH hH1

end
end SharpLogRamsey.HighRankGrowth

namespace SharpLogRamsey.FiniteEventBounds
open scoped BigOperators
open Finset Classical
noncomputable section

noncomputable def indicator (P : Prop) : ℝ := if P then 1 else 0
lemma indicator_nonneg (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num
lemma indicator_le_one (P : Prop) : indicator P ≤ 1 := by unfold indicator; split_ifs <;> norm_num
lemma indicator_mono {P Q : Prop} (H : P → Q) : indicator P ≤ indicator Q := by
  unfold indicator
  by_cases hp : P
  · simp only [hp, ite_eq_left]
    rw [ite_eq_left (H hp)]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num
lemma indicator_or_le (P Q : Prop) : indicator (P ∨ Q) ≤ indicator P+indicator Q := by
  unfold indicator
  by_cases hp : P <;> by_cases hq : Q <;> simp [hp,hq]
lemma indicator_or_five (A B C D E : Prop) :
    indicator (A ∨ B ∨ C ∨ D ∨ E) ≤
      indicator A+indicator B+indicator C+indicator D+indicator E := by
  have h₁ := indicator_or_le A (B ∨ C ∨ D ∨ E)
  have h₂ := indicator_or_le B (C ∨ D ∨ E)
  have h₃ := indicator_or_le C (D ∨ E)
  have h₄ := indicator_or_le D E
  linarith

variable {X Y : Type*} [Fintype X] [Fintype Y]

def mean2 (w : X → ℝ) (v : Y → ℝ) (f : X → Y → ℝ) : ℝ :=
  ∑ x, w x*∑ y, v y*f x y

lemma mean2_nonneg (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y) (f : X → Y → ℝ)
    (hf : ∀ x y, 0 ≤ f x y) : 0 ≤ mean2 w v f := by
  apply sum_nonneg
  intro x _
  apply mul_nonneg (hw x)
  apply sum_nonneg
  intro y _
  exact mul_nonneg (hv y) (hf x y)

lemma mean2_mono (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y) {f g : X → Y → ℝ}
    (H : ∀ x y, f x y ≤ g x y) : mean2 w v f ≤ mean2 w v g := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hw x)
  apply sum_le_sum
  intro y _
  exact mul_le_mul_of_nonneg_left (H x y) (hv y)

lemma mean2_add (w : X → ℝ) (v : Y → ℝ) (f g : X → Y → ℝ) :
    mean2 w v (fun x y => f x y+g x y) = mean2 w v f+mean2 w v g := by
  simp [mean2, mul_add, sum_add_distrib]

lemma mean2_const (w : X → ℝ) (v : Y → ℝ)
    (hw : ∑ x, w x=1) (hv : ∑ y, v y=1) (c : ℝ) :
    mean2 w v (fun _ _ => c) = c := by
  simp [mean2, ← sum_mul, hw, hv]

lemma mean2_left (w : X → ℝ) (v : Y → ℝ) (hv : ∑ y, v y=1) (f : X → ℝ) :
    mean2 w v (fun x _ => f x) = ∑ x, w x*f x := by
  simp [mean2, ← sum_mul, hv]

lemma mean2_right (w : X → ℝ) (v : Y → ℝ) (hw : ∑ x, w x=1) (f : Y → ℝ) :
    mean2 w v (fun _ y => f y) = ∑ y, v y*f y := by
  simp [mean2, ← sum_mul, hw]

lemma mean2_symm (w : X → ℝ) (v : Y → ℝ) (f : X → Y → ℝ) :
    mean2 w v f = mean2 v w (fun y x => f x y) := by
  unfold mean2
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  ring

lemma mean2_cover_five (w : X → ℝ) (v : Y → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hv : ∀ y, 0 ≤ v y)
    (A : X → Prop) (B : Y → Prop) (C : X → Prop) (D : Y → Prop)
    (E J : X → Y → Prop)
    (H : ∀ x y, J x y → A x ∨ B y ∨ C x ∨ D y ∨ E x y) :
    mean2 w v (fun x y => indicator (J x y)) ≤
      mean2 w v (fun x _ => indicator (A x))+
      mean2 w v (fun _ y => indicator (B y))+
      mean2 w v (fun x _ => indicator (C x))+
      mean2 w v (fun _ y => indicator (D y))+
      mean2 w v (fun x y => indicator (E x y)) := by
  have hh := mean2_mono w v hw hv (fun x y =>
    (indicator_mono (H x y)).trans (indicator_or_five (A x) (B y) (C x) (D y) (E x y)))
  simpa only [mean2_add] using hh

variable {Z : Type*} [Fintype Z]

lemma mean2_sum (w : X → ℝ) (v : Y → ℝ) (p : Z → ℝ) (f : Z → X → Y → ℝ) :
    (∑ z, p z*mean2 w v (f z)) =
      mean2 w v (fun x y => ∑ z, p z*f z x y) := by
  unfold mean2
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro z _
  ring

omit [Fintype X] [Fintype Y] in
lemma average_with_exception (p : Z → ℝ) (hp : ∀ z, 0 ≤ p z)
    (ht : ∑ z, p z=1) (G : Z → Prop) (f c : Z → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hc : ∀ z, 0 ≤ c z) (hf : ∀ z, f z ≤ 1)
    (hgood : ∀ z, p z≠0 → G z → f z ≤ b+c z) :
    (∑ z, p z*f z) ≤ (∑ z, p z*indicator (¬G z))+b+∑ z, p z*c z := by
  calc
    _ ≤ ∑ z, p z*(indicator (¬G z)+b+c z) := by
      apply sum_le_sum
      intro z _
      by_cases hz : p z=0
      · simp [hz]
      apply mul_le_mul_of_nonneg_left _ (hp z)
      by_cases hG : G z
      · simpa [indicator, hG] using hgood z hz hG
      · simp only [indicator, hG, not_false_eq_true, ite_true]
        have H := hf z
        linarith [hc z]
    _ = _ := by simp [mul_add, sum_add_distrib, ← sum_mul, ht]

end
end SharpLogRamsey.FiniteEventBounds

namespace SharpLogRamsey.HighRankCoverageProbability
open scoped BigOperators
open Finset Classical FiniteEventBounds HighRankDecoder
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype (Projectivization K V)] [Fintype Ω]

noncomputable def conflictMass (w : Ω → ℝ) (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V)
    (c : Projectivization K (Module.Dual K V)) : ℝ :=
  ∑ z, w z*indicator (a z y.rep=0 ∧ c.rep (b z).rep≠0)

omit [Finite K] [Fintype (Projectivization K V)] in
theorem raw_coverage_union (w : Ω → ℝ) (hw : ∀ z, 0 ≤ w z)
    (ht : ∑ z, w z=1) (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep=0) (h r T : ℕ) :
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator (¬Admitted a b z₁ z₂ r T y c)) ≤
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator (Module.finrank K (hitSpan a b y z)<r))+
    (∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator ((univ.filter (fun i => a (z i) y.rep=0)).card<T))+
    2*(∑ z : Fin h → Ω, ProductLaw.weight w z*
       indicator (∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0))+
    mean2 (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (ProductLaw.weight w : (Fin h → Ω) → ℝ)
      (fun z₁ z₂ => indicator
        (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
         hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)) := by
  have hnt : ∑ z : Fin h → Ω, ProductLaw.weight w z=1 := by
    convert ProductLaw.total (ι := Fin h) w ht using 1
    congr!
  have hnn := fun z : Fin h → Ω => ProductLaw.nonneg w hw z
  have H := mean2_cover_five (ProductLaw.weight w : (Fin h → Ω) → ℝ)
    (ProductLaw.weight w : (Fin h → Ω) → ℝ) hnn hnn
    (fun z => Module.finrank K (hitSpan a b y z) < r)
    (fun z => (univ.filter (fun i => a (z i) y.rep=0)).card < T)
    (fun z => ∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0)
    (fun z => ∃ i, a (z i) y.rep=0 ∧ c.rep (b (z i)).rep≠0)
    (fun z₁ z₂ => r < Module.finrank K
        (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
      hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep)
    (fun z₁ z₂ => ¬Admitted a b z₁ z₂ r T y c) (by
      intro z₁ z₂ hJ
      by_contra hbad
      push Not at hbad
      apply hJ
      apply coverage a b z₁ z₂ r T y c hcy
      · exact hbad.2.2.1
      · exact hbad.2.2.2.1
      · exact hbad.1
      · rintro ⟨hrank,hann⟩
        exact hbad.2.2.2.2 hrank hann
      · exact hbad.2.1)
  rw [mean2_left _ _ hnt, mean2_right _ _ hnt,
    mean2_left _ _ hnt, mean2_right _ _ hnt] at H
  convert H using 1
  ring

omit [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [Finite K] [Fintype (Projectivization K V)] in

end
end SharpLogRamsey.HighRankCoverageProbability
end

end OAI
