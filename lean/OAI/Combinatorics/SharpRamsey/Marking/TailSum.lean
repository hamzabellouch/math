import Mathlib
import OAI.Combinatorics.SharpRamsey.Marking.CardVectorLifts

namespace OAI

/-! High-rank geometric supports and entropy estimates. -/

section
open scoped BigOperators Classical
open Finset
section
namespace SharpLogRamsey.DyadicTail
open scoped BigOperators
open Finset Classical
noncomputable section
variable {Y : Type*} [Fintype Y]
theorem tail_sum (a w : Y → ℝ) (u C M : ℝ) (n T : ℕ)
    (hu : 0 < u) (hC : 0 ≤ C) (hM : 0 ≤ M) (hCu : C*u ≤ 1)
    (ha : ∀ x, 0 ≤ a x) (hw1 : ∀ x, w x ≤ 1)
    (hzero : ∀ x, a x = 0 → w x = 0)
    (hw : ∀ x, 0 < a x → a x ≤ u → w x ≤ (C*a x)^T)
    (hT : n+1 ≤ T)
    (htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n) :
    ∑ x, w x ≤ M*(1+2^(n+1)) := by
  classical
  let H : Finset Y := univ.filter (fun x => u ≤ a x)
  let L : Finset Y := univ.filter (fun x => 0 < a x ∧ a x < u)
  have hH : ∑ x ∈ H, w x ≤ M := by
    calc
      _ ≤ ∑ _x ∈ H, (1 : ℝ) := Finset.sum_le_sum (fun x _ => hw1 x)
      _ = (H.card : ℝ) := by simp
      _ ≤ M := by simpa [H, ne_of_gt hu] using htail u hu le_rfl
  have htailL : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun x : L => v ≤ a x)).card : ℝ) ≤ M*(u/v)^n := by
    intro v hv hvu
    have hc : (univ.filter (fun x : L => v ≤ a x)).card ≤
        (univ.filter (fun x : Y => v ≤ a x)).card := by
      apply Finset.card_le_card_of_injOn (fun x : L => x.val)
      · intro x hx
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩
      · intro x _ y _ hh
        exact Subtype.ext hh
    exact (by exact_mod_cast hc :
      ((univ.filter (fun x : L => v ≤ a x)).card : ℝ) ≤
        ((univ.filter (fun x : Y => v ≤ a x)).card : ℝ)).trans (htail v hv hvu)
  have hL : ∑ x ∈ L, w x ≤ M*2^(n+1) := by
    have hh := small_tail_sum (fun x : L => a x) (fun x : L => w x) u C M n T
      hu hC hM hCu (fun x => ⟨(mem_filter.mp x.2).2.1, (mem_filter.mp x.2).2.2.le⟩)
      (fun x => hw x (mem_filter.mp x.2).2.1 (mem_filter.mp x.2).2.2.le) hT htailL
    simpa only [Finset.sum_coe_sort] using hh
  have he : ∑ x, w x = (∑ x ∈ H, w x)+(∑ x ∈ L, w x) := by
    dsimp [H,L]
    rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hh : u ≤ a x
    · simp [hh, not_lt_of_ge hh]
    · have hxu : a x < u := lt_of_not_ge hh
      by_cases hz : a x = 0
      · simp [hz, hzero x hz]
      · have hx0 : 0 < a x := lt_of_le_of_ne (ha x) (Ne.symm hz)
        simp [hh, hx0, hxu]
  rw [he]
  nlinarith

end
end SharpLogRamsey.DyadicTail
end

section

namespace SharpLogRamsey.HighRankSampling
open scoped BigOperators
open Finset Classical
open SharpLogRamsey.RichUnion SharpLogRamsey.HighRankGeometry
open SharpLogRamsey.FiniteSamplingBounds
noncomputable section
variable {K : Type*} [Field K] [Fintype K] {n : ℕ}
local instance flat_JoinedHighRankAssembly_1 : Fintype (Projectivization K (Fin n → K)) := Fintype.ofFinite _

theorem high_rank_expected (hn : 0 < n)
    (mass : Projectivization K (Fin n → K) → ℝ)
    (hmass : ∀ x, 0 ≤ mass x) (htotal : ∑ x, mass x = 1)
    (X Y : Finset (Projectivization K (Fin n → K)))
    (hsupport : ∀ x, x ∉ X → mass x = 0)
    (A u : ℝ) (hA : 0 < A) (hu : 0 < u) (huA : u ≤ 2*A)
    (hu20 : u ≤ 1/20) (hCu : 20*Real.exp (1/2)*u ≤ 1)
    (r : ℕ) (hr : 0 < r)
    (hcap : ∀ x ∈ X, mass x ≤ A/(Fintype.card K : ℝ)^r)
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K))
    (hrank : ∀ y ∈ Y, Module.finrank K (W y) = r)
    (hy : ∀ y ∈ Y, y.submodule ≤ W y)
    (h T : ℕ) (hT : (h : ℝ)/(10*(Fintype.card K : ℝ)) ≤ T) (hTn : n+1 ≤ T) :
    (∑ y ∈ Y, rowTail mass (projectivePoints (W y)) h T) ≤
      (10*(n : ℝ)*A/u)^n*X.card*(1+2^(n+1)) := by
  classical
  let q : ℝ := Fintype.card K
  let a (y : Y) : ℝ := q * ∑ x ∈ projectivePoints (W y), mass x
  let w (y : Y) : ℝ := rowTail mass (projectivePoints (W y)) h T
  let M : ℝ := (10*(n : ℝ)*A/u)^n*X.card
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := K)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have ha : ∀ y, 0 ≤ a y := fun y =>
    mul_nonneg hq.le (Finset.sum_nonneg (fun x _ => hmass x))
  have hzero : ∀ y, a y = 0 → w y = 0 := by
    intro y hay
    apply rowTail_zero mass hmass _ h T (by omega)
    exact (mul_eq_zero.mp hay).resolve_left (ne_of_gt hq)
  have hw : ∀ y, 0 < a y → a y ≤ u → w y ≤ (20*Real.exp (1/2)*a y)^T := by
    intro y hay hayu
    apply rowTail_small mass hmass htotal _ h T q (a y) hq hay (hayu.trans hu20) _ hT
    dsimp [a]
    rw [mul_div_cancel_left₀ _ (ne_of_gt hq)]
  have htail : ∀ v, 0 < v → v ≤ u →
      ((univ.filter (fun y : Y => v ≤ a y)).card : ℝ) ≤ M*(u/v)^n := by
    intro v hv hvu
    let Z := Y.filter (fun y => v ≤ q * ∑ x ∈ projectivePoints (W y), mass x)
    have hc : (univ.filter (fun y : Y => v ≤ a y)).card = Z.card := by
      apply Finset.card_bij (fun y _ => y.val)
      · intro y hyy
        exact mem_filter.mpr ⟨y.2, (mem_filter.mp hyy).2⟩
      · intro y _ z _ hzz
        exact Subtype.ext hzz
      · intro y hyy
        exact ⟨⟨y,(mem_filter.mp hyy).1⟩,mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hyy).2⟩,rfl⟩
    rw [hc]
    have hb := high_rank_tail hn mass X Z hsupport A v hA hv (hvu.trans huA) r hr hcap W
      (fun y hyy => hrank y (mem_filter.mp hyy).1)
      (fun y hyy => hy y (mem_filter.mp hyy).1)
      (fun y hyy => (mem_filter.mp hyy).2)
    convert hb using 1
    dsimp [M]
    rw [mul_right_comm _ (X.card : ℝ), ← mul_pow]
    congr 2
    field_simp
  have H := DyadicTail.tail_sum a w u (20*Real.exp (1/2)) M n T hu (by positivity)
    hM hCu ha (fun y => rowTail_le_one mass hmass htotal _ h T) hzero hw hTn htail
  change (∑ y : Y, rowTail mass (projectivePoints (W y)) h T) ≤ _ at H
  rw [Finset.sum_coe_sort Y (fun y => rowTail mass (projectivePoints (W y)) h T)] at H
  exact H

lemma mean_admitted_eq
    (mass : Projectivization K (Fin n → K) → ℝ)
    (Y : Finset (Projectivization K (Fin n → K)))
    (W : Projectivization K (Fin n → K) → Submodule K (Fin n → K)) (h T : ℕ) :
    (∑ z : Fin h → Projectivization K (Fin n → K),
      rowWeight mass z * ((Y.filter (fun y => T ≤ hitCount (projectivePoints (W y)) z)).card : ℝ)) =
      ∑ y ∈ Y, rowTail mass (projectivePoints (W y)) h T := by
  classical
  simp_rw [← Finset.sum_boole, Finset.mul_sum, rowTail]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

end
end SharpLogRamsey.HighRankSampling
end

namespace SharpLogRamsey.HighRankDecoder
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V Ω : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def hitSpan {h : ℕ} (a : Ω → Module.Dual K V)
    (b : Ω → Projectivization K V) (y : Projectivization K V) (z : Fin h → Ω) :
    Submodule K V :=
  y.submodule ⊔ ⨆ i, if a (z i) y.rep = 0 then (b (z i)).submodule else ⊥

lemma center_le {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) : y.submodule ≤ hitSpan a b y z := le_sup_left

lemma hit_le {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) (i : Fin h) (hi : a (z i) y.rep = 0) :
    (b (z i)).submodule ≤ hitSpan a b y z := by
  apply le_trans _ le_sup_right
  have H := le_iSup (fun j => if a (z j) y.rep = 0 then (b (z j)).submodule else ⊥) i
  rwa [ite_eq_left hi] at H

lemma line_le_ker (b : Projectivization K V) (c : Module.Dual K V) :
    b.submodule ≤ LinearMap.ker c ↔ c b.rep = 0 := by
  rw [Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem]
  rfl

lemma annihilates_hitSpan {h : ℕ} (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (y : Projectivization K V) (z : Fin h → Ω) (c : Module.Dual K V)
    (hcy : c y.rep = 0)
    (hconflict : ∀ i, a (z i) y.rep = 0 → c (b (z i)).rep = 0) :
    hitSpan a b y z ≤ LinearMap.ker c := by
  apply sup_le ((line_le_ker y c).mpr hcy)
  apply iSup_le
  intro i
  split_ifs with hi
  · exact (line_le_ker _ c).mpr (hconflict i hi)
  · exact bot_le

noncomputable def Admitted [FiniteDimensional K V] {h : ℕ}
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (z₁ z₂ : Fin h → Ω) (r T : ℕ)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V)) : Prop :=
  Module.finrank K (hitSpan a b y z₁) = r ∧
  hitSpan a b y z₁ ≤ LinearMap.ker c.rep ∧
  T ≤ (univ.filter (fun i => (b (z₂ i)).submodule ≤ hitSpan a b y z₁)).card

lemma admitted_incident [FiniteDimensional K V] {h : ℕ}
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (z₁ z₂ : Fin h → Ω) (r T : ℕ)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (H : Admitted a b z₁ z₂ r T y c) : c.rep y.rep = 0 :=
  (line_le_ker y c.rep).mp ((center_le a b y z₁).trans H.2.1)

theorem coverage [FiniteDimensional K V] {h : ℕ}
    (a : Ω → Module.Dual K V) (b : Ω → Projectivization K V)
    (z₁ z₂ : Fin h → Ω) (r T : ℕ)
    (y : Projectivization K V) (c : Projectivization K (Module.Dual K V))
    (hcy : c.rep y.rep = 0)
    (hconflict₁ : ∀ i, a (z₁ i) y.rep = 0 → c.rep (b (z₁ i)).rep = 0)
    (hconflict₂ : ∀ i, a (z₂ i) y.rep = 0 → c.rep (b (z₂ i)).rep = 0)
    (hreach : r ≤ Module.finrank K (hitSpan a b y z₁))
    (hexcess : ¬ (r < Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ∧
      hitSpan a b y z₁ ⊔ hitSpan a b y z₂ ≤ LinearMap.ker c.rep))
    (hhits : T ≤ (univ.filter (fun i => a (z₂ i) y.rep = 0)).card) :
    Admitted a b z₁ z₂ r T y c := by
  have ha₁ := annihilates_hitSpan a b y z₁ c.rep hcy hconflict₁
  have ha₂ := annihilates_hitSpan a b y z₂ c.rep hcy hconflict₂
  have hcombined : Module.finrank K (hitSpan a b y z₁ ⊔ hitSpan a b y z₂ : Submodule K V) ≤ r := by
    by_contra hn
    exact hexcess ⟨Nat.lt_of_not_ge hn, sup_le ha₁ ha₂⟩
  have hle := Submodule.finrank_mono
    (show hitSpan a b y z₁ ≤ hitSpan a b y z₁ ⊔ hitSpan a b y z₂ from le_sup_left)
  have hrank : Module.finrank K (hitSpan a b y z₁) = r := by omega
  have heq : hitSpan a b y z₁ = hitSpan a b y z₁ ⊔ hitSpan a b y z₂ := by
    apply Submodule.eq_of_le_of_finrank_eq le_sup_left
    omega
  refine ⟨hrank, ha₁, hhits.trans (card_le_card ?_)⟩
  intro i hi
  apply mem_filter.mpr
  refine ⟨mem_univ _, ?_⟩
  rw [heq]
  exact (hit_le a b y z₂ i (mem_filter.mp hi).2).trans le_sup_right

end
end SharpLogRamsey.HighRankDecoder

namespace SharpLogRamsey.HighRankExcess
open scoped BigOperators
open Finset Classical
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

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

variable [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

omit [FiniteDimensional K V] [Fintype (Projectivization K (Module.Dual K V))] in
lemma projective_card (W : Submodule K V) :
    (univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card =
      ∑ i ∈ range (Module.finrank K W), Nat.card K^i := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
    ← Nat.card_congr (projectiveSubmoduleEquiv W)]
  exact Projectivization.card_of_finrank K W rfl

omit [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Finite K] in
lemma geom_sum_le_twice {q : ℝ} (hq : 2 ≤ q) (r : ℕ) :
    (∑ i ∈ range (r+1), q^i) ≤ 2*q^r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [sum_range_succ, pow_succ]
    have hp : 0 ≤ q^r := pow_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_right hq hp]

omit [Fintype (Projectivization K (Module.Dual K V))] [FiniteDimensional K V] in
lemma small_span_card (r : ℕ) (hr : 1 ≤ r) (W : Submodule K V)
    (hW : Module.finrank K W ≤ r) :
    ((univ.filter (fun b : Projectivization K V => b.submodule ≤ W)).card : ℝ) ≤
      2*(Nat.card K:ℝ)^(r-1) := by
  rw [projective_card, Nat.cast_sum]
  push_cast
  calc
    _ ≤ ∑ i ∈ range ((r-1)+1), (Nat.card K:ℝ)^i := by
      apply sum_le_sum_of_subset_of_nonneg
      · apply range_mono
        omega
      · intro _ _ _; positivity
    _ ≤ _ := geom_sum_le_twice (by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card K)) _

def partners (W : Submodule K V) : Finset (Projectivization K (Module.Dual K V)) :=
  univ.filter (fun a => W ≤ LinearMap.ker a.rep)

omit [Finite K] [FiniteDimensional K V] [Fintype (Projectivization K V)] in
lemma partners_eq (W : Submodule K V) :
    partners W = univ.filter (fun a => a.submodule ≤ W.dualAnnihilator) := by
  ext a
  simp only [partners, mem_filter, mem_univ, true_and,
    Projectivization.submodule_eq, Submodule.span_singleton_le_iff_mem,
    Submodule.mem_dualAnnihilator]
  rfl

omit [Fintype (Projectivization K V)] in
lemma excess_partners_card {d r : ℕ} (hdim : Module.finrank K V = d+1)
    (hr : r < d) (W : Submodule K V) (hW : r < Module.finrank K W) :
    ((partners W).card:ℝ) ≤ 2*(Nat.card K:ℝ)^(d-r-1) := by
  rw [partners_eq]
  apply small_span_card (d-r) (by omega)
  have h := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  omega

omit [Finite K] [Fintype (Projectivization K V)] in
lemma full_rank_no_partners {d : ℕ} (hdim : Module.finrank K V = d+1)
    (W : Submodule K V) (hW : d < Module.finrank K W) : partners W = ∅ := by
  have htop : W = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hm := Submodule.finrank_le W
    omega
  subst W
  apply filter_eq_empty_iff.mpr
  intro a _ ha
  exact a.rep_nonzero (LinearMap.ker_eq_top.mp (top_unique ha))

def excessCarrier (U : Finset (Projectivization K V))
    (W : Projectivization K V → Submodule K V) (r : ℕ) :
    Finset (Projectivization K V × Projectivization K (Module.Dual K V)) :=
  (U ×ˢ univ).filter (fun z => r < Module.finrank K (W z.1) ∧ W z.1 ≤ LinearMap.ker z.2.rep)

omit [Fintype (Projectivization K V)] in
lemma excessCarrier_card {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r < d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V) :
    ((excessCarrier U W r).card:ℝ) ≤ U.card*(2*(Nat.card K:ℝ)^(d-r-1)) := by
  have he : excessCarrier U W r =
      U.biUnion (fun y => if r < Module.finrank K (W y) then
        (partners (W y)).image (Prod.mk y) else ∅) := by
    ext z
    simp only [excessCarrier, mem_filter, mem_product, mem_univ, and_true, mem_biUnion]
    constructor
    · rintro ⟨hy, hr, hc⟩
      refine ⟨z.1, hy, ?_⟩
      rw [ite_eq_left hr]
      apply mem_image.mpr
      exact ⟨z.2, mem_filter.mpr ⟨mem_univ _, hc⟩, Prod.eta z⟩
    · rintro ⟨y, hy, hz⟩
      split_ifs at hz with hr
      · obtain ⟨c, hc, rfl⟩ := mem_image.mp hz
        exact ⟨hy, hr, (mem_filter.mp hc).2⟩
      · simp at hz
  rw [he]
  calc
    _ ≤ ∑ y ∈ U, ((if r < Module.finrank K (W y) then
        (partners (W y)).image (Prod.mk y) else ∅).card:ℝ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _y ∈ U, 2*(Nat.card K:ℝ)^(d-r-1) := by
      apply sum_le_sum
      intro y _
      split_ifs with hW
      · rw [card_image_of_injective _ (by intro a b h; exact Prod.mk.inj h |>.2)]
        exact excess_partners_card hdim hr (W y) hW
      · simp
    _ = _ := by simp

omit [Fintype (Projectivization K V)] in
theorem target_excess_mass {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r < d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (M : ℝ) (hM : 0 ≤ M) :
    (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ U ×ˢ univ, if M < p z then p z else 0) +
        U.card*(2*(Nat.card K:ℝ)^(d-r-1))*M := by
  have hsplit : (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ excessCarrier U W r, if M < p z then p z else 0) +
        (excessCarrier U W r).card * M := by
    rw [← nsmul_eq_mul, ← sum_const, ← sum_add_distrib]
    apply sum_le_sum
    intro z _
    split_ifs with hz
    · linarith
    · simpa only [zero_add] using le_of_not_gt hz
  have hlarge : (∑ z ∈ excessCarrier U W r, if M < p z then p z else 0) ≤
      ∑ z ∈ U ×ˢ univ, if M < p z then p z else 0 := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro z _ _
    split_ifs <;> first | exact hp z | rfl
  have hc := mul_le_mul_of_nonneg_right (excessCarrier_card hdim hr U W) hM
  linarith

omit [Finite K] [Fintype (Projectivization K V)] in
lemma excessCarrier_full_rank {d : ℕ} (hdim : Module.finrank K V = d+1)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V) :
    excessCarrier U W d = ∅ := by
  apply filter_eq_empty_iff.mpr
  intro z _ hz
  have hm : z.2 ∈ partners (W z.1) := mem_filter.mpr ⟨mem_univ _, hz.2⟩
  rw [full_rank_no_partners hdim (W z.1) hz.1] at hm
  simp at hm

omit [Fintype (Projectivization K V)] in
lemma target_excess_mass_le {d r : ℕ} (hdim : Module.finrank K V = d+1) (hr : r ≤ d)
    (U : Finset (Projectivization K V)) (W : Projectivization K V → Submodule K V)
    (p : Projectivization K V × Projectivization K (Module.Dual K V) → ℝ)
    (hp : ∀ z, 0 ≤ p z) (M : ℝ) (hM : 0 ≤ M) :
    (∑ z ∈ excessCarrier U W r, p z) ≤
      (∑ z ∈ U ×ˢ univ, if M < p z then p z else 0) +
        U.card*(2*(Nat.card K:ℝ)^(d-r-1))*M := by
  obtain hrd | rfl := hr.lt_or_eq
  · exact target_excess_mass hdim hrd U W p hp M hM
  · rw [excessCarrier_full_rank hdim, sum_empty]
    apply add_nonneg
    · apply sum_nonneg
      intro z _
      split_ifs <;> first | exact hp _ | rfl
    · positivity

end
end SharpLogRamsey.HighRankExcess
end

end OAI
