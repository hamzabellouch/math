import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.LabelledFilterCard

namespace OAI

/-! High moments, finite-field subspaces, and incidence bounds. -/

section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]
omit [Fintype D] [Fintype H] [DecidableEq H] in
lemma shift_le_kernel_sum (weight : D → ℝ≥0) (lines : H → Finset D)
    {p K : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p) (hK : K ≠ 0)
    (u : V) (f : V → H) :
    alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K ≤
      ∑ v ∈ Finset.univ.erase u, shiftKernel weight lines p K (f u) (f v) := by
  let s := lines ∘ f
  let T := otherComponents weight s (1 / (100 * p)) u
  have hsub : T ⊆ Finset.univ.erase u := by
    intro v hv
    simp only [T, otherComponents, Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact Finset.mem_erase.mpr ⟨by intro he; subst v; exact hv rfl, Finset.mem_univ _⟩
  have hmass := external_mass_le_sum weight s (1 / (100 * p)) u
  have hα := source_alpha_le weight s hp hc u
  have hα0 := alpha_nonneg weight s (1 / (100 * p)) u
  have hone : alpha weight s (1 / (100 * p)) u ^ K ≤ 1 :=
    pow_le_one₀ hα0 (by linarith)
  by_cases hT : T.Nonempty
  · obtain ⟨v,hv,hmax⟩ := Finset.exists_max_image T
      (fun v => mass weight (s u ∩ s v)) hT
    have hcard : (T.card : ℝ) ≤ p := by
      exact_mod_cast (Finset.card_le_card (Finset.subset_univ T)).trans
        (by simpa only [Finset.card_univ] using hc)
    have hle : alpha weight s (1 / (100 * p)) u ≤ p * mass weight (s u ∩ s v) := calc
      _ ≤ ∑ w ∈ T, mass weight (s u ∩ s w) := hmass
      _ ≤ T.card * mass weight (s u ∩ s v) := by
        simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul T
          (fun w => mass weight (s u ∩ s w)) (mass weight (s u ∩ s v)) hmax
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (mass_nonneg _ _)
    apply (le_min hone (pow_le_pow_left₀ hα0 hle K)).trans
    exact Finset.single_le_sum
      (fun w _ => (shiftKernel_range weight lines p K (f u) (f w)).1) (hsub hv)
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hzero : alpha weight s (1 / (100 * p)) u = 0 := by
      apply le_antisymm _ hα0
      change mass weight (externalPart weight s (1 / (100 * p)) u) ≤ 0
      simpa only [show otherComponents weight s (1 / (100 * p)) u = ∅ from he,
        Finset.sum_empty] using hmass
    change alpha weight s (1 / (100 * p)) u ^ K ≤ _
    rw [hzero, zero_pow hK]
    exact Finset.sum_nonneg (fun w _ => (shiftKernel_range weight lines p K (f u) (f w)).1)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.SingletonEnumeration
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.TupleComponents
open SharpRamseyFive.Designations SharpRamseyFive.AmbientDesignations
open SharpRamseyFive.SelectionBridge SharpRamseyFive.WeightedPrograms
open SharpRamseyFive.ResidualElimination
open Classical
variable {D V H : Type} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H]

theorem actual_shift_bad_enumeration (weight rate : D → ℝ≥0) (lines : H → Finset D)
    {p : ℕ} (hp : 0 < p) (hc : Fintype.card V ≤ p)
    (R : ℕ) (denom b mass C : ℝ)
    (hd : 0 < denom) (hb : 1 ≤ b) (hm : 0 ≤ mass) (hC : 0 ≤ C)
    (hmass : ∀ u, ∑ d ∈ lines u, (rate d : ℝ) ≤ mass)
    (K J h N₁ N₂ : ℕ) (hK : 2 ≤ K) (hh : 0 < h) (low : Bool)
    (hsize : h ≤ (R / 2 - if low then 0 else J) / (2 * K))
    (herr : (Fintype.card V : ℝ) * h * (19 / 20 : ℝ) ^ (h - 1) < 1 / 2)
    (hN₁ : ∀ d, (Finset.univ.filter (fun u => d ∈ lines u)).card ≤ N₁)
    (hN₂ : ∀ d e, d ≠ e →
      (Finset.univ.filter (fun u => d ∈ lines u ∧ e ∈ lines u)).card ≤ N₂)
    (hBC : denom * (1 + branchingBound (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low) ≤ C)
    (hrow : ∀ y, (∑ x : H, shiftKernel weight lines p K x y) ≤ C)
    (hpair : (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤ C ^ 2)
    (E S : Finset V) (hS : S ⊆ E) (g : V → H) :
    completionSum E g (fun f =>
      (∏ u ∈ S, alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K) *
        vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J (E \ S)) ≤
      ((Fintype.card V + 1 : ℝ) * C) ^ E.card := by
  apply shift_bad_enumeration
    (fun u f => alpha weight (lines ∘ f) (1 / (100 * p)) u ^ K)
    (fun A f => vertexBadMass weight rate (lines ∘ f) (1 / (100 * p)) R J A)
    (shiftKernel weight lines p K) C hC
  · intro u f
    exact ⟨pow_nonneg (alpha_nonneg _ _ _ _) _,
      pow_le_one₀ (alpha_nonneg _ _ _ _) (by
        have := source_alpha_le weight (lines ∘ f) hp hc u
        linarith)⟩
  · exact fun x y => (shiftKernel_range weight lines p K x y).1
  · exact fun A f => vertexBadMass_nonneg _ _ _ _ _ _ _
  · exact fun A A' hh f => vertexBadMass_antitone _ _ _ _ _ _ hh
  · exact fun u f => shift_le_kernel_sum weight lines hp hc (by omega) u f
  · exact hrow
  · exact hpair
  · intro A g
    apply (actual_bad_completion weight rate lines (1 / (100 * p)) R denom b mass
      hd hb hm hmass K J h N₁ N₂ hK hh low hsize herr hN₁ hN₂ A g).trans
    apply pow_le_pow_left₀ _ hBC
    apply mul_nonneg hd.le
    have hn := branchingBound_nonneg (V := V) (B := Fin R)
      (fun z : H × V => lines z.1) rate denom b mass hd.le (by linarith) hm K
      (N₁ * Fintype.card V) (N₂ * Fintype.card V) low
    linarith
  · exact hS

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.DyadicMoments

open scoped BigOperators

lemma dyadic_cover (δ x : ℝ) (hδ : 0 ≤ δ) (hx : δ ≤ x) (N : ℕ)
    (hN : x ≤ δ * 2 ^ N) :
    ∃ i ∈ Finset.range (N + 1), δ * 2 ^ i ≤ x ∧ x ≤ 2 * (δ * 2 ^ i) := by
  induction N with
  | zero =>
    refine ⟨0, by simp, ?_, ?_⟩
    · simpa using hx
    · simp only [pow_zero, mul_one] at hN ⊢
      linarith
  | succ N ih =>
    by_cases hh : x ≤ δ * 2 ^ N
    · obtain ⟨i, hi, hix, hxi⟩ := ih hh
      exact ⟨i, Finset.mem_range.mpr (by have := Finset.mem_range.mp hi; omega), hix, hxi⟩
    · refine ⟨N, Finset.mem_range.mpr (by omega), le_of_lt (lt_of_not_ge hh), ?_⟩
      rw [pow_succ] at hN
      nlinarith

section Finite
variable {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]

omit [DecidableEq α] [DecidableEq β] in

theorem moment_le_of_cover (x : α → ℝ) (a : β → ℝ) (T : Finset β)
    (K : ℕ) (hK : K ≠ 0) (C : ℝ) (_hC : 0 ≤ C)
    (hx : ∀ v, 0 ≤ x v) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ v, 0 < x v → ∃ i ∈ T, a i ≤ x v ∧ x v ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K ≤ C) :
    (∑ v, x v ^ K) ≤ (T.card : ℝ) * (2 : ℝ) ^ K * C := by
  classical
  have hp (v : α) : x v ^ K ≤
      ∑ i ∈ T, if a i ≤ x v then (2 * a i) ^ K else 0 := by
    by_cases hv : 0 < x v
    · obtain ⟨i, hi, hain, hle⟩ := hcover v hv
      apply (pow_le_pow_left₀ (hx v) hle K).trans
      have hs := Finset.single_le_sum (f := fun j =>
        if a j ≤ x v then (2 * a j) ^ K else 0)
        (fun j hj => by split_ifs <;> positivity [ha j hj]) hi
      simpa [hain] using hs
    · have hz : x v = 0 := le_antisymm (le_of_not_gt hv) (hx v)
      simp only [hz, zero_pow hK]
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity [ha i hi]
  calc
    (∑ v, x v ^ K) ≤ ∑ v, ∑ i ∈ T, if a i ≤ x v then (2 * a i) ^ K else 0 :=
      Finset.sum_le_sum (fun v _ => hp v)
    _ = ∑ i ∈ T, (2 : ℝ) ^ K *
        (((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_pow]
      ring
    _ ≤ ∑ _i ∈ T, (2 : ℝ) ^ K * C := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hcount i hi) (by positivity)
    _ = _ := by simp; ring

omit [DecidableEq α] [DecidableEq β] in

theorem higher_moment_le_of_cover (x : α → ℝ) (a : β → ℝ) (T : Finset β)
    (K J : ℕ) (hK : K ≠ 0) (hKJ : K ≤ J) (C M : ℝ)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hx : ∀ v, 0 ≤ x v)
    (hmax : ∀ v, x v ≤ M) (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ v, 0 < x v → ∃ i ∈ T, a i ≤ x v ∧ x v ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun v => a i ≤ x v)).card : ℝ) * a i ^ K ≤ C) :
    (∑ v, x v ^ J) ≤ (T.card : ℝ) * (2 : ℝ) ^ K * C * M ^ (J - K) := by
  have hp (v : α) : x v ^ J ≤ x v ^ K * M ^ (J - K) := by
    calc
      x v ^ J = x v ^ K * x v ^ (J - K) := by
        rw [← pow_add, Nat.add_sub_of_le hKJ]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hx v) (hmax v) _) (by positivity [hx v])
  calc
    _ ≤ ∑ v, x v ^ K * M ^ (J - K) := Finset.sum_le_sum (fun v _ => hp v)
    _ = (∑ v, x v ^ K) * M ^ (J - K) := (Finset.sum_mul ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (moment_le_of_cover x a T K hK C hC hx ha hcover hcount) (by positivity)

omit [DecidableEq α] in

theorem integer_strength_moment (m : α → ℕ) (δ : ℝ) (hδ : 0 < δ)
    (N K : ℕ) (hK : K ≠ 0) (hm : ∀ v, (m v : ℝ) ≤ 2 ^ N)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ i ∈ Finset.range (N + 1),
      ((Finset.univ.filter (fun v => δ * 2 ^ i ≤ δ * m v)).card : ℝ) *
        (δ * 2 ^ i) ^ K ≤ C) :
    (∑ v, (δ * m v) ^ K) ≤ (N + 1 : ℝ) * 2 ^ K * C := by
  apply (moment_le_of_cover (fun v => δ * m v) (fun i => δ * 2 ^ i)
    (Finset.range (N + 1)) K hK C hC (by intro v; positivity)
    (by intro i hi; positivity) ?_ hcount).trans_eq
  · simp
  · intro v hv
    have hm0 : 0 < m v := by
      by_contra hn
      have hz : m v = 0 := by omega
      simp [hz] at hv
    apply dyadic_cover δ (δ * m v) hδ.le
    · exact le_mul_of_one_le_right hδ.le (by exact_mod_cast hm0)
    · exact mul_le_mul_of_nonneg_left (hm v) hδ.le

end Finite
end SharpRamseyFive.DyadicMoments

namespace SharpRamseyFive.WeightedPrograms

open scoped BigOperators
open SharpRamseyFive.DyadicMoments

variable {V H D B I : Type*} [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype D] [DecidableEq D]
  [Fintype B] [DecidableEq B] [DecidableEq I]

variable (lines : H → Finset D)

def DistinctPairs (H : Type*) := Σ h : H, {h' : H // h' ≠ h}

instance flat_HighMomentRecovered_7 : Fintype (DistinctPairs H) := by unfold DistinctPairs; infer_instance

noncomputable def strength (a : D → ℝ≥0) (p : DistinctPairs H) : ℝ :=
  ∑ d ∈ lines p.1 ∩ lines p.2.val, (a d : ℝ)

omit [Fintype H] [DecidableEq H] [Fintype D] in
lemma strength_nonneg (a : D → ℝ≥0) (p : DistinctPairs H) :
    0 ≤ strength lines a p := by unfold strength; positivity

omit [DecidableEq B] in
omit [Fintype D] [DecidableEq I] in

theorem pairMoment_dyadic (a : D → ℝ≥0) (L : ℝ≥0) (K : ℕ) (hK : K ≠ 0)
    (T : Finset I) (threshold : I → ℝ) (ht : ∀ i ∈ T, 0 ≤ threshold i)
    (hcover : ∀ p, 0 < strength lines a p →
      ∃ i ∈ T, threshold i ≤ strength lines a p ∧ strength lines a p ≤ 2 * threshold i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun p : DistinctPairs H => threshold i ≤ strength lines a p)).card : ℝ) *
        threshold i ^ K ≤ C) :
    pairMoment (B := B) lines (fun d => L * a d) K ≤
      (T.card : ℝ) * C * (2 * Fintype.card B * (L : ℝ)) ^ K := by
  classical
  have h := moment_le_of_cover (strength lines a) threshold T K hK C hC
    (strength_nonneg lines a) ht hcover hcount
  have he : pairMoment (B := B) lines (fun d => L * a d) K =
      ((Fintype.card B : ℝ) * (L : ℝ)) ^ K *
        ∑ p : DistinctPairs H, strength lines a p ^ K := by
    unfold pairMoment
    change _ = _ * ∑ p : (Σ h : H, {h' : H // h' ≠ h}), _
    rw [Fintype.sum_sigma, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h' _
    simp only [NNReal.coe_mul, ← Finset.mul_sum, strength]
    rw [← mul_assoc, mul_pow]
  rw [he]
  apply (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq
  rw [mul_pow, mul_pow]
  ring

omit [DecidableEq V] in
omit [DecidableEq B] in
omit [Fintype D] [DecidableEq I] in

theorem branchingBound_dyadic (a : D → ℝ≥0) (L : ℝ≥0)
    (denom b mass : ℝ) (_hd : 0 ≤ denom) (K N₁ N₂ : ℕ) (low : Bool)
    (hK : K ≠ 0) (T : Finset I) (threshold : I → ℝ)
    (ht : ∀ i ∈ T, 0 ≤ threshold i)
    (hcover : ∀ p, 0 < strength lines a p →
      ∃ i ∈ T, threshold i ≤ strength lines a p ∧ strength lines a p ≤ 2 * threshold i)
    (C : ℝ) (hC : 0 ≤ C)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun p : DistinctPairs H => threshold i ≤ strength lines a p)).card : ℝ) *
        threshold i ^ K ≤ C) :
    branchingBound (V := V) (B := B) lines (fun d => L * a d) denom b mass K N₁ N₂ low ≤
      ((Fintype.card V : ℝ) * Fintype.card H / denom) / b ^ 8 +
      (if low then Fintype.card V ^ 2 * (N₁ : ℝ) *
        uniformAnchorBudget (V := V) (B := B) K mass / denom else 0) +
      (Fintype.card V ^ 3 * (N₂ : ℝ) *
        uniformAnchorBudget (V := V) (B := B) K mass ^ 2 / denom) * b +
      Fintype.card V ^ 2 * ((T.card : ℝ) * C * (2 * Fintype.card B * (L : ℝ)) ^ K) / denom ^ 2 := by
  unfold branchingBound
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pairMoment_dyadic (B := B) lines a L K hK T threshold
      ht hcover C hC hcount) (by positivity)) (by positivity)

end SharpRamseyFive.WeightedPrograms

namespace SharpRamseyFive.SingletonEnumeration
open scoped BigOperators NNReal
open SharpRamseyFive.PoissonScore SharpRamseyFive.DyadicMoments
open SharpRamseyFive.WeightedPrograms
open Classical
variable {D H V I B : Type} [Fintype D] [DecidableEq D]
  [Fintype H] [DecidableEq H] [Fintype V] [DecidableEq V]
  [Fintype B] [DecidableEq B] [DecidableEq I]

lemma sum_split_diagonal (F : H → ℝ) (y : H) :
    (∑ x : H, F x) = F y + ∑ x : {x : H // x ≠ y}, F x := by
  rw [← Finset.sum_erase_add _ F (Finset.mem_univ y), add_comm]
  congr 1
  exact Finset.sum_subtype _ (by intro x; simp) F

lemma sum_pairs_split_diagonal (F : H → H → ℝ) :
    (∑ x : H, ∑ y : H, F x y) =
      (∑ x : H, F x x) + ∑ z : DistinctPairs H, F z.1 z.2 := by
  change _ = _ + ∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2
  rw [Fintype.sum_sigma, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => sum_split_diagonal (F x) x)

omit [DecidableEq I] in
omit [Fintype D] in

theorem shift_row_dyadic (weight : D → ℝ≥0) (lines : H → Finset D)
    (p K : ℕ) (hK : K ≠ 0) (y : H)
    (T : Finset I) (a : I → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ x : {x : H // x ≠ y}, 0 < mass weight (lines x ∩ lines y) →
      ∃ i ∈ T, a i ≤ mass weight (lines x ∩ lines y) ∧
        mass weight (lines x ∩ lines y) ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun x : {x : H // x ≠ y} =>
        a i ≤ mass weight (lines x ∩ lines y))).card : ℝ) * a i ^ K ≤ C) :
    (∑ x : H, shiftKernel weight lines p K x y) ≤
      1 + (T.card : ℝ) * C * (2 * p) ^ K := by
  rw [sum_split_diagonal _ y]
  apply add_le_add (shiftKernel_range weight lines p K y y).2
  calc
    (∑ x : {x : H // x ≠ y}, shiftKernel weight lines p K x y) ≤
        ∑ x : {x : H // x ≠ y}, ((p : ℝ) * mass weight (lines x ∩ lines y)) ^ K := by
      exact Finset.sum_le_sum (fun x _ => min_le_right _ _)
    _ = (p : ℝ) ^ K * ∑ x : {x : H // x ≠ y}, mass weight (lines x ∩ lines y) ^ K := by
      simp only [mul_pow, Finset.mul_sum]
    _ ≤ (p : ℝ) ^ K * ((T.card : ℝ) * 2 ^ K * C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact moment_le_of_cover _ a T K hK C hC
        (fun x => mass_nonneg _ _) ha hcover hcount
    _ = _ := by rw [mul_pow]; ring

omit [DecidableEq I] in
omit [Fintype D] in

theorem shift_pairs_dyadic (weight : D → ℝ≥0) (lines : H → Finset D)
    (p K : ℕ) (hK : K ≠ 0) (T : Finset I) (a : I → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i ∈ T, 0 ≤ a i)
    (hcover : ∀ z : DistinctPairs H, 0 < strength lines weight z →
      ∃ i ∈ T, a i ≤ strength lines weight z ∧ strength lines weight z ≤ 2 * a i)
    (hcount : ∀ i ∈ T,
      ((Finset.univ.filter (fun z : DistinctPairs H => a i ≤ strength lines weight z)).card : ℝ)
        * a i ^ K ≤ C) :
    (∑ x : H, ∑ y : H, shiftKernel weight lines p K x y) ≤
      Fintype.card H + (T.card : ℝ) * C * (2 * p) ^ K := by
  rw [sum_pairs_split_diagonal]
  apply add_le_add
  · exact (Finset.sum_le_sum (fun x _ => (shiftKernel_range weight lines p K x x).2)).trans_eq
      (by simp)
  · calc
      (∑ z : DistinctPairs H, shiftKernel weight lines p K z.1 z.2) ≤
          ∑ z : DistinctPairs H, ((p : ℝ) * strength lines weight z) ^ K :=
        Finset.sum_le_sum (fun z _ => min_le_right _ _)
      _ = (p : ℝ) ^ K * ∑ z : DistinctPairs H, strength lines weight z ^ K := by
        simp only [mul_pow, Finset.mul_sum]
      _ ≤ (p : ℝ) ^ K * ((T.card : ℝ) * 2 ^ K * C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact moment_le_of_cover _ a T K hK C hC
          (strength_nonneg lines weight) ha hcover hcount
      _ = _ := by rw [mul_pow]; ring

omit [Fintype D] [DecidableEq B] in

theorem pairMoment_labelled_le (lines : H → Finset D) (rate : D → ℝ≥0)
    (K : ℕ) (mass : ℝ) (_hm : 0 ≤ mass)
    (hmass : ∀ x, ∑ d ∈ lines x, (rate d : ℝ) ≤ mass) :
    pairMoment (B := B) (fun x : H × V => lines x.1) rate K ≤
      (Fintype.card V : ℝ) ^ 2 *
        (pairMoment (B := B) lines rate K +
          Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K) := by
  let F : H → H → ℝ := fun x y =>
    ((Fintype.card B : ℝ) * ∑ d ∈ lines x ∩ lines y, (rate d : ℝ)) ^ K
  have hF : ∀ x y, 0 ≤ F x y := by intro x y; dsimp [F]; positivity
  have he : pairMoment (B := B) lines rate K = ∑ x : H, ∑ y : {y : H // y ≠ x}, F x y := rfl
  have hdiag : (∑ x : H, F x x) ≤
      Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    apply (Finset.sum_le_sum (fun x _ => show F x x ≤
      ((Fintype.card B : ℝ) * mass) ^ K from ?_)).trans_eq (by simp)
    dsimp [F]
    simp only [Finset.inter_self]
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left (hmass x) (Nat.cast_nonneg _)) K
  have hfull : (∑ x : H, ∑ y : H, F x y) ≤
      pairMoment (B := B) lines rate K + Fintype.card H * ((Fintype.card B : ℝ) * mass) ^ K := by
    rw [sum_pairs_split_diagonal, add_comm]
    change (∑ z : (Σ x : H, {y : H // y ≠ x}), F z.1 z.2) + _ ≤ _
    rw [Fintype.sum_sigma, ← he]
    exact add_le_add le_rfl hdiag
  calc
    _ ≤ ∑ x : H × V, ∑ y : H × V, F x.1 y.1 := by
      unfold pairMoment
      apply Finset.sum_le_sum
      intro x _
      rw [sum_split_diagonal _ x]
      apply le_add_of_nonneg_left (hF _ _)
    _ = (Fintype.card V : ℝ) ^ 2 * (∑ x : H, ∑ y : H, F x y) := by
      simp only [Fintype.sum_prod_type]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hfull (by positivity)

end SharpRamseyFive.SingletonEnumeration

namespace SharpRamseyFive.ResidualElimination
open scoped BigOperators
open Classical
variable {V H : Type} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

noncomputable def patch (g : V → H) (T : Finset V) (x : T → H) : V → H :=
  fun u => if hu : u ∈ T then x ⟨u,hu⟩ else g u

omit [Fintype V] [Fintype H] [DecidableEq H] in
lemma patch_mem (g : V → H) (T : Finset V) (x : T → H) (u : T) :
    patch g T x u = x u := by simp [patch]

end SharpRamseyFive.ResidualElimination
end

end OAI
