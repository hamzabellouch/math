import Mathlib
import OAI.Combinatorics.IndependentSets.Expansion.Supported

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open scoped BigOperators Classical

noncomputable def heavy {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => θ^2 < influence f i)

lemma heavy_card_bound {n : ℕ} (θ : ℝ) (f : Cube n → ℝ) :
    ((heavy θ f).card : ℝ) * θ^2 ≤ ∑ i, influence f i := by
  calc
    _ = ∑ _i ∈ heavy θ f, θ^2 := by simp [nsmul_eq_mul]
    _ ≤ ∑ i ∈ heavy θ f, influence f i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ ≤ ∑ i, influence f i := Finset.sum_le_univ_sum_of_nonneg (fun i => influence_nonneg f i)

lemma high_degree_tail {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1) (k : ℕ) :
    (∑ s, if k < degree s then (fourier f s)^2 else 0) ≤
      (∑ i, influence f i) / (k+1:ℝ) := by
  apply (le_div_iff₀ (by positivity : (0:ℝ)<k+1)).mpr
  calc
    _ = ∑ s, (if k < degree s then (fourier f s)^2 else 0) * (k+1:ℝ) :=
      Finset.sum_mul ..
    _ ≤ ∑ s, (degree s:ℝ) * (fourier f s)^2 := by
      apply Finset.sum_le_sum
      intro s _
      by_cases hs : k < degree s
      · simp only [ite_eq_left hs]
        have hk : (k+1:ℝ) ≤ degree s := by exact_mod_cast hs
        nlinarith [sq_nonneg (fourier f s)]
      · simp only [ite_eq_right hs, zero_mul]
        positivity
    _ = ∑ i, mean (fun x => diff i f x^2) := weighted_fourier_energy f
    _ ≤ ∑ i, influence f i := Finset.sum_le_sum (fun i _ => diff_square_le_influence f hf i)

lemma low_degree_diff_sum {n : ℕ} (f : Cube n → ℝ) (i : Fin n) (k : ℕ) :
    (∑ s, if degree s ≤ k then (fourier (diff i f) s)^2 else 0) ≤
      (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := by
  rw [← fourier_parseval, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  by_cases hs : degree s ≤ k
  · simpa only [ite_eq_left hs] using low_degree_coefficient (diff i f) s hs
  · simp only [ite_eq_right hs]
    positivity

lemma low_degree_outside {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) ≤
      (4:ℝ)^k * θ * (∑ i, influence f i) := by
  let S := heavy θ f
  have hpoint (s : Cube n) :
      (if degree s ≤ k ∧ ¬Supported S s then (fourier f s)^2 else 0) ≤
      ∑ i : Fin n, if i ∈ S then 0 else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0 := by
    have hn (i : Fin n) : 0 ≤ (if i ∈ S then (0:ℝ) else
        if degree s ≤ k then (fourier (diff i f) s)^2 else 0) := by
      split_ifs <;> positivity
    by_cases hs : degree s ≤ k ∧ ¬Supported S s
    · simp only [ite_eq_left hs]
      obtain ⟨i, hi, hni⟩ : ∃ i, bit s i = true ∧ i ∉ S := by
        obtain ⟨i, hi⟩ := not_forall.mp hs.2
        exact ⟨i, (Classical.not_imp.mp hi).1, (Classical.not_imp.mp hi).2⟩
      have hb := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
      simpa only [ite_eq_right hni, ite_eq_left hs.1, fourier_diff, hi, ↓reduceIte] using hb
    · simp only [ite_eq_right hs]
      exact Finset.sum_nonneg (fun i _ => hn i)
  have hb := Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Cube n))) => hpoint s)
  rw [Finset.sum_comm] at hb
  apply hb.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ S
  · simp only [ite_eq_left hi, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hθ) (influence_nonneg f i)
  · simp only [ite_eq_right hi]
    have hsmall : influence f i ≤ θ^2 := by
      have hh : ¬θ^2 < influence f i := by
        intro hlt
        apply hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
      exact le_of_not_gt hh
    calc
      _ ≤ (4:ℝ)^k * mean (fun x => noise (1/2) (diff i f) x^2) := low_degree_diff_sum f i k
      _ ≤ (4:ℝ)^k * (θ * influence f i) :=
        mul_le_mul_of_nonneg_left (noise_small_influence f hf i hθ hsmall) (by positivity)
      _ = (4:ℝ)^k * θ * influence f i := by ring

theorem boolean_junta_error {n : ℕ} (f : Cube n → ℝ) (hf : ∀ x, |f x| ≤ 1)
    {θ : ℝ} (hθ : 0 ≤ θ) (k : ℕ) :
    mean (fun x => (f x - truncate (heavy θ f) f x)^2) ≤
      (∑ i, influence f i) / (k+1:ℝ) + (4:ℝ)^k * θ * (∑ i, influence f i) := by
  rw [truncate_error]
  have hsplit : (∑ s, if Supported (heavy θ f) s then 0 else (fourier f s)^2) ≤
      (∑ s, if k < degree s then (fourier f s)^2 else 0) +
      (∑ s, if degree s ≤ k ∧ ¬Supported (heavy θ f) s then (fourier f s)^2 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    by_cases ht : Supported (heavy θ f) s <;>
      by_cases hd : degree s ≤ k <;>
      simp [ht, hd, show (k < degree s) ↔ ¬degree s ≤ k from lt_iff_not_ge,
        sq_nonneg]
  exact hsplit.trans (add_le_add (high_degree_tail f hf k) (low_degree_outside f hf hθ k))

lemma mean_const {n : ℕ} (c : ℝ) : mean (fun _ : Cube n => c) = c := Fintype.expect_const c

lemma mean_sum {n : ℕ} {α : Type*} (A : Finset α) (f : α → Cube n → ℝ) :
    mean (fun x => ∑ a ∈ A, f a x) = ∑ a ∈ A, mean (f a) :=
  Finset.expect_sum_comm ..

noncomputable def tailSet {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.succ ∈ S)

@[simp] lemma mem_tailSet {n : ℕ} (S : Finset (Fin (n+1))) (i : Fin n) :
    i ∈ tailSet S ↔ i.succ ∈ S := by simp [tailSet]

lemma supported_cons {n : ℕ} (S : Finset (Fin (n+1))) (b : Bool) (s : Cube n) :
    Supported S (b,s) ↔ (b = true → 0 ∈ S) ∧ Supported (tailSet S) s := by
  constructor
  · intro h
    refine ⟨fun hb => h 0 hb, fun i hi => ?_⟩
    exact (mem_tailSet S i).mpr (h i.succ hi)
  · rintro ⟨h₀, ht⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h₀
    · intro hi
      exact (mem_tailSet S j).mp (ht j hi)

noncomputable def merge : {n : ℕ} → Finset (Fin n) → Cube n → Cube n → Cube n
  | 0, _, x, _ => x
  | _+1, S, (b,x), (c,y) => (if 0 ∈ S then b else c, merge (tailSet S) x y)

lemma bit_merge {n : ℕ} (S : Finset (Fin n)) (x y : Cube n) (i : Fin n) :
    bit (merge S x y) i = if i ∈ S then bit x i else bit y i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨b,x⟩ := x
    obtain ⟨c,y⟩ := y
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [bit, merge]
    · simp [bit, merge, ih]

lemma walsh_merge_mean {n : ℕ} (S : Finset (Fin n)) (s x : Cube n) :
    mean (fun y => walsh s (merge S x y)) = if Supported S s then walsh s x else 0 := by
  induction n with
  | zero =>
    have hs : Supported S s := fun i => Fin.elim0 i
    simp [mean_zero, walsh, hs]
  | succ n ih =>
    obtain ⟨b,s⟩ := s
    obtain ⟨c,x⟩ := x
    rw [mean_succ]
    change (mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else false) then -1 else 1) *
      walsh s (merge (tailSet S) x y)) +
      mean (fun y => (if b && (if (0 : Fin (n+1)) ∈ S then c else true) then -1 else 1) *
      walsh s (merge (tailSet S) x y))) / 2 = _
    rw [mean_mul, mean_mul, ih]
    simp only [supported_cons, walsh]
    by_cases hs : Supported (tailSet S) s <;> by_cases h₀ : (0 : Fin (n+1)) ∈ S <;>
      cases b <;> cases c <;> simp [hs, h₀]

theorem truncate_eq_coordinate_mean {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ) (x : Cube n) :
    truncate S f x = mean (fun y => f (merge S x y)) := by
  rw [truncate, synth_eq_sum]
  calc
    _ = ∑ s, mean (fun y => fourier f s * walsh s (merge S x y)) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [mean_mul, walsh_merge_mean]
      split_ifs <;> simp
    _ = mean (fun y => ∑ s, fourier f s * walsh s (merge S x y)) := (mean_sum _ _).symm
    _ = mean (fun y => f (merge S x y)) := by
      apply mean_congr
      intro y
      rw [← synth_eq_sum, synth_fourier]

lemma truncate_bounded {n : ℕ} (S : Finset (Fin n)) (f : Cube n → ℝ)
    (hf : ∀ x, |f x| ≤ 1) : ∀ x, |truncate S f x| ≤ 1 := by
  intro x
  rw [truncate_eq_coordinate_mean]
  have ha : |mean (fun y => f (merge S x y))| ≤ mean (fun y => |f (merge S x y)|) :=
    Finset.abs_expect_le _ _
  apply ha.trans
  have h := mean_mono (n:=n) (fun y => hf (merge S x y))
  rwa [mean_const] at h

theorem boolean_junta_uniform {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : Cube n → ℝ,
      (∀ x, |f x| ≤ 1) → (∑ i, influence f i) ≤ L →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        mean (fun x => (f x - truncate S f x)^2) < u := by
  obtain ⟨k, hk⟩ := exists_nat_gt (4*L/u)
  have hk₀ : (0:ℝ) < k+1 := by positivity
  have hkL : L/(k+1:ℝ) < u/4 := by
    have he : 4*L < (k:ℝ)*u := (div_lt_iff₀ hu).mp hk
    apply (div_lt_iff₀ hk₀).mpr
    nlinarith
  let θ : ℝ := u / (4 * (4:ℝ)^k * (L+1))
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθeq : (4:ℝ)^k * θ * (L+1) = u/4 := by
    dsimp [θ]
    field_simp
  have hθL : (4:ℝ)^k * θ * L ≤ u/4 := by
    rw [← hθeq]
    gcongr
    linarith
  refine ⟨⌈L/θ^2⌉₊ + 1, by omega, ?_⟩
  intro n f hf hi
  refine ⟨heavy θ f, ?_, ?_⟩
  · have hc : ((heavy θ f).card:ℝ) ≤ L/θ^2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hθ)).mpr
      exact (heavy_card_bound θ f).trans hi
    have hc' := hc.trans (Nat.le_ceil _)
    have hc'' : (heavy θ f).card ≤ ⌈L/θ^2⌉₊ := by exact_mod_cast hc'
    omega
  · have h := boolean_junta_error f hf hθ.le k
    have hd : (∑ i, influence f i)/(k+1:ℝ) ≤ L/(k+1:ℝ) :=
      div_le_div_of_nonneg_right hi hk₀.le
    have hm : (4:ℝ)^k * θ * (∑ i, influence f i) ≤ (4:ℝ)^k * θ * L :=
      mul_le_mul_of_nonneg_left hi (by positivity)
    linarith

end LargeIndependentSets.BooleanJunta

end OAI
