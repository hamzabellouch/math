import OAI.NumberTheory.TwoPoint.Bounds.Dilation
import OAI.NumberTheory.TwoPoint.Bounds.AffineTransfer
import OAI.NumberTheory.TwoPoint.Statements

namespace OAI

open Filter
open scoped BigOperators

namespace TwoPointCorrelations

def ProgressionCorrectedElliott : Prop :=
  ∀ f g : ℕ → ℂ, Multiplicative f → Multiplicative g →
    OneBounded f → OneBounded g →
    (UniformlyNonpretentious f ∨ UniformlyNonpretentious g) →
    ∀ h l b : ℕ, 0 < h → 0 < l →
      Tendsto (fun N : ℕ => residuePrefix (fun n => f n * g (n + h)) l b N / (N : ℂ))
        atTop (nhds 0)

theorem Multiplicative.one_eq_zero_or_one {f : ℕ → ℂ} (hf : Multiplicative f) :
    f 1 = 0 ∨ f 1 = 1 := by
  have heq := hf 1 1 (by decide) (by decide) (by decide)
  have hprod : f 1 * (f 1 - 1) = 0 := by
    calc
      f 1 * (f 1 - 1) = f 1 * f 1 - f 1 := by ring
      _ = 0 := by simpa using congrArg (fun z : ℂ => z - f 1) heq.symm
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem Multiplicative.zero_of_one_eq_zero {f : ℕ → ℂ} (hf : Multiplicative f)
    (h0 : f 1 = 0) {n : ℕ} (hn : 0 < n) : f n = 0 := by
  simpa [h0] using hf 1 n (by decide) hn (Nat.coprime_one_left n)

lemma residuePrefix_congr {u v : ℕ → ℂ} (h : ∀ n, 0 < n → u n = v n)
    (l b N : ℕ) : residuePrefix u l b N = residuePrefix v l b N := by
  unfold residuePrefix
  apply Finset.sum_congr rfl
  intro n hn
  rw [h n (Finset.mem_Ioc.mp hn).1]

lemma residuePrefix_sum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℂ) (l b N : ℕ) :
    residuePrefix (fun n => ∑ i ∈ s, u i n) l b N =
      ∑ i ∈ s, residuePrefix (u i) l b N := by
  unfold residuePrefix
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

lemma residuePrefix_const_mul (c : ℂ) (u : ℕ → ℂ) (l b N : ℕ) :
    residuePrefix (fun n => c * u n) l b N = c * residuePrefix u l b N := by
  unfold residuePrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> simp

/-- Finite signed local expansions preserve an established progression limit. -/
theorem finite_expansion_progression_zero {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (c : ι → ℂ) (d : κ → ℂ)
    (F : ι → ℕ → ℂ) (G : κ → ℕ → ℂ) (u v : ℕ → ℂ)
    (hu : ∀ n, 0 < n → u n = ∑ i ∈ s, c i * F i n)
    (hv : ∀ n, 0 < n → v n = ∑ j ∈ t, d j * G j n)
    (h l b : ℕ)
    (hz : ∀ i ∈ s, ∀ j ∈ t,
      Tendsto (fun N : ℕ => residuePrefix (fun n => F i n * G j (n + h)) l b N /
        (N : ℂ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => residuePrefix (fun n => u n * v (n + h)) l b N /
      (N : ℂ)) atTop (nhds 0) := by
  have heq (N : ℕ) : residuePrefix (fun n => u n * v (n + h)) l b N / (N : ℂ) =
      ∑ i ∈ s, ∑ j ∈ t, (c i * d j) *
        (residuePrefix (fun n => F i n * G j (n + h)) l b N / (N : ℂ)) := by
    rw [residuePrefix_congr (v := fun n => ∑ i ∈ s, ∑ j ∈ t,
      (c i * d j) * (F i n * G j (n + h))) (by
        intro n hn
        rw [hu n hn, hv (n + h) (by omega)]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring)]
    simp only [residuePrefix_sum, residuePrefix_const_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [heq]
  have hout := tendsto_finsetSum s (fun i hi =>
    tendsto_finsetSum t (fun j hj =>
      (tendsto_const_nhds (x := c i * d j)).mul (hz i hi j hj)))
  simpa using hout

theorem ProgressionCorrectedElliott.dilations
    (hprog : ProgressionCorrectedElliott) (f g : ℕ → ℂ)
    (hf : Multiplicative f) (hg : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1)
    (hfb : OneBounded f) (hgb : OneBounded g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (a a' h l b : ℕ) (ha : 0 < a) (ha' : 0 < a') (hh : 0 < h) (hl : 0 < l) :
    Tendsto (fun N : ℕ =>
      residuePrefix (fun n => dilate a f n * dilate a' g (n + h)) l b N / (N : ℂ))
      atTop (nhds 0) := by
  apply finite_expansion_progression_zero a.primeFactors.powerset a'.primeFactors.powerset
    (fun E => (-1 : ℂ) ^ E.card) (fun E => (-1 : ℂ) ^ E.card)
    (dilationComponent a f) (dilationComponent a' g)
    (dilate a f) (dilate a' g)
    (fun n hn => dilate_eq_sum_components a f ha hf hf1 hn)
    (fun n hn => dilate_eq_sum_components a' g ha' hg hg1 hn)
  intro E _ E' _
  apply hprog _ _ (dilationComponent_multiplicative a f E)
    (dilationComponent_multiplicative a' g E')
    (dilationComponent_oneBounded _ _ _ hfb) (dilationComponent_oneBounded _ _ _ hgb)
    _ h l b hh hl
  exact hnp.imp (dilationComponent_nonpretentious a f E hfb)
    (dilationComponent_nonpretentious a' g E' hgb)

private theorem affine_ordered_zero (hprog : ProgressionCorrectedElliott)
    (f g : ℕ → ℂ) (hf : Multiplicative f) (hg : Multiplicative g)
    (hf1 : f 1 = 1) (hg1 : g 1 = 1) (hfb : OneBounded f) (hgb : OneBounded g)
    (hnp : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (a₁ a₂ b₁ b₂ : ℕ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (horder : a₂ * b₁ < a₁ * b₂) :
    Tendsto (fun N : ℕ => affineSum f g a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0) := by
  have hp := hprog.dilations f g hf hg hf1 hg1 hfb hgb hnp a₂ a₁
    (a₁ * b₂ - a₂ * b₁) (a₁ * a₂) (a₂ * b₁) ha₂ ha₁
    (Nat.sub_pos_of_lt horder) (Nat.mul_pos ha₁ ha₂)
  have ht := affine_mean_tendsto_zero
    (fun m => dilate a₂ f m * dilate a₁ g (m + (a₁ * b₂ - a₂ * b₁)))
    (a₁ * a₂) (a₂ * b₁) (Nat.mul_pos ha₁ ha₂) hp
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only
  congr 1
  unfold affineSum
  apply Finset.sum_congr rfl
  intro n hn
  have hl : a₁ * a₂ * n + a₂ * b₁ = a₂ * (a₁ * n + b₁) := by ring
  have hr : a₁ * a₂ * n + a₂ * b₁ + (a₁ * b₂ - a₂ * b₁) =
      a₁ * (a₂ * n + b₂) := by
    calc
      _ = a₁ * a₂ * n + a₁ * b₂ := by omega
      _ = _ := by ring
  rw [hr, hl]
  simp [dilate, ha₁.ne', ha₂.ne']

/-- The manuscript's affine reduction, conditional here on its internal
progression theorem. This is not the published-input conditional main result. -/
theorem ProgressionCorrectedElliott.affine (hprog : ProgressionCorrectedElliott) :
    AffineCorrectedElliott := by
  intro f g hf hg hfb hgb hnp a₁ a₂ b₁ b₂ ha₁ ha₂ hneq
  rcases hf.one_eq_zero_or_one with hf0 | hf1
  · have hz (N : ℕ) : affineSum f g a₁ a₂ b₁ b₂ N = 0 := by
      unfold affineSum
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos := (Finset.mem_Icc.mp hn).1
      rw [hf.zero_of_one_eq_zero hf0 (by nlinarith : 0 < a₁ * n + b₁), zero_mul]
    simpa only [hz, zero_div] using (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
  rcases hg.one_eq_zero_or_one with hg0 | hg1
  · have hz (N : ℕ) : affineSum f g a₁ a₂ b₁ b₂ N = 0 := by
      unfold affineSum
      apply Finset.sum_eq_zero
      intro n hn
      have hnpos := (Finset.mem_Icc.mp hn).1
      rw [hg.zero_of_one_eq_zero hg0 (by nlinarith : 0 < a₂ * n + b₂), mul_zero]
    simpa only [hz, zero_div] using (tendsto_const_nhds (x := (0 : ℂ)) (f := atTop))
  rcases lt_or_gt_of_ne hneq with hlt | hgt
  · have h := affine_ordered_zero hprog g f hg hf hg1 hf1 hgb hfb hnp.symm
      a₂ a₁ b₂ b₁ ha₂ ha₁ hlt
    simpa only [affineSum_swap f g] using h
  · exact affine_ordered_zero hprog f g hf hg hf1 hg1 hfb hgb hnp
      a₁ a₂ b₁ b₂ ha₁ ha₂ hgt

end TwoPointCorrelations

end OAI
