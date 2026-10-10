import OAI.Analysis.BackwardIntertwiners.ConvexEnvelope

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section


structure EnvelopeBounds (A B : ℕ → ℝ) (b c : ℤ → ℂ) : Prop where
  b_pos : ∀ n : ℕ, ‖b n‖ ≤ Real.exp (-B n)
  b_neg : ∀ n : ℕ, ‖b (-(n : ℤ))‖ ≤ Real.exp (A n)
  c_pos : ∀ n : ℕ, ‖c n‖ ≤ Real.exp (B n)
  c_neg : ∀ n : ℕ, ‖c (-(n : ℤ))‖ ≤ Real.exp (-A n)

lemma middle_exponent {A B : ℕ → ℝ} (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {m : ℕ} (hm : 1 ≤ m) (p k : ℕ) (hk : k ≤ m) {lam : ℝ}
    (hbridge : A m - A (m-1) + lam ≤ B (p+1) - B p) :
    -B (p+k) - A (m-k) ≤ -B p - A m - lam * k := by
  have hlow := hB.increment_lower p k
  have hupp := hA.increment_upper (m-k) k (m-1) (by omega)
  rw [Nat.sub_add_cancel hk, Nat.sub_add_cancel hm] at hupp
  have hmul := mul_le_mul_of_nonneg_left hbridge (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  nlinarith


def centeredCorrelation (b c : ℤ → ℂ) (m p : ℕ) (n : ℤ) : ℂ :=
  b ((p : ℤ)+n) * c (-(m : ℤ)+n)

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}

lemma reflected (hb : EnvelopeBounds A B b c) :
    EnvelopeBounds B A (fun n => c (-n)) (fun n => b (-n)) where
  b_pos := hb.c_neg
  b_neg := by simpa only [neg_neg] using hb.c_pos
  c_pos := hb.b_neg
  c_neg := by simpa only [neg_neg] using hb.b_pos

lemma central_norm (_ : EnvelopeBounds A B b c) {m p : ℕ}
    (hp : ‖b (p : ℤ)‖ = Real.exp (-B p))
    (hm : ‖c (-(m : ℤ))‖ = Real.exp (-A m)) :
    ‖centeredCorrelation b c m p 0‖ = Real.exp (-B p - A m) := by
  simp only [centeredCorrelation, add_zero, norm_mul, hp, hm]
  rw [← Real.exp_add]
  congr 1

lemma middle_pos (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {m : ℕ} (hm : 1 ≤ m) (p k : ℕ) (hk : k ≤ m) {lam : ℝ}
    (hbridge : A m - A (m-1) + lam ≤ B (p+1) - B p) :
    ‖centeredCorrelation b c m p k‖ ≤
      Real.exp (-B p - A m) * Real.exp (-lam * k) := by
  have he : -(m : ℤ) + k = -((m-k : ℕ) : ℤ) := by omega
  rw [centeredCorrelation, he, ← Nat.cast_add, norm_mul]
  calc ‖b ((p+k : ℕ) : ℤ)‖ * ‖c (-((m-k : ℕ) : ℤ))‖ ≤
      Real.exp (-B (p+k)) * Real.exp (-A (m-k)) :=
      mul_le_mul (hb.b_pos _) (hb.c_neg _) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ Real.exp (-B p - A m) * Real.exp (-lam * k) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      simpa only [sub_eq_add_neg, neg_mul] using middle_exponent hA hB hm p k hk hbridge

lemma middle_neg (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    {p : ℕ} (hp : 1 ≤ p) (m k : ℕ) (hk : k ≤ p) {lam : ℝ}
    (hbridge : B p - B (p-1) + lam ≤ A (m+1) - A m) :
    ‖centeredCorrelation b c m p (-(k : ℤ))‖ ≤
      Real.exp (-B p - A m) * Real.exp (-lam * k) := by
  have hh := hb.reflected.middle_pos hB hA hp m k hk hbridge
  simpa only [centeredCorrelation, neg_add, neg_neg, mul_comm, neg_add_rev,
    sub_eq_add_neg, add_comm] using hh

lemma tail_pos (hb : EnvelopeBounds A B b c) (m p k : ℕ)
    (hend : B p + A m ≤ B (m+p)) :
    ‖centeredCorrelation b c m p ((m+k+1 : ℕ) : ℤ)‖ ≤
      Real.exp (-B p - A m) * normalizedTailTerm B (m+p) k := by
  have e₁ : (p : ℤ) + ((m+k+1 : ℕ) : ℤ) = ((m+p+k+1 : ℕ) : ℤ) := by omega
  have e₂ : -(m : ℤ) + ((m+k+1 : ℕ) : ℤ) = ((k+1 : ℕ) : ℤ) := by omega
  rw [centeredCorrelation, e₁, e₂, norm_mul]
  calc ‖b ((m+p+k+1 : ℕ) : ℤ)‖ * ‖c ((k+1 : ℕ) : ℤ)‖ ≤
      Real.exp (-B (m+p+k+1)) * Real.exp (B (k+1)) :=
      mul_le_mul (hb.b_pos _) (hb.c_pos _) (norm_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := by
      rw [normalizedTailTerm, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)

lemma tail_neg (hb : EnvelopeBounds A B b c) (m p k : ℕ)
    (hend : B p + A m ≤ A (m+p)) :
    ‖centeredCorrelation b c m p (-((p+k+1 : ℕ) : ℤ))‖ ≤
      Real.exp (-B p - A m) * normalizedTailTerm A (m+p) k := by
  have hh := hb.reflected.tail_pos p m k (by simpa [add_comm] using hend)
  simpa only [centeredCorrelation, neg_add, neg_neg, mul_comm, neg_add_rev,
    sub_eq_add_neg, add_comm, Nat.add_comm] using hh

end EnvelopeBounds



lemma tsum_bound_middle_tail {g t u : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (m : ℕ)
    (hg : ∀ k, 0 ≤ g k) (ht : ∀ k, 0 ≤ t k)
    (hst : Summable t) (hsu : Summable u)
    (hmiddle : ∀ k, k < m → g k ≤ M * t k)
    (htail : ∀ k, g (k+m) ≤ M * u k) :
    Summable g ∧ (∑' k, g k) ≤ M * (∑' k, t k) + M * (∑' k, u k) := by
  have htailSum : Summable (fun k => g (k+m)) := by
    apply (hsu.mul_left M).of_norm_bounded
    intro k
    rw [Real.norm_eq_abs, abs_of_nonneg (hg _)]
    exact htail k
  have hsum : Summable g := (summable_nat_add_iff m).mp htailSum
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add m]
  apply add_le_add
  · calc ∑ k ∈ Finset.range m, g k ≤ ∑ k ∈ Finset.range m, M * t k :=
      Finset.sum_le_sum (fun k hk => hmiddle k (Finset.mem_range.mp hk))
      _ ≤ ∑' k, M * t k := (hst.mul_left M).sum_le_tsum _ (fun k _ => mul_nonneg hM (ht k))
      _ = M * ∑' k, t k := tsum_mul_left
  · calc ∑' k, g (k+m) ≤ ∑' k, M * u k := htailSum.tsum_le_tsum htail (hsu.mul_left M)
      _ = M * ∑' k, u k := tsum_mul_left

lemma central_norm_le_of_correlation_zero (f : ℤ → ℂ)
    (hp : Summable (fun n : ℕ => ‖f (n+1)‖))
    (hn : Summable (fun n : ℕ => ‖f (-(n+1))‖))
    (hz : (∑' n : ℤ, f n) = 0) :
    ‖f 0‖ ≤ (∑' n : ℕ, ‖f (n+1)‖) + ∑' n : ℕ, ‖f (-(n+1))‖ := by
  rw [tsum_of_add_one_of_neg_add_one hp.of_norm hn.of_norm] at hz
  have he : f 0 = -((∑' n : ℕ, f (n+1)) + ∑' n : ℕ, f (-(n+1))) := by
    linear_combination hz
  rw [he, norm_neg]
  exact (norm_add_le _ _).trans (add_le_add (norm_tsum_le_tsum_norm hp) (norm_tsum_le_tsum_norm hn))


def geometricMiddle (lam : ℝ) (k : ℕ) : ℝ := Real.exp (-lam * ((k : ℝ)+1))

lemma geometricMiddle_hasSum {lam : ℝ} (hlam : 0 < lam) :
    HasSum (geometricMiddle lam) (Real.exp (-lam) / (1-Real.exp (-lam))) := by
  have hr : Real.exp (-lam) < 1 := by simpa using hlam
  have hh := (hasSum_geometric_of_lt_one (Real.exp_pos (-lam)).le hr).mul_left (Real.exp (-lam))
  have heq : geometricMiddle lam = (fun k : ℕ => Real.exp (-lam) * Real.exp (-lam)^k) := by
    funext k
    rw [geometricMiddle, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq, div_eq_mul_inv]
  exact hh

lemma geometricMiddle_budget {lam : ℝ} (hlam : Real.log 3 < lam) :
    2 * (∑' k, geometricMiddle lam k) < 1 := by
  have hl0 : 0 < lam := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans hlam
  rw [(geometricMiddle_hasSum hl0).tsum_eq]
  have he : (3 : ℝ) < Real.exp lam := by
    have h := Real.exp_lt_exp.mpr hlam
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)] at h
    exact h
  have hrpos : 0 < Real.exp (-lam) := Real.exp_pos _
  have hrlt : Real.exp (-lam) < 1 := by simpa using hl0
  have hprod : Real.exp lam * Real.exp (-lam) = 1 := by
    rw [← Real.exp_add]; simp
  have hsmall := mul_lt_mul_of_pos_right he hrpos
  rw [hprod] at hsmall
  have hden : 0 < 1 - Real.exp (-lam) := sub_pos.mpr hrlt
  calc 2 * (Real.exp (-lam) / (1-Real.exp (-lam))) =
      (2 * Real.exp (-lam)) / (1-Real.exp (-lam)) := by ring
    _ < 1 := (div_lt_one hden).mpr (by linarith)

namespace EnvelopeBounds

variable {A B : ℕ → ℝ} {b c : ℤ → ℂ}



lemma correlation_budget (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    (hsA : Summable (fun n => Real.exp (-(A (n+1) - A n))))
    (hsB : Summable (fun n => Real.exp (-(B (n+1) - B n))))
    {m p : ℕ} (hm : 1 ≤ m) (hp : 1 ≤ p) {lam : ℝ} (hlam : 0 < lam)
    (hbridge₁ : A m - A (m-1) + lam ≤ B (p+1) - B p)
    (hbridge₂ : B p - B (p-1) + lam ≤ A (m+1) - A m)
    (hcB : ‖b (p : ℤ)‖ = Real.exp (-B p))
    (hcA : ‖c (-(m : ℤ))‖ = Real.exp (-A m))
    (hz : (∑' n : ℤ, centeredCorrelation b c m p n) = 0) :
    1 ≤ 2 * (∑' k, geometricMiddle lam k) +
      (∑' k, normalizedTailTerm A (m+p) k) +
      (∑' k, normalizedTailTerm B (m+p) k) := by
  let M := Real.exp (-B p - A m)
  have hM : 0 < M := Real.exp_pos _
  have hq : 1 ≤ m+p := by omega
  have hendB : B p + A m ≤ B (m+p) := by
    have hh := middle_exponent hA hB hm p m le_rfl hbridge₁
    simp only [Nat.sub_self, hA0, sub_zero] at hh
    rw [Nat.add_comm p m] at hh
    have hmul := mul_nonneg hlam.le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hendA : B p + A m ≤ A (m+p) := by
    have hh := middle_exponent hB hA hp m p le_rfl hbridge₂
    simp only [Nat.sub_self, hB0, sub_zero] at hh
    have hmul := mul_nonneg hlam.le (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
    linarith
  have hpos := tsum_bound_middle_tail hM.le m
    (g := fun k : ℕ => ‖centeredCorrelation b c m p ((k : ℤ)+1)‖)
    (t := geometricMiddle lam) (u := normalizedTailTerm B (m+p))
    (fun _ => norm_nonneg _) (fun _ => (Real.exp_pos _).le)
    (geometricMiddle_hasSum hlam).summable (hB.tail_summable hsB hq) ?_ ?_
  · have hneg := tsum_bound_middle_tail hM.le p
      (g := fun k : ℕ => ‖centeredCorrelation b c m p (-((k : ℤ)+1))‖)
      (t := geometricMiddle lam) (u := normalizedTailTerm A (m+p))
      (fun _ => norm_nonneg _) (fun _ => (Real.exp_pos _).le)
      (geometricMiddle_hasSum hlam).summable (hA.tail_summable hsA hq) ?_ ?_
    · have hh := central_norm_le_of_correlation_zero _ hpos.1 hneg.1 hz
      rw [hb.central_norm hcB hcA] at hh
      change M ≤ _ at hh
      have hmul : M * 1 ≤ M * (2 * (∑' k, geometricMiddle lam k) +
          (∑' k, normalizedTailTerm A (m+p) k) +
          (∑' k, normalizedTailTerm B (m+p) k)) := by
        nlinarith [hpos.2, hneg.2]
      exact (mul_le_mul_iff_right₀ hM).mp hmul
    · intro k hk
      simpa [geometricMiddle, M] using
        hb.middle_neg hA hB hp m (k+1) (by omega) hbridge₂
    · intro k
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, M]
        using hb.tail_neg m p k hendA
  · intro k hk
    simpa [geometricMiddle, M] using
      hb.middle_pos hA hB hm p (k+1) (by omega) hbridge₁
  · intro k
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm, M]
      using hb.tail_pos m p k hendB

end EnvelopeBounds



theorem no_correlation_of_envelopes {A B : ℕ → ℝ} {b c : ℤ → ℂ}
    (hb : EnvelopeBounds A B b c)
    (hA : DiscreteConvex A) (hB : DiscreteConvex B)
    (hA0 : A 0 = 0) (hB0 : B 0 = 0)
    {lam δ : ℝ} (hlam : Real.log 3 < lam) (hδ : lam < δ)
    (hqa : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ A n)
    (hqb : ∀ᶠ n : ℕ in atTop, δ * (n : ℝ)^2 ≤ B n)
    (hcA : ∀ n, 0 < A (n+2) - 2*A (n+1) + A n →
      ‖c (-((n+1 : ℕ) : ℤ))‖ = Real.exp (-A (n+1)))
    (hcB : ∀ n, 0 < B (n+2) - 2*B (n+1) + B n →
      ‖b ((n+1 : ℕ) : ℤ)‖ = Real.exp (-B (n+1)))
    (hz : ∀ r : ℕ, 1 ≤ r → (∑' j : ℤ, b j * c (j-r)) = 0) : False := by
  have hl0 : 0 < lam := (Real.log_pos (by norm_num : (1 : ℝ) < 3)).trans hlam
  have hδ0 : 0 < δ := hl0.trans hδ
  have hsA := hA.summable_exp_neg_slope hA0 hδ0 hqa
  have hsB := hB.summable_exp_neg_slope hB0 hδ0 hqb
  have htA := hA.slopes_tendsto hA0 hδ0 hqa
  have htB := hB.slopes_tendsto hB0 hδ0 hqb
  have ht : Tendsto (fun q => 2 * (∑' k, geometricMiddle lam k) +
      (∑' k, normalizedTailTerm A q k) + (∑' k, normalizedTailTerm B q k))
      atTop (𝓝 (2 * ∑' k, geometricMiddle lam k)) := by
    simpa using (tendsto_const_nhds.add (hA.tail_tsum_tendsto hsA htA)).add
      (hB.tail_tsum_tendsto hsB htB)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht (eventually_lt_nhds (geometricMiddle_budget hlam)))
  obtain ⟨K, hK⟩ := eventually_atTop.1 (htA (eventually_ge_atTop (B 1 - B 0 - lam)))
  obtain ⟨n, hn, hcurv⟩ := large_curvature hδ0 hδ hqa (max N K)
  let m := n+1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hthreshold : B 1 - B 0 ≤ A m - A (m-1) + lam := by
    have hh := hK n (le_trans (le_max_right _ _) hn)
    change B 1 - B 0 - lam ≤ A (n+1) - A n at hh
    dsimp [m]
    simpa only [Nat.add_sub_cancel] using (show B 1 - B 0 ≤ A (n+1) - A n + lam by linarith)
  let C := A m - A (m-1) + lam
  have hex : ∃ p : ℕ, C < B (p+1) - B p := by
    have he : ∀ᶠ p : ℕ in atTop, C < B (p+1) - B p := htB (eventually_gt_atTop C)
    exact he.exists
  let p := Nat.find hex
  have hright : C < B (p+1) - B p := Nat.find_spec hex
  have hp : 1 ≤ p := by
    by_contra! hh
    have hp0 : p = 0 := by omega
    rw [hp0] at hright
    simp only [zero_add] at hright
    exact (not_lt_of_ge hthreshold) hright
  have hleft : B p - B (p-1) ≤ C := by
    have hh := Nat.find_min hex (show p-1 < p by omega)
    simpa only [Nat.sub_add_cancel hp, not_lt] using hh
  have hcontact : 0 < B ((p-1)+2) - 2*B ((p-1)+1) + B (p-1) := by
    have e₁ : p-1+1 = p := by omega
    have e₂ : p-1+2 = p+1 := by omega
    rw [e₁, e₂]
    linarith
  have hcB' : ‖b (p : ℤ)‖ = Real.exp (-B p) := by
    simpa only [Nat.sub_add_cancel hp] using hcB (p-1) hcontact
  have hcA' : ‖c (-(m : ℤ))‖ = Real.exp (-A m) := hcA n (by linarith)
  have hbridge₂ : B p - B (p-1) + lam ≤ A (m+1) - A m := by
    dsimp [C, m] at hleft ⊢
    have e : n+1+1 = n+2 := by omega
    rw [e]
    linarith
  have hzcenter : (∑' i : ℤ, centeredCorrelation b c m p i) = 0 := by
    calc (∑' i : ℤ, centeredCorrelation b c m p i) =
        ∑' i : ℤ, b ((p : ℤ)+i) * c (((p : ℤ)+i) - ((m+p : ℕ) : ℤ)) := by
          apply tsum_congr
          intro i
          unfold centeredCorrelation
          congr 2
          omega
      _ = ∑' j : ℤ, b j * c (j-((m+p : ℕ) : ℤ)) := by
        simpa only [Equiv.coe_addLeft, add_comm] using
          (Equiv.addLeft (p : ℤ)).tsum_eq (fun j : ℤ => b j * c (j-((m+p : ℕ) : ℤ)))
      _ = 0 := hz (m+p) (by omega)
  have hbudget := hb.correlation_budget hA hB hA0 hB0 hsA hsB hm hp hl0 hright.le
    hbridge₂ hcB' hcA' hzcenter
  have hqN : N ≤ m+p := by dsimp [m]; have := le_trans (le_max_left N K) hn; omega
  exact (not_lt_of_ge hbudget) (hN (m+p) hqN)


end
end BackwardIntertwiners

end OAI
