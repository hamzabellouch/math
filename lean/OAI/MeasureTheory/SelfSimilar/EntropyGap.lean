import OAI.MeasureTheory.SelfSimilar.BandSelection

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open MeasureTheory MeasureEntropy
open scoped BigOperators
variable {α : Type uα} {β : Type uβ} [Fintype α] [Nonempty α] [Fintype β] [DecidableEq β]

theorem no_strict_entropy_gap (S : System α) (tag : α → β)
    (hr : ∀ a v, tag a=tag v → S.ratio a=S.ratio v)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : S.SelfSimilar μ)
    {d C A A' : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hA : 0 < A)
    (hA' : S.lyapunov < A') (hAA : A' < A)
    (hb : ∀ s, 0 < s → s < 1 → averaged μ s ≤ d*Real.log (1/s)+C)
    (hgap : d*A*Real.log 2 < S.entropyRate*Real.log 2-Real.log (Fintype.card β)) : False := by
  classical
  obtain ⟨δ,hδ,hdef⟩ := S.uniform_nonsaturation_of_entropy_bound μ hμ hd1 hb
  obtain ⟨M,hM'⟩ := exists_nat_gt (max 4 (10*Real.log 2/δ))
  have hM : 4 < M := by exact_mod_cast (le_max_left _ _).trans_lt hM'
  have hMr : (0 : ℝ)<M := by exact_mod_cast (show 0 < M by omega)
  have he : 5/(M : ℝ)*Real.log 2 ≤ δ/2 := by
    have hh := (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hM')
    apply (le_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
    apply (mul_le_mul_iff_right₀ hMr).mp
    have heq : (5/(M : ℝ)*Real.log 2*2)*(M : ℝ)=10*Real.log 2 := by field_simp; ring
    nlinarith [heq]
  obtain ⟨ε,hε,N,_,hloss⟩ := retained_loss_linear S tag hr μ hμ hd hA hA' hb hgap
  obtain ⟨c,hc,hbands⟩ := pair_bands_of_retained_loss S tag hr A A' hε hloss
  obtain ⟨dmax,_,hdmax⟩ := S.exists_depth_bound
  obtain ⟨D,hD'⟩ := exists_nat_gt (max 1 dmax)
  have hD : 1 ≤ D := by exact_mod_cast ((le_max_left _ _).trans_lt hD').le
  have hdD : ∀ v, S.letterDepth v ≤ (D : ℝ) := fun v => (hdmax v).trans ((le_max_right _ _).trans_lt hD').le
  have hcoef : 0 < δ/2*c := mul_pos (div_pos hδ (by norm_num)) hc
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ))/(δ/2*c))
  obtain ⟨n,B,hn,ha,hbudget,hsep⟩ := select_separated_bands S tag hA hAA hbands q
  obtain ⟨H,hH,hdvd,hBH⟩ := exists_common_horizon n hn B
  let K : Fin q → ℕ := fun i => H/n i
  have hkn (i : Fin q) : K i*n i=H := Nat.div_mul_cancel (hdvd i)
  obtain ⟨R,hR,hcompact⟩ := S.selfSimilar_compact μ hμ
  have hcomp : CompactlyCarried μ := ⟨R,hR.le,hcompact⟩
  have hcount := count_pair_budget_le S tag hr μ hμ hcomp hdef hM he hD hdD n K
    (fun i => bandStart A (n i)) B A' hkn ha hBH hsep
  have hsum : (q : ℝ)*(c*H) ≤ ∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i) := by
    calc
      _ = ∑ _i : Fin q, c*(H : ℝ) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        have hi := mul_le_mul_of_nonneg_left (hbudget i) (Nat.cast_nonneg (K i))
        have hnH : (K i : ℝ)*(n i : ℝ)=(H : ℝ) := by exact_mod_cast hkn i
        nlinarith
  have hlim : (δ/2*c)*(q : ℝ) ≤ 2*(D : ℝ)*Real.log ((M*M : ℕ) : ℝ) := by
    apply (mul_le_mul_iff_right₀ (by exact_mod_cast hH : (0 : ℝ)<H)).mp
    calc
      _ = δ/2*((q : ℝ)*(c*H)) := by ring
      _ ≤ δ/2*(∑ i, (K i : ℝ)*pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ _ := by simpa only [Nat.cast_mul,Nat.cast_ofNat,mul_assoc,mul_comm,mul_left_comm] using hcount
  have hq' := (div_lt_iff₀ hcoef).mp hq
  nlinarith

end EntropyRateDimension.Typed

end OAI
