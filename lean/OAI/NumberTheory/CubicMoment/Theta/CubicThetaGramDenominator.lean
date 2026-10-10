import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGramRowReindex

namespace OAI

/-! Grouping the actual rows by denominator and removing the impossible
ones using the positive height cutoffs. -/
noncomputable section
open Set
open scoped CompactlySupported
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def cubicThetaGramDenominatorBlock (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    (c : Eisenstein) (p : ℂ × ℝ) : ℂ :=
  if hc : (3:Eisenstein)∣c ∧ c≠0 then
    cubicThetaKloostermanRow h k c hc.1 V p.2 p.1 else 0

lemma cubicThetaGramRowLift_tsum (h k c : Eisenstein) (V : C_c(ℝ,ℂ)) (p : ℂ × ℝ) :
    (∑' d : Eisenstein,cubicThetaGramRowLift h k V p (c,d))=
      cubicThetaGramDenominatorBlock h k V c p := by
  by_cases hc : (3:Eisenstein)∣c ∧ c≠0
  · simp only [cubicThetaGramRowLift,cubicThetaGramDenominatorBlock,dite_eq_left hc,
      cubicThetaKloostermanRow]
  · simp only [cubicThetaGramRowLift,cubicThetaGramDenominatorBlock,dite_eq_right hc,tsum_zero]

theorem cubicThetaGramRows_denominator (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {δ : ℝ} (hδ : 0<δ) (hV : ∀ t≤δ,V t=0) {p : ℂ × ℝ} (hp : 0<p.2) :
    star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileSeries k p V=
      star (cubicThetaHorizontalCharacter h p.1)*
        cubicThetaFourierProfileTerm k cubicThetaZeroRow p V+
      ∑' c : Eisenstein,cubicThetaGramDenominatorBlock h k V c p := by
  rw [cubicThetaGramRows_reindex h k V hδ hV hp,
    (cubicThetaGramRowLift_hasSum h k V hδ hV hp).summable.tsum_prod]
  simp_rw [cubicThetaGramRowLift_tsum]

lemma cubicThetaGramKernel_height_zero (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {c : ℂ} (hc : c≠0) {δ v : ℝ} (hδ : 0<δ) (hv : 0<v)
    (hV : ∀ t≤δ,V t=0) (hlarge : 1≤Complex.normSq c*δ*v) (z : ℂ) :
    cubicThetaGramInversionKernel h k V c z v=0 := by
  have hn : 0<Complex.normSq c := Complex.normSq_pos.mpr hc
  have hd : 0<Complex.normSq c*cubicThetaRadius (z,v) :=
    mul_pos hn (cubicThetaRadius_pos hv)
  have hh : (cubicThetaInversion c (z,v)).2≤δ := by
    change v/(Complex.normSq c*cubicThetaRadius (z,v))≤δ
    apply (div_le_iff₀ hd).mpr
    have ha := mul_le_mul_of_nonneg_right hlarge hv.le
    unfold cubicThetaRadius
    dsimp only
    nlinarith [mul_nonneg (mul_nonneg hn.le hδ.le) (Complex.normSq_nonneg z)]
  simp only [cubicThetaGramInversionKernel,hV _ hh,mul_zero,zero_mul]

lemma cubicThetaGramDenominatorBlock_large_zero (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0)
    (c : Eisenstein) {p : ℂ × ℝ} (hp : ε≤p.2) (hlarge : 1≤norm c*ε*δ) :
    cubicThetaGramDenominatorBlock h k V c p=0 := by
  unfold cubicThetaGramDenominatorBlock
  split_ifs with hc
  · have hcC : (c:ℂ)≠0 := fun hz => hc.2 (Subtype.ext hz)
    have hl : 1≤Complex.normSq (c:ℂ)*δ*p.2 := by
      change 1≤norm c*δ*p.2
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg (norm_nonneg c) hδ.le)
      nlinarith
    unfold cubicThetaKloostermanRow
    simp only [cubicThetaGramKernel_height_zero h k V hcC hδ (hε.trans_le hp) hV hl,mul_zero,tsum_zero]
  · rfl

def cubicThetaGramDenominators (ε δ : ℝ) : Finset Eisenstein :=
  (finite_norm_le (1/(ε*δ))).toFinset.filter (fun c => (3:Eisenstein)∣c ∧ c≠0)

lemma cubicThetaGramDenominators_mem {ε δ : ℝ} {c : Eisenstein}
    (hc : c∈cubicThetaGramDenominators ε δ) : (3:Eisenstein)∣c ∧ c≠0 :=
  (Finset.mem_filter.mp hc).2

theorem cubicThetaGramRows_finite_denominators (h k : Eisenstein) (V : C_c(ℝ,ℂ))
    {ε δ : ℝ} (hε : 0<ε) (hδ : 0<δ) (hV : ∀ t≤δ,V t=0)
    {p : ℂ × ℝ} (hp : ε≤p.2) :
    star (cubicThetaHorizontalCharacter h p.1)*cubicThetaFourierProfileSeries k p V=
      star (cubicThetaHorizontalCharacter h p.1)*
        cubicThetaFourierProfileTerm k cubicThetaZeroRow p V+
      ∑ c∈cubicThetaGramDenominators ε δ,cubicThetaGramDenominatorBlock h k V c p := by
  rw [cubicThetaGramRows_denominator h k V hδ hV (hε.trans_le hp)]
  congr 1
  apply tsum_eq_sum
  intro c hc
  by_cases hcc : (3:Eisenstein)∣c ∧ c≠0
  · have hn : 1/(ε*δ)<norm c := by
      apply lt_of_not_ge
      intro hn
      exact hc (Finset.mem_filter.mpr ⟨(finite_norm_le _).mem_toFinset.mpr hn,hcc⟩)
    have hl : 1≤norm c*ε*δ := by
      have hh := (div_lt_iff₀ (mul_pos hε hδ)).mp hn
      nlinarith
    exact cubicThetaGramDenominatorBlock_large_zero h k V hε hδ hV c hp hl
  · simp only [cubicThetaGramDenominatorBlock,dite_eq_right hcc]

end CubicFirstMoment

end

end OAI
