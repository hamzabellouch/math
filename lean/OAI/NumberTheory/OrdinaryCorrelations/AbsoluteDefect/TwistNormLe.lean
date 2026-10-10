import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryCorrelations
namespace PretentiousStability

lemma twist_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) :
    ‖χ (p : ZMod q) * Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I)‖ ≤ 1 := by
  have he : ‖Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,mul_zero,
      Complex.ofReal_im,Complex.I_im,zero_mul,sub_self,Real.exp_zero]
  simpa only [norm_mul,he,mul_one] using χ.norm_le_one (p : ZMod q)

lemma summand_nonneg (f : ℕ → ℂ) (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) :
    0 ≤ (1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re) / (p : ℝ) := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply sub_nonneg.mpr
  exact (Complex.re_le_norm _).trans (by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf p)).trans (twist_norm_le χ t p))

lemma distanceSq_nonneg (f : ℕ → ℂ) (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    0 ≤ distanceSq f χ t X :=
  Finset.sum_nonneg fun p _ => summand_nonneg f hf χ t p

lemma sq_distance (f : ℕ → ℂ) (hf : OneBounded f)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    distance f χ t X ^ 2 = distanceSq f χ t X := Real.sq_sqrt (distanceSq_nonneg f hf χ t X)

lemma summand_difference (f b : ℕ → ℂ) (hf : OneBounded f) (hb : OneBounded b)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) (p : ℕ) :
    |((1 - (b p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I))).re) / (p:ℝ)) -
     ((1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I))).re) / (p:ℝ))| ≤ 2 / p := by
  let z := star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I))
  have hz : ‖z‖ ≤ 1 := by simpa [z] using twist_norm_le χ t p
  have hdiff : ‖f p - b p‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith [hf p,hb p])
  have hr : |((f p - b p) * z).re| ≤ 2 := by
    apply (Complex.abs_re_le_norm _).trans
    rw [norm_mul]
    calc
      _ ≤ 2 * 1 := mul_le_mul hdiff hz (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  calc
    _ = |((f p - b p) * z).re| / (p:ℝ) := by
      rw [← sub_div,abs_div,show |(p:ℝ)| = (p:ℝ) from abs_of_nonneg (Nat.cast_nonneg p)]
      congr 1
      simp only [sub_mul,Complex.sub_re,z]
      congr 1; ring
    _ ≤ _ := div_le_div_of_nonneg_right hr (Nat.cast_nonneg p)

theorem distanceSq_change (f b : ℕ → ℂ) (hf : OneBounded f) (hb : OneBounded b)
    (P : Finset ℕ) (hag : ∀ p, p.Prime → p ∉ P → f p = b p)
    {q : ℕ} (χ : DirichletCharacter ℂ q) (t X : ℝ) :
    |distanceSq b χ t X - distanceSq f χ t X| ≤ ∑ p ∈ P, 2 / (p:ℝ) := by
  classical
  let S := (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime
  let F (v : ℕ → ℂ) (p : ℕ) :=
    (1 - (v p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p:ℝ) : ℝ) * Complex.I))).re) / (p:ℝ)
  change |∑ p ∈ S, F b p - ∑ p ∈ S, F f p| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ S, |F b p - F f p| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ S ∩ P, |F b p - F f p| := by
      symm
      apply Finset.sum_subset (Finset.inter_subset_left)
      intro p hp hn
      have hpP : p ∉ P := by simpa only [Finset.mem_inter,hp,true_and] using hn
      simp only [F,hag p (Finset.mem_filter.mp hp).2 hpP,sub_self,abs_zero]
    _ ≤ ∑ p ∈ S ∩ P, 2 / (p:ℝ) := Finset.sum_le_sum fun p _ =>
      summand_difference f b hf hb χ t p
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun p _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg p))

theorem uniformlyNonpretentious_change (f b : ℕ → ℂ)
    (hf : OneBounded f) (hb : OneBounded b) (P : Finset ℕ)
    (hag : ∀ p, p.Prime → p ∉ P → f p = b p) (hnp : UniformlyNonpretentious f) :
    UniformlyNonpretentious b := by
  intro q hq χ
  let C : ℝ := ∑ p ∈ P, 2 / (p:ℝ)
  apply tendsto_atTop.mpr
  intro M
  have hev := tendsto_atTop.mp (hnp q hq χ) (Real.sqrt ((max M 0)^2+C))
  filter_upwards [hev] with N hN
  apply le_csInf
  · refine Set.Nonempty.image _ ?_
    exact ⟨0,neg_nonpos.mpr (Nat.cast_nonneg N),Nat.cast_nonneg N⟩
  · rintro v ⟨t,ht,rfl⟩
    have hlower : Real.sqrt ((max M 0)^2+C) ≤ distance f χ t N := by
      apply hN.trans
      apply csInf_le
      · exact ⟨0,by rintro v ⟨t,_,rfl⟩; exact Real.sqrt_nonneg _⟩
      · exact ⟨t,ht,rfl⟩
    have hsq := (Real.sqrt_le_iff.mp hlower).2
    rw [sq_distance f hf] at hsq
    have hdiff := (abs_le.mp (distanceSq_change f b hf hb P hag χ t N)).1
    have hbsq := sq_distance b hb χ t N
    have hbnon : 0 ≤ distance b χ t N := Real.sqrt_nonneg _
    have hmax : max M 0 ≤ distance b χ t N :=
      (sq_le_sq₀ (le_max_right M 0) hbnon).mp (by dsimp only [C] at hsq; nlinarith)
    exact (le_max_left _ _).trans hmax

end PretentiousStability
end OrdinaryCorrelations

end

end OAI
