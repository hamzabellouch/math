import OAI.NumberTheory.TotientAsymptotic.LocalOriginalDecay
import OAI.NumberTheory.TotientAsymptotic.LocalSuffixPruning
import OAI.NumberTheory.TotientAsymptotic.LocalCandidateArithmetic

namespace OAI

/-! Finite pruning of the actual candidate family on its original normalization.
The regular comparison estimates are kept explicit here for application to
Ford's finite labeled counts. -/
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

def localFullCandidates (x c : ℝ) (d L H : ℕ) : Finset ℕ :=
  (localNormalCandidates x c d L H).filter (FullFiber d)

def LocalOriginalRegularBound (x c : ℝ) (d L H : ℕ) : Prop :=
  ∀ F : ℕ → ℕ,let R := localOriginalBad x c d L H
    Set.InjOn F (R : Set ℕ) →
    (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
      largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
    ((localWitnessRegular R F (m x)).card:ℝ) ≤ x/Real.log x*(B x)^(-4:ℝ)

def LocalSuffixRegularBound (x c : ℝ) (d L H : ℕ) : Prop :=
  ∀ (i : Fin (m x-H)) (F : ℕ → ℕ),
    let R := localBadSuffixValues x c d L H i
    Set.InjOn F (R : Set ℕ) →
    (∀ r ∈ R,0<F r ∧ (F r).totient=d*r.totient ∧ ¬r ∣ F r ∧
      largestPrimeFactor (F r) ≠ largestPrimeFactor r) →
    (∑ r ∈ localWitnessRegular R F (m x-i.val),(r.totient:ℝ)⁻¹) ≤ rho^(m x-i.val)

lemma local_candidate_card_partition (x c : ℝ) (d L H : ℕ) :
    (localNormalCandidates x c d L H).card =
      (localFullCandidates x c d L H).card+(localBadCandidates x c d L H).card := by
  exact (Finset.card_filter_add_card_filter_not
    (s:=localNormalCandidates x c d L H) (FullFiber d)).symm

theorem local_full_candidate_count {c δ : ℝ} (hc : 0<c) (hδ : 0<δ)
    (d q : ℕ) (hd : 0<d) (hqpos : 0<q) (hq : q.totient=d) (L : ℕ)
    (habundance : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(8*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localNormalCandidates x c d L H).card:ℝ))
    (horiginal : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      LocalOriginalRegularBound x c d L H)
    (hsuffix : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      LocalSuffixRegularBound x c d L H) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(16*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localFullCandidates x c d L H).card:ℝ) := by
  obtain ⟨C,hC,hscount⟩ := local_suffix_count_of_regular_mass hc d q hd hqpos hq L
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have ht : ∀ᶠ H : ℕ in atTop,C*polynomialGeometricTail 0 rho H ≤ δ/32 := by
    have hlim : Tendsto (fun H => C*polynomialGeometricTail 0 rho H) atTop (nhds 0) := by
      simpa only [mul_zero] using (polynomialGeometricTail_tendsto 0 rho).const_mul C
    simpa only [mul_zero] using hlim.eventually
      (eventually_le_nhds (by positivity : (0:ℝ)<δ/32))
  filter_upwards [habundance,horiginal,hsuffix,hscount,ht,
    local_original_count_of_regular hc d q hd hqpos hq L,
    local_bad_candidate_count_cover hc d hd L] with H ha ho hs hsc ht hoc hcover
  filter_upwards [ha,ho,hs,hsc,hoc,hcover,
    ambient_residual_error_negligible H (show 0<δ/(32*d) by positivity),
    eventually_gt_atTop (1:ℝ),B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x ha ho hs hsc hoc hcover he hx hB
  have hscale : 0 ≤ x/Real.log x*G x (m x-H) := by
    exact mul_nonneg (div_nonneg (zero_lt_one.trans hx).le (Real.log_pos hx).le)
      (G_pos hB _).le
  have hsmall : (x/(d*Real.log x))*(C*G x (m x-H))*
      polynomialGeometricTail 0 rho H ≤
      (δ/(32*d))*(x/Real.log x*G x (m x-H)) := by
    have hh := mul_le_mul_of_nonneg_right ht (div_nonneg hscale hdR.le)
    convert hh using 1 <;> ring
  have hb : ((localBadCandidates x c d L H).card:ℝ) ≤
      (δ/(16*d))*(x/Real.log x*G x (m x-H)) := by
    have ho' := (hoc ho).trans he
    have hs' := (hsc hs).trans hsmall
    calc
      _ ≤ (localOriginalBad x c d L H).card+
          ∑ i : Fin (m x-H),((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ) := hcover
      _ ≤ (δ/(32*d))*(x/Real.log x*G x (m x-H))+
          (δ/(32*d))*(x/Real.log x*G x (m x-H)) := add_le_add ho' hs'
      _ = _ := by ring
  have hpart : ((localNormalCandidates x c d L H).card:ℝ) =
      (localFullCandidates x c d L H).card+(localBadCandidates x c d L H).card := by
    exact_mod_cast local_candidate_card_partition x c d L H
  have heq : δ/(8*(d:ℝ))=δ/(16*d)+δ/(16*d) := by ring
  rw [heq,add_mul] at ha
  linarith only [ha,hpart,hb]

end TotientAsymptotic

end

end OAI
