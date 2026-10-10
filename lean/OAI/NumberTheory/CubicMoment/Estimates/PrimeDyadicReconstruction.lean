import OAI.NumberTheory.CubicMoment.Estimates.DyadicLittleO

namespace OAI

/-! The actual prime sums satisfy the small-argument and local-growth
conditions of dyadic reconstruction; closed interval endpoints cost O(1). -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primeDyadicSum (c : Eisenstein → ℂ) (X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), c p*(intervalStep X (2*X) (norm p):ℝ)

lemma primeCutoffSum_on (c : Eisenstein → ℂ) {X Y : ℝ} (hXY : X ≤ Y) :
    primeCutoffSum c X = ∑ p ∈ primeCutoff Y, if norm p ≤ X then c p else 0 := by
  have hs : primeCutoff X = (primeCutoff Y).filter (fun p => norm p ≤ X) := by
    ext p
    simp only [mem_primeCutoff,Finset.mem_filter]
    constructor
    · intro hp
      exact ⟨⟨hp.1,hp.2.trans hXY⟩,hp.2⟩
    · intro hp
      exact ⟨hp.1.1,hp.2⟩
  rw [primeCutoffSum_eq_sum,hs,Finset.sum_filter]

lemma primeCutoffSum_zero_small (c : Eisenstein → ℂ) {X : ℝ} (hX : X < 1) :
    primeCutoffSum c X = 0 := by
  rw [primeCutoffSum_eq_sum]
  apply Finset.sum_eq_zero
  intro p hp
  have hh := mem_primeCutoff.mp hp
  have hl := one_le_norm hh.1.2.ne_zero
  linarith

lemma primeCutoffSum_norm_le (c : Eisenstein → ℂ) {M X : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M) (hX : 0 ≤ X) :
    ‖primeCutoffSum c X‖ ≤ 18*M*X := by
  have hsub : primeCutoff X ⊆ nonzeroNormBall X := by
    intro p hp
    have hh := mem_primeCutoff.mp hp
    exact mem_nonzeroNormBall.mpr ⟨hh.2,hh.1.2.ne_zero⟩
  have hcard := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (nonzeroNormBall_card_le hX)
  rw [primeCutoffSum_eq_sum]
  calc
    _ ≤ ∑ _p ∈ primeCutoff X, M := (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun p hp => hc p (mem_primeCutoff.mp hp).1))
    _ = ((primeCutoff X).card:ℝ)*M := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (18*X)*M := mul_le_mul_of_nonneg_right hcard hM
    _ = _ := by ring

lemma prime_norm_boundary_sum_le (S : Finset Eisenstein)
    (hS : ∀ p ∈ S, primaryPrime p) (c : Eisenstein → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p ∈ S, ‖c p‖ ≤ M) (Y : ℝ) :
    ‖∑ p ∈ S with norm p = Y, c p‖ ≤ 2*M := by
  have hs : S.filter (fun p => norm p = Y) ⊆
      S.filter (fun p => (normNat p:ℤ) = ⌊Y⌋) := by
    intro p hp
    refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,?_⟩
    have he : ((normNat p:ℤ):ℝ) = Y := by
      simpa only [Int.cast_natCast,normNat_cast] using (Finset.mem_filter.mp hp).2
    simpa only [Int.floor_intCast] using (congrArg Int.floor he)
  have hcard := (Finset.card_le_card hs).trans (prime_norm_fiber_card_le_two S hS ⌊Y⌋)
  calc
    _ ≤ ∑ p ∈ S with norm p = Y, M := (norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun p hp => hc p (Finset.mem_filter.mp hp).1))
    _ = ((S.filter (fun p => norm p = Y)).card:ℝ)*M := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 2*M := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hM

lemma prime_dyadic_endpoint_identity (c : Eisenstein → ℂ) {X : ℝ} (hX : 0 ≤ X) :
    dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2) =
      -(∑ p ∈ primeCutoff (2*X) with norm p = X/2, c p) := by
  rw [dyadicDifference,primeCutoffSum_on c (show X ≤ 2*X by linarith),
    primeCutoffSum_on c (show X/2 ≤ 2*X by linarith)]
  unfold primeDyadicSum
  rw [show 4*(X/2)=2*X by ring,show 2*(X/2)=X by ring,
    ←Finset.sum_sub_distrib,←Finset.sum_sub_distrib,Finset.sum_filter,←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro p _
  unfold intervalStep
  simp only [Set.mem_Icc]
  by_cases he : norm p = X/2
  · have hle : norm p ≤ X := by linarith
    have hhalf : X/2 ≤ X := by linarith
    simp only [he,hhalf,le_refl,true_and,ite_true,Complex.ofReal_one,mul_one]
    ring
  · by_cases hlo : norm p ≤ X/2
    · have hn : ¬X/2 ≤ norm p := by intro hh; exact he (le_antisymm hlo hh)
      have hle : norm p ≤ X := by linarith
      simp only [he,hle,hlo,hn,false_and,ite_true,ite_false,Complex.ofReal_zero,mul_zero,sub_self,neg_zero]
    · have hl : X/2 ≤ norm p := (lt_of_not_ge hlo).le
      by_cases hhi : norm p ≤ X
      all_goals simp only [he,hlo,hl,hhi,true_and,ite_true,ite_false,
        Complex.ofReal_one,Complex.ofReal_zero,mul_one,mul_zero,sub_zero,sub_self,neg_zero]

lemma prime_dyadic_endpoint_bound (c : Eisenstein → ℂ) {M X : ℝ} (hM : 0 ≤ M)
    (hc : ∀ p : Eisenstein, primaryPrime p → ‖c p‖ ≤ M) (hX : 0 ≤ X) :
    ‖dyadicDifference (primeCutoffSum c) X-primeDyadicSum c (X/2)‖ ≤ 2*M := by
  rw [prime_dyadic_endpoint_identity c hX,norm_neg]
  exact prime_norm_boundary_sum_le _ (fun p hp => (mem_primeCutoff.mp hp).1) c hM
    (fun p hp => hc p (mem_primeCutoff.mp hp).1) _

end CubicFirstMoment

end

end OAI
