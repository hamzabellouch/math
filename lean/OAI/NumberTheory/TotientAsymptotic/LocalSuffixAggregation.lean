import OAI.NumberTheory.TotientAsymptotic.LocalSuffixFamily
import OAI.NumberTheory.TotientAsymptotic.GeometricCandidateCount
import OAI.NumberTheory.TotientAsymptotic.NormalInternalDiscard

namespace OAI

/-! Convert a reciprocal bound for each actual bad suffix family to the
count of original candidates, summing over all possible removed prefixes. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_suffix_count_aggregation_mul {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ i : Fin (m x-H),
        (∑ r ∈ localBadSuffixValues x c d L H i,(r.totient:ℝ)⁻¹) ≤ K*rho^(m x-i.val)) →
      (∑ i : Fin (m x-H),((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ)) ≤
        (x/(d*Real.log x))*(C*G x (m x-H))*polynomialGeometricTail 0 rho H := by
  classical
  obtain ⟨C,hC,hcount⟩ := local_suffix_candidate_count hc d hd
  refine ⟨C*K,mul_pos hC hK,?_⟩
  filter_upwards [hcount L,head_limited_prime_coordinates hc] with H hH hcoords
  filter_upwards [hH,hcoords,m_tendsto.eventually (eventually_ge_atTop H),
    B_tendsto.eventually (eventually_gt_atTop (0:ℝ)),eventually_gt_atTop (1:ℝ)]
    with x hx hcoords hm hB hx1
  intro hmass
  let N := m x-H
  let Z := x/(d*Real.log x)*(C*G x N)
  have hZ : 0 ≤ Z := by
    have hdR : (0:ℝ)<d := by exact_mod_cast hd
    have hl := Real.log_pos hx1
    have hg := G_pos hB N
    dsimp [Z]
    positivity
  have hi (i : Fin N) :
      ((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ) ≤ Z*(K*rho^(m x-i.val)) := by
    let Q := localBadSuffixTuples x c d L H i
    let T := Q.image (fun p => primeFinal p i.val)
    have hQ (p) (hp : p∈Q) : p ∈ localRegularPrimeTuples x c L H :=
      (Finset.mem_filter.mp hp).1
    have hdata (p) (hp : p∈Q) := hcoords N (Nat.sub_add_cancel hm) p
      (local_regular_tuples_subset (hQ p hp))
    have hT : ∀ p ∈ T,(∀ j,(p j).Prime) ∧ StrictAnti p := by
      intro p hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hprime := (hdata q hq).1
      have hanti := prime_coordinates_strictAnti hprime (hdata q hq).2.1.1.2.1
      refine ⟨fun j => hprime _,?_⟩
      intro j k hjk
      apply hanti
      change i.val+j.val < i.val+k.val
      exact Nat.add_lt_add_left hjk i.val
    have hh := hx i.val (Nat.le_of_lt i.isLt) Q T
      (fun p hp => (Finset.mem_sdiff.mp (hQ p hp)).1) hT
      (fun p hp => Finset.mem_image.mpr ⟨p,hp,rfl⟩)
    have he : T.image (fun p => ∏ j,p j)=localBadSuffixValues x c d L H i := by
      simp only [T,Q,Finset.image_image,Function.comp_def,localBadSuffixValues]
    rw [he] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hmass i) hZ)
  have hsum : (∑ i : Fin N,rho^(m x-i.val)) ≤ polynomialGeometricTail 0 rho H := by
    change (∑ i : Fin N,(fun j : ℕ => rho^(m x-j)) i.val) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun j => rho^(m x-j)) N]
    apply le_trans _ (reverse_geometric_sum hm)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,by have := Finset.mem_range.mp hi; dsimp [N] at this; omega⟩
    · intro i _ _
      exact (pow_pos rho_pos _).le
  calc
    _ ≤ ∑ i : Fin N,Z*(K*rho^(m x-i.val)) := Finset.sum_le_sum (fun i _ => hi i)
    _ = (Z*K)*(∑ i : Fin N,rho^(m x-i.val)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (Z*K)*polynomialGeometricTail 0 rho H :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hZ hK.le)
    _ = _ := by dsimp [Z,N]; ring

theorem local_suffix_count_aggregation {c : ℝ} (hc : 0 < c)
    (d : ℕ) (hd : 0 < d) (L : ℕ) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (∀ i : Fin (m x-H),
        (∑ r ∈ localBadSuffixValues x c d L H i,(r.totient:ℝ)⁻¹) ≤ rho^(m x-i.val)) →
      (∑ i : Fin (m x-H),((tailHeadPairs x d (localBadSuffixTuples x c d L H i)).card:ℝ)) ≤
        (x/(d*Real.log x))*(C*G x (m x-H))*polynomialGeometricTail 0 rho H := by
  simpa only [one_mul] using local_suffix_count_aggregation_mul hc d hd L 1 (by norm_num)

end TotientAsymptotic

end

end OAI
