import OAI.NumberTheory.TotientAsymptotic.LocalSuffixComparisonData
import OAI.NumberTheory.TotientAsymptotic.GeometricLowerBudget

namespace OAI

/-! At each actual residual index the geometric head-prime minimum exceeds
its fourth-power normality cutoff. -/
noncomputable section
open scoped BigOperators Topology
open Filter
namespace TotientAsymptotic

theorem local_geometric_prime_above_normality {c : ℝ} (hc : 0<c) :
    ∀ᶠ h : ℕ in atTop,∀ p : ℕ,p.Prime →
      c*(rho^h)⁻¹≤B p → localNormalityScale h<(p:ℝ) := by
  filter_upwards [geometric_dominates_polynomial hc 2 4,eventually_ge_atTop 1]
    with h hh hh1
  intro p hp hgeo
  have hhpos : (0:ℝ)<h := by exact_mod_cast hh1
  have hs : (h:ℝ)^4<c*(rho^h)⁻¹ := by
    have hbound := hh h le_rfl
    have hp4 : 0<(h:ℝ)^4 := pow_pos hhpos _
    linarith only [hbound,hp4]
  have hlt : (h:ℝ)^4<B p := hs.trans_le hgeo
  have he := Real.exp_lt_exp.mpr (Real.exp_lt_exp.mpr hlt)
  have hp1 : (1:ℝ)<p := by exact_mod_cast hp.one_lt
  simpa only [localNormalityScale,B,Real.exp_log (Real.log_pos hp1),
    Real.exp_log (zero_lt_one.trans hp1)] using he

theorem local_bad_suffix_head_roughness {c : ℝ} (hc : 0<c) (d L : ℕ) :
    ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      ∀ (i : Fin (m x-H)) (r : ℕ),r∈localBadSuffixValues x c d L H i →
        ∃ p : ℕ,p.Prime ∧ p∣r ∧ localNormalityScale (m x-i.val)<(p:ℝ) := by
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (local_geometric_prime_above_normality (half_pos hc))
  filter_upwards [local_bad_suffix_geometric_data hc d L,eventually_ge_atTop H₀]
    with H hdata hH
  filter_upwards [hdata] with x hdata
  intro i r hr
  obtain ⟨q,he,hgeom,_ho,hq,_hnormal,_hembed⟩ := hdata i r hr
  have hj : 0 < m x-H-i.val := by have := i.isLt; omega
  let j : Fin (m x-H-i.val) := ⟨0,hj⟩
  have heq : primeFinal q i.val j=q i := by
    unfold primeFinal
    congr 1
  refine ⟨q i,hq i,?_,?_⟩
  · rw [he,←heq]
    exact Finset.dvd_prod_of_mem (primeFinal q i.val) (Finset.mem_univ j)
  · have hh : H₀ ≤ m x-i.val := by have := i.isLt; omega
    exact hH₀ _ hh _ (hq i) (hgeom.2.1 i)


theorem local_geometric_primes_three {c : ℝ} (hc : 0<c) :
    ∀ᶠ H : ℕ in atTop,∀ m n : ℕ,n+H=m →
      ∀ budget : ℝ,∀ p : Fin n → ℕ,(∀ i,(p i).Prime) →
      primePrefixCoord p ∈ relaxedGeometricFamily m n budget c → ∀ i,3 ≤ p i := by
  obtain ⟨H₀,hH₀⟩ := eventually_atTop.mp (local_geometric_prime_above_normality hc)
  filter_upwards [eventually_ge_atTop H₀] with H hH
  intro m n hmn budget p hp hgeom i
  have hhi : H₀ ≤ m-i.val := by have := i.isLt; omega
  have hbig := hH₀ _ hhi _ (hp i) (hgeom.2.1 i)
  have htwo : (2:ℝ)<p i := (localNormalityScale_gt_two _).trans hbig
  have htwoN : 2<p i := by exact_mod_cast htwo
  omega

lemma ordered_prime_product_largest {N : ℕ} (hN : 0<N) (p : Fin N → ℕ)
    (hp : ∀ i,(p i).Prime) (ho : StrictAnti p) :
    largestPrimeFactor (∏ i,p i)=p ⟨0,hN⟩ := by
  apply le_antisymm
  · apply largestPrimeFactor_prod_le _ _ (hp ⟨0,hN⟩).one_lt.le
    intro i _
    rw [largestPrimeFactor_prime (hp i)]
    exact ho.antitone (show (⟨0,hN⟩ : Fin N) ≤ i from Nat.zero_le _)
  · apply prime_dvd_le_largest (hp ⟨0,hN⟩)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))
    exact Finset.dvd_prod_of_mem p (Finset.mem_univ _)

end TotientAsymptotic

end

end OAI
