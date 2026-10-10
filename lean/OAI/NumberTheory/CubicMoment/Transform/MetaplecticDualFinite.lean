import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShiftedVoronoi

namespace OAI

/-! The retained Voronoi sum is an actual finite frequency polynomial.
Its cutoff is independent of the height parameter. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma metaplectic_frequency_norm_numerator (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n) = norm n.val/3 := by
  have hLambda : Complex.normSq traceLambda = 3 := by
    rw [traceLambda_eq,Complex.normSq_mul,Complex.normSq_ofReal]
    norm_num [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  rw [metaplecticFrequency,Complex.normSq_div,hLambda]
  rfl

lemma metaplecticDualNorm_coordinate_bound (nd : MetaplecticDualArgument × PrimaryArgument)
    {J : ℝ} (hcut : metaplecticDualNorm nd ≤ J) :
    norm nd.1.val ≤ 3*J ∧ norm nd.2.val ≤ 3*J := by
  have hN : 1 ≤ norm nd.1.val := one_le_norm nd.1.property
  have hD : 1 ≤ norm nd.2.val := one_le_norm (primary_ne_zero nd.2.property)
  have hD0 : 0 ≤ norm nd.2.val := norm_nonneg _
  have hN0 : 0 ≤ norm nd.1.val := norm_nonneg _
  have hraw : norm nd.2.val^3*norm nd.1.val ≤ 3*J := by
    unfold metaplecticDualNorm at hcut
    rw [metaplectic_frequency_norm_numerator] at hcut
    nlinarith
  have hD3 : 1 ≤ norm nd.2.val^3 := one_le_pow₀ hD
  have hn : norm nd.1.val ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD3 hN0
  have hd3 : norm nd.2.val^3 ≤ norm nd.2.val^3*norm nd.1.val := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hN (pow_nonneg hD0 3)
  have hd : norm nd.2.val ≤ norm nd.2.val^3 := by
    have hsq : 1 ≤ norm nd.2.val^2 := one_le_pow₀ hD
    have hh := mul_le_mul_of_nonneg_left hsq hD0
    nlinarith
  exact ⟨hn.trans hraw,(hd.trans hd3).trans hraw⟩

def metaplecticDualBall (J : ℝ) : Finset (MetaplecticDualArgument × PrimaryArgument) :=
  (((nonzeroNormBall (3*J)).subtype (fun n => n ≠ 0)).product
    ((primaryElementBall (3*J)).subtype primary)).filter (fun nd => metaplecticDualNorm nd ≤ J)

lemma mem_metaplecticDualBall (nd : MetaplecticDualArgument × PrimaryArgument) (J : ℝ) :
    nd ∈ metaplecticDualBall J ↔ metaplecticDualNorm nd ≤ J := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    obtain ⟨hn,hd⟩ := metaplecticDualNorm_coordinate_bound nd h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_,?_⟩,h⟩
    · exact Finset.mem_subtype.mpr (mem_nonzeroNormBall.mpr ⟨hn,nd.1.property⟩)
    · exact Finset.mem_subtype.mpr (mem_primaryElementBall.mpr ⟨nd.2.property,hd⟩)

def metaplecticRetainedTerm (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (nd : MetaplecticDualArgument × PrimaryArgument) : ℂ :=
  if metaplecticDualNorm nd ≤ J then metaplecticDualTerm a r ℓ W A X nd else 0

lemma metaplecticRetainedTerm_finite (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ) :
    (∑' nd, metaplecticRetainedTerm a r ℓ W A X J nd) =
      ∑ nd ∈ metaplecticDualBall J, metaplecticDualTerm a r ℓ W A X nd := by
  rw [tsum_eq_sum (s := metaplecticDualBall J) (fun nd hnd => ?_)]
  · apply Finset.sum_congr rfl
    intro nd hnd
    simp only [metaplecticRetainedTerm,(mem_metaplecticDualBall nd J).mp hnd,ite_true]
  · have hn : ¬metaplecticDualNorm nd ≤ J := fun h => hnd ((mem_metaplecticDualBall nd J).mpr h)
    simp only [metaplecticRetainedTerm,hn,ite_false]

/-- Exact retained/tail split of the actual absolutely convergent dual
series. The retained part is the displayed finite sum. -/
theorem metaplecticDualTerm_split (a : Eisenstein → MetaplecticDualArgument → ℂ)
    (r : Eisenstein) (ℓ : ℤ) (W : ℝ → ℂ) (A X J : ℝ)
    (hs : Summable (metaplecticDualTerm a r ℓ W A X)) :
    (∑' nd, metaplecticDualTerm a r ℓ W A X nd) =
      (∑ nd ∈ metaplecticDualBall J, metaplecticDualTerm a r ℓ W A X nd)+
        ∑' nd, metaplecticFarTailTerm a r ℓ W A X J nd := by
  have hr : Summable (metaplecticRetainedTerm a r ℓ W A X J) := by
    apply (hasSum_sum_of_ne_finset_zero (s := metaplecticDualBall J) ?_).summable
    intro nd hnd
    have hn : ¬metaplecticDualNorm nd ≤ J := fun h => hnd ((mem_metaplecticDualBall nd J).mpr h)
    simp only [metaplecticRetainedTerm,hn,ite_false]
  have hf : Summable (metaplecticFarTailTerm a r ℓ W A X J) := by
    convert hs.sub hr using 1
    funext nd
    by_cases h : metaplecticDualNorm nd ≤ J
    · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,not_lt_of_ge h,ite_true,ite_false,sub_self]
    · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,lt_of_not_ge h,ite_true,ite_false,sub_zero]
  calc
    _ = ∑' nd, (metaplecticRetainedTerm a r ℓ W A X J nd+
        metaplecticFarTailTerm a r ℓ W A X J nd) := by
      apply tsum_congr
      intro nd
      by_cases h : metaplecticDualNorm nd ≤ J
      · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,not_lt_of_ge h,ite_true,ite_false,add_zero]
      · simp only [metaplecticFarTailTerm,metaplecticRetainedTerm,h,lt_of_not_ge h,ite_true,ite_false,zero_add]
    _ = _ := by rw [hr.tsum_add hf,metaplecticRetainedTerm_finite]

end CubicFirstMoment

end

end OAI
