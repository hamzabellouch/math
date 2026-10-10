import OAI.Analysis.Pureness.Comparison.SupportApproximation
import OAI.Analysis.Pureness.Comparison.FiniteOrthogonalSupply

namespace OAI
open scoped BigOperators ComplexOrder
open Filter Topology
namespace CuntzComparison
variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

lemma hereditary_positive_pair_mul_eq_zero {b c x y : A} (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hbc : b * c = 0)
    (hxm : x ∈ hereditaryCorner b hb) (hym : y ∈ hereditaryCorner c hc) : x * y = 0 := by
  have hxc := hereditaryCorner_mul_eq_zero hb hbc hxm
  have hcx := positive_mul_eq_zero_symm hx hc hxc
  exact positive_mul_eq_zero_symm hy hx (hereditaryCorner_mul_eq_zero hc hcx hym)

lemma positive_le_one_of_square_le {a : A} (ha : 0 ≤ a) (hsq : a * a ≤ a) : a ≤ 1 := by
  apply (CFC.le_one_iff (R := ℝ) a ha.isSelfAdjoint).mpr
  intro t ht
  have heq : cfc (fun t : ℝ => t * t) a ≤ cfc (fun t : ℝ => t) a := by
    rw [cfc_mul (fun t : ℝ => t) (fun t => t) a continuousOn_id continuousOn_id, cfc_id' ℝ a]
    exact hsq
  have h := (cfc_le_iff (fun t : ℝ => t * t) (fun t : ℝ => t) a).mp heq t ht
  nlinarith

lemma supportApprox_square_le {a : A} (ha : 0 ≤ a) (n : ℕ) :
    supportApprox a n * supportApprox a n ≤ supportApprox a n := by
  unfold supportApprox
  rw [← cfc_mul _ _ a (supportCutoff_continuous n).continuousOn
    (supportCutoff_continuous n).continuousOn]
  apply (cfc_le_iff _ _ a ((supportCutoff_continuous n).mul (supportCutoff_continuous n)).continuousOn
    (supportCutoff_continuous n).continuousOn ha.isSelfAdjoint).mpr
  intro t ht
  have h := supportCutoff_bounds n t
  change supportCutoff n t * supportCutoff n t ≤ supportCutoff n t
  nlinarith

lemma orthogonal_supportApprox_sum_le_one (a : ι → A) (ha : ∀ i, 0 ≤ a i)
    (horth : ∀ i j, i ≠ j → a i * a j = 0) (n : ℕ) :
    ∑ i, supportApprox (a i) n ≤ 1 := by
  classical
  have hpos : 0 ≤ ∑ i, supportApprox (a i) n :=
    Finset.sum_nonneg fun i hi => supportApprox_nonneg _ _
  apply positive_le_one_of_square_le hpos
  have hprod (i j : ι) : supportApprox (a i) n * supportApprox (a j) n =
      if i = j then supportApprox (a i) n * supportApprox (a i) n else 0 := by
    split_ifs with hij
    · subst j; rfl
    · exact hereditary_positive_pair_mul_eq_zero (ha i) (ha j)
        (supportApprox_nonneg _ _) (supportApprox_nonneg _ _) (horth i j hij)
        (supportApprox_mem (ha i) n) (supportApprox_mem (ha j) n)
  rw [Finset.sum_mul_sum]
  calc
    _ = ∑ i, supportApprox (a i) n * supportApprox (a i) n := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_eq_single i
      · intro j hj hji
        rw [hprod, ite_eq_right (Ne.symm hji)]
      · simp
    _ ≤ _ := Finset.sum_le_sum fun i hi => supportApprox_square_le (ha i) n

theorem TracialState.orthogonal_support_mass_sum_le_one (τ : TracialState A)
    (a : ι → A) (ha : ∀ i, 0 ≤ a i) (horth : ∀ i j, i ≠ j → a i * a j = 0) :
    ∑ i, (τ.spectralSupportMass (a i) (ha i)).toReal ≤ 1 := by
  have hlim := tendsto_finsetSum Finset.univ fun i hi => τ.supportApprox_trace_tendsto (ha i)
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have h := (Complex.le_def.mp (τ.toPositiveLinearMap.monotone
    (orthogonal_supportApprox_sum_le_one a ha horth n))).1
  change (τ.toPositiveLinearMap (∑ i, supportApprox (a i) n)).re ≤ (τ.toPositiveLinearMap 1).re at h
  simpa only [map_sum, Complex.re_sum, τ.normalized, Complex.one_re] using h
end CuntzComparison

end OAI
