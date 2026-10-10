import Mathlib
import OAI.Probability.SKBarriers.Parisi.QuantileMinimizer

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem finite_quantile_minimizer_interior_fixedPoint {k : ℕ} {β : ℝ} (hβ : β ≠ 0)
    (A : Fin (k+1) → ℝ) (hord : StrictMono A) (hint : ∀ j, A j ∈ Set.Ioo 0 1)
    (hmin : ∀ B ∈ admissibleQuantiles k, extendedQuantileParisi k β A ≤ extendedQuantileParisi k β B)
    (j : Fin (k+1)) : quantileOverlapMean k β A j = A j := by
  classical
  let V : Fin (k+1) → ℝ := fun i => if i=j then 1 else 0
  let Q : ℝ → Fin (k+1) → ℝ := fun t i => A i+t*V i
  have hzero : Q 0 = A := by funext i; simp [Q]
  have hc (i : Fin (k+1)) : Continuous (fun t : ℝ => Q t i) := by
    exact continuous_const.add (continuous_id.mul continuous_const)
  have hi : ∀ᶠ t in 𝓝 (0:ℝ), ∀ i, Q t i ∈ Set.Ioo 0 1 := by
    apply eventually_all.mpr
    intro i
    apply (hc i).continuousAt.eventually_mem
    simpa only [Q,zero_mul,add_zero] using isOpen_Ioo.mem_nhds (hint i)
  have ho : ∀ᶠ t in 𝓝 (0:ℝ), ∀ a b : Fin (k+1), a < b → Q t a < Q t b := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro b
    by_cases hab : a < b
    · have H := (hc a).continuousAt.eventually_lt (hc b).continuousAt
        (show Q 0 a < Q 0 b by simpa [Q] using hord hab)
      exact H.mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ h => (hab h).elim)
  have hm : IsLocalMin (fun t => extendedQuantileParisi k β (Q t)) 0 := by
    apply (hi.and ho).mono
    intro t ht
    change extendedQuantileParisi k β (Q 0) ≤ extendedQuantileParisi k β (Q t)
    rw [hzero]
    exact hmin (Q t) ⟨(show StrictMono (Q t) from ht.2).monotone,
      fun i => ⟨(ht.1 i).1.le,(ht.1 i).2.le⟩⟩
  have hd : HasDerivAt Q V 0 := by
    apply hasDerivAt_pi.mpr
    intro index
    simpa only [Q,id_eq,one_mul] using
      ((hasDerivAt_id (0:ℝ)).mul_const (V index)).const_add (A index)
  have hg (i : Fin (k+1)) : 0 < cumulativeGapMap k (Q 0) i := by
    rw [hzero]
    refine Fin.cases (hint 0).1 (fun l => ?_) i
    rw [cumulativeGapMap_succ]
    exact sub_pos.mpr (hord (Fin.castSucc_lt_succ (i := l)))
  have H := hm.hasDerivAt_eq_zero (extendedQuantileParisi_hasDerivAt β Q hd hg)
  rw [hzero] at H
  have he : (∑ i : Fin (k+1), ((k+1:ℕ):ℝ)⁻¹*V i*(A i-quantileOverlapMean k β A i)) =
      ((k+1:ℕ):ℝ)⁻¹*(A j-quantileOverlapMean k β A j) := by
    simp [V,Finset.sum_ite_eq']
  rw [he] at H
  have hp : 0 < (β^2/2)*((k+1:ℕ):ℝ)⁻¹ := by
    exact mul_pos (div_pos (sq_pos_of_ne_zero hβ) (by norm_num)) (by positivity)
  have H' : (β^2/2)*((k+1:ℕ):ℝ)⁻¹*(A j-quantileOverlapMean k β A j) = 0 := by
    simpa only [mul_assoc] using H
  exact (sub_eq_zero.mp ((mul_eq_zero.mp H').resolve_left hp.ne')).symm

end SK.Analytic

end
end

end

end OAI
