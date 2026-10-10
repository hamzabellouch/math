import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set Filter Topology

lemma local_smooth_taylor {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i) :
    HasFTaylorSeriesUpToOn (↑(⊤:ℕ∞)) (fun x => ∑' i, f i x)
      (fun x n => ∑' i, iteratedFDeriv ℝ n (f i) x) s := by
  constructor
  · intro x hx
    simp_rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]
    have he : (continuousMultilinearCurryFin0 ℝ E F).symm (∑' i, f i x) =
        ∑' i, (continuousMultilinearCurryFin0 ℝ E F).symm (f i x) :=
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.map_tsum
    rw [←he]
    exact (continuousMultilinearCurryFin0 ℝ E F).apply_symm_apply _
  · intro n hn x hx
    have hd : HasFDerivAt (fun y => ∑' i, iteratedFDeriv ℝ n (f i) y)
        (∑' i, fderiv ℝ (iteratedFDeriv ℝ n (f i)) x) x := by
      apply hasFDerivAt_tsum_of_isPreconnected (hv (n+1)) hs hsc
        (x₀ := x) (x := x)
      · intro i y hy
        exact ((hf i).differentiable_iteratedFDeriv (m := n) (by exact_mod_cast (ENat.natCast_lt_top n))).differentiableAt.hasFDerivAt
      · intro i y hy
        simpa only [fderiv_iteratedFDeriv,Function.comp_apply,LinearIsometryEquiv.norm_map]
          using hbound (n+1) i y hy
      · exact hx
      · exact Summable.of_norm_bounded (hv n) (fun i => hbound n i x hx)
      · exact hx
    convert hd.hasFDerivWithinAt (s := s) using 1
    simp_rw [fderiv_iteratedFDeriv,Function.comp_apply]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) F).toContinuousLinearEquiv.map_tsum
  · intro n hn
    exact continuousOn_tsum (fun i => ((hf i).continuous_iteratedFDeriv (m := n) (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).continuousOn)
      (hv n) (fun i x hx => hbound n i x hx)

lemma local_smooth_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (fun x => ∑' i, f i x) s :=
  (local_smooth_taylor hs hsc hf v hv hbound).contDiffOn

lemma local_iteratedFDeriv_tsum {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : ι → E → F} {s : Set E} (hs : IsOpen s) (hsc : IsPreconnected s)
    (hf : ∀ i, ContDiff ℝ (↑(⊤:ℕ∞)) (f i))
    (v : ℕ → ι → ℝ) (hv : ∀ n, Summable (v n))
    (hbound : ∀ n i x, x∈s → ‖iteratedFDeriv ℝ n (f i) x‖≤v n i)
    (n : ℕ) {x : E} (hx : x∈s) :
    iteratedFDeriv ℝ n (fun x => ∑' i, f i x) x = ∑' i, iteratedFDeriv ℝ n (f i) x := by
  have ht := (local_smooth_taylor hs hsc hf v hv hbound).eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤)) (hs.uniqueDiffOn) hx
  rw [iteratedFDerivWithin_of_isOpen n hs hx] at ht
  exact ht.symm

end ScalarConductivity

end

end OAI
