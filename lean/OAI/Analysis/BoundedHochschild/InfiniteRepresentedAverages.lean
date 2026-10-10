import OAI.Analysis.BoundedHochschild.InfiniteOperatorRows
import OAI.Analysis.BoundedHochschild.StrongRowDefect
import OAI.Analysis.BoundedHochschild.RepresentedAveragingOrbit

namespace OAI

/-! Infinite right averages are strong limits of finite normalized averages,
and hence lie in the same weakly closed orbit. Only the target representation
is required to preserve the normalization limit. -/

noncomputable section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

namespace BoundedHochschild.KadisonRingrose

variable {M I H K : Type*} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma representation_row_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1) (s : Finset I) :
    ∑ i ∈ s, π (m i) * star (π (m i)) ≤ 1 := by
  simpa only [map_sum, map_mul, map_star, map_one] using OrderHomClass.mono π (hm s)

def infiniteRepresentedRightAverage (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (W : H →L[ℂ] K) : H →L[ℂ] K :=
  infiniteOperatorRow (fun i => π (m i)) (fun i => σ (m i))
    (representation_row_le π m hm) (representation_row_le σ m hm) W

lemma infiniteRepresentedRightAverage_norm_le (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1) (W : H →L[ℂ] K) :
    ‖infiniteRepresentedRightAverage π σ m hm W‖ ≤ ‖W‖ :=
  infiniteOperatorRow_norm_le _ _ _ _ W

lemma infiniteRepresentedRightAverage_hasSum (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (W : H →L[ℂ] K) (ξ : H) :
    HasSum (fun i => π (m i) (W ((σ (m i)).adjoint ξ)))
      (infiniteRepresentedRightAverage π σ m hm W ξ) :=
  infiniteOperatorRow_hasSum _ _ _ _ W ξ

lemma completedRow_average_tendsto (π : M →⋆ₐ[ℂ] (K →L[ℂ] K))
    (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (W : H →L[ℂ] K) (ξ : H) :
    Tendsto (fun s : Finset I => representedRightAverage π σ (completedRow m s) W ξ)
      atTop (𝓝 (infiniteRepresentedRightAverage π σ m hm W ξ)) := by
  have hd := rowDefect_average_strong_zero π σ m hm hlim W ξ
  have hs := infiniteRepresentedRightAverage_hasSum π σ m hm W ξ
  have he (s : Finset I) : representedRightAverage π σ (completedRow m s) W ξ =
      π (rowDefect m s) (W ((σ (rowDefect m s)).adjoint ξ)) +
      ∑ i ∈ s, π (m i) (W ((σ (m i)).adjoint ξ)) := by
    rw [completedRow_average]
    simp only [add_apply, sum_apply, ContinuousLinearMap.comp_apply]
  simp_rw [he]
  simpa only [zero_add] using hd.add hs

lemma infiniteRepresentedRightAverage_mem_closed_orbit
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (σ : M →⋆ₐ[ℂ] (H →L[ℂ] H)) (m : I → M)
    (hm : ∀ s : Finset I, ∑ i ∈ s, m i * star (m i) ≤ 1)
    (hlim : ∀ ξ : H, Tendsto
      (fun s : Finset I => inner ℂ ξ (σ (∑ i ∈ s, m i * star (m i)) ξ))
      atTop (𝓝 (inner ℂ ξ ξ))) (W : H →WOT[ℂ] K) :
    ContinuousLinearMapWOT.ofCLM (infiniteRepresentedRightAverage π σ m hm W.toCLM) ∈
      closedRepresentedAveragingOrbit π σ W := by
  classical
  have ht : Tendsto (fun s : Finset I => weakRepresentedRightAverage π σ (completedRow m s) W)
      atTop (𝓝 (ContinuousLinearMapWOT.ofCLM
        (infiniteRepresentedRightAverage π σ m hm W.toCLM))) := by
    apply ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr
    intro ξ η
    exact tendsto_const_nhds.inner (completedRow_average_tendsto π σ m hm hlim W.toCLM ξ)
  apply isClosed_closure.mem_of_tendsto ht
  apply Eventually.of_forall
  intro s
  exact subset_closure (weakRepresentedRightAverage_mem_orbit π σ (completedRow m s)
    (completedRow_normalized m s (hm s)) W)

end BoundedHochschild.KadisonRingrose

end

end OAI
