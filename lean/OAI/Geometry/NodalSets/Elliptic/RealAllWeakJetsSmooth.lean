import OAI.Geometry.NodalSets.Elliptic.RealConvolutionContraction
import OAI.Geometry.NodalSets.Elliptic.RealFiniteWordBounds
import OAI.Geometry.NodalSets.Elliptic.RealGlobalJetEmbedding
import OAI.Geometry.NodalSets.Elliptic.RealL2PointwiseLimit
import OAI.Geometry.NodalSets.Elliptic.RealSmoothLocalCompactness
import OAI.Geometry.NodalSets.Elliptic.RealWeakJetConvolution

namespace OAI

namespace Yau
open MeasureTheory Set Filter Metric Yau.Analysis Yau.Geometry
open scoped ContDiff Convolution Topology
noncomputable section

theorem real_all_weak_jets_smooth {K L : Set Jets.Coord}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ interior L)
    (u : Jets.Coord → ℝ)
    (hall : ∀ N : ℕ, ∃ U : List (Fin 4) → Jets.Coord → ℝ,
      U []=u ∧
      (∀ es, es.length ≤ N → MemLp (U es) 2 volume ∧ tsupport (U es) ⊆ K) ∧
      ∀ es, es.length < N → ∀ i psi,
        ContDiff ℝ ∞ psi → HasCompactSupport psi →
        (∫ x, U es x*coordPartial psi x i)=-(∫ x, U (i::es) x*psi x)) :
    ∃ v : Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ tsupport v ⊆ L ∧ v =ᵐ[volume] u := by
  obtain ⟨U₀,hzero₀,hU₀,_⟩ := hall 0
  have hu : MemLp u 2 volume := hzero₀ ▸ (hU₀ [] (by simp)).1
  have hsu : tsupport u ⊆ K := hzero₀ ▸ (hU₀ [] (by simp)).2
  have hcu : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport _) hsu
  obtain ⟨r,hr,hsupport⟩ := real_compact_mollifier_support hK hKL
  let b : ℕ → ContDiffBump (0 : Jets.Coord) := realMollifierBump r hr
  let w : ℕ → Jets.Coord → ℝ := fun j ↦ u ⋆ (b j).normed volume
  have hw (j : ℕ) : ContDiff ℝ ∞ (w j) :=
    (b j).hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ) (hu.locallyIntegrable (by norm_num)) (b j).contDiff_normed
  have hc (j : ℕ) : HasCompactSupport (w j) :=
    hcu.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (b j).hasCompactSupport_normed
  have hs (j : ℕ) : tsupport (w j) ⊆ L := hsupport u hsu j
  have hb : ∀ R n : ℕ, ∃ B ≥ 0, ∀ j (ds : List (Fin 4)), ds.length ≤ n →
      ∀ x ∈ closedBall (0 : Jets.Coord) (R:ℝ), |partialJet (w j) ds x| ≤ B := by
    intro R n
    obtain ⟨U,hzero,hU,hweak⟩ := hall (n+4)
    let E : List (Fin 4) → ℝ := fun es ↦ ∫ x, (U es x)^2
    let D : ℝ := 256 * ∑ k ∈ Finset.range (n+5), ∑ a : Fin k → Fin 4, E (List.ofFn a)
    have hD : 0 ≤ D := mul_nonneg (by norm_num)
      (Finset.sum_nonneg (fun _ _ ↦ Finset.sum_nonneg (fun _ _ ↦ integral_nonneg (fun _ ↦ sq_nonneg _))))
    refine ⟨Real.sqrt D,Real.sqrt_nonneg D,fun j ds hd x _ ↦ ?_⟩
    have hj (es : List (Fin 4)) (he : es.length ≤ n+4) :
        (∫ x, (partialJet (w j) es x)^2) ≤ E es := by
      have hid := real_weak_jet_convolution U (n+4)
        (fun es he ↦ (hU es he).1.locallyIntegrable (by norm_num)) hweak
        ((b j).normed volume) (b j).contDiff_normed (b j).hasCompactSupport_normed es he
      rw [hzero] at hid
      change (∫ x, (partialJet (u ⋆ (b j).normed volume) es x)^2) ≤ E es
      rw [hid]
      exact real_normed_convolution_square_le (U es) (hU es he).1
        (hK.of_isClosed_subset (isClosed_tsupport _) (hU es he).2) (b j)
    have hbound := real_global_jet_l2_embedding (w j) (hw j) (hc j) n E hj ds hd x
    change (partialJet (w j) ds x)^2 ≤ D at hbound
    nlinarith [Real.sq_sqrt hD, abs_nonneg (partialJet (w j) ds x),
      sq_abs (partialJet (w j) ds x), Real.sqrt_nonneg D]
  obtain ⟨v,hv,nu,hnu,ht,_⟩ := real_smooth_local_subsequence w hw hb
  have hp (x : Jets.Coord) : Tendsto (fun j ↦ w (nu j) x) atTop (𝓝 (v x)) :=
    (ht [] {x} (isCompact_singleton)).tendsto_at (mem_singleton x)
  have hsv : tsupport v ⊆ L := by
    apply closure_minimal _ hL.isClosed
    intro x hx
    by_contra hn
    have hz (j : ℕ) : w (nu j) x=0 := image_eq_zero_of_notMem_tsupport (fun hh ↦ hn (hs (nu j) hh))
    have he : v x=0 := tendsto_nhds_unique (hp x) (by simpa only [hz] using tendsto_const_nhds)
    exact hx he
  have hl := (real_compact_convolution_L2_tendsto u hu hcu b
    (realMollifierBump_radius_tendsto r hr)).comp hnu.tendsto_atTop
  refine ⟨v,hv,hsv,?_⟩
  exact real_L2_pointwise_limit_ae (fun j ↦ w (nu j))
    (fun j ↦ real_compact_continuous_memLp _ (hw (nu j)).continuous (hc (nu j))) u v hu hl hp

end
end Yau

end OAI
