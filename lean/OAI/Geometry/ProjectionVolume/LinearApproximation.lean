import OAI.Geometry.ProjectionVolume.SequenceLimits

namespace OAI

open Set Metric Filter
open scoped Pointwise Topology RealInnerProductSpace

namespace Paper092

theorem approximation_linear_image_brightness_uniform {d : ℕ} (hd : 2 ≤ d)
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 1 ≤ scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m)
    (L : Euclidean d ≃ₗ[ℝ] Euclidean d) :
    TendstoUniformlyOn (fun m u => brightness (L '' P m) u) (brightness (L '' K))
      atTop (sphere 0 1) := by
  have hLK : IsCompact (L '' K) := hK.image L.toLinearMap.continuous_of_finiteDimensional
  obtain ⟨R, hR, hbound⟩ := hLK.isBounded.exists_pos_norm_le
  have hball : L '' K ⊆ closedBall 0 R := by
    intro x hx
    simpa only [mem_closedBall, dist_zero_right] using hbound x hx
  apply approximation_brightness_uniform hd
    (fun m => (hP m).image L.toLinearMap.continuous_of_finiteDimensional)
    hLK hscale hscalelim hR.le hball
  · exact fun m => image_mono (hPK m)
  · intro m
    rw [← image_smul_comm L.toLinearMap (scale m) (P m)
      (fun x => L.toLinearMap.map_smul (scale m) x)]
    exact image_mono (hKP m)

theorem approximation_linear_image_support_uniform {d : ℕ} (hd : 2 ≤ d)
    {P : ℕ → Set (Euclidean d)} {K : Set (Euclidean d)}
    (hP : ∀ m, IsCompact (P m)) (hv : ∀ m, Convex ℝ (P m))
    (hi : ∀ m, (interior (P m)).Nonempty) (hK : IsCompact K)
    {scale : ℕ → ℝ} (hscale : ∀ m, 1 ≤ scale m) (hscalelim : Tendsto scale atTop (𝓝 1))
    (hPK : ∀ m, P m ⊆ K) (hKP : ∀ m, K ⊆ scale m • P m)
    (L : Euclidean d ≃ₗ[ℝ] Euclidean d) :
    TendstoUniformlyOn
      (fun m u => SupportGeometry.support (projectionBody (L '' P m)) (innerSL ℝ u))
      (brightness (L '' K)) atTop (sphere 0 1) := by
  have hint : ∀ m, (interior (L '' P m)).Nonempty := by
    intro m
    change (interior (L.toContinuousLinearEquiv.toHomeomorph '' P m)).Nonempty
    rw [← Homeomorph.image_interior]
    exact (hi m).image _
  have heq :
      (fun m u => SupportGeometry.support (projectionBody (L '' P m)) (innerSL ℝ u)) =
      (fun m u => brightness (L '' P m) u) := by
    funext m u
    exact projectionBody_support hd (L '' P m)
      ((hP m).image L.toLinearMap.continuous_of_finiteDimensional)
      ((hv m).linear_image L.toLinearMap) (hint m) u
  rw [heq]
  exact approximation_linear_image_brightness_uniform hd hP hK hscale hscalelim hPK hKP L

end Paper092

end OAI
