import OAI.MeasureTheory.Falconer.Angular.MixedNormalizedCaps
import OAI.MeasureTheory.Falconer.Fourier.SmoothMask

namespace OAI

/-! # Mixed derivative bounds for the actual buffered angular masks -/

namespace Falconer
open Set
open scoped ContDiff Topology

theorem normalizedCap_ambient_derivative_zero {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Sphere d)) (c : Sphere d) (x : Space d)
    (hfar : δ < ‖x-(c : Space d)‖) (k : ℕ) :
    iteratedFDeriv ℝ k (normalizedCap δ hδ S c) x = 0 := by
  have hn : x ∉ tsupport (capBump δ hδ c) := by
    rw [(capBump δ hδ c).tsupport_eq]
    exact not_le.mpr hfar
  have he : normalizedCap δ hδ S c =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with y hy
    change capBump δ hδ c y = (0 : ℝ) at hy
    simp only [normalizedCap,hy,zero_mul]
  simpa using (he.iteratedFDeriv ℝ k).self_of_nhds

theorem capCutoffAmbient_ambient_derivatives (d k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (δ : ℝ) (hδ : 0 < δ)
      (S : Finset (Sphere d)),
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ/2 ≤ dist x y) →
      ∀ (U : Set (Sphere d)) (w : Sphere d),
      ‖iteratedFDeriv ℝ k (capCutoffAmbient δ hδ S U) w‖ ≤ B*(δ⁻¹)^k := by
  classical
  obtain ⟨C,hC,hCb⟩ := normalizedCap_ambient_derivatives d k
  refine ⟨5^d*C, by positivity, ?_⟩
  intro δ hδ S hsep U w
  let S₀ := cutoffCapCenters δ S U
  let T := S₀.filter (fun c => dist w c ≤ δ)
  let f := fun c : Sphere d =>
    iteratedFDeriv ℝ k (normalizedCap δ hδ S c) (w : Space d)
  have hsub : S₀ ⊆ S := Finset.filter_subset _ _
  have hzero (c : Sphere d) (hc : c ∈ S₀) (hct : c ∉ T) : f c = 0 := by
    have hd : δ < dist w c :=
      lt_of_not_ge (fun h => hct (Finset.mem_filter.mpr ⟨hc,h⟩))
    exact normalizedCap_ambient_derivative_zero hδ S c w (by
      simpa only [Subtype.dist_eq, dist_eq_norm] using hd) k
  have hsum : (∑ c ∈ S₀, f c) = ∑ c ∈ T, f c := by
    symm
    exact Finset.sum_subset (Finset.filter_subset _ _) hzero
  change ‖iteratedFDeriv ℝ k (fun x => ∑ c ∈ S₀, normalizedCap δ hδ S c x) w‖ ≤ _
  rw [iteratedFDeriv_fun_sum_apply
    (fun c _ => ((normalizedCap_contDiff hδ S c).of_le (by simp)).contDiffAt)]
  change ‖∑ c ∈ S₀, f c‖ ≤ _
  rw [hsum]
  calc
    _ ≤ ∑ c ∈ T, ‖f c‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ T, C*(δ⁻¹)^k := Finset.sum_le_sum (fun c _ => hCb δ hδ S hsep c w)
    _ = (T.card : ℝ)*(C*(δ⁻¹)^k) := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ 5^d*(C*(δ⁻¹)^k) := mul_le_mul_of_nonneg_right
      (separated_sphere_overlap S₀ hδ
        (fun x hx y hy hxy => hsep x (hsub hx) y (hsub hy) hxy) w) (by positivity)
    _ = _ := by ring

end Falconer

end OAI
