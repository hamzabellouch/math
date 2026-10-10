import Mathlib
import OAI.Geometry.SmoothYau.Estimates.RoundPowerConjugateProjectionUniform
import OAI.Geometry.SmoothYau.Smoothness.ExistsSphericalRadialCutoff

namespace OAI

noncomputable section
open Set Filter Function Manifold
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples
section ProjectionGerm
variable {E M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
lemma chartGradientProjection_congr_nhds (g : SmoothMetric E M) (p : M)
    {u v : M → ℝ} {y : E} (hy : y ∈ (chartAt E p).target)
    (he : u =ᶠ[𝓝 ((chartAt E p).symm y)] v) (i j : CoordIndex E) :
    chartGradientProjection g u p i j =ᶠ[𝓝 y] chartGradientProjection g v p i j := by
  have hec := he.comp_tendsto ((chartAt E p).continuousAt_symm hy).tendsto
  have hdf := hec.fderiv (𝕜 := ℝ)
  filter_upwards [hdf] with z hz
  unfold chartGradientProjection chartGradientField coordinateFlux localGradientPair
  rw [show fderiv ℝ (u ∘ (chartAt E p).symm) z = fderiv ℝ (v ∘ (chartAt E p).symm) z from hz]
end ProjectionGerm

local instance chartGradientProjectionCongrNhdsFinrank :
    Fact (Module.finrank ℝ (Euclidean 4) = 4) := ⟨by simp [Euclidean]⟩

theorem spherical_annular_projection_uniform
    (g₀ g : SmoothMetric (Euclidean 3) (Sphere 3)) (hg₀ : IsRound g₀)
    {F : Set (Sphere 3)} {r a b : ℝ} (hr : 0 < r) (hra : r < a) (hab : a ≤ b) (hb : b < 1)
    (hFr : ∀ q ∈ F, sphericalRadius sourceAxisOne sourceAxisTwo q ≤ r)
    (hext : ∀ q ∉ F, ∀ v w : TangentSpace 𝓘(ℝ,Euclidean 3) q,
      g.inner q v w=g₀.inner q v w)
    (tests : List (CoordinateTest (Euclidean 3) (Sphere 3))) (h : ℕ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C > 0, ∀ (w : Sphere 3 → ℝ), ContMDiff 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,ℝ) ∞ w →
      (∀ q, 1/2 ≤ w q) → (∀ q, w q ≤ 2) →
      (∀ t ∈ tests, ∀ y ∈ t.compactSet, ∀ j ≤ h+1,
        ‖iteratedFDeriv ℝ j (w ∘ (chartAt (Euclidean 3) t.center).symm) y‖ ≤ D) →
      (∀ q, coordinateGradientPair g w w q ≤ (1-b^2)/16) →
      ∀ {u : Euclidean 3 → ℝ}, HasCompactSupport u →
      tsupport u ⊆ {y | sphericalRadius sourceAxisOne sourceAxisTwo
        ((chartAt (Euclidean 3) sourcePole).symm y) < r} →
      ∀ n : ℕ, 1 ≤ n → ∀ t ∈ tests, ∀ y ∈ t.compactSet,
      a ≤ sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) →
      sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) ≤ b →
      ∀ i j : CoordIndex (Euclidean 3), ∀ k ≤ h,
        ‖iteratedFDeriv ℝ k (chartGradientProjection g
          (fun q => (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q/w q)
          t.center i j) y‖ ≤ C*(n:ℝ)^k := by
  classical
  let K (t : CoordinateTest (Euclidean 3) (Sphere 3)) := t.compactSet ∩
    {y | a ≤ sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) ∧
      sphericalRadius sourceAxisOne sourceAxisTwo ((chartAt (Euclidean 3) t.center).symm y) ≤ b}
  have hKt (t : CoordinateTest (Euclidean 3) (Sphere 3)) : IsCompact (K t) := by
    have hc := (sphericalRadius_continuous sourceAxisOne sourceAxisTwo).comp
      (sphere_chart_symm_continuous t.center)
    exact t.isCompact.inter_right ((isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const))
  have hKO (t : CoordinateTest (Euclidean 3) (Sphere 3)) : K t ⊆ (chartAt (Euclidean 3) t.center).target :=
    fun y hy => t.inTarget hy.1
  have hround (t : CoordinateTest (Euclidean 3) (Sphere 3)) (y : Euclidean 3) (hy : y ∈ K t)
      (v z : TangentSpace 𝓘(ℝ,Euclidean 3) ((chartAt (Euclidean 3) t.center).symm y)) :
      g.inner _ v z = (inner ℝ : Euclidean 4 → Euclidean 4 → ℝ)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun q : Sphere 3 => (q : Euclidean 4)) _ v)
        (mfderiv 𝓘(ℝ,Euclidean 3) 𝓘(ℝ,Euclidean 4) (fun q : Sphere 3 => (q : Euclidean 4)) _ z) := by
    apply (hext _ (fun hq => (not_le_of_gt hra) ((hy.2.1).trans (hFr _ hq))) v z).trans
    exact hg₀ _ v z
  have hb0 : 0 ≤ b := (hr.trans hra).le.trans hab
  have hb2 : b^2 < 1 := by nlinarith
  have hKr (t : CoordinateTest (Euclidean 3) (Sphere 3)) : ∀ y ∈ K t,
      a ≤ ‖roundPlanarChart sourceAxisOne sourceAxisTwo t.center y‖ := by
    intro y hy
    have hh := hy.2.1
    rw [sphericalRadius_eq_planar_norm] at hh
    exact hh
  have hKb (t : CoordinateTest (Euclidean 3) (Sphere 3)) : ∀ y ∈ K t,
      Complex.normSq (roundPlanarChart sourceAxisOne sourceAxisTwo t.center y) ≤ b^2 := by
    intro y hy
    rw [Complex.normSq_eq_norm_sq]
    have hh : ‖roundPlanarChart sourceAxisOne sourceAxisTwo t.center y‖ ≤ b := by
      have hh := hy.2.2
      rw [sphericalRadius_eq_planar_norm] at hh
      exact hh
    nlinarith [norm_nonneg (roundPlanarChart sourceAxisOne sourceAxisTwo t.center y)]
  choose C hC hCJ using fun (t : CoordinateTest (Euclidean 3) (Sphere 3)) (k : Fin (h+1)) =>
    roundPower_conjugate_projection_uniform g sourceAxisOne sourceAxisTwo t.center
      source_axes_orthonormal.1 source_axes_orthonormal.2.1 source_axes_orthonormal.2.2
      (hKt t) (hKO t) (hround t) k.val (hr.trans hra) hb2 hD (hKr t) (hKb t)
  let B := 1+∑ t ∈ tests.toFinset, ∑ k : Fin (h+1), C t k
  have hB : 0 < B := by
    apply add_pos_of_pos_of_nonneg zero_lt_one
    exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun k _ => (hC t k).le))
  have hCB (t : CoordinateTest (Euclidean 3) (Sphere 3)) (ht : t ∈ tests) (k : Fin (h+1)) : C t k ≤ B := by
    have hk := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin (h+1)))) => (hC t k).le)
      (Finset.mem_univ k)
    have ht' := Finset.single_le_sum (fun t (_ : t ∈ tests.toFinset) =>
      Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin (h+1)))) => (hC t k).le))
      (List.mem_toFinset.mpr ht)
    change C t k ≤ 1+_
    linarith
  refine ⟨B,hB,?_⟩
  intro w hw hwl hwu hwJ hwG u hc hs n hn t ht y hy hya hyb i j k hk
  let k' : Fin (h+1) := ⟨k,by omega⟩
  have hK : y ∈ K t := ⟨hy,hya,hyb⟩
  have hw0 : ∀ q, w q ≠ 0 := fun q => ne_of_gt (by linarith [hwl q])
  have hp := hCJ t k' w hw hw0 (fun y _ => hwl _) (fun y _ => hwu _)
    (fun j _ hj y hy => hwJ t ht y hy.1 j (by have := k'.isLt; omega))
    (fun y _ => hwG _) n hn y hK i j
  have he := spherical_wave_exterior_germ hc hs n (hra.le.trans hya)
  have hew : (fun q => (roundPower sourceAxisOne sourceAxisTwo n+sphericalWaveLift u) q/w q) =ᶠ[𝓝 ((chartAt (Euclidean 3) t.center).symm y)]
      (fun q => roundPower sourceAxisOne sourceAxisTwo n q/w q) := by
    filter_upwards [he] with q hq
    rw [hq]
  have heP := (chartGradientProjection_congr_nhds g t.center (t.inTarget hy) hew i j).iteratedFDeriv ℝ k
  rw [heP.eq_of_nhds]
  exact hp.trans (mul_le_mul_of_nonneg_right (hCB t ht k') (pow_nonneg (Nat.cast_nonneg n) k))
end YauCounterexamples
end

end OAI
