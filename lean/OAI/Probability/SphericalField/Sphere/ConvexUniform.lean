import Mathlib

namespace OAI

section
noncomputable section
open Filter Set Metric
open scoped Topology NNReal

namespace SphericalPerceptron

lemma equicontinuous_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) : Equicontinuous F := by
  let G : E → ℝ := fun x => sSup (Set.range (fun n => F n x))
  have hb (x : E) : BddAbove (Set.range (fun n => F n x)) := (ht x).bddAbove_range
  have hle (n : ℕ) (x : E) : F n x ≤ G x := le_csSup (hb x) ⟨n,rfl⟩
  have hG : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb' hab
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨n,rfl⟩
    exact ((hcv n).2 trivial trivial ha hb' hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hle n x) ha)
        (mul_le_mul_of_nonneg_left (hle n y) hb'))
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  intro x
  have hn : {y : E | G y < G x+1} ∈ 𝓝 x :=
    (hGc.continuousAt).preimage_mem_nhds (Iio_mem_nhds (by linarith))
  obtain ⟨r,hr,hrG⟩ := Metric.mem_nhds_iff.mp hn
  let K : ℝ≥0 := (2*(G x+1)/(r/2)).toNNReal
  have hLip (n : ℕ) : LipschitzOnWith K (F n) (ball x (r-r/2)) := by
    apply ((hcv n).subset (Set.subset_univ _) (convex_ball _ _)).lipschitzOnWith_of_abs_le
      (half_pos hr)
    intro y hy
    rw [abs_of_nonneg (h0 n y)]
    exact (hle n y).trans (hrG hy).le
  apply Metric.equicontinuousAt_of_continuity_modulus (fun y => (K:ℝ)*dist x y)
    (by
      have hc : Continuous (fun y : E => (K:ℝ)*dist x y) := by fun_prop
      simpa only [dist_self,mul_zero] using hc.tendsto x) F
  filter_upwards [ball_mem_nhds x (by linarith : 0 < r-r/2)] with y hy n
  have hx : x ∈ ball x (r-r/2) := by rw [mem_ball,dist_self]; linarith
  exact (hLip n).dist_le_mul x hx y hy

lemma tendstoUniformlyOn_of_convex_nonneg_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : ℕ → E → ℝ) (f : E → ℝ)
    (hcv : ∀ n, ConvexOn ℝ Set.univ (F n)) (h0 : ∀ n x, 0 ≤ F n x)
    (ht : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    {K : Set E} (hK : IsCompact K) : TendstoUniformlyOn F f atTop K := by
  have he := equicontinuous_of_convex_nonneg_tendsto F f hcv h0 ht
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have he' : Equicontinuous (fun n (x : K) => F n x) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ,hδ,hd⟩ := Metric.equicontinuousAt_iff.mp (he (x:E)) ε hε
    exact ⟨δ,hδ,fun y hy n => hd (y:E) hy n⟩
  have hp : Tendsto (fun n (x : K) => F n x) atTop (𝓝 (fun x : K => f x)) :=
    tendsto_pi_nhds.mpr (fun x => ht x)
  have hu := (he'.tendsto_uniformFun_iff_pi atTop (fun x : K => f x)).mpr hp
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

end SphericalPerceptron
end
end

end OAI
