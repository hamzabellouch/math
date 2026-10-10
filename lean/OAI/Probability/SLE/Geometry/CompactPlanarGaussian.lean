import OAI.Probability.SLE.Stochastic.PlanarGaussianMean
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI

/-! Compact smooth planar tests have one uniform Gaussian-generator
error constant. These are the tests needed for Brownian localization. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

lemma compact_planar_test_bounds
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0,
      (∀ a b j, j ≤ 3 → |iteratedDeriv j (fun x => f (x,b)) a| ≤ K) ∧
      (∀ a b j, j ≤ 3 → |iteratedDeriv j (fun y => f (a,y)) b| ≤ K) ∧
      ∀ a, LipschitzWith K (fun b => iteratedDeriv 2 (fun x => f (x,b)) a) := by
  let g : ℝ × ℝ → ℝ := f ∘ Prod.swap
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hf.comp (contDiff_snd.prodMk contDiff_fst)
  have hgc : HasCompactSupport g := hc.comp_homeomorph (Homeomorph.prodComm ℝ ℝ)
  have hx (j : ℕ) := compact_smooth_bounded_lipschitz (spatialPartial g j)
    (spatialPartial_smooth g hg j) (spatialPartial_compact g hgc j)
  have hy (j : ℕ) := compact_smooth_bounded_lipschitz (spatialPartial f j)
    (spatialPartial_smooth f hf j) (spatialPartial_compact f hc j)
  choose C hCb hCl using hx
  choose D hDb hDl using hy
  let K : ℝ≥0 := ∑ j ∈ Finset.range 4, (C j+D j)
  have hC (j : ℕ) (hj : j ≤ 3) : C j ≤ K := by
    have hle : C j ≤ C j+D j := le_add_of_nonneg_right (show 0 ≤ D j from zero_le)
    exact hle.trans (Finset.single_le_sum (s := Finset.range 4) (f := fun i => C i+D i)
      (fun i _ => (show 0 ≤ C i+D i from zero_le))
      (Finset.mem_range.mpr (by omega)))
  have hD (j : ℕ) (hj : j ≤ 3) : D j ≤ K := by
    have hle : D j ≤ C j+D j := le_add_of_nonneg_left (show 0 ≤ C j from zero_le)
    exact hle.trans (Finset.single_le_sum (s := Finset.range 4) (f := fun i => C i+D i)
      (fun i _ => (show 0 ≤ C i+D i from zero_le))
      (Finset.mem_range.mpr (by omega)))
  refine ⟨K,?_,?_,?_⟩
  · intro a b j hj
    have hh := (hCb j (b,a)).trans (show (C j:ℝ)≤K by exact_mod_cast hC j hj)
    simpa only [spatialPartial_eq_iteratedDeriv g hg, g, Function.comp_apply,
      Prod.swap_prod_mk, Real.norm_eq_abs] using hh
  · intro a b j hj
    have hh := (hDb j (a,b)).trans (show (D j:ℝ)≤K by exact_mod_cast hD j hj)
    simpa only [spatialPartial_eq_iteratedDeriv f hf, Real.norm_eq_abs] using hh
  · intro a
    apply LipschitzWith.of_dist_le_mul
    intro b c
    have hh := ((hCl 2).weaken (hC 2 (by decide))).dist_le_mul (b,a) (c,a)
    simpa only [spatialPartial_eq_iteratedDeriv g hg, g, Function.comp_apply,
      Prod.swap_prod_mk, Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hh

def planarGenerator (f : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ :=
  (1/2:ℝ)*(iteratedDeriv 2 (fun x => f (x,z.2)) z.1+
    iteratedDeriv 2 (fun y => f (z.1,y)) z.2)

lemma compact_planar_gaussian_generator
    (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ C : ℝ≥0, ∀ (δ : ℝ≥0) (z : ℝ × ℝ),
      |planarGaussianMean δ f z.1 z.2-f z-(δ:ℝ)*planarGenerator f z| ≤
        (C:ℝ)*(δ:ℝ)*Real.sqrt δ := by
  obtain ⟨K,hx,hy,hxy⟩ := compact_planar_test_bounds f hf hc
  let M := 2*standardGaussianAbsMoment 3+(1/2:ℝ)*standardGaussianAbsMoment 1
  have hM : 0≤M := by
    dsimp [M]
    have h3 := standardGaussianAbsMoment_nonneg 3
    have h1 := standardGaussianAbsMoment_nonneg 1
    positivity
  refine ⟨K*⟨M,hM⟩,?_⟩
  intro δ z
  have h1 (b : ℝ) : ContDiff ℝ 3 (fun a => f (a,b)) :=
    (hf.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have h2 (a : ℝ) : ContDiff ℝ 3 (fun b => f (a,b)) :=
    (hf.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  have h := planar_gaussian_generator_error f hf.continuous K h1 h2 hx hy hxy δ z.1 z.2
  calc
    _ = |planarGaussianMean δ f z.1 z.2-f z-(1/2:ℝ)*(δ:ℝ)*
        (iteratedDeriv 2 (fun x => f (x,z.2)) z.1+
          iteratedDeriv 2 (fun y => f (z.1,y)) z.2)| := by
      congr 1
      dsimp [planarGenerator]
      ring
    _ ≤ (K:ℝ)*(δ:ℝ)*Real.sqrt δ*M := h
    _ = _ := by
      change (K:ℝ)*(δ:ℝ)*Real.sqrt δ*M=(K:ℝ)*M*(δ:ℝ)*Real.sqrt δ
      ring

end SLEExactGauge

end

end OAI
