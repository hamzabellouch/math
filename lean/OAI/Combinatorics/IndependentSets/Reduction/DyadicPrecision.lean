import Mathlib
import OAI.Combinatorics.IndependentSets.Reduction.RowBitsEquiv

namespace OAI

namespace LargeIndependentSets.BooleanJunta
open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal ENNReal Topology

lemma exists_dyadic_precision (n : ℕ) (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ m : ℕ, (L*(1/2:ℝ)^m)^2 < u/16 ∧ (n:ℝ)*m*(L*(1/2:ℝ)^m) < 1 := by
  have hp : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : Tendsto (fun m : ℕ => (L*(1/2:ℝ)^m)^2) atTop (𝓝 0) := by
    simpa using (hp.const_mul (L:ℝ)).pow 2
  have hn : Tendsto (fun m : ℕ => (n:ℝ)*m*(L*(1/2:ℝ)^m)) atTop (𝓝 0) := by
    have h := (tendsto_self_mul_const_pow_of_lt_one (r:=(1/2:ℝ)) (by norm_num) (by norm_num)).const_mul ((n:ℝ)*L)
    convert h using 1 <;> (try funext m) <;> ring_nf
  exact ((he.eventually_lt_const (by positivity : 0 < u/16)).and
    (hn.eventually_lt_const (by norm_num : (0:ℝ)<1))).exists

lemma cubeSampler_mix {n m : ℕ} (S : Finset (Fin n))
    (p q : Fin n → Cube m × ℝ) :
    cubeSampler (ProductAveraging.mix S (p,q)) =
      ProductAveraging.mix S (cubeSampler p,cubeSampler q) := by
  funext i
  by_cases hi : i ∈ S <;> simp [cubeSampler, ProductAveraging.mix, hi]

lemma seed_average_eq {n m : ℕ} (S : Finset (Fin n))
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) (p : Fin n → Cube m × ℝ) :
    ProductAveraging.average (seedLaw m) S (f ∘ cubeSampler) p =
      ProductAveraging.average unitLaw S f (cubeSampler p) := by
  unfold ProductAveraging.average
  simp only [Function.comp_def, cubeSampler_mix]
  have hm : Measurable (fun y : Fin n → ℝ => f (ProductAveraging.mix S (cubeSampler p,y))) :=
    hf.comp ((ProductAveraging.mix_measurable S).comp (measurable_const.prodMk measurable_id))
  exact ProductAveraging.integral_preserving (cubeSampler_preserving n m) hm.aestronglyMeasurable

theorem real_cube_junta_uniform (L : ℝ≥0) {u : ℝ} (hu : 0 < u) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ n : ℕ, ∀ f : (Fin n → ℝ) → ℝ,
      LipschitzWith L f → (∀ x, |f x| ≤ 1) →
      ∃ S : Finset (Fin n), S.card ≤ J ∧
        Integrable (fun x => (f x-ProductAveraging.average unitLaw S f x)^2) (unitCubeLaw n) ∧
        (∫ x, (f x-ProductAveraging.average unitLaw S f x)^2 ∂unitCubeLaw n) < u := by
  obtain ⟨J,hJ,H⟩ := rows_junta_uniform (L:=(L:ℝ)+1) (u:=u/16) (by positivity) (by positivity)
  refine ⟨J,hJ,?_⟩
  intro n f hf hb
  obtain ⟨m,hmerr,hminf⟩ := exists_dyadic_precision n L hu
  have hI : (∑ i, ∑ k, rowInfluence (f ∘ cellPoint (n:=n) (m:=m)) i k) ≤ (L:ℝ)+1 :=
    (total_rowInfluence_cell_bound hf hb).trans (by linarith)
  obtain ⟨S,hS,g,hg,hdep,he⟩ := H n m (f ∘ cellPoint) (fun x => hb _) hI
  let F : (Fin n → Cube m × ℝ) → ℝ := f ∘ cubeSampler
  let G : (Fin n → Cube m × ℝ) → ℝ := fun p => g (fun i => (p i).1)
  let C : (Fin n → Cube m × ℝ) → ℝ := fun p => f (cellPoint (fun i => (p i).1))
  have hFm : Measurable F := hf.continuous.measurable.comp (cubeSampler_preserving n m).measurable
  have hGm : Measurable G := (measurable_of_countable g).comp (cells_preserving n m).measurable
  have hCm : Measurable C := (measurable_of_countable (f ∘ cellPoint)).comp (cells_preserving n m).measurable
  have hFb : ∀ p, |F p| ≤ 1 := fun p => hb _
  have hGb : ∀ p, |G p| ≤ 1 := fun p => hg _
  have hCb : ∀ p, |C p| ≤ 1 := fun p => hb _
  have herr (a b : ℝ) (ha : |a| ≤ 1) (hb : |b| ≤ 1) : |a-b| ≤ 2 :=
    (abs_sub a b).trans (by linarith)
  have hij : Integrable (fun p => (F p-G p)^2) (seedCubeLaw n m) :=
    ProductAveraging.bounded_sq_integrable (hFm.sub hGm) (fun p => herr _ _ (hFb p) (hGb p))
  have hic : Integrable (fun p => (C p-G p)^2) (seedCubeLaw n m) :=
    ProductAveraging.bounded_sq_integrable (hCm.sub hGm) (fun p => herr _ _ (hCb p) (hGb p))
  have hice : (∫ p, (C p-G p)^2 ∂seedCubeLaw n m) = 𝔼 q, (f (cellPoint q)-g q)^2 := by
    calc
      _ = ∫ q, (f (cellPoint q)-g q)^2 ∂cellLaw n m :=
        ProductAveraging.integral_preserving (cells_preserving n m) Integrable.of_finite.aestronglyMeasurable
      _ = _ := integral_uniformLaw _
  have herrInt : (∫ p, (F p-G p)^2 ∂seedCubeLaw n m) < u/4 := by
    have hle : (∫ p, (F p-G p)^2 ∂seedCubeLaw n m) ≤
        2*(L*(1/2:ℝ)^m)^2 + 2*(𝔼 q, (f (cellPoint q)-g q)^2) := by
      have hdom : Integrable (fun p => 2*(L*(1/2:ℝ)^m)^2 + 2*(C p-G p)^2) (seedCubeLaw n m) :=
        (integrable_const _).add (hic.const_mul 2)
      have hpt : ∀ᵐ p ∂seedCubeLaw n m, (F p-G p)^2 ≤
          2*(L*(1/2:ℝ)^m)^2+2*(C p-G p)^2 := by
        filter_upwards [sample_cell_error hf] with p hp
        have hp2 : (F p-C p)^2 ≤ (L*(1/2:ℝ)^m)^2 := by
          have hn : 0 ≤ L*(1/2:ℝ)^m := by positivity
          simpa only [sq_abs, F, C, Function.comp_def] using (sq_le_sq₀ (abs_nonneg _) hn).mpr hp
        nlinarith [sq_nonneg ((F p-C p)-(C p-G p))]
      have hn := integral_mono_ae hij hdom hpt
      have him : Integrable (fun p => 2*(C p-G p)^2) (seedCubeLaw n m) := hic.const_mul 2
      rw [integral_add (integrable_const _) him] at hn
      simp only [integral_const_mul, integral_const, measureReal_def, measure_univ,
        ENNReal.toReal_one, one_smul, hice] at hn
      simpa using hn
    dsimp only [Function.comp_def] at he
    linarith
  have hGdep : ∀ p q, (∀ i ∈ S, p i = q i) → G p = G q := by
    intro p q hpq
    exact hdep _ _ (fun i hi => congrArg Prod.fst (hpq i hi))
  have hproj := ProductAveraging.junta_average_error (seedLaw m) S hFm hGm hFb hGb hGdep
  have hAm := ProductAveraging.average_measurable unitLaw S hf.continuous.measurable
  have hAb := ProductAveraging.average_bound unitLaw S hb
  have hfinali : Integrable (fun x => (f x-ProductAveraging.average unitLaw S f x)^2) (unitCubeLaw n) :=
    ProductAveraging.bounded_sq_integrable (hf.continuous.measurable.sub hAm)
      (fun x => herr _ _ (hb x) (hAb x))
  have hfinale : (∫ p, (F p-ProductAveraging.average (seedLaw m) S F p)^2 ∂seedCubeLaw n m) =
      ∫ x, (f x-ProductAveraging.average unitLaw S f x)^2 ∂unitCubeLaw n := by
    simp only [F, seed_average_eq S hf.continuous.measurable]
    exact ProductAveraging.integral_preserving (cubeSampler_preserving n m) hfinali.aestronglyMeasurable
  refine ⟨S,hS,hfinali,?_⟩
  change (∫ p, (F p-ProductAveraging.average (seedLaw m) S F p)^2 ∂seedCubeLaw n m) ≤
    4*(∫ p, (F p-G p)^2 ∂seedCubeLaw n m) at hproj
  rw [hfinale] at hproj
  linarith

end LargeIndependentSets.BooleanJunta

end OAI
