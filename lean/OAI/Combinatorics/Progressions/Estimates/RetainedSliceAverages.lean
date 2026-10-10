import OAI.Combinatorics.Progressions.Probability.PositiveDensityRetained

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem retained_fiber_condition_mean_ge {X R : Type*} [Fintype X] [Fintype R] [DecidableEq X]
    (p : FiniteProbabilityWeights X) (F : X → R) (w : X → ℝ) (η : ℝ) (r : R)
    (hr : r ∉ p.lowWeightFibers F w η)
    (hG : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    η ≤ (p.condition (Finset.univ.filter (fun x => F x = r)) hG).mean w := by
  have hb : 0 < (p.fiberLaw F).weight r := by rw [fiberLaw_weight_eq_mass]; exact hG
  calc
    η ≤ p.fiberMean F r w / (p.fiberLaw F).weight r := p.retained_fiber_weight_mean_ge F w η r hr hb
    _ = _ := by
      rw [fiberMean_eq_mass_mul_condition p F r w hG, fiberLaw_weight_eq_mass]
      field_simp [hG.ne']

theorem retained_embedding_mean_ge {X Y R : Type*} [Fintype X] [Fintype Y] [Fintype R]
    [DecidableEq X] [Nonempty X]
    (F : X → R) (w : X → ℝ) (η : ℝ) (r : R) (e : Y ↪ X)
    (hr : r ∉ (uniform X).lowWeightFibers F w η)
    (hcell : finiteEmbeddingRange e = Finset.univ.filter (fun x => F x = r))
    (hG : 0 < (uniform X).mass (finiteEmbeddingRange e)) : η ≤ 𝔼 y, w (e y) := by
  rw [← uniform_condition_embedding_mean e hG w]
  have hG' : 0 < (uniform X).mass (Finset.univ.filter (fun x => F x = r)) := by rw [← hcell]; exact hG
  have h := (uniform X).retained_fiber_condition_mean_ge F w η r hr hG'
  simpa only [← hcell] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem retained_cubeSlice_mean_ge {q : ℕ} {R : Type*} [Fintype R]
    (s : FiniteCubeSlice q) (P : Set ℤ) [Finite P] [Nonempty (SupportedCube q P)]
    (hP : Set.Ico s.root (s.root + s.length) ⊆ P)
    (F : SupportedCube q P → R) (w : (Option (Fin q) → ℤ) → ℝ) (η : ℝ) (r : R)
    (hr : r ∉ (FiniteProbabilityWeights.uniform (SupportedCube q P)).lowWeightFibers
      F (fun x => w (supportedCubeCoordinates x.val)) η)
    (hcell : cubeSliceEvent s P = Finset.univ.filter (fun x => F x = r))
    (hG : 0 < (FiniteProbabilityWeights.uniform (SupportedCube q P)).mass (cubeSliceEvent s P)) :
    η ≤ 𝔼 x : s.Domain, w (s.coordinates x) := by
  have he := cubeSliceEmbedding_range s P hP
  apply FiniteProbabilityWeights.retained_embedding_mean_ge
    F (fun x => w (supportedCubeCoordinates x.val)) η r (cubeSliceEmbedding s P hP) hr
  · exact he.trans hcell
  · rw [he]
    exact hG

theorem retained_coefficientSlice_mean_ge {R : Type*} [Fintype R]
    (s : FiniteCoefficientSlice) (P : Set ℤ) [Fintype P] [Nonempty P]
    (hstride : s.stride ≠ 0) (hP : ∀ x : s.Domain, s.value x ∈ P)
    (F : P → R) (w : ℤ → ℝ) (η : ℝ) (r : R)
    (hr : r ∉ (FiniteProbabilityWeights.uniform P).lowWeightFibers F (fun x => w x.val) η)
    (hcell : coefficientSliceEvent s P = Finset.univ.filter (fun x => F x = r))
    (hG : 0 < (FiniteProbabilityWeights.uniform P).mass (coefficientSliceEvent s P)) :
    η ≤ 𝔼 x : s.Domain, w (s.value x) := by
  have he := coefficientSliceEmbedding_range s P hstride hP
  apply FiniteProbabilityWeights.retained_embedding_mean_ge
    F (fun x => w x.val) η r (coefficientSliceEmbedding s P hstride hP) hr
  · exact he.trans hcell
  · rw [he]
    exact hG

end Erdos3

end

end OAI
