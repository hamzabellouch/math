import Mathlib
import OAI.Computability.VertexCover.Reduction.SeparatorContinuousSumOdd
import OAI.Computability.VertexCover.Analysis.CanonicalGradientValid
import OAI.Computability.VertexCover.Analysis.BlockLawNegInvariant

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.GridCoupling
open MeasureTheory ProbabilityTheory

theorem block_measurePreserving {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) (hp : 0 < p) :
    MeasurePreserving (fun s : ι → κ → ℝ => fun j k => index p hp (s j k))
      (VertexCover.Cube.blockLaw ι κ)
      (uniformOn (Set.univ : Set (ι → κ → Fin p))) := by
  classical
  let : NeZero p := ⟨hp.ne'⟩
  have h := VertexCover.Product.piMap_measurePreserving (ι := ι)
    (VertexCover.Cube.law κ) (uniformOn (Set.univ : Set (κ → Fin p)))
    (fun s : κ → ℝ => fun k => index p hp (s k)) (vector_measurePreserving p hp)
  simpa only [pi_uniformOn_univ, VertexCover.Cube.blockLaw] using h

theorem block_rounding_error_ae {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ℕ) (hp : 0 < p) :
    ∀ᵐ s ∂VertexCover.Cube.blockLaw ι κ, ∀ j k,
      |s j k - midpoint p (index p hp (s j k))| ≤ 1/p := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  have h1 := measurePreserving_eval (fun _ : ι => VertexCover.Cube.law κ) j
  have h2 := measurePreserving_eval (fun _ : κ => VertexCover.Cube.intervalLaw) k
  exact (h2.comp h1).quasiMeasurePreserving.ae (rounding_error_ae p hp)

theorem midpoint_eq_gridRational (d : ℕ) (i : Fin (2*d+1)) :
    midpoint (2*d+1) i = (VertexCover.LabelCover.gridRational d i : ℝ) := by
  have hn : (2*(d:ℝ)+1) ≠ 0 := by positivity
  simp only [midpoint, VertexCover.LabelCover.gridRational]
  push_cast
  field_simp
  ring
end VertexCover.GridCoupling

namespace VertexCover.LabelCover
open MeasureTheory ProbabilityTheory

noncomputable def continuousSumCLM (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    (Fin d → Fin (Φ.WeightDimension d) → ℝ) →L[ℝ] (Φ.Coordinate d → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := Φ.continuousSum seed
    map_add' := by
      intro s t
      simp only [continuousSum, Pi.add_apply, Φ.increment_add, Finset.sum_add_distrib]
    map_smul' := by
      intro a s
      change (∑ j, Φ.increment (Φ.query seed j) (fun k => a*s j k)) = _
      simp only [Φ.increment_mul]
      ext p
      simp [continuousSum, Finset.mul_sum]
  }

theorem separator_continuousSum_continuous (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    Continuous (fun s => Φ.separator A hA (Φ.continuousSum seed s)) :=
  (Φ.separator_continuous A hA).comp (Φ.continuousSumCLM seed).continuous

theorem separator_continuousSum_mean_zero (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    (∫ s, Φ.separator A hA (Φ.continuousSum seed s)
      ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d))) = 0 := by
  have h := integral_neg_eq_self
    (fun s => Φ.separator A hA (Φ.continuousSum seed s))
    (VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)))
  simp only [Φ.separator_continuousSum_odd, integral_neg] at h
  linarith

noncomputable def roundedVertex (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (s : Fin d → Fin (Φ.WeightDimension d) → ℝ) : Φ.Vertex d :=
  (seed, fun j k => VertexCover.GridCoupling.index (2*d+1) (by omega) (s j k))

theorem separator_rounding_error_ae (Φ : LabelCover) {d : ℕ}
    (A : Finset (Φ.Coordinate d → ℝ)) (hA : A.Nonempty) (seed : Φ.Seeds d) :
    ∀ᵐ s ∂VertexCover.Cube.blockLaw (Fin d) (Fin (Φ.WeightDimension d)),
      |Φ.separator A hA (Φ.continuousSum seed s) -
        Φ.separator A hA (Φ.sumVector (Φ.roundedVertex seed s))| ≤
          (d:ℝ)/(2*d+1) := by
  filter_upwards [VertexCover.GridCoupling.block_rounding_error_ae
    (ι := Fin d) (κ := Fin (Φ.WeightDimension d)) (2*d+1) (by omega)] with s hs
  apply (Φ.separator_lipschitz A hA _ _).trans
  rw [Φ.sumVector_eq_continuousSum]
  have h := Φ.continuousSum_close seed s
    (fun j k => (gridRational d ((Φ.roundedVertex seed s).2 j k) : ℝ))
    (b := 1/(2*d+1)) (by positivity) (by
      intro j k
      simpa only [roundedVertex, ← VertexCover.GridCoupling.midpoint_eq_gridRational,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hs j k)
  simpa only [div_eq_mul_inv, one_mul, roundedVertex] using h

end VertexCover.LabelCover

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
