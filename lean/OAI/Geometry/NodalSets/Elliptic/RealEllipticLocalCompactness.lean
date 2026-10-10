import OAI.Geometry.NodalSets.Elliptic.CompactFamilyPointwiseEstimate
import OAI.Geometry.NodalSets.Elliptic.RealSmoothLocalCompactness

namespace OAI

namespace Yau.Geometry
open Yau.Analysis Set Metric Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem real_elliptic_local_subsequence
    (C : T → Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (V : T → Yau.Jets.Coord → ℝ)
    (hC : ∀ t i j, ContDiff ℝ ∞ (fun x ↦ C t x i j)) (hV : ∀ t, ContDiff ℝ ∞ (V t))
    (hs : ∀ t x i j, C t x i j=C t x j i) (hp : ∀ t x, (C t x).PosDef)
    (hCjoint : ∀ i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ C z.1 x i j) ds z.2))
    (hVjoint : ∀ ds, Continuous (fun z : T × Yau.Jets.Coord ↦ partialJet (V z.1) ds z.2))
    (t : ℕ → T) (W : ℕ → Yau.Jets.Coord → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (he : ∀ j x, Yau.coordDiv (realMatrixFlux (C (t j)) (W j)) x+V (t j) x*W j x=0)
    (hL2 : ∀ R : ℕ, ∃ D ≥ 0, ∀ j, (∫ z in closedBall (0 : Yau.Jets.Coord) ((R:ℝ)+2), W j z^2) ≤ D) :
    ∃ v : Yau.Jets.Coord → ℝ, ContDiff ℝ ∞ v ∧ ∃ nu : ℕ → ℕ, StrictMono nu ∧
      (∀ ds (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ partialJet (W (nu j)) ds) (partialJet v ds) atTop Q) ∧
      (∀ n (Q : Set Yau.Jets.Coord), IsCompact Q →
        TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (W (nu j)))
          (iteratedFDeriv ℝ n v) atTop Q) := by
  apply real_smooth_local_subsequence W hW
  intro R n
  obtain ⟨K,hK,hest⟩ := compact_family_pointwise_estimate n C V 0 (R:ℝ) (by positivity)
    hC hV hs (fun t x _ ↦ hp t x)
    (fun i j ds _ ↦ (hCjoint i j ds).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun ds _ ↦ (hVjoint ds).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  obtain ⟨D,hD,hsize⟩ := hL2 R
  refine ⟨Real.sqrt (K*D),Real.sqrt_nonneg _,?_⟩
  intro j ds hd x hx
  have hh := (hest (t j) (W j) (hW j) (he j) ds hd x hx).trans
    (mul_le_mul_of_nonneg_left (hsize j) hK.le)
  simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt hh

end
end Yau.Geometry

end OAI
