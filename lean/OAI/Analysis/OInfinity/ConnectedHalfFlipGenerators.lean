import OAI.Analysis.WeakInfiniteness.HalfFlipGenerators
import OAI.Analysis.JiangSu.Absorption.ConnectedUnitaryLift

namespace OAI

/-! Connected conjugacy on a dense family of star-polynomial generators
extends to finite subsets. The same witnessing unitary and path are retained. -/
noncomputable section
open scoped TensorProduct
namespace WeakPureInfiniteness

universe u v
variable {D : Type u} {T : Type v} [CStarAlgebra D] [CStarAlgebra T]

theorem connectedConjugacy_of_generators
    (s : ℕ → D) (hs : ∀ i, ‖s i‖ ≤ 1)
    (hdense : DenseRange (cuntzPolynomial s))
    (φ ψ : D →⋆ₐ[ℂ] T)
    (h : ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ u : unitary T, Joined 1 u ∧
      ∀ i < N, ‖(u : T) * φ (s i) * star (u : T) - ψ (s i)‖ < δ) :
    ∀ (K : Finset D) (ε : ℝ), 0 < ε → ∃ u : unitary T, Joined 1 u ∧
      ∀ d ∈ K, ‖(u : T) * φ d * star (u : T) - ψ d‖ < ε := by
  classical
  intro K ε hε
  have happ (d : D) : ∃ c : List (ℕ × Bool) →₀ ℂ,
      ‖d - cuntzPolynomial s c‖ < ε / 8 := by
    obtain ⟨c, hc⟩ := Metric.denseRange_iff.mp hdense d (ε / 8) (by positivity)
    exact ⟨c, by simpa only [dist_eq_norm] using hc⟩
  choose c hc using happ
  let C : ℝ := 1 + ∑ d ∈ K, cuntzPolynomialHomWeight (c d)
  have hC : 0 < C := by
    have hh := Finset.sum_nonneg (fun d (_ : d ∈ K) => cuntzPolynomialHomWeight_nonneg (c d))
    dsimp only [C]
    linarith
  have hdC (d : D) (hd : d ∈ K) : cuntzPolynomialHomWeight (c d) ≤ C := by
    have hb := Finset.single_le_sum (f := fun d => cuntzPolynomialHomWeight (c d))
      (fun _ _ => cuntzPolynomialHomWeight_nonneg _) hd
    dsimp only [C]
    linarith
  let L := K.biUnion (fun d => (c d).support.biUnion (fun w => w.toFinset.image Prod.fst))
  let N := L.sup id + 1
  have hN (d : D) (hd : d ∈ K) (w : List (ℕ × Bool)) (hw : w ∈ (c d).support)
      (ib : ℕ × Bool) (hib : ib ∈ w) : ib.1 < N := by
    have hi : ib.1 ∈ L := Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_biUnion.mpr
      ⟨w, hw, Finset.mem_image.mpr ⟨ib, by simpa using hib, rfl⟩⟩⟩
    exact lt_of_le_of_lt (Finset.le_sup (f := id) hi) (Nat.lt_succ_self _)
  let δ := ε / (4 * C)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  obtain ⟨u, huPath, hu⟩ := h N δ hδ
  let Φ : D →⋆ₐ[ℂ] T := (Unitary.conjStarAlgAut ℂ T u).toStarAlgHom.comp φ
  have hΦ (d : D) : Φ d = (u : T) * φ d * star (u : T) := rfl
  have h1 : ‖Φ 1 - ψ 1‖ ≤ δ := by
    rw [map_one, map_one, sub_self, norm_zero]
    exact hδ.le
  refine ⟨u, huPath, ?_⟩
  intro d hd
  have hpoly : ‖Φ (cuntzPolynomial s (c d)) - ψ (cuntzPolynomial s (c d))‖ ≤
      cuntzPolynomialHomWeight (c d) * δ := by
    apply norm_starHom_cuntzPolynomial_sub_le Φ.toNonUnitalStarAlgHom
      ψ.toNonUnitalStarAlgHom s hs (c d) δ hδ.le h1
    intro w hw ib hib
    exact (hu ib.1 (hN d hd w hw ib hib)).le
  have hm : cuntzPolynomialHomWeight (c d) * δ ≤ ε / 4 := by
    calc
      _ ≤ C * δ := mul_le_mul_of_nonneg_right (hdC d hd) hδ.le
      _ = _ := by dsimp only [δ]; field_simp
  have hf : ‖Φ d - Φ (cuntzPolynomial s (c d))‖ < ε / 8 := by
    rw [← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le Φ.toNonUnitalStarAlgHom _).trans_lt (hc d)
  have hg : ‖ψ (cuntzPolynomial s (c d)) - ψ d‖ < ε / 8 := by
    rw [norm_sub_rev, ← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le ψ.toNonUnitalStarAlgHom _).trans_lt (hc d)
  rw [← hΦ]
  have he : Φ d - ψ d = (Φ d - Φ (cuntzPolynomial s (c d))) +
      (Φ (cuntzPolynomial s (c d)) - ψ (cuntzPolynomial s (c d))) +
      (ψ (cuntzPolynomial s (c d)) - ψ d) := by abel
  rw [he]
  have hb := norm_add₃_le (a := Φ d - Φ (cuntzPolynomial s (c d)))
    (b := Φ (cuntzPolynomial s (c d)) - ψ (cuntzPolynomial s (c d)))
    (c := ψ (cuntzPolynomial s (c d)) - ψ d)
  linarith

theorem connectedHalfFlip_of_generators
    (s : ℕ → D) (hs : ∀ i, ‖s i‖ ≤ 1)
    (hdense : DenseRange (cuntzPolynomial s)) (f : D ⊗[ℂ] D →⋆ₐ[ℂ] T)
    (h : ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ u : unitary T, Joined 1 u ∧
      ∀ i < N, ‖(u : T) * f (s i ⊗ₜ[ℂ] 1) * star (u : T) -
        f (1 ⊗ₜ[ℂ] s i)‖ < δ) : CStarAbsorption.ConnectedApproximateInnerHalfFlip f := by
  let φ : D →⋆ₐ[ℂ] T := f.comp
    { __ := (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] D)
      map_star' := fun a => by simp }
  let ψ : D →⋆ₐ[ℂ] T := f.comp
    { __ := (Algebra.TensorProduct.includeRight : D →ₐ[ℂ] D ⊗[ℂ] D)
      map_star' := fun a => by simp }
  exact connectedConjugacy_of_generators s hs hdense φ ψ h

theorem oInfinity_connectedHalfFlip_of_generators
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] T)
    (h : ∀ (N : ℕ) (δ : ℝ), 0 < δ → ∃ u : unitary T, Joined 1 u ∧
      ∀ i < N, ‖(u : T) * f (oInfinityIsometry i ⊗ₜ[ℂ] 1) * star (u : T) -
        f (1 ⊗ₜ[ℂ] oInfinityIsometry i)‖ < δ) :
    CStarAbsorption.ConnectedApproximateInnerHalfFlip f :=
  connectedHalfFlip_of_generators oInfinityIsometry
    (fun i => norm_isometry_le_one (by rw [oInfinityIsometry_relations, ite_eq_left rfl]))
    oInfinityPolynomial_denseRange f h

end WeakPureInfiniteness

end

end OAI
