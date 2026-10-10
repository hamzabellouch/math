import OAI.Analysis.LipschitzHilbert.Trees.SourceGramSchur

namespace OAI

/-! Apply the finite Gram-matrix estimate to actual planar Schwartz
functions and their product-Lebesgue square integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

theorem planar_toL2_norm_sq (f : SchwartzMap (ℝ×ℝ) ℂ) :
    ‖f.toLp 2 (volume.prod volume)‖^2=∫ z, ‖f z‖^2 ∂volume.prod volume := by
  have h := SchwartzMap.inner_toL2_toL2_eq f f (volume.prod volume)
  simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  change ((‖f.toLp 2 (volume.prod volume)‖^2 : ℝ) : ℂ) =
    ∫ x, ((‖f x‖^2 : ℝ) : ℂ) ∂volume.prod volume at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_injective h

theorem planar_sparse_gram_energy {ι : Type*} [Fintype ι]
    (f : ι → SchwartzMap (ℝ×ℝ) ℂ) (near : ι → ι → Prop) (C : ℝ)
    (hsym : ∀ i j, near i j ↔ near j i)
    (hrow : ∀ i, ((Finset.univ.filter fun j => near i j).card:ℝ)≤C)
    (hortho : ∀ i j, ¬near i j →
      (∫ z, inner ℂ (f i z) (f j z) ∂volume.prod volume)=0) :
    (∫ z, ‖∑ i, f i z‖^2 ∂volume.prod volume)≤
      C*∑ i, ∫ z, ‖f i z‖^2 ∂volume.prod volume := by
  have h := sparse_gram_energy (fun i => (f i).toLp 2 (volume.prod volume)) near C hsym hrow
    (fun i j hij => (SchwartzMap.inner_toL2_toL2_eq (f i) (f j) (volume.prod volume)).trans (hortho i j hij))
  have heq : (∑ i, (f i).toLp 2 (volume.prod volume))=
      (∑ i, f i).toLp 2 (volume.prod volume) := by
    exact (map_sum (SchwartzMap.toLpCLM ℂ ℂ 2 (volume.prod volume)) f Finset.univ).symm
  rw [heq,planar_toL2_norm_sq] at h
  simpa only [sum_apply,planar_toL2_norm_sq] using h

end LipschitzHilbert

end

end OAI
