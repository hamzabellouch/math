import OAI.MeasureTheory.Falconer.Geometry.ScalarRuzsaCovering
import OAI.MeasureTheory.Falconer.Estimates.ScalarMixedRefinement

namespace OAI

/-! A small mixed sumset covers the other factor by few short intervals,
with centers and radius in the original scalar coordinates. -/
namespace Falconer
open scoped Pointwise

 theorem scalar_small_sum_cover {δ R z c M K : ℝ} (hδ : 0 < δ)
    (hR : δ ≤ R) (hc : c ≠ 0) (hM : |c⁻¹| ≤ M)
    (F Y : Finset ℝ) (hF : F.Nonempty)
    (hsep : ∀ x ∈ F, ∀ y ∈ F, x ≠ y → δ ≤ |x-y|)
    (hlocal : ∀ x ∈ F, |x-z| ≤ R)
    (hsum : ((scalarCells δ (F+Y.image (fun y => c*y))).card:ℝ) ≤ K*(F.card:ℝ)) :
    ∃ Q : Finset ℝ, (Q.card:ℝ) ≤ 2*K ∧
      ∀ y ∈ Y, ∃ q ∈ Q, |y-q| ≤ 4*M*R := by
  classical
  have hcard : (scalarCells δ F).card = F.card :=
    Finset.card_image_of_injOn (scalarCells_injective hδ hsep)
  have hs : ((scalarCells δ (Y.image (fun y => c*y)+F)).card:ℝ) ≤
      K*(scalarCells δ F).card := by
    rwa [add_comm,hcard]
  obtain ⟨D,hD,hDcard,hcover⟩ := scalar_ruzsa_covering hδ _ F hF hs
  refine ⟨D.image (fun d => d/c),?_,?_⟩
  · exact (Nat.cast_le.mpr (Finset.card_image_le (s := D))).trans hDcard
  · intro y hy
    obtain ⟨d,hd,u,hu,v,hv,he⟩ := hcover (c*y) (Finset.mem_image_of_mem _ hy)
    refine ⟨d/c,Finset.mem_image_of_mem _ hd,?_⟩
    have huv : |u-v| ≤ 2*R := by
      have hh := abs_sub_le u z v
      rw [abs_sub_comm z v] at hh
      linarith [hlocal u hu,hlocal v hv]
    have hcy : |c*y-d| ≤ 4*R := by
      have hh := abs_sub_le (c*y) (d+(u-v)) d
      have heq : d+(u-v)-d = u-v := by ring
      rw [heq] at hh
      linarith
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
    have heq : y-d/c = c⁻¹*(c*y-d) := by field_simp
    rw [heq,abs_mul]
    exact (mul_le_mul hM hcy (abs_nonneg _) hM0).trans_eq (by ring)

end Falconer

end OAI
