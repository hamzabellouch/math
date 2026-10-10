import OAI.MeasureTheory.Falconer.Geometry.TripleGridRounding
import OAI.MeasureTheory.Falconer.Incidence.TransverseTubeCount

namespace OAI

/-! # A finite ball cover of an actual three-direction tube intersection -/

namespace Falconer
open Set Metric

theorem physical_three_tube_cover (e : Space 3 ≃L[ℝ] Space 3)
    (he : ‖e.toContinuousLinearMap‖ ≤ 3) (v : Fin 3 → Space 3)
    (hv : ∀ i, ‖v i‖ = 1)
    (haxis : ∀ i j : Fin 3, j ≠ i → (e.symm (v i)) j = 0)
    (E : Set (Space 3)) (A : Fin 3 → Finset (Space 3)) (R : ℝ)
    (hE : ∀ x ∈ E, ‖x‖ ≤ R) {δ C : ℝ} (hδ : 0 < δ)
    (L : ℕ) (hL : ‖e.symm.toContinuousLinearMap‖*(C+5)+1/2 ≤ (L:ℝ))
    (hcover : ∀ i : Fin 3, ∀ x ∈ E, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (x-a)‖ ≤ C*δ) :
    ∃ P : Finset (Space 3), (∀ x ∈ E, ∃ p ∈ P, dist x p ≤ 5*δ) ∧
      (P.card:ℝ)^2 ≤ ((A 0).card:ℝ)*((A 1).card:ℝ)*((A 2).card:ℝ)*(2*(L:ℝ)+1)^6 := by
  classical
  let E' := e.symm '' E
  obtain ⟨N,hN⟩ := exists_nat_ge (‖e.symm.toContinuousLinearMap‖*R/δ+1)
  have hE' : ∀ y ∈ E', ‖y‖ ≤ ‖e.symm.toContinuousLinearMap‖*R := by
    rintro y ⟨x,hx,rfl⟩
    exact (e.symm.toContinuousLinearMap.le_opNorm x).trans
      (mul_le_mul_of_nonneg_left (hE x hx) (norm_nonneg _))
  let S := roundedTripleGrid E' δ N
  have hclose (y : Space 3) :
      dist (e y) (e (tripleGridPoint δ (tripleRound δ y))) ≤ 5*δ := by
    calc
      _ = ‖e (y-tripleGridPoint δ (tripleRound δ y))‖ := by rw [dist_eq_norm,map_sub]
      _ ≤ ‖e.toContinuousLinearMap‖*‖y-tripleGridPoint δ (tripleRound δ y)‖ :=
        e.toContinuousLinearMap.le_opNorm _
      _ ≤ 3*(3*δ/2) := by
        apply mul_le_mul he
          (by simpa only [dist_eq_norm] using tripleRound_distance hδ y)
          (norm_nonneg _) (by norm_num)
      _ ≤ _ := by linarith
  have hgrid : ∀ i : Fin 3, ∀ z ∈ S, ∃ a ∈ A i,
      ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)‖ ≤ (C+5)*δ := by
    intro i z hz
    obtain ⟨y,hy,hz'⟩ := roundedTripleGrid_original hz
    obtain ⟨x,hx,rfl⟩ := hy
    obtain ⟨a,ha,hta⟩ := hcover i x hx
    have hd := hclose (e.symm x)
    rw [e.apply_symm_apply,hz',dist_comm] at hd
    have herr : ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
        perpendicularPart (v i) (x-a)‖ ≤ 5*δ := by
      rw [← perpendicularPart_sub,sub_sub_sub_cancel_right]
      exact (norm_perpendicularPart_le (hv i) _).trans (by simpa only [dist_eq_norm] using hd)
    refine ⟨a,ha,?_⟩
    calc
      _ = ‖(perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
          perpendicularPart (v i) (x-a))+perpendicularPart (v i) (x-a)‖ := by congr 1; abel
      _ ≤ ‖perpendicularPart (v i) (e (tripleGridPoint δ z)-a)-
          perpendicularPart (v i) (x-a)‖+‖perpendicularPart (v i) (x-a)‖ := norm_add_le _ _
      _ ≤ 5*δ+C*δ := add_le_add herr hta
      _ = _ := by ring
  let P := S.image (fun z => e (tripleGridPoint δ z))
  refine ⟨P,?_,?_⟩
  · intro x hx
    have hy : e.symm x ∈ E' := mem_image_of_mem _ hx
    have hz : tripleRound δ (e.symm x) ∈ S := roundedTripleGrid_mem hδ N hN hE' hy
    refine ⟨e (tripleGridPoint δ (tripleRound δ (e.symm x))),Finset.mem_image.mpr ⟨_,hz,rfl⟩,?_⟩
    simpa only [e.apply_symm_apply] using hclose (e.symm x)
  · have hcard : (P.card:ℝ) ≤ S.card := by exact_mod_cast Finset.card_image_le
    exact (pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2).trans
      (transverse_grid_tube_count e v A S hδ haxis L hL hgrid)

end Falconer

end OAI
