import OAI.NumberTheory.TotientAsymptotic.PerturbationEnclosure
import OAI.NumberTheory.TotientAsymptotic.PointEnclosure
import OAI.NumberTheory.TotientAsymptotic.FullBoxConcentration

namespace OAI

/-! A box crossing a witness-region boundary meets a retained slack slice
or a fixed-deviation band exceptional set. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma join_witness_band_lower {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hη : IsWitness H (theta x) η) (hPH : P H ≤ H) (hHm : H ≤ m x)
    {u : Fin (R x H) → ℝ} (hb : u ∈ prefixBandRegion x H) :
    ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤
      joinCoordinates (R x H) (H-P H) (u,tailVector η) i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [joinCoordinates_left, Fin.val_castAdd] using (hb j).1
  · simp only [joinCoordinates_right, Fin.val_natAdd]
    have hj := j.isLt
    have he : m x-(R x H+j.val+1) = H-1-j.val := by unfold R; omega
    have hm : H-1-j.val ∈ Finset.Ico (P H) H := Finset.mem_Ico.mpr (by omega)
    simpa only [tailVector, bandScale, he, mul_assoc] using (hη.2.2.1 _ hm).2.1

lemma witness_full_cube_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hs : 0 ≤ theta x) (hcut : 4 ≤ lam*(P H : ℝ))
    (hP : 1 ≤ P H) (hPH : P H < H) (hHm : H ≤ m x)
    (hBr : 1 ≤ B x*rho^(m x)) (hη : IsWitness H (theta x) η)
    {u u₀ : Fin (R x H) → ℝ}
    (hu₀ : u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hu : ∀ i, |u₀ i-u i| ≤ 1) {v : Fin (H-P H) → ℝ}
    (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      fullBoxSimplex x (R x H+(H-P H)) ∩ additiveBoxSimplex x (R x H+(H-P H)) := by
  have hN : R x H+(H-P H) < m x := by unfold R; omega
  have hz := join_witness_perturbed_enlarged hη hPH hHm hu₀.1 hu₀.2
  have hlo := join_witness_band_lower hη hPH.le hHm hu₀.2
  have hhi := join_witness_band_upper hη hPH.le hHm hu₀.2
  have hd : ∀ i, |joinCoordinates (R x H) (H-P H) (u₀,tailVector η) i-
      joinCoordinates (R x H) (H-P H) (u,v) i| ≤ 1 := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using hu j
    · simpa only [joinCoordinates_right] using hv j
  refine ⟨point_cube_full_enclosure hN hBr hz hd ?_,
    banded_simplex_cube_additive hN hz hhi hd⟩
  intro i
  exact cube_band_lower hs hcut (by have hi := i.isLt; unfold R at hi; omega) (hlo i) (hd i)

lemma exact_failure_shell {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hB : 0 ≤ B x) (hN : R x H+(H-P H) < m x)
    (hPH : P H ≤ H) (hHm : H ≤ m x)
    {w : Fin (R x H) → ℝ} (hw : w ∉ tailPrefixRegion x H η)
    {y : Fin (R x H+(H-P H)) → ℝ} (hy : y ∈ additiveBoxSimplex x (R x H+(H-P H)))
    (hd : ∀ i, |joinCoordinates (R x H) (H-P H) (w,tailVector η) i-y i| ≤ 1) :
    y ∈ additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  let z := joinCoordinates (R x H) (H-P H) (w,tailVector η)
  by_cases htop : (∑ i, a (i.val+1)*w i) ≤ B x-D (m x) η
  · have hfail : ∃ i, prefixLinear (R x H) w i < D (m x-(i.val+1)) η := by
      by_contra! hall
      exact hw ⟨hall, htop⟩
    obtain ⟨i, hi⟩ := hfail
    have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
        Fin.castAdd (H-P H) i := Fin.ext rfl
    have hzneg : prefixLinear (R x H+(H-P H)) z (Fin.castAdd (H-P H) i) < 0 := by
      rw [joined_witness_prefixLinear η hPH hHm]
      linarith
    have hdiff := (neg_le_abs _).trans (prefixLinear_cube_error z y hd (Fin.castAdd (H-P H) i))
    have hrow := row_cube_error_le_boxSlack hN (Fin.castAdd (H-P H) i)
    simp only [Fin.val_castAdd] at hrow hdiff
    have hstrict : prefixLinear (R x H+(H-P H)) y (Fin.castAdd (H-P H) i) <
        boxSlackError x (i.val+1) := by linarith
    apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i, hy, ?_⟩
    intro hgood
    have hh := hgood.1 (Fin.castLE (Nat.le_add_right _ _) i)
    rw [raiseThreshold, Function.update_self, he] at hh
    simp only [Fin.val_castAdd] at hh
    linarith
  · apply Or.inl
    refine ⟨hy, ?_⟩
    intro hgood
    have hzgt : B x < ∑ j, a (j.val+1)*z j := by
      dsimp [z]
      rw [joined_budget, ← top_D_tailVector η hPH hHm]
      linarith
    have hdiff := (le_abs_self _).trans (prefixBudget_cube_error z y hd)
    have herr := top_cube_error_le_boxTop hB hN.le
    have hh := hgood.2
    linarith

lemma band_endpoint_neighborhood {x : ℝ} {H : ℕ} {u w : Fin (R x H) → ℝ}
    (hw : w ∉ prefixBandRegion x H) (hd : ∀ i, |w i-u i| ≤ 1)
    (hlarge : ∀ i : Fin (R x H), 100 < bandScale x (i.val+1)) :
    ∃ i, u i < (91/100 : ℝ)*bandScale x (i.val+1) ∨
      (109/100 : ℝ)*bandScale x (i.val+1) < u i := by
  change ¬ ∀ i, (9/10 : ℝ)*bandScale x (i.val+1) ≤ w i ∧
    w i ≤ (11/10 : ℝ)*bandScale x (i.val+1) at hw
  push Not at hw
  obtain ⟨i, hi⟩ := hw
  refine ⟨i, ?_⟩
  have hdist := abs_le.mp (hd i)
  have hb := hlarge i
  by_cases hlo : (9/10 : ℝ)*bandScale x (i.val+1) ≤ w i
  · right
    have hh := hi hlo
    linarith
  · left
    have hh := lt_of_not_ge hlo
    linarith

/-- Every point in a crossing box belongs to one of the two already
controlled full-dimensional exceptional regions. -/
theorem witness_boundary_enclosure {x : ℝ} {H : ℕ} {η : TailDatum H}
    (hs : 0 ≤ theta x) (hB : 0 ≤ B x) (hcut : 4 ≤ lam*(P H : ℝ))
    (hP : 1 ≤ P H) (hPH : P H < H) (hHm : H ≤ m x)
    (hBr : 1 ≤ B x*rho^(m x)) (hη : IsWitness H (theta x) η)
    (hlarge : ∀ i : Fin (R x H), 100 < bandScale x (i.val+1))
    {u u₀ w : Fin (R x H) → ℝ}
    (hu₀ : u₀ ∈ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hu : ∀ i, |u₀ i-u i| ≤ 1)
    (hw : w ∉ perturbedTailPrefixRegion x H η ∩ prefixBandRegion x H)
    (hwu : ∀ i, |w i-u i| ≤ 1) {v : Fin (H-P H) → ℝ}
    (hv : ∀ i, |tailVector η i-v i| ≤ 1) :
    joinCoordinates (R x H) (H-P H) (u,v) ∈
      additiveBoxShell x (R x H) (R x H+(H-P H)) (Nat.le_add_right _ _) ∪
        retainedPhaseBad x H (R x H+(H-P H)) (Nat.le_add_right _ _) := by
  have hy := witness_full_cube_enclosure hs hcut hP hPH hHm hBr hη hu₀ hu hv
  by_cases hwb : w ∈ prefixBandRegion x H
  · left
    have hwt : w ∉ tailPrefixRegion x H η := fun ht =>
      hw ⟨banded_tailRegion_subset_perturbed η hB ⟨ht, hwb⟩, hwb⟩
    apply exact_failure_shell hB (by unfold R; omega) hPH.le hHm hwt hy.2
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [joinCoordinates_left] using hwu j
    · simpa only [joinCoordinates_right] using hv j
  · right
    obtain ⟨i, hi⟩ := band_endpoint_neighborhood hwb hwu hlarge
    change _ ∈ ⋃ i : Fin (R x H), fullBoxSimplex x _ ∩
      phaseCoordinateBad x (Fin.castLE (Nat.le_add_right _ _) i)
    refine Set.mem_iUnion.mpr ⟨i, hy.1, ?_⟩
    have he : Fin.castLE (Nat.le_add_right (R x H) (H-P H)) i =
        Fin.castAdd (H-P H) i := Fin.ext rfl
    change _ < _ ∨ _ < _
    rw [he, joinCoordinates_left]
    simpa only [Fin.val_castAdd] using hi

end TotientAsymptotic

end

end OAI
