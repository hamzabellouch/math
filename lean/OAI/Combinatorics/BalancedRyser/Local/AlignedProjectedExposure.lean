import OAI.Combinatorics.BalancedRyser.Incidence.AffineInjectionGuards
import OAI.Combinatorics.BalancedRyser.Local.AlignedTokenPointLaw

namespace OAI

namespace Balanced.InjectionExposure

noncomputable section
open scoped Classical

variable {I J Z : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem auxiliaryLaw_fst_mem_completions (K : Finset I) (base : I ↪ J)
    (noise : (I ↪ J) → PMF Z) (x : (I ↪ J) × Z)
    (hx : x ∈ (auxiliaryLaw K base noise).support) : x.1 ∈ completions K base := by
  change x ∈ ((PMF.uniformOfFinset (completions K base)
    (completions_nonempty K base)).bind
      (fun e => (noise e).map (fun z => (e,z)))).support at hx
  rw [PMF.mem_support_bind_iff] at hx
  obtain ⟨e,he,hx⟩ := hx
  rw [PMF.mem_support_map_iff] at hx
  obtain ⟨z,hz,hx⟩ := hx
  have he' : e ∈ completions K base := by simpa using he
  have hf := congrArg Prod.fst hx
  simpa only [← hf] using he'

end
end Balanced.InjectionExposure

namespace Balanced.Local.TokenExposure

open AlignedListProbability PartialAlignment InjectionExposure
noncomputable section
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {b κ : ℕ} {Z : Type*} [Fintype Z]

def pointOutput (P : EqualityPattern b κ) (bits : Bits b) (p : Point F)
    (i : Fin b) (J : Finset (Fin 4)) (hJ : J.card ≤ 1)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (e : DirectionToken b κ ↪ Direction F) (z : Z) (j : Fin 4) : Point F :=
  generatedPositions (tupleDirections P e i) (tupleDirections_adjacent P e i)
    (bits i) (e (Sum.inl i)) (tupleDirections_ne_target P e i)
    (lineEval (e (Sum.inl i)) p) J hJ (a z) (x z) j

theorem projected_left_probability_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  let l : Z → Line F := fun z => (base (Sum.inr (P.classOf i j)), a z j (bits i j))
  have h := auxiliary_guarded_projection_probability_le K base (Sum.inl i) htarget
    noise hnoise (fun _ => p) l m
  apply le_trans _ h
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ez hez
    have he := (mem_completions K base ez.1).mp
      (auxiliaryLaw_fst_mem_completions K base noise ez hez.2)
    have hd : tupleDirections P ez.1 i j = base (Sum.inr (P.classOf i j)) :=
      he _ hold
    have hp : pointOutput P bits p i J hJ a x ez.1 ez.2 j =
        lineIntersection (l ez.2) (lineThrough (ez.1 (Sum.inl i)) p) := by
      change generatedPositions _ _ _ _ _ _ _ _ _ _ j = _
      rw [generatedPositions_old_left _ _ _ _ _ _ J hJ _ _ j hj]
      rw [hd]
      rfl
    have hne : ez.1 (Sum.inl i) ≠ (l ez.2).1 := by
      change ez.1 (Sum.inl i) ≠ base (Sum.inr (P.classOf i j))
      rw [← hd]
      exact (tupleDirections_ne_target P ez.1 i j).symm
    exact ⟨by simpa only [l, hd] using hez.1.1, hne,
      by simpa only [hp] using hez.1.2.1,
      by simpa only [hp] using hez.1.2.2⟩

theorem projected_right_probability_le
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      1 / ((Fintype.card F + 1 - K.card : ℕ) : ℝ) := by
  let l : Z → Line F := fun z =>
    (base (Sum.inr (P.classOf i (j+1))), a z (j+1) (!(bits i (j+1))))
  have h := auxiliary_guarded_projection_probability_le K base (Sum.inl i) htarget
    noise hnoise (fun _ => p) l m
  apply le_trans _ h
  apply ENNReal.toReal_mono
  · rw [PMF.toOuterMeasure_apply]
    exact PMF.tsum_coe_indicator_ne_top _ _
  · apply PMF.toOuterMeasure_mono
    intro ez hez
    have he := (mem_completions K base ez.1).mp
      (auxiliaryLaw_fst_mem_completions K base noise ez hez.2)
    have hd : tupleDirections P ez.1 i (j+1) = base (Sum.inr (P.classOf i (j+1))) :=
      he _ hold
    have hp : pointOutput P bits p i J hJ a x ez.1 ez.2 j =
        lineIntersection (l ez.2) (lineThrough (ez.1 (Sum.inl i)) p) := by
      change generatedPositions _ _ _ _ _ _ _ _ _ _ j = _
      rw [generatedPositions_old_right _ _ _ _ _ _ J hJ _ _ j hj]
      rw [hd]
      rfl
    have hne : ez.1 (Sum.inl i) ≠ (l ez.2).1 := by
      change ez.1 (Sum.inl i) ≠ base (Sum.inr (P.classOf i (j+1)))
      rw [← hd]
      exact (tupleDirections_ne_target P ez.1 i (j+1)).symm
    exact ⟨by simpa only [l, hd] using hez.1.1, hne,
      by simpa only [hp] using hez.1.2.1,
      by simpa only [hp] using hez.1.2.2⟩

theorem projected_left_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i j) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i j, a ez.2 j (bits i j)) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (projected_left_probability_le P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

theorem projected_right_probability_le_two_div
    (P : EqualityPattern b κ) (bits : Bits b) (p : Point F) (i : Fin b)
    (J : Finset (Fin 4)) (hJ : J.card ≤ 1) (j : Fin 4) (hj : j+1 ∈ J)
    (K : Finset (DirectionToken b κ)) (base : DirectionToken b κ ↪ Direction F)
    (htarget : Sum.inl i ∉ K) (hold : Sum.inr (P.classOf i (j+1)) ∈ K)
    (noise : (DirectionToken b κ ↪ Direction F) → PMF Z)
    (hnoise : DependsOnExposed K noise)
    (a : Z → Fin 4 → Bool → F)
    (x : Z → {j : Fin 4 // j ∈ freePositions J} → F)
    (m : Z → Line F) (hK : K.card ≤ 5 * b)
    (hb : 10 * b ≤ Fintype.card F) :
    ((auxiliaryLaw K base noise).toOuterMeasure
      {ez | (tupleDirections P ez.1 i (j+1), a ez.2 (j+1) (!(bits i (j+1)))) ≠ m ez.2 ∧
        pointOutput P bits p i J hJ a x ez.1 ez.2 j ≠ p ∧
        OnLine (pointOutput P bits p i J hJ a x ez.1 ez.2 j) (m ez.2)}).toReal ≤
      2 / (Fintype.card F : ℝ) := by
  exact (projected_right_probability_le P bits p i J hJ j hj K base
    htarget hold noise hnoise a x m).trans
    (inverse_remaining_le_two_div (Fintype.card F) K.card b
      Fintype.card_pos hK hb)

end
end Balanced.Local.TokenExposure

end OAI
