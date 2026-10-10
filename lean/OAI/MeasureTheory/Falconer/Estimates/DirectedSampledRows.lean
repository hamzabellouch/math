import OAI.MeasureTheory.Falconer.Estimates.DirectedPacketRows

namespace OAI

/-! Simultaneous row construction from the actual large subsets of the
coarse cells. Cardinality and regularity use a common explicit budget. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem directed_sampled_packet_rows (n : ℕ) {s t KI KP ρ D c b : ℝ}
    (hs : 0 ≤ s) (hst : s < t) (hKI : 0 ≤ KI) (hKP : 0 ≤ KP) (hρ : 0 < ρ)
    (hc : |c| ≤ 1) (hD : 0 ≤ D) (hbudget : projectedSubsetSampleConstant n s t KI KP ρ ≤ D)
    (Y : Finset ℝ) (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
    (S : Finset (Space 2))
    (hdata : ∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧ A y ⊆ S ∧
      ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
      (∀ p ∈ P y, |p 0-y| ≤ 1/(2:ℝ)^n ∧ |p 1-a y| ≤ 1/(2:ℝ)^n) ∧
      planarProjectionEnergy n s c ((P y).image (localPacketPoint (1/(2:ℝ)^n) y (a y))) ≤
        2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) :
    let Δ := 1/(2:ℝ)^n
    let α := Δ/4
    ∃ R : ℝ → Finset (Space 2), ∀ y ∈ Y,
      (R y).Nonempty ∧ FiniteSeparatedAt Δ (R y) ∧
      NormalizedFiniteBallBound Δ s D (R y) ∧
      1 ≤ D*α^s*((R y).card:ℝ) ∧ (R y).card ≤ Nat.ceil (α^(-s)) ∧
      ∀ x ∈ R y, x 0 = y ∧ ∃ p ∈ S, p 1+c*p 0-b = Δ*x 1 ∧ |p 0-x 0| ≤ Δ := by
  dsimp only
  let Δ := 1/(2:ℝ)^n
  let α := Δ/4
  let K := projectedSubsetSampleConstant n s t KI KP ρ
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have h4 : (1:ℝ) ≤ (4:ℝ)^s := Real.one_le_rpow (by norm_num) hs
  have h4p : 0 < (4:ℝ)^s := Real.rpow_pos_of_pos (by norm_num) _
  have hK : K/(4:ℝ)^s ≤ D := (div_le_iff₀ h4p).2
    (hbudget.trans (le_mul_of_one_le_right hD h4))
  have hlocal (y : ℝ) (hy : y ∈ Y) := directed_local_packet_row n (c := c) (b := b) hs hst hKI hKP hρ hc
    (P y) (A y) (hdata y hy).1 (hdata y hy).2.1 (hdata y hy).2.2.2.1
    (hdata y hy).2.2.2.2.1 (hdata y hy).2.2.2.2.2
  let R : ℝ → Finset (Space 2) := fun y =>
    if hy : y ∈ Y then Classical.choose (hlocal y hy) else ∅
  refine ⟨R,?_⟩
  intro y hy
  have hr := Classical.choose_spec (hlocal y hy)
  have heR : R y = Classical.choose (hlocal y hy) := dite_eq_left hy
  rw [← heR] at hr
  obtain ⟨hne,hcard,hsep,hreg,hlow,hrep⟩ := hr
  have hcoef : (K/(4:ℝ)^s)*Δ^s = K*α^s := by
    have he : Δ = 4*α := by dsimp [α]; ring
    rw [he,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hα.le]
    field_simp
  have hlow' : 1 ≤ K*α^s*((R y).card:ℝ) := by
    change 1 ≤ (K/(4:ℝ)^s)*Δ^s*((R y).card:ℝ) at hlow
    rwa [hcoef] at hlow
  refine ⟨hne,hsep,?_,?_,hcard,?_⟩
  · intro z r hdr hr1
    have hr0 : 0 ≤ r := hΔ.le.trans hdr
    exact (hreg z r hdr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hr0 _)) (Nat.cast_nonneg _))
  · exact hlow'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg hα.le _)) (Nat.cast_nonneg _))
  · intro x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := hrep x hx
    exact ⟨hx0,p,(hdata y hy).2.2.1 hp,hp1,hp0⟩

end Falconer

end OAI
