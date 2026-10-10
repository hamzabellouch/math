import OAI.NumberTheory.CubicMoment.Estimates.DivisorCoefficient

namespace OAI

/-! The dyads used by the divisor Poisson sum are dyads of d*h.
They form an exact finite-fiber partition, with no lost multiplicity. -/
noncomputable section
open scoped BigOperators
open Set
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def divisorFrequencyDyad (d : Eisenstein) (hd : d ≠ 0) (j : ℕ) : Finset Eisenstein :=
  (frequencyDyad j).preimage (fun h => d*h) (fun _ _ _ _ he => mul_left_cancel₀ hd he)

@[simp] lemma mem_divisorFrequencyDyad {d : Eisenstein} {hd : d ≠ 0} {j : ℕ} {h : Eisenstein} :
    h ∈ divisorFrequencyDyad d hd j ↔ d*h ∈ frequencyDyad j := Finset.mem_preimage

lemma divisorFrequencyDyad_card_le (d : Eisenstein) (hd : d ≠ 0) (j : ℕ) :
    (divisorFrequencyDyad d hd j).card ≤ (frequencyDyad j).card := by
  let H := divisorFrequencyDyad d hd j
  have he : H.image (fun h => d*h) ⊆ frequencyDyad j := by
    intro h hh
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hh
    exact mem_divisorFrequencyDyad.mp hx
  have hc : (H.image (fun h => d*h)).card = H.card :=
    Finset.card_image_iff.mpr (fun _ _ _ _ h => mul_left_cancel₀ hd h)
  rw [← hc]
  exact Finset.card_le_card he

lemma divisorFrequencyDyad_norm {d : Eisenstein} {hd : d ≠ 0} {j : ℕ} {h : Eisenstein}
    (hh : h ∈ divisorFrequencyDyad d hd j) :
    (2:ℝ)^j/norm d ≤ norm h ∧ norm h ≤ 2*(2:ℝ)^j/norm d := by
  have hn := frequencyDyad_norm (mem_divisorFrequencyDyad.mp hh)
  rw [norm_mul_eq] at hn
  have hdN := norm_pos_of_ne_zero hd
  constructor
  · exact (div_le_iff₀ hdN).mpr (by simpa only [mul_comm] using hn.1)
  · exact (le_div_iff₀ hdN).mpr (by simpa only [mul_comm] using hn.2)

theorem hasSum_divisorFrequencyDyad (d : Eisenstein) (hd : d ≠ 0)
    (F : Eisenstein → ℂ) (hF : Summable F) (h0 : F 0 = 0) :
    HasSum (fun j : ℕ => ∑ h ∈ divisorFrequencyDyad d hd j, F h) (∑' h : Eisenstein, F h) := by
  have he := hF.hasSum.tsum_fiberwise (fun h : Eisenstein => Nat.log 2 (normNat (d*h)))
  have hf (j : ℕ) : (∑' h : ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}), F h) =
      ∑ h ∈ divisorFrequencyDyad d hd j, F h := by
    rw [tsum_subtype]
    calc
      _ = ∑ h ∈ divisorFrequencyDyad d hd j,
          Set.indicator ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) F h := by
        apply tsum_eq_sum
        intro h hh
        by_cases hz : h = 0
        · subst h
          simp [h0]
        · have hj : Nat.log 2 (normNat (d*h)) ≠ j := fun hj =>
            hh (mem_divisorFrequencyDyad.mpr (mem_frequencyDyad.mpr ⟨mul_ne_zero hd hz,hj⟩))
          exact Set.indicator_of_notMem (show h ∉
            ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) from hj) F
      _ = _ := by
        apply Finset.sum_congr rfl
        intro h hh
        exact Set.indicator_of_mem
          (show h ∈ ((fun h : Eisenstein => Nat.log 2 (normNat (d*h))) ⁻¹' {j}) from
            (mem_frequencyDyad.mp (mem_divisorFrequencyDyad.mp hh)).2) F
  simpa only [hf] using he

end CubicFirstMoment

end

end OAI
