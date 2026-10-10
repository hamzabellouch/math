import OAI.MeasureTheory.Falconer.Estimates.CenteredPacketGain

namespace OAI

/-! Assemble the separately selected original cell pencils into one
packet. The pointwise choice preserves the common original tube cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_gain_from_local_pencils {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let L := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let U := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t KI KP ρ c b : ℝ) (Y : Finset ℝ)
        (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
        (T : ℝ → Space 2 → Finset (Space 2)) (G : Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → s < t → 0 ≤ KI → 0 ≤ KP → 0 < ρ → |c| ≤ 1 →
      Y.Nonempty → (∀ y ∈ Y, |y| ≤ 1) → 2 ≤ D →
      projectedSubsetSampleConstant n s t KI KP ρ ≤ D →
      (∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧
        ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
        (∀ p ∈ P y, |p 0-y| ≤ Δ ∧ |p 1-a y| ≤ Δ) ∧
        planarProjectionEnergy n s c ((P y).image (localPacketPoint Δ y (a y))) ≤
          2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) →
      (∀ y ∈ Y, ∀ p ∈ A y, T y p ⊆ G ∧ FiniteSeparatedAt (Δ^2) (T y p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T y p) ∧
        L s ≤ ((T y p).card:ℝ) ∧ ((T y p).card:ℝ) ≤ U s ∧
        ∀ l ∈ T y p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, Δ/4 ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ (G.card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_gain_of_local_energy hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t KI KP ρ c b Y P A a T G hs hs1 hst hKI hKP hρ hc hY hYbound hD hbudget hdata hT hYball
  let S := Y.biUnion A
  have hrep (p : Space 2) (hp : p ∈ S) : ∃ y ∈ Y, p ∈ A y := Finset.mem_biUnion.mp hp
  let V := fun p => if hp : p ∈ S then T (Classical.choose (hrep p hp)) p else ∅
  have hV (p : Space 2) (hp : p ∈ S) := by
    have hw := Classical.choose_spec (hrep p hp)
    have ht := hT (Classical.choose (hrep p hp)) hw.1 p hw.2
    have he : V p = T (Classical.choose (hrep p hp)) p := dite_eq_left hp
    rw [← he] at ht
    exact ht
  have hgain := hmain n hn s t KI KP ρ c b Y P A a S V hs hs1 hst hKI hKP hρ hc hY hYbound hD hbudget
    (by
      intro y hy
      obtain ⟨hp,hap,hsize,hcell,henergy⟩ := hdata y hy
      exact ⟨hp,hap,Finset.subset_biUnion_of_mem A hy,hsize,hcell,henergy⟩)
    (fun p hp => (hV p hp).2) hYball
  have hcover : S.biUnion V ⊆ G := by
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact (hV p hp).1 hl
  exact hgain.trans (Nat.cast_le.mpr (Finset.card_le_card hcover))

end Falconer

end OAI
