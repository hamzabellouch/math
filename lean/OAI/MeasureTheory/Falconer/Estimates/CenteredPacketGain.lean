import OAI.MeasureTheory.Falconer.Estimates.CenteredPacketPower
import OAI.MeasureTheory.Falconer.Estimates.DirectedSampledRows
import OAI.MeasureTheory.Falconer.Estimates.SampledRowCardinality

namespace OAI

/-! Actual coarse-cell projections yield the product gain for the original
packet. The projected rows are constructed in the proof; neither product
structure nor a separated output pencil family is assumed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem centered_packet_gain_of_local_energy {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+2 →
      let Δ := 1/(2:ℝ)^n
      let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
      let L := fun s : ℝ => Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2)
      let U := fun s : ℝ => Real.exp ((s+ε)*((n+2:ℕ):ℝ)*Real.log 2)
      ∀ (s t KI KP ρ c b : ℝ) (Y : Finset ℝ)
        (P A : ℝ → Finset (Space 2)) (a : ℝ → ℝ)
        (S : Finset (Space 2)) (T : Space 2 → Finset (Space 2)),
      κ ≤ s → s ≤ 1-8*κ → s < t → 0 ≤ KI → 0 ≤ KP → 0 < ρ → |c| ≤ 1 →
      Y.Nonempty → (∀ y ∈ Y, |y| ≤ 1) → 2 ≤ D →
      projectedSubsetSampleConstant n s t KI KP ρ ≤ D →
      (∀ y ∈ Y, (P y).Nonempty ∧ A y ⊆ P y ∧ A y ⊆ S ∧
        ρ*((P y).card:ℝ) ≤ ((A y).card:ℝ) ∧
        (∀ p ∈ P y, |p 0-y| ≤ Δ ∧ |p 1-a y| ≤ Δ) ∧
        planarProjectionEnergy n s c ((P y).image (localPacketPoint Δ y (a y))) ≤
          2*projectionEnergyBudget n s t KI KP*((P y).card:ℝ)^2) →
      (∀ p ∈ S, FiniteSeparatedAt (Δ^2) (T p) ∧
        NormalizedFiniteBallBound (Δ^2) s (D/Δ^s) (T p) ∧
        L s ≤ ((T p).card:ℝ) ∧ ((T p).card:ℝ) ≤ U s ∧
        ∀ l ∈ T p, |l 0| ≤ 1 ∧ |l 0+c| ≤ Δ ∧ |l 1-b| ≤ Δ ∧ TubeIncident (Δ^2) p l) →
      (∀ u r : ℝ, Δ/4 ≤ r → r ≤ 1 → scalarBallMass Y u r ≤ D*r^(2*κ)*(Y.card:ℝ)) →
      Real.exp ((2*s+η)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((S.biUnion T).card:ℝ) := by
  obtain ⟨ε,η,N0,hε,hη,hN0,hmain⟩ := centered_packet_product_power hκ hκ1
  refine ⟨ε,η,N0,hε,hη,hN0,?_⟩
  intro n hn
  dsimp only
  intro s t KI KP ρ c b Y P A a S T hs hs1 hst hKI hKP hρ hc hY hYbound hD2 hbudget hdata hT hYball
  let Δ := 1/(2:ℝ)^n
  let α := (1/2:ℝ)^(n+2)
  let D := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let NP := Nat.ceil (α^(-s))
  have hscale : Δ = 4*α := by
    dsimp [Δ,α]
    rw [pow_add]
    norm_num
    rw [div_pow,one_pow]
    ring
  have hαeq : Δ/4 = α := by rw [hscale]; ring
  have hscale' : 1/(2:ℝ)^n = 4*(1/2:ℝ)^(n+2) := hscale
  have hs0 : 0 ≤ s := hκ.le.trans hs
  obtain ⟨R,hR⟩ := directed_sampled_packet_rows n (c := c) (b := b) hs0 hst hKI hKP hρ hc
    (zero_le_two.trans hD2) hbudget Y P A a S hdata
  obtain ⟨hNPup,hsize⟩ := sampled_row_cardinality_bounds (n+2) hs0 hD2
  have hNP : 0 < NP := Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by dsimp [α]; positivity) _)
  have hrows : ∀ y ∈ Y, |y| ≤ 1 ∧ FiniteSeparatedAt (4*α) (R y) ∧
      NormalizedFiniteBallBound (4*α) s D (R y) ∧
      Real.exp ((s-ε)*((n+2:ℕ):ℝ)*Real.log 2) ≤ ((R y).card:ℝ) ∧
      (R y).card ≤ NP ∧ ∀ x ∈ R y, x 0 = y := by
    intro y hy
    obtain ⟨_,hsep,hreg,hlow,hup,hrep⟩ := hR y hy
    have hlow' : 1 ≤ D*α^s*((R y).card:ℝ) := by
      change 1 ≤ D*(Δ/4)^s*((R y).card:ℝ) at hlow
      rwa [hαeq] at hlow
    have hlo := hsize ((R y).card:ℝ) hlow'
    refine ⟨hYbound y hy,?_,?_,hlo,?_,?_⟩
    · simpa only [← hscale] using hsep
    · simpa only [← hscale] using hreg
    · simpa only [NP,← hαeq] using hup
    · exact fun x hx => (hrep x hx).1
  have hrep : ∀ y ∈ Y, ∀ x ∈ R y, ∃ p ∈ S,
      p 1+c*p 0-b = (4*α)*x 1 ∧ |p 0-y| ≤ 4*α := by
    intro y hy x hx
    obtain ⟨hx0,p,hp,hp1,hp0⟩ := (hR y hy).2.2.2.2.2 x hx
    rw [hx0] at hp0
    exact ⟨p,hp,by simpa only [← hscale] using hp1,by simpa only [← hscale] using hp0⟩
  apply hmain (n+2) hn s c b Y R S T NP hs hs1 hY hNP hNPup hrows hrep
  · simpa only [← hscale'] using hT
  · intro u r hr hr1
    apply hYball u r ?_ hr1
    change Δ/4 ≤ r
    rwa [hαeq]

end Falconer

end OAI
