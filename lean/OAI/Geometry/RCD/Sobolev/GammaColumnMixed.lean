import OAI.Geometry.RCD.Harmonic.GramDirectionalError

namespace OAI

/-! # Mixed energy pairings with a finite coordinate column -/

open Set Filter MeasureTheory Finset
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

theorem localGamma_column_right {n : ℕ} (f : SobolevSpace μ hQ)
    (u : Fin n → SobolevSpace μ hQ) (a : Euclidean n) :
    localGamma μ hQ f (sobolevColumnMap μ hQ u a) =ᵐ[μ]
      fun x => ∑ i, a i*localGamma μ hQ f (u i) x := by
  classical
  have hsum (s : Finset (Fin n)) : localGamma μ hQ f (∑ i∈s, a i • u i) =ᵐ[μ]
      fun x => ∑ i∈s, a i*localGamma μ hQ f (u i) x := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [sum_empty,zero_smul,zero_mul] using
        localGamma_smul_right μ hQ 0 f (0 : SobolevSpace μ hQ)
    | @insert i s hi ih =>
      simp only [sum_insert hi]
      filter_upwards [localGamma_add_right μ hQ f (a i • u i) (∑ j∈s, a j • u j),
        localGamma_smul_right μ hQ (a i) f (u i),ih] with x hx hs ht
      rw [hx,hs,ht]
  simpa only [sobolevColumnMap_apply] using! hsum univ

end RegularPointCoordinates

end

end OAI
