import Mathlib
import OAI.Geometry.CAT0Fillings.Tangent.CurrentDensity
import OAI.Geometry.CAT0Fillings.Minimizers.CriticalEnergy
import OAI.Geometry.CAT0Fillings.Chord.Moments
import OAI.Geometry.CAT0Fillings.Euler.Moments
import OAI.Geometry.CAT0Fillings.Chord.DensityContradiction
import OAI.Geometry.CAT0Fillings.Euler.OppositeIntegral
import OAI.Geometry.CAT0Fillings.Chord.Distribution

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal

namespace CAT0Fillings.ChartGeometry
open AnalyticMinimizer

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
theorem euler_chord_contradiction (hX : IsCAT0 X) (hk : 2 < k+1) (hz : IsCycle T)
    (v : q.Sobolev) {β : ℝ} (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ R : q.Sobolev,
      (q.inclusion R : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT] (fun x => (q.inclusion v x)^γ) ∧
      (q.closedGradient R : _ → _) =ᵐ[q.atlasMeasure]
        (fun w => (γ*(q.inclusion v (q.atlasParam w))^(γ-1)) • q.closedGradient v w))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (o : X) (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < criticalMass q.inclusion (2+4*β) v)
    (hWs : criticalMass q.inclusion (2+4*β) v < sphereArea (k+1))
    (hE : energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (criticalNorm q.inclusion (2+4*β) P)^2 ≤
      energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (criticalNorm q.inclusion (2+4*β) v)^2) : False := by
  let μ := MassMeasure.currentMassMeasure hT
  obtain ⟨U,hU,hU0,heq⟩ := ChordMeasure.exists_nonnegative_borel (hm 2 (by norm_num)).aestronglyMeasurable hv
  have hpowEq (p : ℝ) : (fun x => U x^p) =ᵐ[μ] (fun x => q.inclusion v x^p) :=
    heq.mono fun x hx => congrArg (fun t : ℝ => t^p) hx
  have hρ : (fun x => U x^(2+4*β)) =ᵐ[μ] (fun x => |q.inclusion v x|^(2+4*β)) := by
    filter_upwards [heq,hv] with x hx hp
    rw [hx,abs_of_nonneg hp]
  have hmass : ChordMeasure.total μ (fun x => U x^(2+4*β)) = criticalMass q.inclusion (2+4*β) v :=
    integral_congr_ae hρ
  have hip (p : ℝ) (hp : 0 ≤ p) : Integrable (fun x => U x^p) μ :=
    (ChordMeasure.integral_power μ hv hm hp).congr (hpowEq p).symm
  have hν := ChordMeasure.probability_congr hρ
  have heν := ChordMeasure.ae_of_ae heq (fun x => |q.inclusion v x|^(2+4*β))
  apply q.density_contradiction hX hk U hU hU0 hb (by simpa only [Nat.cast_add,Nat.cast_one] using hn)
    (hip _ (by positivity)) (hip _ (by positivity)) (by rwa [hmass]) (by rwa [hmass])
  · intro y
    have hI : (∫ x, dist y x^2*U x^(2+6*β) ∂μ) =
        ∫ x, dist y x^2*(q.inclusion v x)^(2+6*β) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hpowEq (2+6*β)] with x hx
      rw [hx]
    rw [ChordMeasure.total,integral_congr_ae (hpowEq (2+4*β)),
      integral_congr_ae (hpowEq (2+6*β)),hI]
    exact q.opposite_all_center hz y v hb hn hv hm hpow heuler (hr y)
  · intro y a ha
    have hP : (fun x => (U y^β*dist y x*U x^β)^2) =ᵐ[ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))] (fun x => (U y^β*dist y x*(q.inclusion v x)^β)^2) := by
      filter_upwards [heν] with x hx
      rw [hx]
    have htrans : ChordTransform.transform (ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))) (k+1)
        (fun x => (U y^β*dist y x*U x^β)^2) a =
        ChordTransform.transform (ChordMeasure.probability μ
        (fun x => |q.inclusion v x|^(2+4*β))) (k+1)
        (fun x => (U y^β*dist y x*(q.inclusion v x)^β)^2) a := by
      apply integral_congr_ae
      filter_upwards [hP] with x hx
      simp only [hx]
    simp only [Nat.cast_add,Nat.cast_one]
    rw [hν,htrans,integral_congr_ae hP]
    exact q.chord_distribution hz y v hb hn hv hm (fun γ hγ => by
      obtain ⟨R,_,hR⟩ := hpow γ hγ
      exact ⟨R,hR⟩) heuler (hr y) hW hE hmin ha
end CAT0Fillings.ChartGeometry
end

end OAI
