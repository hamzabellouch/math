import Mathlib
import OAI.Geometry.CAT0Fillings.Chord.ProfileBound
import OAI.Geometry.CAT0Fillings.Chord.Moments

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
lemma chord_scalar_average (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β a : ℝ}
    (hb : 0 < β) (ha : 0 < a) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) :
    let μ := MassMeasure.currentMassMeasure hT
    let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
    let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
    (ChordTransform.transform ν (k+1) b a)^(((k+1:ℝ)-2)/(k+1:ℝ)) ≤
      ChordAverage.average (((k+1:ℝ)-2)/2) (ChordTransform.transform ν (k+1) b) a := by
  let μ := MassMeasure.currentMassMeasure hT
  let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
  let s : X → ℝ := fun x => κ*dist o x*(q.inclusion v x)^β
  let c := 1/(2*β)
  let w := chordBubble c a
  let f := averageProfile (k+1) (chordBubbleD c a)
  have hc : 0 < c := by dsimp [c]; positivity
  have hnc : (k+1:ℝ) = 2*c+2 := by
    dsimp [c]
    rw [beta_half_dimension hb hn]
    ring
  have hp : 0 < 2+4*β := by positivity
  have hin := AnalyticMinimizer.criticalMass_integrable q.inclusion hp v (hm _ hp)
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ _ hin
    (Eventually.of_forall fun point => Real.rpow_nonneg (abs_nonneg (q.inclusion v point)) _) hW
  have hsm : AEStronglyMeasurable s μ := ChordMeasure.chord_measurable μ o
    (Lp.aestronglyMeasurable (q.inclusion v)) κ β
  have hsν : AEStronglyMeasurable s ν := hsm.mono_ac (withDensity_absolutelyContinuous _ _)
  obtain ⟨P,hP,hEP⟩ := q.chord_combined hz o v (κ := κ) hb ha hn hv hm hpow heuler hr
  have hEP' : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P ≤
      (k+1:ℝ)*(∫ x, |q.inclusion v x|^(2+4*β)*(w (s x))^2 ∂μ)+
      β*(k+1:ℝ)*(∫ x, |q.inclusion v x|^(2+4*β)*((s x)^2*f (s x)) ∂μ) := by
    convert hEP using 1; try rfl
    congr 2
    · apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [abs_of_nonneg hx]
    · apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [abs_of_nonneg hx]
      ring
  have hvar := AnalyticMinimizer.critical_scalar_start q.inclusion
    (AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ)) hp
    (by positivity : (0:ℝ) < k+1) v P hW hE (hmin P)
    (fun x => w (s x)) (fun x => (s x)^2*f (s x))
    (Eventually.of_forall fun x => (chordBubble_pos ha.le c (s x)).le) hP hEP'
  have hav := profile_average ν hsν (Nat.succ_pos k) hc ha (by simpa only [Nat.cast_succ] using hnc)
  rw [show 1/(2*c) = β from beta_inverse_half hb] at hav
  have hk : (∫ x, (w (s x))^(2+4*β) ∂ν) =
      ChordTransform.transform ν (k+1) (fun x => (s x)^2) a := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp only [w,chordBubble,ChordTransform.kernel]
    rw [←Real.rpow_mul (by positivity : (0:ℝ) ≤ 1+a*(s x)^2)]
    rw [show -c*(2+4*β) = -(k+1:ℝ) from beta_critical_product hb hn]
  rw [hk,beta_critical_ratio hb hn,hav] at hvar
  simpa only [c,beta_half_dimension hb hn,Nat.cast_succ] using hvar
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open CAT0Fillings.Conformal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)
theorem chord_distribution (hz : IsCycle T) (o : X) (v : q.Sobolev) {κ β : ℝ}
    (hb : 0 < β) (hn : (k+1:ℝ)*β = 1+2*β)
    (hv : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion v x)
    (hm : ∀ b : ℝ, 0 < b → MemLp (q.inclusion v) (ENNReal.ofReal b) (MassMeasure.currentMassMeasure hT))
    (hpow : ∀ γ : ℝ, 1 ≤ γ → ∃ L : q.Sobolev,
      (q.closedGradient L : _ → _) =ᵐ[q.atlasMeasure]
        (fun z => (γ*(q.inclusion v (q.atlasParam z))^(γ-1)) • q.closedGradient v z))
    (heuler : ∀ ψ : q.Sobolev,
      4*β*inner ℝ (q.closedGradient v) (q.closedGradient ψ) +
        (k+1:ℝ)*inner ℝ (q.inclusion v) (q.inclusion ψ) =
      (k+1:ℝ)*(∫ x, ((q.inclusion v) x)^(1+4*β)*(q.inclusion ψ) x ∂MassMeasure.currentMassMeasure hT))
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (hW : 0 < AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hE : AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v =
      (k+1:ℝ)*AnalyticMinimizer.criticalMass q.inclusion (2+4*β) v)
    (hmin : ∀ P : q.Sobolev,
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) v *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) P)^2 ≤
      AnalyticMinimizer.energy q.inclusion q.closedGradient (4*β) (k+1:ℝ) P *
        (AnalyticMinimizer.criticalNorm q.inclusion (2+4*β) v)^2) {a : ℝ} (ha : 0 ≤ a) :
    let μ := MassMeasure.currentMassMeasure hT
    let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
    let b := fun x => (κ*dist o x*(q.inclusion v x)^β)^2
    ChordTransform.transform ν (k+1) b a ≤
      (1+2*(∫ x, b x ∂ν)*a)^(-(k+1:ℝ)/2) := by
  let μ := MassMeasure.currentMassMeasure hT
  let ν := ChordMeasure.probability μ (fun x => |q.inclusion v x|^(2+4*β))
  have hp : 0 < 2+4*β := by positivity
  let : IsProbabilityMeasure ν := ChordMeasure.isProbability μ _
    (AnalyticMinimizer.criticalMass_integrable q.inclusion hp v (hm _ hp))
    (Eventually.of_forall fun point => Real.rpow_nonneg (abs_nonneg (q.inclusion v point)) _) hW
  apply ChordTransform.distribution_bound ν
    (ChordMeasure.chord_second_moment μ o hv hm hb hW κ)
    (Eventually.of_forall fun point => sq_nonneg (κ*dist o point*(q.inclusion v point)^β))
    (beta_dimension hb hn) ?_ ha
  intro a ha
  exact q.chord_scalar_average hz o v hb ha hn hv hm hpow heuler hr hW hE hmin
end CAT0Fillings.ChartGeometry
end

end OAI
