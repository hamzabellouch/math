import OAI.Analysis.CircleDomains.Topology.MixedModelExhaustion
import OAI.Analysis.CircleDomains.Selection.RealSequenceRetention

namespace OAI

/-! Every fixed coordinate is eventually retained, with its actual
values and differential, on every compact source set of the common
model sequence. -/

open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

variable {S C : Type*} [LinearOrder C]
  {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ}
  {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
  {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}

namespace MixedModelExhaustion

variable (M : MixedModelExhaustion d data retained O ε ρ)

def coordinateIndex (c : C) (n : ℕ) : Fin (M.size n) := by
  classical
  exact if h : c ∈ range (M.label n) then Classical.choose h
    else M.slot n ⟨0, Nat.succ_pos n⟩

theorem coordinateIndex_eventually (c : C) :
    ∀ᶠ n in atTop, M.label n (M.coordinateIndex c n) = c := by
  classical
  filter_upwards [M.coordinate_eventually c] with n hn
  simp only [coordinateIndex, dite_eq_left hn]
  exact Classical.choose_spec hn

theorem eventually_coordinate_eq {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ x ∈ realChartDomain K,
      (M.stages n).model.functions (M.coordinateIndex c n) =ᶠ[𝓝 x] (data c).physical := by
  filter_upwards [M.real.eventually_core_contains hK hKG, M.coordinateIndex_eventually c]
    with n hn hc
  intro x hx
  have hcore : x ∈ (M.stages n).core :=
    interior_subset ((M.stages n).core_contains (show x ∈ realChartDomain (M.real.cores n) from hn hx))
  change ∀ᶠ y in 𝓝 x, (M.stages n).model.functions (M.coordinateIndex c n) y = (data c).physical y
  filter_upwards [(M.stages n).model.retained.filter_mono (nhds_le_nhdsSet hcore)] with y hy
  simpa only [hc] using hy (M.coordinateIndex c n)

theorem eventually_coordinate_values {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ x ∈ realChartDomain K,
      (M.stages n).model.functions (M.coordinateIndex c n) x = (data c).physical x :=
  (M.eventually_coordinate_eq hK hKG c).mono fun _ hn x hx => (hn x hx).self_of_nhds

theorem eventually_coordinate_gradient {K : Set Sphere} (hK : IsCompact K) (hKG : K ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ x ∈ realChartDomain K,
      circleGradient ((M.stages n).model.functions (M.coordinateIndex c n)) x =
        circleGradient (data c).physical x :=
  (M.eventually_coordinate_eq hK hKG c).mono fun _ hn x hx =>
    circleGradient_congr_of_eventuallyEq (hn x hx)

def withRadius (R : ℝ) (hR : M.real.radius ≤ R) :
    MixedModelExhaustion d data retained O ε ρ :=
  { M with real := M.real.withRadius R hR }

end MixedModelExhaustion
end CircleDomainRigidity.FiniteTransfer

end

end OAI
