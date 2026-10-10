import Mathlib
import OAI.Analysis.BiholderTransport.Duality.CompactDual
import OAI.Analysis.BiholderTransport.Volume.DensityBounds

namespace OAI

section
section
noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ENNReal NNReal ContDiff Topology BoundedContinuousFunction

namespace WeakMTWTransport

section MeasureContacts
variable {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

def contactImage (u v : M → ℝ) (A : Set M) : Set M :=
  {y | ∃ x ∈ A, contactGap u v x y = 0}

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma dual_minimum_swap {μ ν : Measure M} {u v : M →ᵇ ℝ}
    (hmin : ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective μ ν (u,v) ≤ dualObjective μ ν (a,b)) :
    ∀ a b : M →ᵇ ℝ, (∀ x y, 0 ≤ contactGap a b x y) →
      dualObjective ν μ (v,u) ≤ dualObjective ν μ (a,b) := by
  intro a b hab
  have hh := hmin b a (fun x y => by rw [contactGap_symm]; exact hab y x)
  simpa only [dualObjective,add_comm] using hh

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_ae_eq_preimage {μ : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂μ, ∀ x, contactGap u v x y = 0 → x = S y)
    (A : Set M) : contactImage u v A =ᵐ[μ] S ⁻¹' A := by
  filter_upwards [hsingle] with y hy
  apply propext
  change (∃ x ∈ A, contactGap u v x y = 0) ↔ S y ∈ A
  constructor
  · rintro ⟨x,hx,hxy⟩
    simpa only [hy x hxy] using hx
  · intro hx
    exact ⟨S y,hx,hcontact y⟩

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_measure {μ ν : Measure M} {u v : M → ℝ} {S : M → M}
    (hcontact : ∀ y, contactGap u v (S y) y = 0)
    (hsingle : ∀ᵐ y ∂ν, ∀ x, contactGap u v x y = 0 → x = S y)
    (hS : AEMeasurable S ν) (hpush : Measure.map S ν = μ)
    {A : Set M} (hA : MeasurableSet A) :
    NullMeasurableSet (contactImage u v A) ν ∧ ν (contactImage u v A) = μ A := by
  have he := contactImage_ae_eq_preimage hcontact hsingle A
  refine ⟨?_,?_⟩
  · exact (hS.nullMeasurableSet_preimage hA).congr he.symm
  · rw [measure_congr he,← Measure.map_apply_of_aemeasurable hS hA,hpush]

omit [CompactSpace M] [Nonempty M] [BorelSpace M] in

lemma contactImage_volume_comparison {vol : Measure M} {lam cap : ℝ}
    {rho0 rho1 u v : M → ℝ}
    (hrho0 : AdmissibleDensity vol lam cap rho0)
    (hrho1 : AdmissibleDensity vol lam cap rho1)
    {A : Set M} (hmass : densityMeasure vol rho1 (contactImage u v A) =
      densityMeasure vol rho0 A) :
    ENNReal.ofReal lam * vol A ≤ ENNReal.ofReal cap * vol (contactImage u v A) ∧
    ENNReal.ofReal lam * vol (contactImage u v A) ≤ ENNReal.ofReal cap * vol A := by
  have h0 := densityMeasure_bounds hrho0
  have h1 := densityMeasure_bounds hrho1
  constructor
  · calc
      _ ≤ densityMeasure vol rho0 A := h0.1 A
      _ = densityMeasure vol rho1 (contactImage u v A) := hmass.symm
      _ ≤ _ := h1.2 (contactImage u v A)
  · calc
      _ ≤ densityMeasure vol rho1 (contactImage u v A) := h1.1 (contactImage u v A)
      _ = densityMeasure vol rho0 A := hmass
      _ ≤ _ := h0.2 A

end MeasureContacts

end WeakMTWTransport
end
end
end

end OAI
