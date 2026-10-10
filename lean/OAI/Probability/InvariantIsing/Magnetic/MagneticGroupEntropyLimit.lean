import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupParameterBound
import OAI.Probability.InvariantIsing.Magnetic.MagneticSliceFieldBound
import OAI.Probability.InvariantIsing.Arrays.TensorContactStep

namespace OAI

/-! Bounded-height entropy control for attainable groups whose proportions
and interior magnetizations converge. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped BigOperators Topology
namespace InvariantIsing

theorem magnetic_group_entropy_limit {A : Type*} [Fintype A] [DecidableEq A]
    (N : ℕ → ℕ) (hN : ∀ k, 0<N k)
    (group : ∀ k, Fin (N k) → A) (count : ℕ → A → ℕ)
    (hcount : ∀ k a, count k a ≤ spinGroupSize (group k) a)
    (γs mags : ℕ → A → ℝ) (γ mag : A → ℝ)
    (hγ : Tendsto γs atTop (𝓝 γ)) (hm : Tendsto mags atTop (𝓝 mag))
    {r : ℝ} (hr : r<1) (hmag : ∀ a, |mag a| ≤ r)
    (hmags : ∀ᶠ k in atTop, ∀ a, |mags k a| ≤ r)
    (hγs : ∀ k a, (spinGroupSize (group k) a : ℝ)=N k*γs k a)
    (hms : ∀ k a, (count k a : ℝ)=spinGroupSize (group k) a*((1+mags k a)/2))
    (p : OverlapPath) (S : ℝ) (hS : magneticEntropyFunctional γ mag p ≤ (S : EReal))
    {n : ℕ} (cut : Fin (n+2) → ℝ) (hc : StrictMono cut)
    (hfirst : cut 0=0) (hlast : cut (Fin.last (n+1))=1) :
    ∀ H ε : ℝ, 0<ε → ∀ᶠ k in atTop,
      ∀ (a : Fin (n+1) → ℝ) (ha : ∀ i, 0 ≤ a i), (∑ i, a i) ≤ H →
        constrainedBlockValue (spinGroupSlice (group k) (count k)) (contactFieldStep cut hc hfirst hlast a ha)+
          fieldPairing p (contactFieldStep cut hc hfirst hlast a ha)/2 ≤ S+ε := by
  intro H ε hε
  have he := magneticGroupValue_parameters_uniform γs mags γ mag hγ hm hr hmag hmags H ε hε
  filter_upwards [he,hmags] with k hk hkm a ha hcap
  let step := contactFieldStep cut hc hfirst hlast a ha
  have hheight : step.height (Fin.last step.depth) ≤ H := by
    change finiteFieldPath a n ≤ H
    rw [finiteFieldPath_last]
    exact hcap
  have hv := hk step hheight
  have hb := constrainedBlockValue_group_le (hN k) (group k) (count k) (hcount k)
    (mags k) (γs k) (fun x => (hkm x).trans_lt hr) (hms k) (hγs k) step
  have hs' : magneticGroupValue γ mag step+fieldPairing p step/2 ≤ S := by
    apply EReal.coe_le_coe_iff.mp
    exact (le_iSup (fun h : FieldStep =>
      ((magneticGroupValue γ mag h+fieldPairing p h/2 : ℝ) : EReal)) step).trans hS
  change constrainedBlockValue (spinGroupSlice (group k) (count k)) step+fieldPairing p step/2 ≤ S+ε
  have hd := (le_abs_self _).trans hv.le
  linarith

end InvariantIsing

end

end OAI
