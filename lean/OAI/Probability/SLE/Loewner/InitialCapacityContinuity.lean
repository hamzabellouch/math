import OAI.Probability.SLE.Loewner.InitialCapacityTerminal
import OAI.Probability.SLE.Loewner.InitialForwardComparison
import OAI.Probability.SLE.Mass.VerticalDisplacementMass

namespace OAI

/-! Continuity of the full capacity parameter. The capacity of the initial
slit and its complementary capacity relative to the final slit give the two
inequalities for every subsequential limit. -/
noncomputable section
open Set Filter Function Complex
open scoped Topology

namespace SLEExactGauge

lemma initialCapacity_limit_value_at (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    {t : ℕ → unitInterval} {F : ℂ → ℂ} {c : ℝ}
    (hF : DifferentiableOn ℂ F upperHalfPlane)
    (hlim : TendstoLocallyUniformlyOn (fun n => initialInverseChart p hi h0 hH (t n))
      F atTop upperHalfPlane) {s : unitInterval} (hs : s≠0) (ht : Tendsto t atTop (𝓝 s))
    (hcap : Tendsto (fun n => initialCapacity p hi h0 hH (t n)) atTop (𝓝 c)) :
    c=initialCapacity p hi h0 hH s := by
  let P := initialSlitChart p hi h0 hH s hs
  have heF : EqOn F P.inverse upperHalfPlane := by
    simpa only [initialInverseChart,dite_eq_right hs] using
      initialInverse_limit_eq_at p hi h0 hH hF hlim hs ht
  have hlow : P.capacity≤c := by
    apply hydrodynamic_mass_le_of_displacement
      (inverse_hydrodynamic_coefficient P.coefficient P.inverse_normalized P.right_inverse)
    intro z hz
    rw [← heF hz]
    exact initialInverse_limit_displacement p hi h0 hH hlim hcap hz
  obtain ⟨Q⟩ := exists_simpleSlitChart p hi h0 hH
  obtain ⟨φ,hφ,hforward⟩ := initialInverse_limit_forward_on_final p hi h0 hH hF hlim hs ht
  have hbound (z : ℂ) (hz : z∈upperHalfPlane) :
      ‖P.forward (Q.inverse z)-z‖≤(Q.capacity-c)/z.im := by
    have hleft := ((hforward (Q.inverse z) (Q.inverse_mapsTo hz)).sub_const z).norm
    have hright := ((tendsto_const_nhds (x := Q.capacity)).sub
      (hcap.comp hφ.tendsto_atTop)).div_const z.im
    exact le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun n => initialForward_comparison_to_final p hi h0 hH Q _ hz)
  have hcomp : Tendsto (fun z : ℂ => z*(P.forward (Q.inverse z)-z))
      (cocompact ℂ ⊓ 𝓟 upperHalfPlane) (𝓝 (-((Q.capacity-P.capacity:ℝ):ℂ))) := by
    have he : -((Q.capacity-P.capacity:ℝ):ℂ)=(P.capacity:ℂ)-Q.capacity := by
      push_cast
      ring
    rw [he]
    exact hydrodynamic_composition_coefficient P.coefficient Q.coefficient
      Q.inverse_normalized Q.right_inverse
  have hupper := hydrodynamic_mass_le_of_displacement hcomp hbound
  rw [initialCapacity,dite_eq_right hs]
  change c=P.capacity
  exact le_antisymm (by linarith) hlow

theorem initialCapacity_continuousAt (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (s : unitInterval) : ContinuousAt (initialCapacity p hi h0 hH) s := by
  by_cases hs : s=0
  · subst s
    exact initialCapacity_continuousAt_zero p hi h0 hH
  apply tendsto_of_subseq_tendsto
  intro t ht
  have hb (n : ℕ) : initialCapacity p hi h0 hH (t n)∈
      Icc 0 (initialCapacity p hi h0 hH 1) :=
    ⟨initialCapacity_nonneg p hi h0 hH _,initialCapacity_monotone p hi h0 hH le_top⟩
  obtain ⟨c,_,φ,hφ,hcap⟩ := isCompact_Icc.tendsto_subseq hb
  obtain ⟨ψ,F,hψ,hF,hFlim⟩ := initialInverseChart_subsequence p hi h0 hH (t ∘ φ)
  have ht' : Tendsto (fun n => t (φ (ψ n))) atTop (𝓝 s) :=
    (ht.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hc' := hcap.comp hψ.tendsto_atTop
  have he := initialCapacity_limit_value_at p hi h0 hH hF hFlim hs ht' hc'
  refine ⟨φ ∘ ψ,?_⟩
  change Tendsto (fun n => initialCapacity p hi h0 hH (t (φ (ψ n))))
    atTop (𝓝 (initialCapacity p hi h0 hH s))
  change Tendsto (fun n => initialCapacity p hi h0 hH (t (φ (ψ n)))) atTop (𝓝 c) at hc'
  rwa [he] at hc'

theorem initialCapacity_continuous (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane) :
    Continuous (initialCapacity p hi h0 hH) :=
  continuous_iff_continuousAt.mpr (initialCapacity_continuousAt p hi h0 hH)

end SLEExactGauge

end

end OAI
