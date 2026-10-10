import OAI.Probability.SLE.Mass.RadonProcessUniqueness

namespace OAI

/-! A single almost-sure Radon certificate suffices when upgrading
simultaneous positive-test identities to identities of measure paths. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported NNReal

namespace SLEExactGauge

 theorem random_radon_process_eq_of_positive_tests_ae
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : LocalTestFamily X) (N M : ℝ≥0 → Ω → Measure X)
    (hNr : ∀ᵐ ω ∂P, ∀ t, (N t ω).Regular)
    (hMr : ∀ᵐ ω ∂P, ∀ t, (M t ω).Regular)
    (htest : ∀ f : C_c(X,ℝ), (∀ x, 0 ≤ f x) →
      ∀ᵐ ω ∂P, ∀ t, (∫ x, f x ∂N t ω)=∫ x, f x ∂M t ω) :
    ∀ᵐ ω ∂P, ∀ t, N t ω=M t ω := by
  have hp (j : ℕ) := htest (D.test j ⊔ 0) (fun x => le_max_right _ _)
  have hn (j : ℕ) := htest ((-D.test j) ⊔ 0) (fun x => le_max_right _ _)
  filter_upwards [hNr,hMr,ae_all_iff.mpr hp,ae_all_iff.mpr hn] with ω hN hM hωp hωn
  intro t
  let := hN t
  let := hM t
  apply D.measure_eq_of_test_integrals
  intro j
  rw [compact_test_integral_pos_sub_neg (N t ω) (D.test j),
    compact_test_integral_pos_sub_neg (M t ω) (D.test j),hωp j t,hωn j t]

end SLEExactGauge

end

end OAI
