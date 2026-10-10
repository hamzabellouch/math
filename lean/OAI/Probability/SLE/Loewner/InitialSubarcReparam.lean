import OAI.Probability.SLE.Loewner.SlitChartRangeUniqueness
import OAI.Probability.SLE.Loewner.InitialForwardChart

namespace OAI

/-! Exact capacity and inverse-chart identities under initial-subarc
reparametrization. -/
noncomputable section
open Set Filter Function
open scoped Topology

namespace SLEExactGauge

lemma initialSubarc_mul (p : C(unitInterval,ℂ)) (b u : unitInterval) :
    initialSubarc (initialSubarc p b) u=initialSubarc p (b*u) := by
  ext v
  simp only [initialSubarc_apply,mul_assoc]

lemma initialCapacity_subarc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (b : unitInterval) (hb : b≠0)
    (hib : Injective (initialSubarc p b)) (h0b : initialSubarc p b 0=0)
    (hHb : ∀ t : unitInterval, t ≠ 0 → initialSubarc p b t∈upperHalfPlane)
    (u : unitInterval) :
    initialCapacity (initialSubarc p b) hib h0b hHb u=initialCapacity p hi h0 hH (b*u) := by
  by_cases hu : u=0
  · simp only [hu,mul_zero,initialCapacity_zero]
  have hbu : b*u≠0 := mul_ne_zero hb hu
  rw [initialCapacity,dite_eq_right hu,initialCapacity,dite_eq_right hbu]
  exact ((initialSlitChart (initialSubarc p b) hib h0b hHb u hu).eq_of_range_eq
    (initialSlitChart p hi h0 hH (b*u) hbu)
    (congrArg (fun q : C(unitInterval,ℂ) => range q) (initialSubarc_mul p b u))).1

lemma initialInverseChart_subarc (p : C(unitInterval,ℂ)) (hi : Injective p)
    (h0 : p 0=0) (hH : ∀ t : unitInterval, t ≠ 0 → p t ∈ upperHalfPlane)
    (b : unitInterval) (hb : b≠0)
    (hib : Injective (initialSubarc p b)) (h0b : initialSubarc p b 0=0)
    (hHb : ∀ t : unitInterval, t ≠ 0 → initialSubarc p b t∈upperHalfPlane)
    (u : unitInterval) :
    EqOn (initialInverseChart (initialSubarc p b) hib h0b hHb u)
      (initialInverseChart p hi h0 hH (b*u)) upperHalfPlane := by
  by_cases hu : u=0
  · simp only [hu,mul_zero,initialInverseChart_zero]
    exact fun _ _ => rfl
  have hbu : b*u≠0 := mul_ne_zero hb hu
  rw [initialInverseChart,dite_eq_right hu,initialInverseChart,dite_eq_right hbu]
  exact ((initialSlitChart (initialSubarc p b) hib h0b hHb u hu).eq_of_range_eq
    (initialSlitChart p hi h0 hH (b*u) hbu)
    (congrArg (fun q : C(unitInterval,ℂ) => range q) (initialSubarc_mul p b u))).2.1

end SLEExactGauge

end

end OAI
