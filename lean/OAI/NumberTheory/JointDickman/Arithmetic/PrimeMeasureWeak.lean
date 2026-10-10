import OAI.NumberTheory.JointDickman.Arithmetic.PrimeMeasureSupport
import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! # Weak convergence of the logarithmic prime measure -/
namespace JointDickman
open Filter MeasureTheory
open scoped Topology NNReal ENNReal

theorem finiteMeasure_tendsto_of_Ioc {μ : ℝ → FiniteMeasure ℝ} {ν : FiniteMeasure ℝ}
    (hν : ν ≠ 0)
    (hm : Tendsto (fun x => (μ x).mass) atTop (𝓝 ν.mass))
    (hi : ∀ a b : ℝ, Tendsto (fun x => μ x (Set.Ioc a b)) atTop (𝓝 (ν (Set.Ioc a b)))) :
    Tendsto μ atTop (𝓝 ν) := by
  have hm0 : ν.mass ≠ 0 := ν.mass_nonzero_iff.mpr hν
  have hnz : ∀ᶠ x in atTop, μ x ≠ 0 := by
    filter_upwards [hm.eventually (eventually_ne_nhds hm0)] with x hx
    exact (μ x).mass_nonzero_iff.mp hx
  have hn : Tendsto (fun x => (μ x).normalize) atTop (𝓝 ν.normalize) := by
    apply (isPiSystem_Ioc (id : ℝ → ℝ) (id : ℝ → ℝ)).tendsto_probabilityMeasure_of_tendsto_of_mem
    · rintro s ⟨a,b,hab,rfl⟩
      exact measurableSet_Ioc
    · intro u hu x hx
      obtain ⟨a,b,hx',hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
      let b' := (x+b)/2
      have hxb : x < b' := by dsimp [b']; linarith [hx'.2]
      have hbb : b' < b := by dsimp [b']; linarith [hx'.2]
      refine ⟨Set.Ioc a b', ⟨a,b',hx'.1.trans hxb,rfl⟩, Ioc_mem_nhds hx'.1 hxb, ?_⟩
      intro y hy
      exact hsub ⟨hy.1,hy.2.trans_lt hbb⟩
    · rintro s ⟨a,b,hab,rfl⟩
      have ht := (hm.inv₀ hm0).mul (hi a b)
      rw [← ν.normalize_eq_of_nonzero hν] at ht
      apply ht.congr'
      filter_upwards [hnz] with x hx
      exact ((μ x).normalize_eq_of_nonzero hx _).symm
  exact (FiniteMeasure.tendsto_normalize_iff_tendsto hν).mp ⟨hn,hm⟩

theorem primeLogMeasure_tendsto {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    Tendsto (primeLogMeasure c) atTop (𝓝 (logarithmicPrimeMeasure c)) := by
  have hm0 : (logarithmicPrimeMeasure c).mass ≠ 0 := by
    intro h
    have hz := congrArg ((↑) : ℝ≥0 → ℝ) h
    rw [logarithmicPrimeMeasure_mass hc hc1.le, NNReal.coe_zero] at hz
    have : Real.log c < 0 := Real.log_neg hc hc1
    linarith
  apply finiteMeasure_tendsto_of_Ioc ((logarithmicPrimeMeasure c).mass_nonzero_iff.mp hm0)
  · exact NNReal.tendsto_coe.mp (primeLogMeasure_mass_tendsto hc hc1.le)
  · intro a b
    exact NNReal.tendsto_coe.mp (primeLogMeasure_all_intervals_tendsto hc a b)

end JointDickman

end OAI
