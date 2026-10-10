import OAI.NumberTheory.DukePrimeDegree.Entropy.SparseFineObservation
import OAI.NumberTheory.DukePrimeDegree.Entropy.FinitePrefixChartCodes
import Mathlib.Data.Nat.Pairing

namespace OAI

/-! # One low-entropy observation for a countable coordinate atlas -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

theorem exists_countable_sparse_fine_observation
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    (A : ℕ → Set Y) (hA : ∀ i, MeasurableSet (A i))
    (hfree : ∀ i x, x ∈ A i → ∀ n : ℕ, 0 < n → (e^n) x ≠ x)
    {d : ℕ} (f : ℕ → Y → Fin d → ℝ) (hf : ∀ i, Measurable (f i))
    (R : ℕ → ℝ) (hR : ∀ i, 0 ≤ R i)
    (hbound : ∀ i x, x ∈ A i → ∀ j, |f i x j| ≤ R i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Y → ℕ, Measurable Q ∧
      Summable (fun n => Real.negMulLog (μ.real {x | Q x=n})) ∧
      (∑' n, Real.negMulLog (μ.real {x | Q x=n})) < ε ∧
      ∀ᵐ x ∂μ, ∀ i, x ∈ A i → ∀ y,
        (∀ k : ℕ, Q ((e^(k+1)) y)=Q ((e^(k+1)) x)) →
        ∀ η : ℝ, 0 < η → ∃ k : ℕ, (e^(k+1)) x ∈ A i ∧ (e^(k+1)) y ∈ A i ∧
          ∀ j, |f i ((e^(k+1)) y) j-f i ((e^(k+1)) x) j| < η := by
  obtain ⟨K,B,hB,hclose⟩ := exists_finite_prefix_chart_codes A hA f hf R hR hbound
  obtain ⟨δ,hδ,hδs,_,Hδ⟩ := exists_lastActiveObservation_entropy_budget
    (Y := Y) K hε
  choose S hS hSA hSm hcover using fun n : ℕ =>
    exists_small_complete_orbit_section μ e he (hA n.unpair.1)
      (hfree n.unpair.1) (hδ n)
  have hsμ : (∑' n, μ (S n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hδs.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro n
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (hδ n).le).mpr (hSm n).le
  have hfinite := ae_finite_setOfPred_mem hsμ
  have hfiniteAll : ∀ᵐ x ∂μ, ∀ k : ℕ, {n | (e^k) x ∈ S n}.Finite :=
    ae_all_iff.mpr fun k => (measurePreserving_homeomorph_pow μ e he k).quasiMeasurePreserving.ae hfinite
  have hvisitAll : ∀ᵐ x ∂μ, ∀ n, x ∈ A n.unpair.1 → ∀ M : ℕ,
      ∃ k : ℕ, M ≤ k ∧ (e^k) x ∈ S n :=
    ae_all_iff.mpr fun n => ae_future_visits_of_orbit_section μ e he (hS n) (hcover n)
  let I := Option (Σ n : ℕ, Fin (K n))
  let : MeasurableSpace I := ⊤
  let Q : Y → ℕ := fun x => Encodable.encode (lastActiveObservation S B x)
  have hQ : Measurable Q := (measurable_of_countable Encodable.encode).comp
    (measurable_lastActiveObservation hS B hB)
  have hcost := Hδ μ S hS (fun n => (hSm n).le) B hB
  have hencode := encoded_observation_information μ (lastActiveObservation S B)
  refine ⟨Q,hQ,hencode.1.mpr hcost.1,hencode.2.trans_lt hcost.2,?_⟩
  filter_upwards [hfiniteAll,hvisitAll] with x hxfin hxvisit
  intro i hxA y hxy η hη
  obtain ⟨p,hp⟩ := exists_nat_gt (2/η)
  let n := Nat.pair i p
  have hindex : n.unpair.1=i := by simp only [n,Nat.unpair_pair]
  have hxA' : x ∈ A n.unpair.1 := by rwa [hindex]
  obtain ⟨k,hk,hkx⟩ := hxvisit n hxA' 1
  obtain ⟨m,hnm,hm⟩ := lastActiveObservation_scale_ge S B (hxfin k) hkx
  have him : i ≤ m := (Nat.left_le_pair i p).trans hnm
  have hpm : p ≤ m := (Nat.right_le_pair i p).trans hnm
  have hkcode : lastActiveObservation S B ((e^k) y)=lastActiveObservation S B ((e^k) x) := by
    apply Encodable.encode_injective
    have hh := hxy (k-1)
    simpa only [Nat.sub_add_cancel hk] using hh
  have hycode : lastActiveObservation S B ((e^k) y)=some ⟨m,B m ((e^k) x)⟩ := hkcode.trans hm
  have hmy : (e^k) y ∈ lastActiveObservationAtom S B (some ⟨m,B m ((e^k) x)⟩) := by
    rw [←lastActiveObservation_fiber]
    exact hycode
  have hxmem : (e^k) x ∈ A i := by
    have H := hSA n hkx
    rwa [hindex] at H
  obtain ⟨hymem,hfine⟩ := hclose m i him _ hxmem _ hmy.2
  refine ⟨k-1,by simpa only [Nat.sub_add_cancel hk] using hxmem,
    by simpa only [Nat.sub_add_cancel hk] using hymem,?_⟩
  intro j
  have hpmR : (p:ℝ) ≤ m := by exact_mod_cast hpm
  have hlarge : 2 < (p:ℝ)*η := (div_lt_iff₀ hη).mp hp
  have hsmall : 2*(1/(m+1:ℝ)) < η := by
    have hd : (0:ℝ) < m+1 := by positivity
    rw [mul_one_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have H := (hfine j).trans hsmall
  simpa only [Nat.sub_add_cancel hk] using H

end DukePrimeDegree

end

end OAI
