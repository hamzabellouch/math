import OAI.NumberTheory.DukePrimeDegree.Entropy.LastActiveEntropy
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ForwardOrbitSection
import OAI.NumberTheory.DukePrimeDegree.Geometry.FiniteTransverseCode

namespace OAI

/-! # Low-entropy fine observations without map ergodicity

Small complete sections at all precisions give arbitrarily fine future
returns. Only the aperiodicity of the points in the prescribed chart is
used; the selected transformation need not be ergodic.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace DukePrimeDegree

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

theorem exists_sparse_fine_future_observation
    (μ : Measure Y) [IsProbabilityMeasure μ]
    (e : Y ≃ₜ Y) (he : MeasurePreserving e μ μ)
    {A : Set Y} (hA : MeasurableSet A)
    (hfree : ∀ x ∈ A, ∀ n : ℕ, 0 < n → (e^n) x ≠ x)
    {d : ℕ} (f : Y → Fin d → ℝ) (hf : Measurable f)
    {R : ℝ} (hR : 0 ≤ R) (hbound : ∀ x ∈ A, ∀ i, |f x i| ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : Y → ℕ, Measurable Q ∧
      Summable (fun n => Real.negMulLog (μ.real {x | Q x=n})) ∧
      (∑' n, Real.negMulLog (μ.real {x | Q x=n})) < ε ∧
      ∀ᵐ x ∂μ, x ∈ A → ∀ y, (∀ k : ℕ, Q ((e^(k+1)) y)=Q ((e^(k+1)) x)) →
        ∀ η : ℝ, 0 < η → ∃ k : ℕ, (e^(k+1)) x ∈ A ∧ (e^(k+1)) y ∈ A ∧
          ∀ i, |f ((e^(k+1)) y) i-f ((e^(k+1)) x) i| < η := by
  have hscale (n : ℕ) : (0:ℝ) < 1/(n+1) := by positivity
  have hscale1 (n : ℕ) : 1/(n+1:ℝ) ≤ 1 := by
    apply div_le_self zero_le_one
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose K B hB _hcard hclose using fun n : ℕ =>
    exists_bounded_vector_code f hf hR (hscale n) (hscale1 n)
  obtain ⟨δ,hδ,hδs,_,Hδ⟩ := exists_lastActiveObservation_entropy_budget
    (Y := Y) K hε
  choose S hS hSA hSm hcover using fun n =>
    exists_small_complete_orbit_section μ e he hA hfree (hδ n)
  have hsμ : (∑' n, μ (S n)) ≠ ∞ := by
    apply ne_top_of_le_ne_top hδs.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro n
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ _) (hδ n).le).mpr (hSm n).le
  have hfinite := ae_finite_setOfPred_mem hsμ
  have hfiniteAll : ∀ᵐ x ∂μ, ∀ k : ℕ, {n | (e^k) x ∈ S n}.Finite :=
    ae_all_iff.mpr fun k => (measurePreserving_homeomorph_pow μ e he k).quasiMeasurePreserving.ae hfinite
  have hvisitAll : ∀ᵐ x ∂μ, ∀ n, x ∈ A → ∀ M : ℕ,
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
  filter_upwards [hfiniteAll,hvisitAll] with x hxfin hxvisit hxA
  intro y hxy η hη
  obtain ⟨n,hn⟩ := exists_nat_gt (2/η)
  obtain ⟨k,hk,hkx⟩ := hxvisit n hxA 1
  obtain ⟨m,hnm,hm⟩ := lastActiveObservation_scale_ge S B (hxfin k) hkx
  have hkcode : lastActiveObservation S B ((e^k) y)=lastActiveObservation S B ((e^k) x) := by
    apply Encodable.encode_injective
    have hh := hxy (k-1)
    simpa only [Nat.sub_add_cancel hk] using hh
  have hycode : lastActiveObservation S B ((e^k) y)=some ⟨m,B m ((e^k) x)⟩ := hkcode.trans hm
  have hmy : (e^k) y ∈ lastActiveObservationAtom S B (some ⟨m,B m ((e^k) x)⟩) := by
    rw [←lastActiveObservation_fiber]
    exact hycode
  have hxmem : (e^k) x ∈ A := hSA n hkx
  have hymem : (e^k) y ∈ A := hSA m hmy.1.1
  refine ⟨k-1,by simpa only [Nat.sub_add_cancel hk] using hxmem,
    by simpa only [Nat.sub_add_cancel hk] using hymem,?_⟩
  intro i
  have hnmR : (n:ℝ) ≤ m := by exact_mod_cast hnm
  have hlarge : 2 < (n:ℝ)*η := (div_lt_iff₀ hη).mp hn
  have hsmall : 2*(1/(m+1:ℝ)) < η := by
    have hd : (0:ℝ) < m+1 := by positivity
    rw [mul_one_div]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have H := (hclose m ((e^k) x) ((e^k) y) (hbound _ hxmem) hmy.2 i).trans hsmall
  simpa only [Nat.sub_add_cancel hk] using H

end DukePrimeDegree

end

end OAI
