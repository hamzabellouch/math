import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

namespace OAI

open MeasureTheory Set

namespace Invariant233

theorem exists_invariant_conull_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧
      (∀ᵐ x ∂μ, x ∈ t) ∧ ∀ k, σ k ⁻¹' t = t := by
  let t : Set X := ⋂ k : ℤ, σ k ⁻¹' s
  have ht_mem : ∀ x, x ∈ t ↔ ∀ k, σ k x ∈ s := by
    intro x
    simp only [t, mem_iInter, mem_preimage]
  refine ⟨t, MeasurableSet.iInter (fun k ↦ hs.preimage (hmp k).measurable), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hzero] using (ht_mem x).mp hx 0
  · have h : ∀ᵐ x ∂μ, ∀ k : ℤ, σ k x ∈ s :=
      ae_all_iff.mpr (fun k ↦ (hmp k).quasiMeasurePreserving.ae hfull)
    exact h.mono fun x hx ↦ (ht_mem x).mpr hx
  · intro k
    ext x
    change σ k x ∈ t ↔ x ∈ t
    rw [ht_mem, ht_mem]
    constructor
    · intro hx n
      have h := hx (n - k)
      rw [← hadd] at h
      rw [← add_sub_assoc, add_comm k n, add_sub_cancel_right] at h
      exact h
    · intro hx n
      rw [← hadd]
      exact hx (k + n)

theorem exists_invariant_conull_property
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, P x) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨u, hsub, hu, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  have hfull : ∀ᵐ x ∂μ, x ∈ uᶜ := by
    rw [ae_iff]
    simpa using hnull
  obtain ⟨t, ht, htu, htf, hinv⟩ :=
    exists_invariant_conull_subset σ hzero hadd hmp hu.compl hfull
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx
  by_contra hbad
  exact htu hx (hsub hbad)

theorem exists_invariant_conull_forall
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : I → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, ∀ k i, P i (σ k x)) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨t, ht, htf, hprop, hinv⟩ :=
    exists_invariant_conull_property σ hzero hadd hmp
      (fun x ↦ ∀ i, P i x) (ae_all_iff.mpr hP)
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx k i
  apply hprop (σ k x) _ i
  change x ∈ σ k ⁻¹' t
  rw [hinv]
  exact hx

end Invariant233

end OAI
