import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportTemplates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveVariationEquality

namespace OAI

/-! # The segment-volume lower bound saturates every scalar variation bound -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set
open scoped BigOperators

variable {W I B : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
  (D : PolycyclicRecognition.SupportDatum W I B)

/-- For a centered absolutely continuous profile, equality of its support
lower bound and derivative-speed upper bound forces every weight to exhaust
its positive variation at a maximizing time. The scalar integral identities
are the fundamental theorem of calculus data for the line restriction. -/
theorem exists_ordered_weight_signs
    (h : ℝ → W) (q : ℝ → W) (hc : Continuous h)
    {T c : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (hbound : ∀ b, ∀ᵐ t ∂volume.restrict (Icc 0 T), D.basisSupport b (q t) ≤ c)
    (hlower : T * c ≤ D.templateSupport (h '' Icc 0 T)) :
    ∃ τ : I → ℝ, (∀ i, τ i ∈ Icc 0 T) ∧
      (∀ i, D.weight i (h (τ i)) = D.weightSupport (h '' Icc 0 T) i) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc 0 (τ i)), 0 ≤ D.weight i (q t)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Ioc (τ i) T), D.weight i (q t) ≤ 0) := by
  classical
  let E := h '' Icc 0 T
  have hE : IsCompact E := isCompact_Icc.image hc
  have hne : E.Nonempty := (nonempty_Icc.mpr hT).image h
  have hp (i : I) : IntervalIntegrable (fun t => max (D.weight i (q t)) 0) volume 0 T :=
    ⟨(hq i).1.pos_part, (hq i).2.pos_part⟩
  have hweight (i : I) : D.weightSupport E i ≤
      ∫ t in 0..T, max (D.weight i (q t)) 0 := by
    obtain ⟨_, ⟨t, ht, rfl⟩, heq⟩ := D.exists_weightSupport_point hE hne i
    rw [heq, hFTC i t ht]
    have hqi := (hq i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
    have hpi := (hp i).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hT]
      exact Icc_subset_Icc le_rfl ht.2)
    exact (intervalIntegral.integral_mono ht.1 hqi hpi (fun _ => le_max_left _ _)).trans
      (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun _ => le_max_right _ _)) (hp i))
  have hbupper (b : B) :
      (∑ i, (D.multiplicity b i : ℝ) *
        ∫ t in 0..T, max (D.weight i (q t)) 0) ≤ T * c := by
    have hbi : IntervalIntegrable (fun t => D.basisSupport b (q t)) volume 0 T := by
      convert IntervalIntegrable.sum Finset.univ
        (fun i _ => (hp i).const_mul (D.multiplicity b i : ℝ)) using 1
      ext t
      simp only [basisSupport, Finset.sum_apply, max_comm]
    have hsum : (∫ t in 0..T, D.basisSupport b (q t)) =
        ∑ i, (D.multiplicity b i : ℝ) * ∫ t in 0..T, max (D.weight i (q t)) 0 := by
      simp only [basisSupport, max_comm (0 : ℝ)]
      rw [intervalIntegral.integral_finsetSum (fun i _ =>
        (hp i).const_mul (D.multiplicity b i : ℝ))]
      simp only [intervalIntegral.integral_const_mul]
    rw [← hsum]
    have hh := intervalIntegral.integral_mono_ae_restrict hT hbi
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 T) (hbound b)
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hh
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (D.basisTemplateSupport E)
  have hb' : D.templateSupport E = D.basisTemplateSupport E b := hb
  have hsumzero : (∑ i, (D.multiplicity b i : ℝ) *
      ((∫ t in 0..T, max (D.weight i (q t)) 0) - D.weightSupport E i)) = 0 := by
    have hnonneg : 0 ≤ ∑ i, (D.multiplicity b i : ℝ) *
        ((∫ t in 0..T, max (D.weight i (q t)) 0) - D.weightSupport E i) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hweight i)))
    have hsumle := hbupper b
    change T * c ≤ D.templateSupport E at hlower
    rw [hb'] at hlower
    simp only [mul_sub, Finset.sum_sub_distrib] at hnonneg ⊢
    unfold basisTemplateSupport at hlower
    exact le_antisymm (by linarith) hnonneg
  have hsaturated (i : I) : D.weightSupport E i =
      ∫ t in 0..T, max (D.weight i (q t)) 0 := by
    have hterm := Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j => (D.multiplicity b j : ℝ) *
        ((∫ t in 0..T, max (D.weight j (q t)) 0) - D.weightSupport E j))
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (hweight j)))
      (Finset.mem_univ i)
    rw [hsumzero] at hterm
    have hpos : (0 : ℝ) < D.multiplicity b i := Nat.cast_pos.mpr (D.positive b i)
    nlinarith [hweight i]
  have hmax (i : I) : ∃ t ∈ Icc 0 T,
      D.weight i (h t) = D.weightSupport E i := by
    obtain ⟨_, ⟨t, ht, rfl⟩, heq⟩ := D.exists_weightSupport_point hE hne i
    exact ⟨t, ht, heq.symm⟩
  choose τ hτ hτmax using hmax
  refine ⟨τ, hτ, hτmax, ?_, ?_⟩
  · intro i
    exact (positive_variation_equality_signs (fun t => D.weight i (q t))
      (hτ i).1 (hτ i).2 (hq i) (by
        rw [← hFTC i (τ i) (hτ i), hτmax i, hsaturated i])).1
  · intro i
    exact (positive_variation_equality_signs (fun t => D.weight i (q t))
      (hτ i).1 (hτ i).2 (hq i) (by
        rw [← hFTC i (τ i) (hτ i), hτmax i, hsaturated i])).2

end PolycyclicRecognition.SupportDatum

end

end OAI
