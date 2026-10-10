import OAI.NumberTheory.DukePrimeDegree.Dynamics.ErgodicReturnLevels

namespace OAI

/-! # The return towers cover an ergodic probability space -/

noncomputable section
open MeasureTheory Set Filter
namespace DukePrimeDegree

theorem ae_mem_firstReturnTower
    {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]
    {T : Y → Y} (hT : Ergodic T μ) (hE : MeasurableEmbedding T)
    {S : Set Y} (hS : MeasurableSet S) (hpos : μ S ≠ 0) :
    ∀ᵐ x ∂μ, ∃ p : Σ n : ℕ, Fin (n+1), x ∈ firstReturnTower T S p := by
  let A := ⋃ p : Σ n : ℕ, Fin (n+1), firstReturnTower T S p
  have hEi (j : ℕ) : MeasurableEmbedding (T^[j]) := by
    induction j with
    | zero => exact MeasurableEmbedding.id
    | succ j ih =>
        rw [Function.iterate_succ]
        exact ih.comp hE
  have hA : MeasurableSet A := MeasurableSet.iUnion fun p =>
    (hEi p.2.val).measurableSet_image.mpr
      (measurableSet_firstReturnLevel hT.measurable hS p.1)
  have hsection : ∀ᵐ x ∂μ, x ∈ S → x ∈ A := by
    filter_upwards [ae_section_mem_firstReturnLevel μ hT.toMeasurePreserving hS]
      with x hx hxs
    obtain ⟨n,hn⟩ := hx hxs
    exact mem_iUnion.mpr ⟨⟨n,⟨0,Nat.succ_pos n⟩⟩,x,hn,rfl⟩
  have hinv : A ≤ᵐ[μ] T ⁻¹' A := by
    filter_upwards [hT.quasiMeasurePreserving.ae hsection] with x hx hAx
    obtain ⟨⟨n,j⟩,y,hy,hxy⟩ := mem_iUnion.mp hAx
    change T^[j.val] y=x at hxy
    by_cases hj : j.val < n
    · apply mem_iUnion.mpr
      refine ⟨⟨n,⟨j.val+1,by omega⟩⟩,y,hy,?_⟩
      change T^[j.val+1] y=T x
      rw [Function.iterate_succ_apply',hxy]
    · apply hx
      have he : j.val=n := by omega
      have hret := hy.2.1
      change T^[n+1] y ∈ S at hret
      rw [←he,Function.iterate_succ_apply',hxy] at hret
      exact hret
  rcases hT.ae_empty_or_univ_of_ae_le_preimage hA.nullMeasurableSet hinv with hn | hf
  · have hempty : ∀ᵐ x ∂μ, x ∉ A := by
      filter_upwards [hn.mem_iff] with x hx
      exact fun h => (hx.mp h).elim
    have hz : μ S=0 := measure_eq_zero_iff_ae_notMem.mpr (by
      filter_upwards [hempty,hsection] with x hx hs hxs
      exact hx (hs hxs))
    exact (hpos hz).elim
  · filter_upwards [ae_eq_univ.mp hf] with x hx
    exact mem_iUnion.mp hx

end DukePrimeDegree

end

end OAI
