import OAI.MeasureTheory.Falconer.Radial.HeavyMaximal
import OAI.MeasureTheory.Falconer.Radial.TwoSlabSingleScale
import OAI.MeasureTheory.Falconer.Radial.PublishedHeavyPlates

namespace OAI

/-! # Discharging the application-level heavy-hyperplane input

The maximal heavy family has at most 2/m representatives. A substantial
intersection forces the normals to be close, because transverse slabs have
small mass by the stated single-scale codimension-two concentration bound.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem published_heavy_hyperplanes : PublishedHeavyHyperplanes := by
  intro d _hd a C ha ha1 hC
  let b := heavyPlateExponent a
  let c := a-2*b
  let K := max 2 (2016*C+3)
  have hb : 0 < b := heavyPlateExponent_pos (by linarith)
  have hc1 : c < 1 := by dsimp [c]; linarith
  refine ⟨K,(by dsimp [K]; exact le_trans (by norm_num) (le_max_left _ _)),?_⟩
  intro μ δ hδ hδ1 hbounded hplane
  let m := δ^b
  let τ := 504*C*δ^c
  have hm : 0 < m := Real.rpow_pos_of_pos hδ _
  have hm1 : m ≤ 1 := Real.rpow_le_one hδ.le hδ1 hb.le
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let A : Space d × ℝ → Set (Space d) := fun p =>
    {x | ‖x‖ < 1 ∧ |inner ℝ p.1 x-p.2| ≤ δ}
  let U : Set (Space d × ℝ) := {p | ‖p.1‖ = 1 ∧ ENNReal.ofReal m ≤ (μ : Measure (Space d)) (A p)}
  have hA (p : Space d × ℝ) : MeasurableSet (A p) := by
    change MeasurableSet ({x : Space d | ‖x‖ < 1} ∩
      {x : Space d | |inner ℝ p.1 x-p.2| ≤ δ})
    exact (measurableSet_lt measurable_norm measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hmass (p : Space d × ℝ) : (μ : Measure (Space d)) (A p) =
      (μ : Measure (Space d)) {x | |inner ℝ p.1 x-p.2| ≤ δ} := by
    apply measure_congr
    filter_upwards [hbounded] with x hx
    exact propext (and_iff_right hx)
  obtain ⟨S,hS,hcard,hcover⟩ := maximal_heavy_family (μ : Measure (Space d)) U A
    (fun p _ => hA p) hm hm1 (fun p hp => hp.2)
  refine ⟨S,fun p hp => (hS p hp).1,?_,?_⟩
  · apply hcard.trans
    have hK2 : 2 ≤ K := le_max_left _ _
    dsimp [m]
    rw [div_eq_mul_inv,← Real.rpow_neg hδ.le]
    exact mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hδ.le _)
  · intro w hw t hheavy
    have hi : (w,t) ∈ U := by
      exact ⟨hw,by rw [hmass]; exact hheavy⟩
    obtain ⟨p,hp,hinter⟩ := hcover (w,t) hi
    have hpunit : ‖p.1‖ = 1 := (hS p hp).1
    have hnonempty : (A (w,t) ∩ A p).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty,measure_empty] at hinter
      exact (not_lt_of_ge bot_le) hinter
    obtain ⟨z,hz⟩ := hnonempty
    have hclose : normalDistance p.1 w ≤ 2*τ := by
      by_cases hτ1 : τ ≤ 1
      · by_cases hnear : normalDistance p.1 w ≤ τ
        · exact hnear.trans (by linarith)
        · have htrans := two_slab_single_scale_bound (μ : Measure (Space d)) p.1 w
            hpunit hw p.2 t hδ hτ hτ1 hC.le (le_of_lt (lt_of_not_ge hnear)) hplane
          have hsub : A (w,t) ∩ A p ⊆
              {x | |inner ℝ p.1 x-p.2| ≤ δ ∧ |inner ℝ w x-t| ≤ δ} :=
            fun x hx => ⟨hx.2.2,hx.1.2⟩
          have hpower : δ^a = δ^c*m^2 := by
            dsimp [m]
            rw [pow_two,← Real.rpow_add hδ,← Real.rpow_add hδ]
            congr 1
            dsimp [c]
            ring
          have heq : 252*C*δ^a/τ = m^2/2 := by
            rw [hpower]
            dsimp [τ]
            field_simp
            ring
          rw [heq] at htrans
          exact False.elim ((not_lt_of_ge ((measure_mono hsub).trans htrans)) hinter)
      · have hnormal : normalDistance p.1 w ≤ 2 := by
          apply (min_le_left _ _).trans
          exact (norm_sub_le _ _).trans_eq (by rw [hpunit,hw]; norm_num)
        exact hnormal.trans (by linarith)
    refine ⟨p,hp,fun x hx hxw => ?_⟩
    have hcluster := affine_slab_cluster (M := 1) hz.1.1.le hx.le hclose hz.2.2 hz.1.2 hxw
    have hδc : δ ≤ δ^c := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hc1.le
    apply hcluster.trans
    have hK : 2016*C+3 ≤ K := le_max_right _ _
    calc
      2*1*(2*τ)+3*δ ≤ (2016*C+3)*δ^c := by dsimp [τ]; nlinarith
      _ ≤ K*δ^c := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hδ.le _)

end Falconer

end OAI
