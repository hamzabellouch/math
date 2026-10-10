import Mathlib
import OAI.Probability.SKRatio.Gaussian.ExponentialEvents
import OAI.Probability.SKRatio.Gaussian.EmpiricalIntervals
import OAI.Probability.SKRatio.Variational.ScalarMoments
import OAI.Probability.SKRatio.Quantization.BinParameters

namespace OAI

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Real Set
namespace SKRatio.Bins
open Planted Scalar SKRatioClock.Regression
attribute [local instance] Classical.propDecidable

def intervalBin {N : ℕ} (e : Fin N → ℝ) (x : ℝ) : Fin (N+1) :=
  ⟨(Finset.univ.filter (fun i => e i<x)).card,by
    have h := Finset.card_le_card (Finset.filter_subset (s:=Finset.univ) (p:=fun i => e i<x))
    simpa only [Finset.card_univ,Fintype.card_fin] using Nat.lt_succ_of_le h⟩

lemma intervalBin_le_cut {N : ℕ} {e : Fin N → ℝ} (he : StrictMono e)
    (x : ℝ) (j : Fin N) : (intervalBin e x).val≤j.val ↔ x≤e j := by
  constructor
  · intro hj
    by_contra hh
    have hx : e j<x := lt_of_not_ge hh
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => e i<x) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(he.monotone (Finset.mem_Iic.mp hi)).trans_lt hx⟩
    have hc := Finset.card_le_card hsub
    rw [Fin.card_Iic] at hc
    change (Finset.univ.filter (fun i => e i<x)).card≤j.val at hj
    omega
  · intro hx
    have hsub : Finset.univ.filter (fun i => e i<x) ⊆ Finset.Iio j := by
      intro i hi
      exact Finset.mem_Iio.mpr (he.lt_iff_lt.mp ((Finset.mem_filter.mp hi).2.trans_le hx))
    have hc := Finset.card_le_card hsub
    rwa [Fin.card_Iio] at hc

lemma intervalBin_eq_zero {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) (x : ℝ) :
    intervalBin e x=0 ↔ x≤e ⟨0,hN⟩ := by
  rw [←intervalBin_le_cut he x ⟨0,hN⟩]
  simp only [Fin.ext_iff,Fin.val_zero,Nat.le_zero_eq]

lemma intervalBin_eq_last {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) (x : ℝ) :
    intervalBin e x=Fin.last N ↔ e ⟨N-1,by omega⟩<x := by
  have hh := intervalBin_le_cut he x ⟨N-1,by omega⟩
  simp only [Fin.ext_iff,Fin.val_last]
  have hbound := (intervalBin e x).isLt
  constructor
  · intro h
    exact lt_of_not_ge (fun hx => by have := hh.mpr hx; omega)
  · intro h
    have hh' : ¬ (intervalBin e x).val≤N-1 := fun hu => not_le.mpr h (hh.mp hu)
    omega

lemma intervalBin_eq_middle {N : ℕ} {e : Fin N → ℝ} (he : StrictMono e)
    (x : ℝ) (j : Fin (N+1)) (hj0 : 0<j.val) (hjN : j.val<N) :
    intervalBin e x=j ↔ e ⟨j.val-1,by omega⟩<x ∧ x≤e ⟨j.val,hjN⟩ := by
  have hlo := intervalBin_le_cut he x ⟨j.val-1,by omega⟩
  have hhi := intervalBin_le_cut he x ⟨j.val,hjN⟩
  dsimp only [Fin.val_mk] at hlo hhi
  rw [Fin.ext_iff]
  constructor
  · intro hh
    constructor
    · exact lt_of_not_ge (fun hx => by have := hlo.mpr hx; omega)
    · exact hhi.mp (by omega)
  · rintro ⟨hl,hu⟩
    have h1 := hhi.mpr hu
    have h2 : ¬ (intervalBin e x).val≤j.val-1 := fun h => not_le.mpr hl (hlo.mp h)
    omega

lemma measurableSet_intervalBin {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    (j : Fin (N+1)) : MeasurableSet {x | intervalBin e x=j} := by
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simp only [hj,intervalBin_eq_zero hN he]
    exact measurableSet_Iic
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simp only [hj,intervalBin_eq_last hN he]
      exact measurableSet_Ioi
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simp only [intervalBin_eq_middle he _ j h1 h2]
      exact measurableSet_Ioc

lemma measurable_intervalBin {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e) :
    Measurable (intervalBin e) := by
  apply measurable_to_countable'
  intro j
  exact measurableSet_intervalBin hN he j

lemma intervalBin_empirical {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {ρ : ∀ n, Measure (Ω n)} {X : ∀ n, Ω n → Fin n → ℝ}
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hX : ExponentialEmpiricalConcentration ρ X μ) (j : Fin (N+1)) :
    ExponentialConvergence ρ
      (fun n ω => (count (fun i => intervalBin e (X n ω i)) j:ℝ)/(n:ℝ))
      (μ.real {x | intervalBin e x=j}) := by
  have heq (n : ℕ) (ω : Ω n) : (count (fun i => intervalBin e (X n ω i)) j:ℝ) =
      ∑ i, {x | intervalBin e x=j}.indicator (fun _ : ℝ => (1:ℝ)) (X n ω i) := by
    simp only [count,Finset.cast_card,Set.indicator,Set.mem_ofPred_eq]
    exact Finset.sum_filter _ _
  simp_rw [heq]
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simpa only [hj,intervalBin_eq_zero hN he,Set.Iic_def] using hX.Iic (e ⟨0,hN⟩)
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simpa only [hj,intervalBin_eq_last hN he,Set.Ioi_def] using hX.Ioi (e ⟨N-1,by omega⟩)
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simpa only [intervalBin_eq_middle he _ j h1 h2,Set.Ioc_def] using
        hX.Ioc (he.monotone (show (⟨j.val-1,by omega⟩ : Fin N)≤⟨j.val,h2⟩ from by simp))

lemma gaussianReal_real_pos_of_volume_pos (μ : ℝ) {s : ℝ≥0} (hs : s≠0)
    {E : Set ℝ} (hE : 0<volume E) : 0<(gaussianReal μ s).real E := by
  apply ENNReal.toReal_pos _ (measure_ne_top _ _)
  exact fun h => hE.ne' (gaussianReal_absolutelyContinuous' μ hs h)

lemma intervalBin_mass_pos {N : ℕ} (hN : 0<N) {e : Fin N → ℝ} (he : StrictMono e)
    (β : ℝ) (hβ : β≠0) (j : Fin (N+1)) :
    0<(fieldLaw β).real {x | intervalBin e x=j} := by
  have hv : variance β≠0 := by
    intro hh
    have hh' := congrArg (fun x : ℝ≥0 => (x:ℝ)) hh
    rw [variance_coe,NNReal.coe_zero] at hh'
    exact hβ (sq_eq_zero_iff.mp hh')
  apply gaussianReal_real_pos_of_volume_pos (β^2) hv
  by_cases hj0 : j.val=0
  · have hj : j=0 := Fin.ext hj0
    simp only [hj,intervalBin_eq_zero hN he,Set.Iic_def,Real.volume_Iic]
    exact ENNReal.zero_lt_top
  · by_cases hjN : j.val=N
    · have hj : j=Fin.last N := Fin.ext hjN
      simp only [hj,intervalBin_eq_last hN he,Set.Ioi_def,Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · have h1 : 0<j.val := Nat.pos_of_ne_zero hj0
      have h2 : j.val<N := by have := j.isLt; omega
      simp only [intervalBin_eq_middle he _ j h1 h2]
      change 0<volume (Ioc _ _)
      rw [Real.volume_Ioc,ENNReal.ofReal_pos]
      exact sub_pos.mpr (he (show (⟨j.val-1,by omega⟩ : Fin N)<⟨j.val,h2⟩ from by change j.val-1<j.val; omega))

end SKRatio.Bins

end

end OAI
