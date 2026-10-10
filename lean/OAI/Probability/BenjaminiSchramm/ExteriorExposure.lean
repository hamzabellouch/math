import OAI.Probability.BenjaminiSchramm.KernelExterior

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Percolation.BenjaminiSchramm

universe u v
variable {V : Type u} {E : Type v}
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exteriorSusceptibility_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x b : V) (ω : Set E) :
    exteriorSusceptibility G p x b ω ≤ susceptibility G p b := by
  by_cases hf : (cluster G ω x).Finite
  · rw [exteriorSusceptibility_eq G p x b ω hf]
    exact inducedSusceptibility_le_susceptibility G hloc hqt p hp _ b
  · simp only [exteriorSusceptibility,Set.Infinite.ncard hf,Nat.cast_zero,div_zero]
    exact susceptibility_nonneg G p b

theorem integrable_exteriorSusceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x b : V) :
    Integrable (exteriorSusceptibility G p x b) (law p) := by
  apply (integrable_const (susceptibility G p b)).mono'
    (measurable_exteriorSusceptibility G hloc p x b).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (exteriorSusceptibility_nonneg G p x b ω)]
    exact exteriorSusceptibility_le G hloc hqt p hp x b ω)

theorem integral_exterior_connection [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    (∫ ω, (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) ∂law p) =
      ∫ ω, (if Conn G ω x a ∧ ¬Conn G ω x b then
        ((cluster G ω b).ncard : ℝ) else 0) ∂law p := by
  have hl : Integrable (fun ω => if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) (law p) :=
    (integrable_exteriorSusceptibility G hloc hqt p hp x b).indicator
      (measurableSet_conn G x a)
  have hr : Integrable (fun ω => if Conn G ω x a ∧ ¬Conn G ω x b then
      ((cluster G ω b).ncard : ℝ) else 0) (law p) := by
    have hs : MeasurableSet {ω | Conn G ω x a ∧ ¬Conn G ω x b} :=
      (measurableSet_conn G x a).inter (measurableSet_conn G x b).compl
    apply ((susceptibility_eq_integral G hloc hqt p hp b).1.indicator hs).congr
    exact Filter.Eventually.of_forall (fun ω => by
      by_cases h : Conn G ω x a ∧ ¬Conn G ω x b <;> simp [h])
  rw [integral_cluster_finite_partition G p hp x _ hl,
    integral_cluster_finite_partition G p hp x _ hr]
  apply tsum_congr
  intro W
  by_cases ha : a ∈ W
  · have hleft : (∫ ω, (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) else 0) ∂law p) =
        inducedSusceptibility G (W : Set V)ᶜ p b *
          (law p).real {ω | cluster G ω x = (W : Set V)} := by
      rw [←integral_event_indicator p _ (measurableSet_cluster_eq G x W),
        ←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : cluster G ω x = (W : Set V)
        · have hca : Conn G ω x a := by
            change a ∈ cluster G ω x
            rw [hc]
            exact ha
          have hf : (cluster G ω x).Finite := by rw [hc]; exact W.finite_toSet
          simp only [hc,ite_true,hca,exteriorSusceptibility_eq G p x b ω hf,mul_one,
            Set.mem_ofPred_eq]
        · simp only [hc,ite_false,Set.mem_ofPred_eq,mul_zero])
    have hright : (∫ ω, (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a ∧ ¬Conn G ω x b then ((cluster G ω b).ncard : ℝ) else 0)
        else 0) ∂law p) =
        (law p).real {ω | cluster G ω x = (W : Set V)} *
          inducedSusceptibility G (W : Set V)ᶜ p b := by
      rw [←cluster_cell_exterior_susceptibility G hloc hqt p hp W x b]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases hc : cluster G ω x = (W : Set V)
        · have hca : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hc]
          simp only [hc,ite_true,hca,true_and]
        · simp only [hc,ite_false,false_and])
    rw [hleft,hright,mul_comm]
  · have hz (ω : Set E) (hc : cluster G ω x = (W : Set V)) : ¬Conn G ω x a := by
      intro h
      have hh : a ∈ cluster G ω x := h
      rw [hc] at hh
      exact ha hh
    have he : (fun ω => if cluster G ω x = (W : Set V) then
        (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) else 0) =
        fun _ => (0 : ℝ) := by
      funext ω
      by_cases hc : cluster G ω x = (W : Set V)
      · simp only [hc,ite_true,ite_eq_right (hz ω hc)]
      · exact ite_eq_right hc
    rw [he,integral_zero]
    symm
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall (fun ω => by
      change (if cluster G ω x = (W : Set V) then
        (if Conn G ω x a ∧ ¬Conn G ω x b then ((cluster G ω b).ncard : ℝ) else 0)
        else 0) = 0
      by_cases hc : cluster G ω x = (W : Set V)
      · simp only [hc,ite_true,hz ω hc,false_and,ite_false]
      · exact ite_eq_right hc)

theorem exteriorConnectionMoment_eq_tsum [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x a b : V) :
    exteriorConnectionMoment G p x a b =
      ∑' y, law p {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} := by
  have hi : Integrable (fun ω => if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) (law p) :=
    (integrable_exteriorSusceptibility G hloc hqt p hp x b).indicator
      (measurableSet_conn G x a)
  have hn (ω : Set E) : 0 ≤ (if Conn G ω x a then
      exteriorSusceptibility G p x b ω else 0) := by
    split_ifs
    · exact exteriorSusceptibility_nonneg G p x b ω
    · rfl
  have he : exteriorConnectionMoment G p x a b = ENNReal.ofReal
      (∫ ω, (if Conn G ω x a then exteriorSusceptibility G p x b ω else 0) ∂law p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn)]
    apply lintegral_congr
    intro ω
    split_ifs <;> simp only [ENNReal.ofReal_zero]
  have hsEvent : MeasurableSet {ω | Conn G ω x a ∧ ¬Conn G ω x b} :=
    (measurableSet_conn G x a).inter (measurableSet_conn G x b).compl
  have hv := integral_cluster_size_event G hloc hqt p hp b _ hsEvent
  have hv' : (∫ ω, (if Conn G ω x a ∧ ¬Conn G ω x b then
      ((cluster G ω b).ncard : ℝ) else 0) ∂law p) =
      ∑' y, (law p).real {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y} := by
    convert hv using 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        by_cases h : Conn G ω x a ∧ ¬Conn G ω x b <;> simp [h])
    · rfl
  rw [he,integral_exterior_connection G hloc hqt p hp x a b,hv']
  have hs : Summable (fun y => (law p).real
      {ω | (Conn G ω x a ∧ ¬Conn G ω x b) ∧ Conn G ω b y}) := by
    apply (summable_twoPoint_subcritical G hloc hqt p hp b).of_nonneg_of_le
      (fun _ => measureReal_nonneg)
    intro y
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ h => h.2))
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => measureReal_nonneg) hs]
  exact tsum_congr (fun _ => ENNReal.ofReal_toReal (measure_ne_top _ _))

end Percolation.BenjaminiSchramm

end OAI
