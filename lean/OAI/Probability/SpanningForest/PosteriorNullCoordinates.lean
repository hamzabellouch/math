import OAI.Probability.SpanningForest.PosteriorTiltLimit

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Problem336.TiltLimit

theorem finiteEnergy_eq_of_zero_extra {I : Type*}
    {S T : Finset I} (hST : S ⊆ T) (h : I → ℝ) (x : I → Bool)
    (hzero : ∀ i ∈ T, i ∉ S → x i = false) :
    finiteEnergy S h x = finiteEnergy T h x := by
  classical
  apply Finset.sum_subset hST
  intro i hi hiS
  simp [hzero i hi hiS, bit]

theorem finiteTiltMean_eq_of_zero_extra {I : Type*}
    (ν : ProbabilityMeasure (I → Bool)) {S T : Finset I} (hST : S ⊆ T)
    (hzero : ∀ᵐ x ∂(ν : Measure (I → Bool)), ∀ i ∈ T, i ∉ S → x i = false)
    (h : I → ℝ) (e : I) :
    finiteTiltMean ν S h e = finiteTiltMean ν T h e := by
  have henergy : finiteEnergy S h =ᵐ[(ν : Measure (I → Bool))] finiteEnergy T h :=
    hzero.mono (fun x hx => finiteEnergy_eq_of_zero_extra hST h x hx)
  unfold finiteTiltMean tiltedMean
  congr 1
  · apply integral_congr_ae
    filter_upwards [henergy] with x hx
    rw [hx]
  · apply integral_congr_ae
    filter_upwards [henergy] with x hx
    rw [hx]

theorem limsup_finiteTiltMean_eq_of_zero_extra {I : Type*}
    (ν : ProbabilityMeasure (I → Bool)) (S T : ℕ → Finset I)
    (hST : ∀ n, S n ⊆ T n)
    (hzero : ∀ n, ∀ᵐ x ∂(ν : Measure (I → Bool)),
      ∀ i ∈ T n, i ∉ S n → x i = false)
    (h : I → ℝ) (e : I) :
    Filter.limsup (fun n => finiteTiltMean ν (S n) h e) Filter.atTop =
      Filter.limsup (fun n => finiteTiltMean ν (T n) h e) Filter.atTop := by
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall
    (fun n => finiteTiltMean_eq_of_zero_extra ν (hST n) (hzero n) h e)

end Problem336.TiltLimit

end

end OAI
