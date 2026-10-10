import OAI.Analysis.AncientFlat.Regularity.ParabolicInterpolation

namespace OAI
noncomputable section
open Set Filter Metric ParabolicInterior
open scoped ContDiff
namespace ParabolicInterpolation
lemma exists_interpolation_scale (α ε g : ℝ) (hα1 : α<1) (hε : 0<ε) (hg : 0<g) :
    ∃ q : ℝ, 0<q ∧ q≤1 ∧ 12*q≤g ∧ 110*q^(1-α)≤ε := by
  have hp : 0<1-α := sub_pos.mpr hα1
  have hc : ContinuousAt (fun q : ℝ => 110*q^(1-α)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 (1-α) (Or.inr hp.le))
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc ε hε
  let q := min (1/2) (min (g/24) (δ/2))
  have hq : 0<q := by dsimp [q]; positivity
  have hq1 : q≤1/2 := min_le_left _ _
  have hqg : q≤g/24 := (min_le_right _ _).trans (min_le_left _ _)
  have hqδ : q≤δ/2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q,hq,by linarith,by linarith,?_⟩
  have hh := @hclose q (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hq] using (show q<δ by linarith))
  simpa only [Real.dist_eq,Real.zero_rpow hp.ne',mul_zero,sub_zero,
    abs_of_nonneg (show 0≤110*q^(1-α) by positivity)] using hh.le
lemma lower_scale_epsilon (j : ℕ) (hj : j≤3) (q U M α ε : ℝ)
    (hq : 0<q) (hq1 : q≤1) (hU : 0≤U) (hM : 0≤M)
    (hsmall : 110*q^(1-α)≤ε) :
    110*(U/q^j+q^(4-j)*M)/q^α≤(110/(q^3*q^α))*U+ε*M := by
  have hqa : 0<q^α := Real.rpow_pos_of_pos hq _
  have hpow : q^3≤q^j := pow_le_pow_of_le_one hq.le hq1 hj
  have hu : U/q^j≤U/q^3 := by gcongr
  have hm : q^(4-j)*M≤q*M := mul_le_mul_of_nonneg_right
    (pow_le_of_le_one hq.le hq1 (by omega)) hM
  have heq : 110*q/q^α=110*q^(1-α) := by rw [Real.rpow_sub hq,Real.rpow_one]; ring
  calc
    _≤110*(U/q^3+q*M)/q^α := by gcongr
    _=(110/(q^3*q^α))*U+(110*q/q^α)*M := by ring
    _≤_ := by rw [heq]; gcongr
variable {V : Type} {E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem lower_jet_interpolation (α ε r R : ℝ) (hα : 0<α) (hα1 : α<1)
    (hε : 0<ε) (hrR : r<R) :
    ∃ C : ℝ, 0<C ∧ ∀ (u ut : ℝ → V → E) (I : Set ℝ), OrdConnected I →
      ∀ (U M : ℝ), 0≤U → 0≤M →
      (∀ t∈I, ContDiff ℝ 4 (u t)) →
      (∀ t∈I, ∀ x, ‖x‖<R → HasDerivAt (fun t => u t x) (ut t x) t) →
      (∀ t∈I, ∀ x, ‖x‖<R → ‖ut t x‖≤M) →
      (∀ t∈I, ∀ x, ‖x‖<R → ‖u t x‖≤U) →
      (∀ t∈I, ∀ x, ‖x‖<R → ‖iteratedFDeriv ℝ 4 (u t) x‖≤M) →
      ∀ j : ℕ, j≤3 → HolderBound α {p : V × ℝ | ‖p.1‖<r ∧ p.2∈I}
        (fun p => iteratedFDeriv ℝ j (u p.2) p.1) (ε*M+C*U) := by
  obtain ⟨q,hq,hq1,hqgap,hsmall⟩ := exists_interpolation_scale α ε (R-r) hα1 hε (sub_pos.mpr hrR)
  refine ⟨110/(q^3*q^α),by positivity,?_⟩
  intro u ut I hI U M hU hM hs hdt hUt hu hD j hj
  obtain ⟨hbs,hbh⟩ := lower_parabolic_bound j hj u ut I hI r R q U M α hq hq1
    (by linarith) hU hM hα.le hα1.le hs hdt hUt hu hD
  have hc : 110*(U/q^j+q^(4-j)*M)/q^α≤ε*M+110/(q^3*q^α)*U := by
    simpa only [add_comm] using lower_scale_epsilon j hj q U M α ε hq hq1 hU hM hsmall
  refine ⟨fun p hp => (hbs p hp).trans hc,?_⟩
  intro p hp z hz
  apply (hbh p hp z hz).trans
  exact mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg
    (by unfold pdist; positivity) _)
end ParabolicInterpolation

end

end OAI
