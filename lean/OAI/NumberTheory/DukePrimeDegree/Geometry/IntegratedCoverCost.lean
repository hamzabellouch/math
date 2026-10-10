import OAI.NumberTheory.DukePrimeDegree.Entropy.SubexponentialCoverAlphabet

namespace OAI

/-! # Integrating the sublinear covering cost

Capping by the finite observation's per-step cost gives an integrable
bound even when the cusp height itself has infinite mean.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DukePrimeDegree

lemma measurable_windowHeight {Y : Type*} [MeasurableSpace Y]
    {T : Y → Y} (hT : Measurable T) {H : Y → ℕ} (hH : Measurable H) (N : ℕ) :
    Measurable (windowHeight T H N) := by
  have hm := Finset.measurable_range_sup'' (n := N)
    (f := fun k x => H (T^[k] x)) (fun k _ => hH.comp (hT.iterate k))
  change Measurable (fun x => (Finset.range (N+1)).sup (fun k => H (T^[k] x)))
  simpa only [Finset.sup'_eq_sup] using hm

theorem integral_capped_coverCost_tendsto_zero {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (H Q : Y → ℕ) (hH : Measurable H) (hstep : ∀ x, H (T x) ≤ H x+1)
    (J : ℕ → ℕ) {K C : ℝ} (hK : 0 < K) (hC : 0 ≤ C)
    (hJ : ∀ m, (J m:ℝ) ≤ K*Real.exp (C*(m:ℝ)))
    (hcode : ∀ m, Q '' {x | H x=m} ⊆ (Nat.pair m) '' Set.Iio (J m))
    {L : ℝ} (hL : 0 ≤ L) :
    Tendsto (fun N : ℕ => ∫ x, min
      (Real.log (coverAlphabet J (windowHeight T H N x)).card / N) L ∂μ)
      atTop (𝓝 0) := by
  let F : ℕ → Y → ℝ := fun N x =>
    min (Real.log (coverAlphabet J (windowHeight T H N x)).card / N) L
  have hm (N : ℕ) : Measurable (F N) := by
    exact (((measurable_of_countable (fun m : ℕ =>
      Real.log (coverAlphabet J m).card)).comp
        (measurable_windowHeight hT.measurable hH N)).div_const (N:ℝ)).min measurable_const
  have hn (N : ℕ) (x : Y) : 0 ≤ F N x := by
    apply le_min _ hL
    apply div_nonneg _ (Nat.cast_nonneg N)
    apply Real.log_nonneg
    have hmem := mem_coverAlphabet Q H J hcode
      (height_le_windowHeight T H (Nat.zero_le N) x)
    have hp : 0 < (coverAlphabet J (windowHeight T H N x)).card :=
      Finset.card_pos.mpr ⟨Q (T^[0] x),hmem⟩
    exact_mod_cast Nat.succ_le_of_lt hp
  have hb (N : ℕ) : ∀ᵐ x ∂μ, ‖F N x‖ ≤ L := by
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (hn N x)]
    exact min_le_right _ _
  have hl : ∀ᵐ x ∂μ, Tendsto (fun N => F N x) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_coverAlphabet_cost_tendsto_zero μ hT H Q hH hstep J hK hC hJ hcode]
      with x hx
    have hh := hx.2.min (tendsto_const_nhds (x := L))
    simpa only [F,min_eq_left hL] using hh
  have hi := tendsto_integral_of_dominated_convergence (fun _ : Y => L)
    (fun N => (hm N).aestronglyMeasurable) (integrable_const L) hb hl
  simpa only [integral_zero] using hi

end DukePrimeDegree

end

end OAI
