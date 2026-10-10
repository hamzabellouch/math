import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Countable local Lipschitz bounds that approximate the norm of the
actual differential. These are used to localize the published curve
coarea inequality without adding a weighted curve-coarea input. -/

open Set Filter Metric
open scoped Topology NNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_local_derivative_bound
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) {x : ℂ} (hx : x ∈ D) :
    ∃ U : Set ℂ, ∃ L : ℝ≥0, IsOpen U ∧ x ∈ U ∧ U ⊆ D ∧
      LipschitzOnWith L f U ∧ ∀ z ∈ U, (L : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  have hdf := (hf.continuousOn_fderiv_of_isOpen hD (by norm_num)).continuousAt
    (hD.mem_nhds hx)
  have hnear : {z | ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2} ∈ 𝓝 x := by
    have hc : ContinuousAt (fun z => ‖fderiv ℝ f z - fderiv ℝ f x‖) x :=
      (hdf.sub continuousAt_const).norm
    exact hc.preimage_mem_nhds (Iio_mem_nhds (by simpa using half_pos hε))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem (hD.mem_nhds hx) hnear)
  let L : ℝ≥0 := ⟨‖fderiv ℝ f x‖ + ε / 2, by positivity⟩
  refine ⟨ball x r, L, isOpen_ball, mem_ball_self hr, fun z hz => (hball hz).1, ?_, ?_⟩
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun z hz => (hf.differentiableOn (by norm_num) z (hball hz).1).differentiableAt
        (hD.mem_nhds (hball hz).1)) ?_ (convex_ball x r)
    intro z hz
    change ‖fderiv ℝ f z‖ ≤ ‖fderiv ℝ f x‖ + ε / 2
    have hn := norm_sub_norm_le (fderiv ℝ f z) (fderiv ℝ f x)
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith
  · intro z hz
    change ‖fderiv ℝ f x‖ + ε / 2 ≤ ‖fderiv ℝ f z‖ + ε
    have hn := norm_sub_norm_le (fderiv ℝ f x) (fderiv ℝ f z)
    rw [norm_sub_rev] at hn
    have hclose : ‖fderiv ℝ f z - fderiv ℝ f x‖ < ε / 2 := (hball hz).2
    linarith

theorem exists_countable_derivative_cover
    {D : Set ℂ} (hD : IsOpen D) {f : ℂ → ℝ} (hf : ContDiffOn ℝ 1 f D)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℕ → Set ℂ, ∃ L : ℕ → ℝ≥0,
      (∀ n, IsOpen (U n)) ∧ D ⊆ ⋃ n, U n ∧
      (∀ n, U n ⊆ D) ∧ (∀ n, LipschitzOnWith (L n) f (U n)) ∧
      ∀ n z, z ∈ U n → (L n : ℝ) ≤ ‖fderiv ℝ f z‖ + ε := by
  classical
  rcases D.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ => ∅, fun _ => 0, fun _ => isOpen_empty, empty_subset _,
      fun _ => empty_subset _, fun _ => ?_, ?_⟩
    · intro z hz
      exact hz.elim
    · simp
  let : Nonempty D := hne.to_subtype
  choose U L hU hxU hUD hLip hbound using
    fun x : D => exists_local_derivative_bound hD hf hε x.property
  have hcover : D ⊆ ⋃ x : D, U x := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  obtain ⟨q, hq⟩ := (IsLindelof.of_coe : IsLindelof D).indexed_countable_subcover U hU hcover
  exact ⟨fun n => U (q n), fun n => L (q n), fun n => hU (q n), hq,
    fun n => hUD (q n), fun n => hLip (q n), fun n => hbound (q n)⟩

end CircleDomainRigidity

end

end OAI
