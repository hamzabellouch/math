import OAI.Probability.RadialTransition.BoundedCore

namespace OAI

universe uE uX uY

noncomputable section

open scoped BigOperators NNReal ContDiff ENNReal
open Filter MeasureTheory Set

namespace RadialTransition

section CompactEnvelope

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem support_norm_bound {F : E → ℝ} {D : Set E} {x v : E} {r M : ℝ}
    (hr : 0 < r) (hM : 0 ≤ M) (hball : Metric.closedBall x r ⊆ D)
    (hbound : ∀ y ∈ Metric.closedBall x r, |F y| ≤ M)
    (hv : SupportsOn F D x v) : ‖v‖ ≤ 2 * M / r := by
  apply norm_le_of_unit_inner_le _ (by positivity)
  intro z hz
  have hy : x + r • z ∈ Metric.closedBall x r := by
    simp [Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hr, hz]
  have hx : x ∈ Metric.closedBall x r := Metric.mem_closedBall_self hr.le
  have hh := hv (x + r • z) (hball hy)
  simp only [add_sub_cancel_left, real_inner_smul_right] at hh
  have hlo := (abs_le.mp (hbound x hx)).1
  have hhi := (abs_le.mp (hbound _ hy)).2
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem supportsOn_of_tendsto {F : ℕ → E → ℝ} {F₀ : E → ℝ} {D : Set E}
    {x v : ℕ → E} {x₀ v₀ : E}
    (hx : Tendsto x atTop (nhds x₀)) (hv : Tendsto v atTop (nhds v₀))
    (hbase : Tendsto (fun n => F n (x n)) atTop (nhds (F₀ x₀)))
    (hpoint : ∀ y ∈ D, Tendsto (fun n => F n y) atTop (nhds (F₀ y)))
    (hs : ∀ n, SupportsOn (F n) D (x n) (v n)) :
    SupportsOn F₀ D x₀ v₀ := by
  intro y hy
  exact le_of_tendsto_of_tendsto
    (hbase.add (hv.inner (tendsto_const_nhds.sub hx))) (hpoint y hy)
    (Eventually.of_forall fun n => hs n y hy)

theorem continuousOn_tendsto_sequence {X : Type uX} {Y : Type uY} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {S : Set X} (hf : ContinuousOn f S)
    {a : X} (ha : a ∈ S) {s : ℕ → X} (hs : ∀ n, s n ∈ S)
    (hsa : Tendsto s atTop (nhds a)) : Tendsto (fun n => f (s n)) atTop (nhds (f a)) := by
  apply (hf.continuousWithinAt ha).tendsto.comp
  exact tendsto_nhdsWithin_iff.mpr ⟨hsa, Eventually.of_forall hs⟩

theorem supportSet_envelope_closedHull [FiniteDimensional ℝ E]
    {F : ℝ → E → ℝ} {P : E → ℝ} {D : Set E} {K : Set ℝ} {x : E} {r : ℝ}
    (hD : IsOpen D) (hK : IsCompact K) (hr : 0 < r)
    (hball : Metric.closedBall x (2 * r) ⊆ D)
    (hF : ∀ i ∈ K, ConvexOn ℝ D (F i))
    (hFc : ContinuousOn (fun z : ℝ × E => F z.1 z.2) (K ×ˢ D))
    (hPc : ContinuousOn P D)
    (hle : ∀ i ∈ K, ∀ y ∈ D, F i y ≤ P y)
    (hactive : ∀ y ∈ Metric.closedBall x r, ∃ i ∈ K, F i y = P y) :
    supportSet P D x = closure (convexHull ℝ
      {v | ∃ i ∈ K, F i x = P x ∧ SupportsOn (F i) D x v}) := by
  classical
  let G : Set E := {v | ∃ i ∈ K, F i x = P x ∧ SupportsOn (F i) D x v}
  have hx : x ∈ D := hball (Metric.mem_closedBall_self (by positivity))
  have hG : G ⊆ supportSet P D x := by
    rintro v ⟨i, hi, heq, hv⟩ y hy
    rw [← heq]
    exact (hv y hy).trans (hle i hi y hy)
  have hback : closure (convexHull ℝ G) ⊆ supportSet P D x :=
    closure_minimal (convexHull_min hG (convex_supportSet P D x))
      (isClosed_supportSet P D x)
  apply Set.Subset.antisymm ?_ hback
  intro v hv
  by_contra hvout
  obtain ⟨ell, c, hsep, hvc⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ G).closure isClosed_closure hvout
  let z : E := (InnerProductSpace.toDual ℝ E).symm ell
  have hell (w : E) : inner ℝ w z = ell w := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  obtain ⟨M₀, hM₀⟩ := (hK.prod (isCompact_closedBall x (2 * r))).exists_bound_of_continuousOn
    (hFc.mono (Set.prod_mono Subset.rfl hball))
  let M := max 0 M₀
  have hM : 0 ≤ M := le_max_left _ _
  have hbound (i : ℝ) (hi : i ∈ K) (y : E) (hy : y ∈ Metric.closedBall x (2 * r)) :
      |F i y| ≤ M := (hM₀ (i, y) ⟨hi, hy⟩).trans (le_max_right _ _)
  let s : ℕ → ℝ := fun n => (r / (‖z‖ + 1)) * (1 / ((n : ℝ) + 1))
  have hspos (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  have hsbound (n : ℕ) : s n * ‖z‖ ≤ r := by
    have hn : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hden : 0 < ‖z‖ + 1 := by positivity
    have hdiv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one (by positivity)).mpr hn
    have hq : r / (‖z‖ + 1) * ‖z‖ ≤ r := by
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hden).mpr (show r * ‖z‖ ≤ r * (‖z‖ + 1) by nlinarith)
    calc
      s n * ‖z‖ = (r / (‖z‖ + 1) * ‖z‖) * (1 / ((n : ℝ) + 1)) := by dsimp [s]; ring
      _ ≤ (r / (‖z‖ + 1) * ‖z‖) * 1 :=
        mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ r := by simpa using hq
  have hs0 : Tendsto s atTop (nhds 0) := by
    simpa [s] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (r / (‖z‖ + 1))
  let y : ℕ → E := fun n => x + s n • z
  have hymem (n : ℕ) : y n ∈ Metric.closedBall x r := by
    simpa [y, Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos (hspos n)] using hsbound n
  have hyD (n : ℕ) : y n ∈ D :=
    hball (Metric.closedBall_subset_closedBall (by linarith) (hymem n))
  have hy0 : Tendsto y atTop (nhds x) := by
    simpa [y] using tendsto_const_nhds.add (hs0.smul (tendsto_const_nhds (x := z)))
  choose i hi hia using fun n => hactive (y n) (hymem n)
  choose w hw using fun n => supportSet_nonempty hD (hF (i n) (hi n)) (hyD n)
  have hwbound (n : ℕ) : ‖w n‖ ≤ 2 * M / r := by
    have hb : Metric.closedBall (y n) r ⊆ Metric.closedBall x (2 * r) := by
      intro q hq
      apply (dist_triangle q (y n) x).trans
      have hqn := Metric.mem_closedBall.mp hq
      have hyn := Metric.mem_closedBall.mp (hymem n)
      linarith
    exact support_norm_bound hr hM (hb.trans hball)
      (fun q hq => hbound (i n) (hi n) q (hb hq)) (hw n)
  obtain ⟨iw, hiw, σ, hσ, hlim⟩ :=
    (hK.prod (isCompact_closedBall (0 : E) (2 * M / r))).tendsto_subseq
      (x := fun n => (i n, w n)) (fun n => ⟨hi n, by simpa using hwbound n⟩)
  have hiwK : iw.1 ∈ K := hiw.1
  have hilim : Tendsto (fun n => i (σ n)) atTop (nhds iw.1) :=
    continuous_fst.tendsto iw |>.comp hlim
  have hwlim : Tendsto (fun n => w (σ n)) atTop (nhds iw.2) :=
    continuous_snd.tendsto iw |>.comp hlim
  have hylim : Tendsto (fun n => y (σ n)) atTop (nhds x) := hy0.comp hσ.tendsto_atTop
  have hbase : Tendsto (fun n => F (i (σ n)) (y (σ n))) atTop (nhds (F iw.1 x)) :=
    continuousOn_tendsto_sequence hFc (a := (iw.1, x)) ⟨hiwK, hx⟩
      (fun n => ⟨hi (σ n), hyD (σ n)⟩) (hilim.prodMk_nhds hylim)
  have hPbase : Tendsto (fun n => P (y (σ n))) atTop (nhds (P x)) :=
    continuousOn_tendsto_sequence hPc hx (fun n => hyD (σ n)) hylim
  have hia0 : F iw.1 x = P x := by
    apply tendsto_nhds_unique hbase
    simpa only [hia] using hPbase
  have hiws : SupportsOn (F iw.1) D x iw.2 := by
    apply supportsOn_of_tendsto hylim hwlim hbase ?_ (fun n => hw (σ n))
    intro q hq
    exact continuousOn_tendsto_sequence hFc (a := (iw.1, q)) ⟨hiwK, hq⟩
      (fun n => ⟨hi (σ n), hq⟩) (hilim.prodMk_nhds tendsto_const_nhds)
  have hiwG : iw.2 ∈ G := ⟨iw.1, hiwK, hia0, hiws⟩
  have hendpoint (n : ℕ) : inner ℝ v z ≤ inner ℝ (w n) z := by
    have hleft := hv (y n) (hyD n)
    have hright := hw n x hx
    have hdom := hle (i n) (hi n) x hx
    have hyx : y n - x = s n • z := by simp [y]
    have hxy : x - y n = -(s n • z) := by simp [y]
    rw [hyx, real_inner_smul_right] at hleft
    rw [hxy, inner_neg_right, real_inner_smul_right, hia n] at hright
    exact (mul_le_mul_iff_right₀ (hspos n)).mp (by nlinarith [hleft, hright, hdom])
  have hfinal : inner ℝ v z ≤ inner ℝ iw.2 z :=
    le_of_tendsto_of_tendsto tendsto_const_nhds (hwlim.inner tendsto_const_nhds)
      (Eventually.of_forall fun n => hendpoint (σ n))
  rw [hell, hell] at hfinal
  have hh := hsep iw.2 (subset_closure (subset_convexHull ℝ G hiwG))
  linarith

end CompactEnvelope

end RadialTransition

end

end OAI
