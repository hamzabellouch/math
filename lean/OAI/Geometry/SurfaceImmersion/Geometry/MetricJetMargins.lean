import OAI.Geometry.Immersion.ClosedSurface.MetricBounds
import OAI.Geometry.Immersion.ClosedSurface.ProjectionStability
import OAI.Geometry.Immersion.ClosedSurface.ForcedModes

namespace OAI

/-! Compact metric positivity controls the first jets of all sufficiently
accurate approximate isometries. -/
noncomputable section
open Set
open scoped Topology BigOperators Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma norm_le_one_add_dot_self (X : RVec 4) : ‖X‖ ≤ 1+X ⬝ᵥ X := by
  have hsum : 0 ≤ X ⬝ᵥ X := Finset.sum_nonneg (fun j _ => mul_self_nonneg (X j))
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ 1+X ⬝ᵥ X)).mpr
  intro i
  have hi : X i*X i ≤ X ⬝ᵥ X :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (X j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|X i|-1/2),sq_abs (X i)]

lemma firstJetPair_norm_le_metric (F : RField 4) (p : Base) :
    ‖firstJetPair F p‖ ≤ 1+‖realMetricTensor F p‖ := by
  apply (max_le_iff).mpr
  constructor
  · have h := (le_abs_self (realMetricTensor F p 0)).trans
      (norm_le_pi_norm (realMetricTensor F p) (0 : Fin 3))
    exact (norm_le_one_add_dot_self _).trans (by
      change 1+realMetricTensor F p 0 ≤ _
      linarith)
  · have h := (le_abs_self (realMetricTensor F p 2)).trans
      (norm_le_pi_norm (realMetricTensor F p) (2 : Fin 3))
    exact (norm_le_one_add_dot_self _).trans (by
      change 1+realMetricTensor F p 2 ≤ _
      linarith)

lemma gramDet_firstJetPair (F : RField 4) (p : Base) :
    NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 =
      realMetricTensor F p 0*realMetricTensor F p 2-(realMetricTensor F p 1)^2 := rfl

/-- Only the compact set of prescribed positive metrics is fixed. The
approximate immersion and all its higher derivatives remain arbitrary. -/
theorem compact_metric_firstJet_margin {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hpos : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) :
    ∃ ε R c : ℝ, 0 < ε ∧ 0 < R ∧ 0 < c ∧
      ∀ (F : RField 4) (p : Base) (H : PhaseMean.Tensor), H ∈ T →
      ‖realMetricTensor F p-H‖ < ε →
      ‖firstJetPair F p‖ ≤ R ∧ c ≤ NormalFrame.gramDet
        (firstJetPair F p).1 (firstJetPair F p).2 := by
  let det : PhaseMean.Tensor → ℝ := fun H => H 0*H 2-(H 1)^2
  have hd : Continuous det := by unfold det; fun_prop
  by_cases hne : T.Nonempty
  · obtain ⟨H₀,hH₀,hmin⟩ := hT.exists_isMinOn hne hd.continuousOn
    let c := det H₀/2
    have hc : 0 < c := half_pos (hpos H₀ hH₀)
    have hs : T ⊆ {H | c < det H} := by
      intro H hH
      exact (half_lt_self (hpos H₀ hH₀)).trans_le (hmin hH)
    obtain ⟨ε,hε,hthick⟩ := hT.exists_thickening_subset_open
      (isOpen_lt continuous_const hd) hs
    obtain ⟨B,hB⟩ := hT.exists_bound_of_continuousOn continuousOn_id
    let R := |B|+2
    have hR : 0 < R := by dsimp [R]; positivity
    refine ⟨min ε 1,R,c,lt_min hε zero_lt_one,hR,hc,?_⟩
    intro F p H hH hclose
    have hclose1 : ‖realMetricTensor F p-H‖ ≤ 1 :=
      (hclose.trans_le (min_le_right _ _)).le
    have hmetric : ‖realMetricTensor F p‖ ≤ |B|+1 := by
      calc
        ‖realMetricTensor F p‖ = ‖(realMetricTensor F p-H)+H‖ := by congr 1; abel
        _ ≤ ‖realMetricTensor F p-H‖+‖H‖ := norm_add_le _ _
        _ ≤ 1+B := add_le_add hclose1 (hB H hH)
        _ ≤ |B|+1 := by linarith [le_abs_self B]
    refine ⟨(firstJetPair_norm_le_metric F p).trans (by dsimp [R]; linarith),?_⟩
    rw [gramDet_firstJetPair]
    exact (hthick (Metric.mem_thickening_iff.mpr
      ⟨H,hH,by simpa only [dist_eq_norm] using hclose.trans_le (min_le_left _ _)⟩)).le
  · refine ⟨1,1,1,zero_lt_one,zero_lt_one,zero_lt_one,?_⟩
    intro F p H hH _
    exact False.elim (hne ⟨H,hH⟩)

end ClosedSurfaceR4.RealModes

end

end OAI
