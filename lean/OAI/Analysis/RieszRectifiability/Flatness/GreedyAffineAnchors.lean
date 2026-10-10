import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.LeastSquaredExcess
import OAI.Analysis.RieszRectifiability.Kernel.OrderedSpanConditioning

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped BigOperators

theorem infDist_affine_translate {d : ℕ} (p x : Ambient d)
    (U : Submodule ℝ (Ambient d)) :
    infDist x (AffineSubspace.mk' p U : Set (Ambient d)) =
      infDist (x - p) (U : Set (Ambient d)) := by
  have hi : Isometry (fun v : Ambient d => v + p) := (IsometryEquiv.vaddConst p).isometry
  have hset : (AffineSubspace.mk' p U : Set (Ambient d)) =
      (fun v : Ambient d => v + p) '' (U : Set (Ambient d)) := by
    ext y
    constructor
    · intro hy
      refine ⟨y - p, ?_, sub_add_cancel y p⟩
      exact AffineSubspace.mem_mk'.mp hy
    · rintro ⟨v, hv, rfl⟩
      apply AffineSubspace.mem_mk'.mpr
      simpa only [vsub_eq_sub, add_sub_cancel_right] using! hv
  rw [hset]
  simpa only [sub_add_cancel] using! (infDist_image hi (x := x - p) (t := (U : Set (Ambient d))))

theorem exists_ordered_separated_anchors_from_escape {n d : ℕ}
    (good : Set (Ambient d)) (p0 : Ambient d) (r : ℝ)
    (hescape : ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
      ∃ x ∈ good, r ≤ infDist x (S : Set (Ambient d))) :
    ∃ p : Fin n → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated n (fun i => p i - p0) r := by
  have hbuild : ∀ m : ℕ, m ≤ n → ∃ p : Fin m → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated m (fun i => p i - p0) r := by
    intro m
    induction m with
    | zero =>
      intro _hm
      refine ⟨Fin.elim0, ?_, trivial⟩
      intro i
      exact Fin.elim0 i
    | succ m ih =>
      intro hm
      obtain ⟨p, hp, hsep⟩ := ih (by omega)
      let U := Submodule.span ℝ (range (fun i => p i - p0))
      let S := AffineSubspace.mk' p0 U
      have hdim : finrank ℝ U ≤ m := by
        simpa only [Fintype.card_fin] using! (finrank_range_le_card (R := ℝ) (fun i => p i - p0))
      have hS : IsAffineNPlane (finrank ℝ U) S :=
        ⟨AffineSubspace.mk'_nonempty p0 U,
          congrArg (fun V : Submodule ℝ (Ambient d) => finrank ℝ V)
            (AffineSubspace.direction_mk' p0 U)⟩
      obtain ⟨x, hx, hxr⟩ := hescape (finrank ℝ U) (lt_of_le_of_lt hdim (by omega)) S hS
      have hxU : r ≤ infDist (x - p0) (U : Set (Ambient d)) := by
        rw [← infDist_affine_translate p0 x U]
        exact hxr
      have hinit : Fin.init (fun i : Fin (m + 1) =>
          Fin.snoc (α := fun _ => Ambient d) p x i - p0) =
          (fun i : Fin m => p i - p0) := by
        funext i
        simp only [Fin.init, Fin.snoc_castSucc]
      refine ⟨Fin.snoc p x, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Fin.snoc_last] using! hx
        · simpa only [Fin.snoc_castSucc] using! hp j
      · constructor
        · change OrderedSpanSeparated m (Fin.init (fun i =>
            Fin.snoc (α := fun _ => Ambient d) p x i - p0)) r
          rw [hinit]
          exact hsep
        · change r ≤ infDist (Fin.snoc (α := fun _ => Ambient d) p x (Fin.last m) - p0)
            (Submodule.span ℝ (range (Fin.init (fun i =>
              Fin.snoc (α := fun _ => Ambient d) p x i - p0))) : Set (Ambient d))
          rw [hinit, Fin.snoc_last]
          exact hxU
  exact hbuild n le_rfl

theorem exists_conditioned_anchors_from_escape {n d : ℕ}
    (good : Set (Ambient d)) (p0 : Ambient d) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 < r)
    (hgood : good ⊆ ball (0 : Ambient d) R) (hp0 : p0 ∈ good)
    (hescape : ∀ k : ℕ, k < n → ∀ S : AffineSubspace ℝ (Ambient d), IsAffineNPlane k S →
      ∃ x ∈ good, r ≤ infDist x (S : Set (Ambient d))) :
    ∃ p : Fin n → Ambient d, (∀ i, p i ∈ good) ∧
      OrderedSpanSeparated n (fun i => p i - p0) r ∧
      LinearIndependent ℝ (fun i => p i - p0) ∧
      ∀ t : Fin n → ℝ, (∑ i, |t i|) ≤
        spanConditionConstant (2 * R) r n * ‖∑ i, t i • (p i - p0)‖ := by
  obtain ⟨p, hp, hsep⟩ := exists_ordered_separated_anchors_from_escape good p0 r hescape
  have hnorm : ∀ i, ‖p i - p0‖ ≤ 2 * R := by
    intro i
    have hi : ‖p i‖ < R := by simpa only [mem_ball, dist_zero_right] using! hgood (hp i)
    have h0 : ‖p0‖ < R := by simpa only [mem_ball, dist_zero_right] using! hgood hp0
    exact (norm_sub_le (p i) p0).trans (by linarith)
  exact ⟨p, hp, hsep,
    ordered_span_linearIndependent (fun i => p i - p0) (2 * R) r (by positivity) hr hnorm hsep,
    ordered_span_coefficient_bound (fun i => p i - p0) (2 * R) r (by positivity) hr hnorm hsep⟩

end

end RieszRectifiability

end OAI
