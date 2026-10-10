import OAI.Geometry.ProjectionVolume.FiniteVertices
import OAI.Geometry.ProjectionVolume.PolytopeOperations
import OAI.Geometry.ProjectionVolume.SupportGeometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace OAI

open Set MeasureTheory
open scoped RealInnerProductSpace Pointwise

noncomputable section
namespace Paper092

def halfspacePolar {d : ℕ} (K : Set (Euclidean d)) : Set (Euclidean d) :=
  {u | ∀ x ∈ K, ⟪u, x⟫ ≤ 1}

theorem halfspacePolar_convexHull {d : ℕ} (S : Set (Euclidean d)) :
    halfspacePolar (convexHull ℝ S) = halfspacePolar S := by
  ext u
  constructor
  · intro h x hx
    exact h x (subset_convexHull ℝ S hx)
  · intro h x hx
    have hc : Convex ℝ {y : Euclidean d | ⟪u, y⟫ ≤ 1} :=
      (convex_Iic (1 : ℝ)).linear_preimage (innerSL ℝ u).toLinearMap
    exact convexHull_min h hc hx

theorem halfspacePolar_isClosed {d : ℕ} (K : Set (Euclidean d)) :
    IsClosed (halfspacePolar K) := by
  unfold halfspacePolar
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le (by fun_prop) continuous_const

theorem halfspacePolar_bipolar {d : ℕ} {K : Set (Euclidean d)}
    (hK : IsClosed K) (hc : Convex ℝ K) (h0 : (0 : Euclidean d) ∈ K) :
    halfspacePolar (halfspacePolar K) = K := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨f, r, hr, hxgt⟩ := geometric_hahn_banach_closed_point hc hK hnot
    have hr0 : 0 < r := by simpa using hr 0 h0
    obtain ⟨u, hu⟩ := (InnerProductSpace.toDual ℝ (Euclidean d)).surjective f
    have hf (z : Euclidean d) : ⟪u, z⟫ = f z := by
      exact congrArg (fun g : StrongDual ℝ (Euclidean d) => g z) hu
    have hp : r⁻¹ • u ∈ halfspacePolar K := by
      intro z hz
      rw [real_inner_smul_left, hf]
      have := mul_le_mul_of_nonneg_left (hr z hz).le (inv_nonneg.mpr hr0.le)
      simpa [hr0.ne'] using this
    have h := hx (r⁻¹ • u) hp
    rw [real_inner_smul_right, real_inner_comm u x, hf] at h
    have hh := mul_le_mul_of_nonneg_left h hr0.le
    have hle : f x ≤ r := by simpa [← mul_assoc, hr0.ne'] using hh
    exact (not_le_of_gt hxgt) hle
  · intro hx u hu
    simpa only [real_inner_comm] using hu x hx

theorem halfspacePolar_isCompact {d : ℕ} {K : Set (Euclidean d)}
    (h0 : (0 : Euclidean d) ∈ interior K) : IsCompact (halfspacePolar K) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h0)
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨halfspacePolar_isClosed K, isBounded_iff_forall_norm_le.mpr ⟨2 / r, ?_⟩⟩
  intro y hy
  by_cases hz : y = 0
  · subst y
    simp only [norm_zero]
    positivity
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hz
  have hx : ((r / 2) / ‖y‖) • y ∈ K := by
    apply hball
    simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (div_pos (half_pos hr) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have h := hy _ hx
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at h
  have heq : (r / 2 / ‖y‖) * ‖y‖ ^ 2 = (r / 2) * ‖y‖ := by field_simp
  rw [heq] at h
  apply (le_div_iff₀ hr).mpr
  nlinarith

theorem finite_polar_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hc : IsCompact (halfspacePolar (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = halfspacePolar (S : Set (Euclidean d)) := by
  classical
  let T := S.filter (fun x => x ≠ 0)
  let J := {x // x ∈ T}
  have hn (i : J) : 0 < ‖(i : Euclidean d)‖ :=
    norm_pos_iff.mpr (Finset.mem_filter.mp i.property).2
  have heq : {x : Euclidean d | ∀ i : J,
      ⟪‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d), x⟫ ≤ ‖(i : Euclidean d)‖⁻¹} =
      halfspacePolar (S : Set (Euclidean d)) := by
    ext x
    constructor
    · intro hx y hy
      by_cases hy0 : y = 0
      · simp [hy0]
      let i : J := ⟨y, Finset.mem_filter.mpr ⟨hy, hy0⟩⟩
      have h := mul_le_mul_of_nonneg_left (hx i) (hn i).le
      rw [real_inner_smul_left] at h
      dsimp only [i] at h
      simpa only [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy0), one_mul, real_inner_comm] using h
    · intro hx i
      have h := mul_le_mul_of_nonneg_left (hx i (Finset.mem_filter.mp i.property).1)
        (inv_nonneg.mpr (hn i).le)
      rw [real_inner_smul_left]
      simpa only [mul_one, real_inner_comm] using h
  let P : HPolytope d J := {
    normal := fun i => ‖(i : Euclidean d)‖⁻¹ • (i : Euclidean d)
    offset := fun i => ‖(i : Euclidean d)‖⁻¹
    normal_unit := fun i => by simp [norm_smul, (hn i).ne']
    compact := by rw [heq]; exact hc
    strict_feasible := ⟨0, fun i => by simpa using inv_pos.mpr (hn i)⟩
    distinct := by
      intro i j h
      have hnorm : ‖(i : Euclidean d)‖ = ‖(j : Euclidean d)‖ :=
        inv_inj.mp (congrArg Prod.snd h)
      have hv := congrArg Prod.fst h
      apply Subtype.ext
      have hs := congrArg (fun v : Euclidean d => ‖(i : Euclidean d)‖ • v) hv
      simpa only [smul_smul, ← hnorm, mul_inv_cancel₀ (hn i).ne', one_smul] using hs }
  refine ⟨Fintype.card J, P.reindex (Fintype.equivFin J).symm, ?_⟩
  rw [HPolytope.reindex_body]
  exact heq

theorem finite_convex_hull_has_halfspaces_centered {d : ℕ} (S : Finset (Euclidean d))
    (h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S : Set (Euclidean d)))) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  have hc : IsCompact (halfspacePolar (S : Set (Euclidean d))) := by
    rw [← halfspacePolar_convexHull]
    exact halfspacePolar_isCompact h0
  obtain ⟨m, P, hP⟩ := finite_polar_has_halfspaces S hc
  obtain ⟨T, hT⟩ := halfspaces_are_finite_convex_hull P
  have heq : halfspacePolar (T : Set (Euclidean d)) = convexHull ℝ (S : Set (Euclidean d)) := by
    calc
      halfspacePolar (T : Set (Euclidean d)) =
          halfspacePolar (convexHull ℝ (T : Set (Euclidean d))) := (halfspacePolar_convexHull _).symm
      _ = halfspacePolar P.body := by rw [hT]
      _ = halfspacePolar (halfspacePolar (S : Set (Euclidean d))) := by rw [hP]
      _ = halfspacePolar (halfspacePolar (convexHull ℝ (S : Set (Euclidean d)))) := by
        rw [halfspacePolar_convexHull]
      _ = convexHull ℝ (S : Set (Euclidean d)) := halfspacePolar_bipolar
        (S.finite_toSet.isClosed_convexHull ℝ) (convex_convexHull ℝ _) (interior_subset h0)
  obtain ⟨n, Q, hQ⟩ := finite_polar_has_halfspaces T
    (by rw [heq]; exact S.finite_toSet.isCompact_convexHull ℝ)
  exact ⟨n, Q, hQ.trans heq⟩

theorem finite_convex_hull_has_halfspaces {d : ℕ} (S : Finset (Euclidean d))
    (hint : (interior (convexHull ℝ (S : Set (Euclidean d)))).Nonempty) :
    ∃ (m : ℕ) (P : HPolytope d (Fin m)), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  obtain ⟨v, hv⟩ := hint
  let S₀ : Finset (Euclidean d) := S.image (fun x => x - v)
  have hS₀ : convexHull ℝ (S₀ : Set (Euclidean d)) =
      (-v) +ᵥ convexHull ℝ (S : Set (Euclidean d)) := by
    dsimp [S₀]
    rw [Finset.coe_image]
    have himage : (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (-v) +ᵥ (S : Set (Euclidean d)) := by
      change (fun x : Euclidean d => x - v) '' (S : Set (Euclidean d)) =
        (fun x => -v + x) '' (S : Set (Euclidean d))
      congr 1
      funext x
      abel
    rw [himage, convexHull_vadd]
  have h0 : (0 : Euclidean d) ∈ interior (convexHull ℝ (S₀ : Set (Euclidean d))) := by
    rw [hS₀, interior_vadd]
    exact ⟨v, hv, by simp⟩
  obtain ⟨m, P, hP⟩ := finite_convex_hull_has_halfspaces_centered S₀ h0
  refine ⟨m, P.translate v, ?_⟩
  rw [HPolytope.translate_body, hP, hS₀]
  simp

end Paper092

end

end OAI
