import OAI.Geometry.ProjectionVolume.PolytopeDefinitions
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith

namespace OAI

universe uι

open Set Filter Topology
open scoped RealInnerProductSpace

namespace Paper092
namespace HPolytope

variable {d : ℕ} {ι : Type uι} [Fintype ι] (P : HPolytope d ι)

theorem extreme_active_unique {x y : Euclidean d}
    (hx : x ∈ P.body.extremePoints ℝ)
    (ha : ∀ i, ⟪P.normal i, x⟫ = P.offset i → ⟪P.normal i, y⟫ = P.offset i) :
    y = x := by
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,
      ⟪P.normal i, x⟫ < P.offset i →
        ⟪P.normal i, x + t • (y - x)⟫ < P.offset i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : ⟪P.normal i, x⟫ < P.offset i
    · have h : ∀ᶠ t : ℝ in 𝓝 0,
          ⟪P.normal i, x + t • (y - x)⟫ < P.offset i :=
        (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simpa using hi)
      filter_upwards [h] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall fun _ h => (hi h).elim
  obtain ⟨ε, hε, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  have hpert (t : ℝ) (ht : dist t 0 < ε) : x + t • (y - x) ∈ P.body := by
    intro i
    rcases (hx.1 i).lt_or_eq with hi | hi
    · exact (hsmall ht i hi).le
    · simp [inner_add_right, inner_smul_right, inner_sub_right, hi, ha i hi]
  have hp : dist (ε / 2) 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]
    linarith
  have hm : dist (-(ε / 2)) 0 < ε := by simpa using hp
  have hxplus := hx.2 (hpert (ε / 2) hp)
    (show x - (ε / 2) • (y - x) ∈ P.body by simpa only [neg_smul, ← sub_eq_add_neg] using hpert (-(ε / 2)) hm)
    (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • (y - x)))
  have hz : (ε / 2) • (y - x) = 0 := add_left_cancel (hxplus.trans (add_zero x).symm)
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt (half_pos hε)))

theorem finite_extremePoints : (P.body.extremePoints ℝ).Finite := by
  classical
  let active (x : Euclidean d) : Finset ι :=
    Finset.univ.filter (fun i => ⟪P.normal i, x⟫ = P.offset i)
  have hi : Set.InjOn active (P.body.extremePoints ℝ) := by
    intro x hx y _ hxy
    apply (P.extreme_active_unique hx ?_).symm
    intro i hix
    have hm : i ∈ active x := by simp [active, hix]
    rw [hxy] at hm
    exact (Finset.mem_filter.mp hm).2
  exact (Set.toFinite (Set.univ : Set (Finset ι))).of_injOn
    (fun _ _ => Set.mem_univ _) hi

theorem eq_convexHull_extremePoints : P.body = convexHull ℝ (P.body.extremePoints ℝ) := by
  have hc : Convex ℝ P.body := by
    change Convex ℝ {x : Euclidean d | ∀ i, ⟪P.normal i, x⟫ ≤ P.offset i}
    simp only [Set.ofPred_forall]
    exact convex_iInter fun i => (convex_Iic (P.offset i)).linear_preimage
      (innerSL ℝ (P.normal i)).toLinearMap
  have h := closure_convexHull_extremePoints P.compact hc
  change closure (convexHull ℝ (P.body.extremePoints ℝ)) = P.body at h
  rw [P.finite_extremePoints.isClosed_convexHull ℝ |>.closure_eq] at h
  exact h.symm

end HPolytope

theorem halfspaces_are_finite_convex_hull {d : ℕ} {ι : Type uι} [Fintype ι]
    (P : HPolytope d ι) :
    ∃ S : Finset (Euclidean d), P.body = convexHull ℝ (S : Set (Euclidean d)) := by
  classical
  exact ⟨P.finite_extremePoints.toFinset, by simpa using P.eq_convexHull_extremePoints⟩
end Paper092

end OAI
