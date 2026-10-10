import Mathlib

namespace OAI

universe uE

noncomputable section

open Set Filter
open scoped Topology

namespace Problem326

/-- Two differentiable curves with the same value and derivative at a joining
time can be glued there without losing differentiability. -/
theorem hasDerivAt_join
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x y : ℝ → E} {c : ℝ} {v : E}
    (hx : HasDerivAt x v c) (hy : HasDerivAt y v c) (hxy : x c = y c) :
    HasDerivAt (fun t => if t ≤ c then x t else y t) v c := by
  have hl : HasDerivWithinAt (fun t => if t ≤ c then x t else y t) v (Iic c) c :=
    hx.hasDerivWithinAt.congr (fun t ht => ite_eq_left ht) (ite_eq_left le_rfl)
  have hr : HasDerivWithinAt (fun t => if t ≤ c then x t else y t) v (Ioi c) c :=
    hy.hasDerivWithinAt.congr (fun t ht => ite_eq_right (not_le.mpr ht))
      (by simpa using hxy)
  have h := hl.union hr
  simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using h

/-- Concatenation of autonomous ODE solutions. Ordinary derivatives at the end
points avoid a separate endpoint extension argument. -/
theorem hasDerivAt_join_on_Icc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {x y : ℝ → E} {a c b : ℝ}
    (hx : ∀ t ∈ Icc a c, HasDerivAt x (f (x t)) t)
    (hy : ∀ t ∈ Icc c b, HasDerivAt y (f (y t)) t)
    (hxy : x c = y c) :
    ∀ t ∈ Icc a b,
      HasDerivAt (fun s => if s ≤ c then x s else y s)
        (f (if t ≤ c then x t else y t)) t := by
  intro t ht
  rcases lt_trichotomy t c with htc | heq | hct
  · have heq : (fun s => if s ≤ c then x s else y s) =ᶠ[𝓝 t] x := by
      filter_upwards [eventually_lt_nhds htc] with s hs
      exact ite_eq_left hs.le
    simpa only [ite_eq_left htc.le] using
      (hx t ⟨ht.1, htc.le⟩).congr_of_eventuallyEq heq
  · subst t
    have hxc := hx c ⟨ht.1, le_rfl⟩
    have hyc : HasDerivAt y (f (x c)) c := by
      simpa only [hxy] using hy c ⟨le_rfl, ht.2⟩
    simpa only [ite_eq_left le_rfl] using hasDerivAt_join hxc hyc hxy
  · have heq : (fun s => if s ≤ c then x s else y s) =ᶠ[𝓝 t] y := by
      filter_upwards [eventually_gt_nhds hct] with s hs
      exact ite_eq_right (not_le.mpr hs)
    simpa only [ite_eq_right (not_le.mpr hct)] using
      (hy t ⟨hct.le, ht.2⟩).congr_of_eventuallyEq heq

/-- A uniform local existence statement extends a finite solution by one fixed
step whenever its endpoint remains in the allowed set. -/
theorem exists_extend_solution_on_Icc
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {K : Set E} {T a c : ℝ} {x : ℝ → E}
    (hlocal : ∀ z ∈ K, ∃ y : ℝ → E, y 0 = z ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt y (f (y t)) t)
    (hx : ∀ t ∈ Icc a c, HasDerivAt x (f (x t)) t)
    (hxc : x c ∈ K) :
    ∃ x' : ℝ → E, EqOn x' x (Iic c) ∧
      ∀ t ∈ Icc a (c + T), HasDerivAt x' (f (x' t)) t := by
  obtain ⟨y, hy0, hy⟩ := hlocal (x c) hxc
  let ys : ℝ → E := fun t => y (t - c)
  have hys : ∀ t ∈ Icc c (c + T), HasDerivAt ys (f (ys t)) t := by
    intro t ht
    have htd : t - c ∈ Icc (0 : ℝ) T := by
      constructor <;> linarith [ht.1, ht.2]
    simpa [ys, Function.comp_def] using (hy (t - c) htd).scomp t ((hasDerivAt_id t).sub_const c)
  have hxy : x c = ys c := by simp [ys, hy0]
  refine ⟨fun t => if t ≤ c then x t else ys t, ?_, ?_⟩
  · exact fun t ht => ite_eq_left ht
  · exact hasDerivAt_join_on_Icc hx hys hxy

end Problem326

end

end OAI
