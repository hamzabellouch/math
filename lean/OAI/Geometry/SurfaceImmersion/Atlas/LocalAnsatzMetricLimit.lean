import OAI.Geometry.SurfaceImmersion.Primitive.LocalAnsatzProfiles

namespace OAI

/-! The leading pullback metric of the actual supported periodic ansatz. -/

noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

/-- Local smoothness and periodicity suffice for a compact uniform value bound;
the local family need not be smooth across the boundary of its domain. -/
lemma Family.compact_value_bound (U : Family O E) {Q : Set A}
    (hQ : IsCompact Q) (hQO : Q ⊆ O) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Q, ∀ t : Period, ‖U.val p t‖ ≤ B := by
  have hdom : Q ×ˢ Icc (0 : ℝ) 1 ⊆ (O : Set A) ×ˢ (univ : Set ℝ) := by
    intro y hy
    exact ⟨hQO hy.1,mem_univ _⟩
  obtain ⟨B,hb⟩ := (hQ.prod (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))).exists_bound_of_continuousOn
    (U.smooth.continuousOn.mono hdom)
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro p hp t
  let s : ℝ := AddCircle.equivIco 1 0 t
  have hs : s ∈ Ico (0 : ℝ) 1 := by
    simpa only [zero_add] using (AddCircle.equivIco 1 0 t).property
  have ht : (s : Period) = t := AddCircle.coe_equivIco
  rw [← ht]
  exact (hb (p,s) ⟨hp,hs.1,hs.2.le⟩).trans (le_max_right _ _)

private lemma inner_error_bound {u v a b : E} {B C z : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hu : ‖u-a‖ ≤ C*z) (hv : ‖v-b‖ ≤ C*z)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖inner ℝ u v-inner ℝ a b‖ ≤ (C*C+2*B*C)*z := by
  have he : inner ℝ u v-inner ℝ a b =
      inner ℝ (u-a) (v-b)+inner ℝ (u-a) b+inner ℝ a (v-b) := by
    simp only [inner_sub_left,inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℝ (u-a) (v-b)‖+‖inner ℝ (u-a) b‖+‖inner ℝ a (v-b)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖u-a‖*‖v-b‖+‖u-a‖*‖b‖+‖a‖*‖v-b‖ :=
      add_le_add (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
        (norm_inner_le_norm _ _)
    _ ≤ (C*z)*(C*z)+(C*z)*B+B*(C*z) := by gcongr
    _ = C*C*(z*z)+(2*B*C)*z := by ring
    _ ≤ C*C*z+(2*B*C)*z := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hz1 hz).trans_eq (mul_one z)) (mul_self_nonneg C)
    _ = (C*C+2*B*C)*z := by ring

namespace Geometry

variable [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E]
  {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The circular velocity law makes the leading metric independent of its
fast phase, including the mixed coefficient. -/
lemma leading_metric_values {p : A} (hp : p ∈ O) (t : Period) :
    inner ℝ (g.longitudinal.val p t) (g.longitudinal.val p t) =
      inner ℝ (g.X₀ p) (g.X₀ p)+g.q p ∧
    inner ℝ (g.longitudinal.val p t) (g.Y p) = inner ℝ (g.X₀ p) (g.Y p) := by
  have hx := g.perpX₀ p hp _ (g.V_mem p hp t)
  have hy := g.perpY p hp _ (g.V_mem p hp t)
  have hx' : inner ℝ (g.V.val p t) (g.X₀ p) = 0 := by
    rw [real_inner_comm]
    exact hx
  have hy' : inner ℝ (g.V.val p t) (g.Y p) = 0 := by
    rw [real_inner_comm]
    exact hy
  simp only [longitudinal,Family.add_apply,Family.constant_apply _ _ hp,
    inner_add_left,inner_add_right,hx,hx',hy',g.circle p hp t,zero_add,add_zero]
  trivial

omit [FiniteDimensional ℝ A] [CompleteSpace E] in
/-- Relative to the old immersion, the leading metric increases precisely the
longitudinal coefficient by the velocity variance. -/
lemma leading_metric_increment {F : A → E} (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p)
    {p : A} (hp : p ∈ O) (t : Period) :
    inner ℝ (g.longitudinal.val p t) (g.longitudinal.val p t) =
      inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dx)+
        (g.q p-inner ℝ (average (g.V.val p)) (average (g.V.val p))) ∧
    inner ℝ (g.longitudinal.val p t) (g.Y p) =
      inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dy) := by
  have hmean : average (g.V.val p) ∈ g.plane p :=
    average_mem_submodule (g.plane p) (g.V.val p).continuous (g.V_mem p hp)
  have hx := g.perpX₀ p hp _ hmean
  have hy := g.perpY p hp _ hmean
  have hx' : inner ℝ (average (g.V.val p)) (g.X₀ p) = 0 := by
    rw [real_inner_comm]
    exact hx
  have hy' : inner ℝ (average (g.V.val p)) (g.Y p) = 0 := by
    rw [real_inner_comm]
    exact hy
  obtain ⟨hxx,hxy⟩ := g.leading_metric_values hp t
  rw [hX p hp,hY p hp]
  simp only [inner_add_left,inner_add_right,hx,hx',hy',zero_add,add_zero]
  constructor
  · rw [hxx]
    ring
  · exact hxy

/-- The three actual metric coefficients approach the old pullback metric plus
the variance in the phase direction, uniformly at linear rate in `z`. -/
theorem compact_initial_ansatz_metric {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period)))
    (hinit : U 0 = g.initial) {Q : Set A} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hx : ℓ dx = 1) (hy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      let f := finiteAnsatz F U ℓ (n+1) z
      ‖inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx)-
        (inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dx)+
          (g.q p-inner ℝ (average (g.V.val p)) (average (g.V.val p))))‖ ≤ C*z ∧
      ‖inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy)-
        inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dy)‖ ≤ C*z ∧
      ‖inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy)-
        inner ℝ (fderiv ℝ F p dy) (fderiv ℝ F p dy)‖ ≤ C*z := by
  obtain ⟨N,hN,hn⟩ := g.compact_initial_ansatz_profiles hF U hU hinit hQ hQO
    ℓ dx hx hy hX hY n
  obtain ⟨B,hB,hb⟩ := g.longitudinal.compact_value_bound hQ hQO
  obtain ⟨D,hD,hd⟩ := g.transverse.compact_value_bound hQ hQO
  refine ⟨N*N+2*(B+D)*N,by positivity,?_⟩
  intro z hz hz1 p hp
  dsimp only
  let f := finiteAnsatz F U ℓ (n+1) z
  let t : Period := ((ℓ p/z : ℝ) : Period)
  have hpO := hQO hp
  obtain ⟨hyerr,_,hxerr,_,_⟩ := hn z hz hz1 p hp
  change ‖fderiv ℝ f p dx-g.longitudinal.val p t‖ ≤ N*z at hxerr
  change ‖fderiv ℝ f p dy-g.Y p‖ ≤ N*z at hyerr
  have hxb : ‖g.longitudinal.val p t‖ ≤ B+D :=
    (hb p hp t).trans (by linarith)
  have hyb : ‖g.Y p‖ ≤ B+D := by
    have hd' := hd p hp t
    rw [transverse,Family.constant_apply _ _ hpO] at hd'
    linarith
  have hxx := inner_error_bound (add_nonneg hB hD) hN hz.le hz1 hxerr hxerr hxb hxb
  have hxy := inner_error_bound (add_nonneg hB hD) hN hz.le hz1 hxerr hyerr hxb hyb
  have hyy := inner_error_bound (add_nonneg hB hD) hN hz.le hz1 hyerr hyerr hyb hyb
  obtain ⟨hxx',hxy'⟩ := g.leading_metric_increment dx hX hY hpO t
  rw [hxx'] at hxx
  rw [hxy'] at hxy
  refine ⟨hxx,hxy,?_⟩
  simpa only [hY p hpO] using hyy

/-- The usual amplitude normalization identifies the variance with `a²`, so
the limiting metric is the prescribed rank-one metric increment. -/
theorem compact_initial_ansatz_metric_amplitude {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period)))
    (hinit : U 0 = g.initial) {Q : Set A} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hx : ℓ dx = 1) (hy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p) (a : A → ℝ)
    (ha : ∀ p ∈ Q, g.q p-inner ℝ (average (g.V.val p)) (average (g.V.val p)) = a p^2)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      let f := finiteAnsatz F U ℓ (n+1) z
      ‖inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dx)-
        (inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dx)+a p^2)‖ ≤ C*z ∧
      ‖inner ℝ (fderiv ℝ f p dx) (fderiv ℝ f p dy)-
        inner ℝ (fderiv ℝ F p dx) (fderiv ℝ F p dy)‖ ≤ C*z ∧
      ‖inner ℝ (fderiv ℝ f p dy) (fderiv ℝ f p dy)-
        inner ℝ (fderiv ℝ F p dy) (fderiv ℝ F p dy)‖ ≤ C*z := by
  obtain ⟨C,hC,hb⟩ := g.compact_initial_ansatz_metric hF U hU hinit hQ hQO ℓ dx hx hy hX hY n
  refine ⟨C,hC,?_⟩
  intro z hz hz1 p hp
  simpa only [ha p hp] using hb z hz hz1 p hp

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
