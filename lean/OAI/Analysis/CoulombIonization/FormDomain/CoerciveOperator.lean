import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
section CoerciveOperator
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

lemma coercive_operator_bijective (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) : Function.Bijective A := by
  have hb (u : V) : c * ‖u‖ ≤ ‖A u‖ := by
    have hi := re_inner_le_norm (𝕜 := ℂ) u (A u)
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · have hp : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu)
      apply (mul_le_mul_iff_left₀ hp).mp
      calc
        c * ‖u‖ * ‖u‖ = c * ‖u‖ ^ 2 := by ring
        _ ≤ (⟪u, A u⟫_ℂ).re := hA u
        _ ≤ ‖A u‖ * ‖u‖ := by simpa only [RCLike.re_eq_complex_re, mul_comm] using hi
  have ha : AntilipschitzWith c⁻¹.toNNReal A := by
    apply A.antilipschitz_of_bound
    intro u
    rw [Real.coe_toNNReal _ (le_of_lt (inv_pos.mpr hc))]
    exact (le_inv_mul_iff₀ hc).mpr (hb u)
  have hcl : IsClosed (A.range : Set V) := ha.isClosed_range A.uniformContinuous
  let : CompleteSpace A.range := hcl.completeSpace_coe
  have hr : A.range = ⊤ := by
    rw [← A.range.orthogonal_orthogonal, Submodule.eq_top_iff']
    intro u w hw
    have hw0 : w = 0 := by
      have hi := hw (A w) ⟨w, rfl⟩
      have hh := hA w
      have hz : (⟪w, A w⟫_ℂ).re = 0 := by
        rw [← inner_conj_symm, hi]
        rfl
      rw [hz] at hh
      have hs : c * ‖w‖ ^ 2 = 0 := le_antisymm hh (mul_nonneg hc.le (sq_nonneg _))
      have hn : ‖w‖ = 0 := (sq_eq_zero_iff).mp ((mul_eq_zero.mp hs).resolve_left hc.ne')
      exact norm_eq_zero.mp hn
    simp [hw0]
  exact ⟨ha.injective, LinearMap.range_eq_top.mp hr⟩

def coerciveEquiv (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) : V ≃L[ℂ] V :=
  ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr (coercive_operator_bijective A hc hA).1)
    (LinearMap.range_eq_top.mpr (coercive_operator_bijective A hc hA).2)

end CoerciveOperator
section InverseOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma selfAdjoint_denseRange {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : DenseRange R := by
  have horth : R.rangeᗮ = ⊥ := by
    rw [R.orthogonal_range, hR.adjoint_eq]
    exact LinearMap.ker_eq_bot.mpr hinj
  change Dense (R.range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]

def inverseOperator (R : H →L[ℂ] H) : H →ₗ.[ℂ] H := (R.toPMap ⊤).inverse

omit [CompleteSpace H] in
lemma toPMap_top_ker {R : H →L[ℂ] H} (hinj : Function.Injective R) :
    (R.toPMap ⊤).toFun.ker = ⊥ := by
  apply LinearMap.ker_eq_bot.mpr
  intro x y hxy
  apply Subtype.ext
  exact hinj hxy

omit [CompleteSpace H] in
lemma inverseOperator_graph {R : H →L[ℂ] H} (hinj : Function.Injective R) (x y : H) :
    (x, y) ∈ (inverseOperator R).graph ↔ R y = x := by
  have hker : (R.toPMap ⊤).ker = ⊥ := by
    simp only [LinearPMap.ker, toPMap_top_ker hinj, Submodule.map_bot]
  rw [inverseOperator, LinearPMap.inverse_graph hker]
  simp only [Submodule.mem_map, LinearPMap.mem_graph_iff, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨z, hz1, hz2⟩, hb, ha⟩
    exact (congrArg R (hz1.trans ha).symm).trans (hz2.trans hb)
  · intro h
    exact ⟨y, x, ⟨⟨y, trivial⟩, rfl, h⟩, rfl, rfl⟩

omit [CompleteSpace H] in
lemma inverseOperator_domain (R : H →L[ℂ] H) :
    (inverseOperator R).domain = R.range := by
  rw [inverseOperator, LinearPMap.inverse_domain]
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.val, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a, trivial⟩, rfl⟩

theorem inverseOperator_selfAdjoint {R : H →L[ℂ] H} (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) : IsSelfAdjoint (inverseOperator R) := by
  have hd : Dense ((inverseOperator R).domain : Set H) := by
    rw [inverseOperator_domain]
    exact selfAdjoint_denseRange hR hinj
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  ext p
  rcases p with ⟨x, y⟩
  rw [Submodule.mem_adjoint_iff, inverseOperator_graph hinj]
  constructor
  · intro h
    apply ext_inner_left ℂ
    intro z
    have hh := h (R z) z ((inverseOperator_graph hinj _ _).mpr rfl)
    rw [sub_eq_zero] at hh
    have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hR) z y
    exact hsym.symm.trans hh.symm
  · intro h a b hab
    have he := (inverseOperator_graph hinj a b).mp hab
    rw [← he, ← h, ← R.adjoint_inner_right, hR.adjoint_eq, sub_self]

end InverseOperator

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma selfAdjoint_equiv_symm (e : V ≃L[ℂ] V) (he : IsSelfAdjoint e.toContinuousLinearMap) :
    IsSelfAdjoint e.symm.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hh := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp he) (e.symm x) (e.symm y)
  change ⟪e (e.symm x), e.symm y⟫_ℂ = ⟪e.symm x, e (e.symm y)⟫_ℂ at hh
  change ⟪e.symm x, y⟫_ℂ = ⟪x, e.symm y⟫_ℂ
  simpa only [e.apply_symm_apply] using hh.symm

lemma adjoint_injective_of_denseRange (j : V →L[ℂ] H) (hd : DenseRange j) :
    Function.Injective j.adjoint := by
  intro x y hxy
  apply hd.eq_of_inner_right ℂ
  intro v
  rw [← j.adjoint_inner_right, ← j.adjoint_inner_right, hxy]

def formResolvent (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) : H →L[ℂ] H :=
  j.comp ((coerciveEquiv A hc hA).symm.toContinuousLinearMap.comp j.adjoint)

lemma formResolvent_injective (j : V →L[ℂ] H) (hj : Function.Injective j) (hd : DenseRange j)
    (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    Function.Injective (formResolvent j A hc hA) :=
  hj.comp ((coerciveEquiv A hc hA).symm.injective.comp (adjoint_injective_of_denseRange j hd))

lemma formResolvent_selfAdjoint (j : V →L[ℂ] H) (A : V →L[ℂ] V) (hs : IsSelfAdjoint A)
    {c : ℝ} (hc : 0 < c) (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    IsSelfAdjoint (formResolvent j A hc hA) := by
  have he : IsSelfAdjoint (coerciveEquiv A hc hA).toContinuousLinearMap := hs
  exact (selfAdjoint_equiv_symm _ he).conj_adjoint j

def representedOperator (j : V →L[ℂ] H) (A : V →L[ℂ] V) {c : ℝ} (hc : 0 < c)
    (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) : H →ₗ.[ℂ] H :=
  inverseOperator (formResolvent j A hc hA)

theorem representedOperator_selfAdjoint (j : V →L[ℂ] H) (hj : Function.Injective j)
    (hd : DenseRange j) (A : V →L[ℂ] V) (hs : IsSelfAdjoint A)
    {c : ℝ} (hc : 0 < c) (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) :
    IsSelfAdjoint (representedOperator j A hc hA) :=
  inverseOperator_selfAdjoint (formResolvent_selfAdjoint j A hs hc hA)
    (formResolvent_injective j hj hd A hc hA)

theorem representedOperator_graph (j : V →L[ℂ] H) (hj : Function.Injective j)
    (hd : DenseRange j) (A : V →L[ℂ] V)
    {c : ℝ} (hc : 0 < c) (hA : ∀ u, c * ‖u‖ ^ 2 ≤ (⟪u, A u⟫_ℂ).re) (x y : H) :
    (x, y) ∈ (representedOperator j A hc hA).graph ↔
      ∃ u : V, j u = x ∧ ∀ v : V, ⟪v, A u⟫_ℂ = ⟪j v, y⟫_ℂ := by
  rw [representedOperator, inverseOperator_graph (formResolvent_injective j hj hd A hc hA)]
  constructor
  · intro h
    refine ⟨(coerciveEquiv A hc hA).symm (j.adjoint y), h, ?_⟩
    intro v
    have he : A ((coerciveEquiv A hc hA).symm (j.adjoint y)) = j.adjoint y :=
      (coerciveEquiv A hc hA).apply_symm_apply _
    rw [he, j.adjoint_inner_right]
  · rintro ⟨u, hu, h⟩
    have he : A u = j.adjoint y := by
      apply ext_inner_left ℂ
      intro v
      rw [j.adjoint_inner_right]
      exact h v
    have he' : (coerciveEquiv A hc hA).symm (j.adjoint y) = u := by
      rw [← he]
      exact (coerciveEquiv A hc hA).symm_apply_apply u
    change j ((coerciveEquiv A hc hA).symm (j.adjoint y)) = x
    rw [he', hu]

end CoulombAtom

end

end OAI
