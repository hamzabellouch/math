import OAI.Analysis.KadisonKastler.ConcreteTraceUniqueness
import OAI.Analysis.KadisonKastler.ConcreteTraceComplete
import OAI.Analysis.KadisonKastler.MatrixVonNeumann
import Mathlib.Order.Bounds.OrderIso

namespace OAI

/-! # Tracial and bounded strong transport by a factor isomorphism

Uniqueness of the normalized finite-factor trace makes an algebraic
star-isomorphism preserve the tracial two-norm. The concrete finite-vector
trace formulas then give strong-operator continuity on every bounded ball,
in both directions. No continuity of the isomorphism is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- An algebraic star-isomorphism out of a II₁ factor preserves normalized
faithful tracial states. -/
theorem trace_starAlgEquiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    τN.toLinearMap (e x) = τM.toLinearMap x := by
  exact faithfulTracialState_unique hM (τN.comapStarAlgEquiv e) τM x

/-- Consequently the same isomorphism is an isometry for the two-norm. -/
theorem traceTwoNorm_starAlgEquiv
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (x : Algebra M) :
    traceTwoNorm τN (e x) = traceTwoNorm τM x := by
  have hstar : e (star x) = star (e x) := StarHomClass.map_star e x
  have hmul : e (star x * x) = e (star x) * e x := map_mul e _ _
  unfold traceTwoNorm
  rw [← hstar, ← hmul, trace_starAlgEquiv hM τM τN e]

/-- Strong convergence of any norm-bounded net is preserved. -/
theorem starAlgEquiv_tendsto_strong_of_bounded
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {I : Type*} {l : Filter I} (x : I → Algebra M) (a : Algebra M)
    {C : ℝ} (hC : 0 ≤ C) (hx : ∀ i, ‖x i‖ ≤ C)
    (hs : ∀ ξ, Tendsto (fun i => (x i : H →L[ℂ] H) ξ) l
      (𝓝 ((a : H →L[ℂ] H) ξ))) :
    ∀ η, Tendsto (fun i => (e (x i) : K →L[ℂ] K) η) l
      (𝓝 ((e a : K →L[ℂ] K) η)) := by
  have h2 := hτM.traceTwoNorm_tendsto_of_strong x a hx hs
  have he2 : Tendsto (fun i => traceTwoNorm τN (e (x i - a))) l (𝓝 0) := by
    simpa only [traceTwoNorm_starAlgEquiv hM τM τN e] using h2
  have heC (i : I) : ‖e (x i - a)‖ ≤ C + ‖a‖ := by
    have hn : ‖e (x i - a)‖ = ‖x i - a‖ :=
      injective_starAlgHom_norm e.toStarAlgHom e.injective _
    rw [hn]
    exact (norm_sub_le _ _).trans (add_le_add (hx i) le_rfl)
  intro η
  have hz := hτN.strongContinuous.tendsto l (fun i => e (x i - a))
    (add_nonneg hC (norm_nonneg a)) heC he2 η
  change Tendsto (fun i => (e (x i - a) : K →L[ℂ] K) η) l (𝓝 0) at hz
  apply tendsto_sub_nhds_zero_iff.mp
  have heval (i : I) : (e (x i - a) : K →L[ℂ] K) η =
      (e (x i) : K →L[ℂ] K) η - (e a : K →L[ℂ] K) η := by
    rw [map_sub]
    rfl
  simpa only [heval] using hz

/-- The bounded strong-operator topologies agree under a star-isomorphism
between two concrete II₁ factors. -/
theorem starAlgEquiv_tendsto_strong_iff_of_bounded
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hN : Generator.IsII1Factor N.toStarSubalgebra)
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (hτM : FiniteVectorTrace τM) (hτN : FiniteVectorTrace τN)
    (e : Algebra M ≃⋆ₐ[ℂ] Algebra N)
    {I : Type*} {l : Filter I} (x : I → Algebra M) (a : Algebra M)
    {C : ℝ} (hC : 0 ≤ C) (hx : ∀ i, ‖x i‖ ≤ C) :
    (∀ ξ, Tendsto (fun i => (x i : H →L[ℂ] H) ξ) l
      (𝓝 ((a : H →L[ℂ] H) ξ))) ↔
    (∀ η, Tendsto (fun i => (e (x i) : K →L[ℂ] K) η) l
      (𝓝 ((e a : K →L[ℂ] K) η))) := by
  constructor
  · exact starAlgEquiv_tendsto_strong_of_bounded hM τM τN hτM hτN e x a hC hx
  · intro hs
    have heC (i : I) : ‖e (x i)‖ ≤ C := by
      have hn : ‖e (x i)‖ = ‖x i‖ :=
        injective_starAlgHom_norm e.toStarAlgHom e.injective _
      rw [hn]
      exact hx i
    simpa only [e.symm_apply_apply] using
      starAlgEquiv_tendsto_strong_of_bounded hN τN τM hτN hτM e.symm
        (fun i => e (x i)) (e a) hC heC hs

section Order

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- The order isomorphism underlying an algebraic star-isomorphism. -/
def starAlgEquivOrderIso (e : A ≃⋆ₐ[ℂ] B) : A ≃o B where
  toEquiv := e.toAlgEquiv.toEquiv
  map_rel_iff' := NonUnitalStarAlgHom.map_le_map_iff e e.injective

/-- Every existing supremum is preserved. In particular this is the
order formulation of normality for bounded increasing operator nets. -/
theorem starAlgEquiv_isLUB_image (e : A ≃⋆ₐ[ℂ] B) {s : Set A} {a : A}
    (ha : IsLUB s a) : IsLUB (e '' s) (e a) :=
  (starAlgEquivOrderIso e).isLUB_image'.mpr ha

/-- A convenient net-indexed version of supremum preservation. -/
theorem starAlgEquiv_isLUB_range (e : A ≃⋆ₐ[ℂ] B) {I : Type*}
    (x : I → A) {a : A} (ha : IsLUB (Set.range x) a) :
    IsLUB (Set.range (fun i => e (x i))) (e a) := by
  have hi : e '' Set.range x = Set.range (fun i => e (x i)) :=
    by
      ext y
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨x i, ⟨i, rfl⟩, rfl⟩
  rw [← hi]
  exact starAlgEquiv_isLUB_image e ha

end Order

end

end KadisonKastler

end OAI
