import OAI.Analysis.KadisonSimilarity.Representation.NormalSupportTransport
import OAI.Analysis.FactorGeneration.OperatorLimits

namespace OAI

/-! Strong limits of increasing projections agree with their algebraic
least upper bound. This permits transport between faithful normal models
without assuming continuity of the intervening star isomorphism. -/

noncomputable section
namespace KadisonSimilarity
open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem rangeSupport_of_isStarProjection (p : H →L[ℂ] H) (hp : IsStarProjection p) :
    rangeSupport p = p := by
  have h₁ := rangeSupport_least_left p p hp.isIdempotentElem.eq
  have h₂ := rangeSupport_mul p
  have h₃ := congrArg star h₂
  rw [star_mul, hp.isSelfAdjoint.star_eq,
    (rangeSupport_isStarProjection p).isSelfAdjoint.star_eq] at h₃
  exact h₁.symm.trans h₃

/-- A monotone sequence of projections has a strong limit which is its
least upper bound inside the concrete von Neumann algebra. -/
theorem exists_monotone_projection_limit (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hmono : ∀ i j, i ≤ j → p j * p i = p i) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ x : H, Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 ((q : H →L[ℂ] H) x))) ∧
      (∀ n, q * p n = p n) ∧
      ∀ r : M.toStarSubalgebra, IsStarProjection r → (∀ n, r * p n = p n) → r * q = q := by
  let U : ℕ → Submodule ℂ H := fun n => operatorRangeClosure (p n : H →L[ℂ] H)
  have hU : Monotone U := by
    intro i j hij
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      apply Submodule.le_topologicalClosure
      refine ⟨(p i : H →L[ℂ] H) x, ?_⟩
      exact congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) x) (hmono i j hij)
    · exact Submodule.isClosed_topologicalClosure _
  let W := (⨆ n, U n).topologicalClosure
  let Q : H →L[ℂ] H := W.starProjection
  have hproj (n : ℕ) : (U n).starProjection = (p n : H →L[ℂ] H) :=
    rangeSupport_of_isStarProjection _ ((hp n).map M.toStarSubalgebra.subtype)
  have hlim (x : H) : Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 (Q x)) := by
    simpa only [hproj] using Submodule.starProjection_tendsto_closure_iSup U hU x
  have hQM : Q ∈ M :=
    Generator.Tracial.weak_operator_limit_mem M p Q (fun x y =>
      (continuous_const.inner continuous_id).continuousAt.tendsto.comp (hlim x))
  let q : M.toStarSubalgebra := ⟨Q, hQM⟩
  have hq : IsStarProjection q := by
    constructor
    · apply Subtype.ext
      exact Submodule.isIdempotentElem_starProjection W
    · apply Subtype.ext
      exact isSelfAdjoint_starProjection W
  have hupper (n : ℕ) : q * p n = p n := by
    apply Subtype.ext
    ext x
    apply Submodule.starProjection_eq_self_iff.mpr
    exact (le_iSup U n).trans (Submodule.le_topologicalClosure _)
      (Submodule.le_topologicalClosure _ ⟨x, rfl⟩)
  refine ⟨q, hq, hlim, hupper, ?_⟩
  intro r hr hru
  apply Subtype.ext
  ext x
  have he : W ≤ operatorRangeClosure (r : H →L[ℂ] H) := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro n
      apply Submodule.topologicalClosure_minimal
      · rintro _ ⟨y, rfl⟩
        apply Submodule.le_topologicalClosure
        exact ⟨(p n : H →L[ℂ] H) y,
          congrArg (fun a : M.toStarSubalgebra => (a : H →L[ℂ] H) y) (hru n)⟩
      · exact Submodule.isClosed_topologicalClosure _
    · exact Submodule.isClosed_topologicalClosure _
  have hfix := Submodule.starProjection_eq_self_iff.mpr
    (he (W.starProjection_apply_mem x))
  rw [show (operatorRangeClosure (r : H →L[ℂ] H)).starProjection = (r : H →L[ℂ] H) from
    rangeSupport_of_isStarProjection _ (hr.map M.toStarSubalgebra.subtype)] at hfix
  exact hfix

/-- Decreasing projections have a strong limit below every member. -/
theorem exists_antitone_projection_limit (M : VonNeumannAlgebra H)
    (p : ℕ → M.toStarSubalgebra) (hp : ∀ n, IsStarProjection (p n))
    (hanti : ∀ i j, i ≤ j → p i * p j = p j) :
    ∃ q : M.toStarSubalgebra, IsStarProjection q ∧
      (∀ x : H, Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop (𝓝 ((q : H →L[ℂ] H) x))) ∧
      ∀ n, p n * q = q := by
  let a : ℕ → M.toStarSubalgebra := fun n => 1 - p n
  have ha (n : ℕ) : IsStarProjection (a n) := (hp n).one_sub
  have hmono (i j : ℕ) (hij : i ≤ j) : a j * a i = a i := by
    have hji : p j * p i = p j := by
      simpa only [star_mul, (hp i).isSelfAdjoint.star_eq, (hp j).isSelfAdjoint.star_eq]
        using congrArg star (hanti i j hij)
    change (1 - p j) * (1 - p i) = 1 - p i
    simp only [sub_mul, mul_sub, one_mul, mul_one, hji]
    abel
  obtain ⟨r, hr, hlim, hupper, -⟩ := exists_monotone_projection_limit M a ha hmono
  refine ⟨1 - r, hr.one_sub, ?_, ?_⟩
  · intro x
    have h := (tendsto_const_nhds (x := x)).sub (hlim x)
    change Tendsto (fun n => x - (x - (p n : H →L[ℂ] H) x)) atTop
      (𝓝 (x - (r : H →L[ℂ] H) x)) at h
    change Tendsto (fun n => (p n : H →L[ℂ] H) x) atTop
      (𝓝 (x - (r : H →L[ℂ] H) x))
    simpa only [sub_sub_cancel] using h
  · intro n
    have hu := hupper n
    change r * (1 - p n) = 1 - p n at hu
    rw [mul_sub, mul_one] at hu
    have hqp : (1 - r) * p n = 1 - r := by
      rw [sub_mul, one_mul]
      apply (sub_eq_sub_iff_add_eq_add).mpr
      simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add).mp hu
    simpa only [star_mul, (hp n).isSelfAdjoint.star_eq, hr.one_sub.isSelfAdjoint.star_eq]
      using congrArg star hqp

end KadisonSimilarity

end

end OAI
