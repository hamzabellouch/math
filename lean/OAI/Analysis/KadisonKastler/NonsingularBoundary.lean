import OAI.Analysis.KadisonKastler.Algebra
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

/-- A measurable group action preserving the measure class. -/
structure NonsingularAction (G D : Type*) [Group G] [MeasurableSpace D]
    (μ : Measure D) where
  toPerm : G →* Equiv.Perm D
  quasi : ∀ g, Measure.QuasiMeasurePreserving (toPerm g) μ μ

namespace NonsingularAction

variable {μ : Measure D} (α : NonsingularAction G D μ)

@[simp]
theorem one_apply (x : D) : α.toPerm 1 x = x := by
  rw [map_one]
  rfl

@[simp]
theorem mul_apply (g h : G) (x : D) :
    α.toPerm (g * h) x = α.toPerm g (α.toPerm h x) := by
  rw [map_mul]
  rfl

/-- The separate action on the product is again nonsingular. -/
def prod [SFinite μ] : NonsingularAction (G × G) (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (α.toPerm g.1) (α.toPerm g.2)
      map_one' := by ext x <;> simp
      map_mul' g h := by ext x <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap (α.quasi g.1) (α.quasi g.2)

@[simp]
theorem prod_apply [SFinite μ] (g : G × G) (x : D × D) :
    α.prod.toPerm g x = (α.toPerm g.1 x.1, α.toPerm g.2 x.2) := rfl

/-- Restricting the separate action to the diagonal. -/
def diagonal [SFinite μ] : NonsingularAction G (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => α.prod.toPerm (g, g)
      map_one' := by ext x <;> simp
      map_mul' g h := by ext x <;> simp }
  quasi g := α.prod.quasi (g, g)

@[simp]
theorem diagonal_apply [SFinite μ] (g : G) (x : D × D) :
    α.diagonal.toPerm g x = (α.toPerm g x.1, α.toPerm g x.2) := rfl

/-- Countably many almost-everywhere properties, together with all their
translates, hold on a single invariant conull set. -/
theorem exists_invariant_conull [Countable G] {ι : Type*} [Countable ι]
    (P : ι → D → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ S : Set D, (∀ᵐ x ∂μ, x ∈ S) ∧
      (∀ g x, x ∈ S → α.toPerm g x ∈ S) ∧
      (∀ x ∈ S, ∀ i, P i x) := by
  let S : Set D := {x | ∀ g : G, ∀ i : ι, P i (α.toPerm g x)}
  refine ⟨S, ?_, ?_, ?_⟩
  · exact eventually_countable_forall.mpr fun g =>
      eventually_countable_forall.mpr fun i => (α.quasi g).ae (hP i)
  · intro g x hx h i
    exact α.mul_apply h g x ▸ hx (h * g) i
  · intro x hx i
    simpa only [α.one_apply] using hx 1 i

/-- A conull set contains a point when the measure is nonzero. -/
theorem exists_simultaneous_point [Countable G] [NeZero μ]
    {ι : Type*} [Countable ι] (P : ι → D → Prop)
    (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ x, ∀ g i, P i (α.toPerm g x) := by
  have h : ∀ᵐ x ∂μ, ∀ g i, P i (α.toPerm g x) :=
    eventually_countable_forall.mpr fun g =>
      eventually_countable_forall.mpr fun i => (α.quasi g).ae (hP i)
  exact h.exists

/-- If an equivariant function is almost everywhere constant, its constant
value is fixed. This uses nonsingularity and does not use invariance of μ. -/
theorem fixed_of_ae_constant [NeZero μ]
    {E : Type*} (σ : G → E → E) (f : D → E) (v : E)
    (hf : f =ᵐ[μ] fun _ => v)
    (heq : ∀ g, ∀ᵐ x ∂μ, f (α.toPerm g x) = σ g (f x)) :
    ∀ g, σ g v = v := by
  intro g
  have hp := (α.quasi g).ae hf
  have hall : ∀ᵐ x ∂μ, σ g v = v := by
    filter_upwards [hf, hp, heq g] with x hx hpx hex
    rw [hx, hpx] at hex
    exact hex.symm
  exact hall.exists.choose_spec

end NonsingularAction

variable {μ : Measure D} [SFinite μ]

/-- The exact double-ergodicity property with unitary coefficients used
below. It is the bounded-map specialization of Björklund's Theorem 2.1,
Remark 2.2 (arXiv:1406.0763), for a symmetric Poisson boundary. -/
def UnitaryDoubleErgodic (α : NonsingularAction G D μ) : Prop :=
  ∀ (K : Type*) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] [TopologicalSpace.SeparableSpace K]
    (σ : G →* unitary (K →L[ℂ] K)) (f : D × D → K),
    AEStronglyMeasurable f (μ.prod μ) →
    (∃ C : ℝ, ∀ᵐ x ∂μ.prod μ, ‖f x‖ ≤ C) →
    (∀ g, ∀ᵐ x ∂μ.prod μ, f (α.diagonal.toPerm g x) = (σ g : K →L[ℂ] K) (f x)) →
    ∃ v : K, (∀ g, (σ g : K →L[ℂ] K) v = v) ∧ f =ᵐ[μ.prod μ] fun _ => v

end

end KadisonKastler

end OAI
