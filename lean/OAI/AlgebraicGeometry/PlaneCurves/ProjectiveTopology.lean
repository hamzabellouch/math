import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Constructions
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-!
# Hausdorff projective spaces and topological projective maps
-/

section

/-! The canonical quotient topology on genuine projectivization. -/
namespace Nagata.W21

instance projectivizationTopologicalSpace (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    TopologicalSpace (Projectivization K V) :=
  inferInstanceAs (TopologicalSpace (Quotient (projectivizationSetoid K V)))

theorem continuous_projectivization_mk' (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  continuous_quotient_mk'

theorem isQuotientMap_projectivization_mk' (K V : Type*) [DivisionRing K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] :
    Topology.IsQuotientMap (Projectivization.mk' K : {v : V // v ≠ 0} → Projectivization K V) :=
  isQuotientMap_quotient_mk'

end Nagata.W21

end

section

/-! The usual complex quotient topology on genuine projectivization is
Hausdorff. The proof uses the closed proportionality relation given by all
coordinate 2×2 minors and the openness of scalar-orbit saturation. This is
separate from the algebraic Zariski predicate used for very-general points. -/

noncomputable section
open Topology Set

namespace Nagata.Workers.W11

variable {ι : Type*}

/-- Proportionality of nonzero complex vectors is detected by the actual
coordinate minors. -/
theorem projectivization_mk'_eq_iff_minors
    (v w : {x : ι → ℂ // x ≠ 0}) :
    Projectivization.mk' ℂ v = Projectivization.mk' ℂ w ↔
      ∀ i j, v.val i * w.val j = v.val j * w.val i := by
  rw [Projectivization.mk'_eq_mk, Projectivization.mk'_eq_mk,
    Projectivization.mk_eq_mk_iff']
  constructor
  · rintro ⟨a, ha⟩ i j
    have hi := congrFun ha i
    have hj := congrFun ha j
    change a * w.val i = v.val i at hi
    change a * w.val j = v.val j at hj
    rw [← hi, ← hj]
    ring
  · intro h
    have hn : ∃ i, w.val i ≠ 0 := by
      by_contra hn
      apply w.property
      funext i
      exact not_not.mp (fun hi => hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hn
    refine ⟨v.val i / w.val i, ?_⟩
    funext j
    change v.val i / w.val i * w.val j = v.val j
    rw [div_mul_eq_mul_div, div_eq_iff hi]
    exact h i j

/-- The relation defining projective points is closed in the product of the
actual nonzero-vector spaces. -/
theorem isClosed_projectivization_relation :
    IsClosed {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} := by
  have heq : {p : {x : ι → ℂ // x ≠ 0} × {x : ι → ℂ // x ≠ 0} |
      Projectivization.mk' ℂ p.1 = Projectivization.mk' ℂ p.2} =
      ⋂ i, ⋂ j, {p | p.1.val i * p.2.val j = p.1.val j * p.2.val i} := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter]
    exact projectivization_mk'_eq_iff_minors p.1 p.2
  rw [heq]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (((continuous_apply i).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply j).comp continuous_subtype_val).comp continuous_snd)
  · exact (((continuous_apply j).comp continuous_subtype_val).comp continuous_fst).mul
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd)

/-- Multiplication by a nonzero scalar on actual nonzero vectors. -/
def scaleNonzeroVector (a : ℂˣ) (v : {x : ι → ℂ // x ≠ 0}) :
    {x : ι → ℂ // x ≠ 0} :=
  ⟨(a : ℂ) • v.val, smul_ne_zero (Units.ne_zero a) v.property⟩

theorem continuous_scaleNonzeroVector (a : ℂˣ) :
    Continuous (scaleNonzeroVector (ι := ι) a) := by
  exact (continuous_const_smul (a : ℂ)).comp continuous_subtype_val |>.subtype_mk _

/-- Saturation of an open set by scalar equivalence is open; hence the genuine
projectivization quotient map is an open map. -/
theorem isOpenMap_projectivization_mk' :
    IsOpenMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) := by
  intro U hU
  apply (Nagata.W21.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)).isOpen_preimage.mp
  have heq : (Projectivization.mk' ℂ) ⁻¹' (Projectivization.mk' ℂ '' U) =
      ⋃ a : ℂˣ, scaleNonzeroVector a ⁻¹' U := by
    ext v
    constructor
    · rintro ⟨u, hu, huv⟩
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff ℂ u.val v.val
        u.property v.property).mp huv
      apply mem_iUnion.mpr
      refine ⟨a, ?_⟩
      have hs : scaleNonzeroVector a v = u := Subtype.ext ha
      simpa only [mem_preimage, hs] using hu
    · intro hv
      obtain ⟨a, ha⟩ := mem_iUnion.mp hv
      refine ⟨scaleNonzeroVector a v, ha, ?_⟩
      apply (Projectivization.mk_eq_mk_iff ℂ _ _ _ _).mpr
      exact ⟨a, rfl⟩
  rw [heq]
  exact isOpen_iUnion fun a => hU.preimage (continuous_scaleNonzeroVector a)

theorem isOpenQuotientMap_projectivization_mk' :
    IsOpenQuotientMap (Projectivization.mk' ℂ : {x : ι → ℂ // x ≠ 0} →
      Projectivization ℂ (ι → ℂ)) :=
  ⟨(Nagata.W21.isQuotientMap_projectivization_mk' ℂ (ι → ℂ)).surjective,
    Nagata.W21.continuous_projectivization_mk' ℂ (ι → ℂ),
    isOpenMap_projectivization_mk'⟩

/-- The actual projectivization with its canonical complex quotient topology
is Hausdorff. In particular this applies to the genuine projective plane with
index type `Fin 3`. -/
instance complexProjectivizationT2Space (ι : Type*) :
    T2Space (Projectivization ℂ (ι → ℂ)) :=
  (t2Space_iff_of_isOpenQuotientMap
    (isOpenQuotientMap_projectivization_mk' (ι := ι))).mpr
      isClosed_projectivization_relation

end Nagata.Workers.W11

end
end

end OAI
