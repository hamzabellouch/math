import Mathlib
import OAI.Analysis.WeakInfiniteness.CyclicOrbit
import OAI.Analysis.WeakInfiniteness.IdealSeparation
import OAI.Analysis.WeakInfiniteness.TensorFoundations

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped Topology ComplexOrder InnerProductSpace CStarAlgebra

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def unitizationClosedIdeal (I : NonUnitalStarSubalgebra ℂ A) :
    NonUnitalStarSubalgebra ℂ (Unitization ℂ A) where
  carrier := {x | x.fst=0 ∧ x.snd ∈ I}
  zero_mem' := ⟨rfl,I.zero_mem⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp only [Unitization.fst_add,hx.1,hy.1,add_zero],I.add_mem hx.2 hy.2⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by simp only [Unitization.fst_smul,hx.1,smul_zero],I.smul_mem c hx.2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨by simp only [Unitization.fst_mul,hx.1,zero_mul],?_⟩
    simp only [Unitization.snd_mul,hx.1,hy.1,zero_smul,zero_add]
    exact I.mul_mem hx.2 hy.2
  star_mem' := by
    intro x hx
    exact ⟨by simp only [Unitization.fst_star,hx.1,star_zero],star_mem hx.2⟩

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_isClosed (I : NonUnitalStarSubalgebra ℂ A)
    (hI : IsClosed (I : Set A)) : IsClosed (unitizationClosedIdeal I : Set (Unitization ℂ A)) :=
  (isClosed_eq Unitization.continuous_fst continuous_const).inter
    (hI.preimage Unitization.continuous_snd)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_mul_left (I : NonUnitalStarSubalgebra ℂ A)
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) {x : Unitization ℂ A}
    (hx : x ∈ unitizationClosedIdeal I) (a : Unitization ℂ A) :
    a*x ∈ unitizationClosedIdeal I := by
  refine ⟨by simp only [Unitization.fst_mul,hx.1,mul_zero],?_⟩
  simp only [Unitization.snd_mul,hx.1,zero_smul,add_zero]
  exact I.add_mem (I.smul_mem a.fst hx.2) (hIL x.snd hx.2 a.snd)

omit [PartialOrder A] [StarOrderedRing A] in
lemma unitizationClosedIdeal_mul_right (I : NonUnitalStarSubalgebra ℂ A)
    (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I) {x : Unitization ℂ A}
    (hx : x ∈ unitizationClosedIdeal I) (a : Unitization ℂ A) :
    x*a ∈ unitizationClosedIdeal I := by
  refine ⟨by simp only [Unitization.fst_mul,hx.1,zero_mul],?_⟩
  simp only [Unitization.snd_mul,hx.1,zero_smul,zero_add]
  exact I.add_mem (I.smul_mem a.fst hx.2) (hIR x.snd hx.2 a.snd)

theorem exists_irreducible_separating_closed_ideal
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b) (hbI : b ∉ I) :
    ∃ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π ∧ (∀ x ∈ I,π x=0) ∧ π b ≠ 0 := by
  let J := unitizationClosedIdeal I
  let u : Unitization ℂ A := (b : Unitization ℂ A)
  have hu : 0 ≤ u := map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) hb
  have huJ : u ∉ J := fun h => hbI h.2
  obtain ⟨g,hg,hgb⟩ := exists_annihilator_state_of_not_mem J
    (unitizationClosedIdeal_isClosed I hI)
    (fun x hx a => unitizationClosedIdeal_mul_left I hIL hx a)
    (fun x hx a => unitizationClosedIdeal_mul_right I hIR hx a) hu huJ
  obtain ⟨f,hf,hfJ,hgf⟩ := exists_extreme_annihilator_state hg ⟨u,hu.isSelfAdjoint⟩
  let Φ := realStateComplexification f hf.1
  let π := Φ.gnsStarAlgHom.toNonUnitalStarAlgHom.comp (Unitization.inrNonUnitalStarAlgHom ℂ A)
  let H : ComplexHilbert.{u} := { Carrier := Φ.GNS }
  refine ⟨H,π,irreducible_restrict_unitization Φ.gnsStarAlgHom
    (extreme_real_state_gns_irreducible f hf),?_,?_⟩
  · intro x hx
    exact annihilatorStates_gns_zero hfJ (show (x : Unitization ℂ A) ∈ J from ⟨rfl,hx⟩)
  · intro hz
    have he := DFunLike.congr_fun (gns_vectorFunctional_eq f hf.1) ⟨u,hu.isSelfAdjoint⟩
    change (inner ℂ (gnsCyclicVector Φ) (Φ.gnsStarAlgHom u (gnsCyclicVector Φ))).re =
      f ⟨u,hu.isSelfAdjoint⟩ at he
    change Φ.gnsStarAlgHom u=0 at hz
    rw [hz,zero_apply,inner_zero_right,Complex.zero_re] at he
    linarith

theorem mem_closed_ideal_of_irreducible_test
    (I : NonUnitalStarSubalgebra ℂ A) (hI : IsClosed (I : Set A))
    (hIL : ∀ x ∈ I,∀ a : A,a*x ∈ I) (hIR : ∀ x ∈ I,∀ a : A,x*a ∈ I)
    {b : A} (hb : 0 ≤ b)
    (htest : ∀ (H : ComplexHilbert.{u}) (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)),
      NonUnitalRepresentationIrreducible π → (∀ x ∈ I,π x=0) → π b=0) : b ∈ I := by
  by_contra hn
  obtain ⟨H,π,hπ,hπI,hπb⟩ := exists_irreducible_separating_closed_ideal I hI hIL hIR hb hn
  exact hπb (htest H π hπ hπI)

end

end WeakPureInfiniteness
end

end OAI
