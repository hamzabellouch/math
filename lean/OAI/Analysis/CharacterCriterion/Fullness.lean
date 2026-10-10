import OAI.Analysis.CharacterCriterion.Representations

namespace OAI

noncomputable section
open scoped TensorProduct
open scoped InnerProductSpace
open scoped BigOperators
open Set Module
open Topology
open NormedSpace
open scoped ComplexOrder
open scoped ComplexOrder
open scoped InnerProductSpace


namespace KirchbergRordam.GenericRW
namespace PrimitiveSeparation
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (I : Ideal A) [I.IsTwoSided] [IsClosed (I : Set A)]

instance quotientNormedAlgebra : NormedAlgebra ℂ (A ⧸ I) where
  norm_smul_le := norm_smul_le

def quotientCLM : A →L[ℂ] (A ⧸ I) :=
  (Ideal.Quotient.mkₐ ℂ I).toLinearMap.mkContinuous 1 fun a => by
    change ‖(Submodule.Quotient.mk a : A ⧸ I)‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le I a

omit [Nontrivial A] in
@[simp] lemma quotientCLM_apply (a : A) : quotientCLM I a = Ideal.Quotient.mk I a := rfl

lemma quotient_norm_one (hI : I ≠ ⊤) : ‖(1 : A ⧸ I)‖ = 1 := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  apply le_antisymm _ (one_le_norm_one (A ⧸ I))
  change ‖(Submodule.Quotient.mk (1 : A) : A ⧸ I)‖ ≤ 1
  simpa only [norm_one] using Submodule.Quotient.norm_mk_le I (1 : A)


def stateFace : Set (WeakDual ℂ A) := PureStates.normStates A ∩ {φ | ∀ a ∈ I, φ a = 0}

omit [Nontrivial A] [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_compact : IsCompact (stateFace I) :=
  (PureStates.normStates_compact A).inter_right
    (by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun a => isClosed_iInter fun _ =>
        isClosed_eq (WeakDual.eval_continuous a) continuous_const)

lemma stateFace_nonempty (hI : I ≠ ⊤) : (stateFace I).Nonempty := by
  let _ : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨f, hfn, hf1⟩ := exists_dual_vector ℂ (1 : A ⧸ I) (by rw [quotient_norm_one I hI]; exact one_ne_zero)
  have hf1 : f 1 = 1 := by simpa [quotient_norm_one I hI] using hf1
  let g := f.comp (quotientCLM I)
  have hg : ‖g‖ ≤ 1 := by
    apply g.opNorm_le_bound (by norm_num)
    intro a
    have hq : ‖quotientCLM I a‖ ≤ ‖a‖ := Submodule.Quotient.norm_mk_le I a
    change ‖f (quotientCLM I a)‖ ≤ 1 * ‖a‖
    calc
      ‖f (quotientCLM I a)‖ ≤ ‖f‖ * ‖quotientCLM I a‖ := f.le_opNorm _
      _ ≤ 1 * ‖a‖ := by rw [hfn, one_mul, one_mul]; exact hq
  refine ⟨StrongDual.toWeakDual g, ⟨hg, ?_⟩, ?_⟩
  · change f (Ideal.Quotient.mk I 1) = 1
    simpa only [map_one] using hf1
  · intro a ha
    change f (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

variable [PartialOrder A] [StarOrderedRing A]

omit [I.IsTwoSided] [IsClosed (I : Set A)] in
lemma stateFace_isFace (φ ψ χ : WeakDual ℂ A) (hφ : ∀ a ∈ I, φ a = 0)
    (hψ : ψ ∈ PureStates.normStates A) (hχ : χ ∈ PureStates.normStates A)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (he : s • ψ + t • χ = φ) :
    (∀ a ∈ I, ψ a = 0) ∧ (∀ a ∈ I, χ a = 0) := by
  have hψp (a : A) (ha : 0 ≤ a) : 0 ≤ ψ a :=
    States.eval_nonneg ψ.toStrongDual hψ.1 hψ.2 a ha
  have hχp (a : A) (ha : 0 ≤ a) : 0 ≤ χ a :=
    States.eval_nonneg χ.toStrongDual hχ.1 hχ.2 a ha
  have hz (a : A) (ha : a ∈ I) : ψ (star a * a) = 0 ∧ χ (star a * a) = 0 := by
    have hpa := hψp (star a * a) (star_mul_self_nonneg a)
    have hca := hχp (star a * a) (star_mul_self_nonneg a)
    have he' := congrArg (fun f : WeakDual ℂ A => (f (star a * a)).re) he
    have hf := hφ (star a * a) (I.mul_mem_left _ ha)
    change ((s • ψ (star a * a) + t • χ (star a * a)) : ℂ).re = (φ (star a * a)).re at he'
    simp only [Complex.add_re, Complex.smul_re, smul_eq_mul] at he'
    rw [hf, Complex.zero_re] at he'
    have hp0 : (ψ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    have hc0 : (χ (star a * a)).re = 0 := by
      nlinarith [(Complex.nonneg_iff.mp hpa).1, (Complex.nonneg_iff.mp hca).1]
    constructor <;> apply Complex.ext
    · exact hp0
    · exact (Complex.nonneg_iff.mp hpa).2.symm
    · exact hc0
    · exact (Complex.nonneg_iff.mp hca).2.symm
  constructor
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ ψ.toStrongDual.toLinearMap hψp) a (hz a ha).1
  · intro a ha
    exact Representations.positive_zero_of_square_zero
      (PositiveLinearMap.mk₀ χ.toStrongDual.toLinearMap hχp) a (hz a ha).2


theorem exists_pure_annihilating (hI : I ≠ ⊤) :
    ∃ φ : A →L[ℂ] ℂ, PureStates.IsPure A φ ∧ ∀ a ∈ I, φ a = 0 := by
  obtain ⟨φ, hφ⟩ := (stateFace_compact I).extremePoints_nonempty (stateFace_nonempty I hI)
  refine ⟨φ.toStrongDual, ⟨hφ.1.1, ?_⟩, hφ.1.2⟩
  intro ψ hψ χ hχ he
  obtain ⟨s, t, hs, ht, hst, heq⟩ := he
  obtain ⟨hψI, hχI⟩ := stateFace_isFace I φ ψ χ hφ.1.2 hψ hχ s t hs ht heq
  exact hφ.2 ⟨hψ, hψI⟩ ⟨hχ, hχI⟩ ⟨s, t, hs, ht, hst, heq⟩

omit [IsClosed (I : Set A)] in
lemma pureRepresentation_annihilates (φ : A →L[ℂ] ℂ) (hp : PureStates.IsPure A φ)
    (hφ : ∀ a ∈ I, φ a = 0) (a : A) (ha : a ∈ I) :
    (Representations.pureRepresentation φ hp).representation a = 0 := by
  let f := Representations.stateOfPure φ hp
  have hv (b : A) : Representations.gnsVector f (a * b) = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [Representations.gnsVector_inner]
    exact hφ _ (I.mul_mem_left _ (I.mul_mem_right _ ha))
  apply ContinuousLinearMap.ext
  intro x
  have hd := Representations.gns_cyclic f
  apply hd.induction_on (p := fun x => f.gnsStarAlgHom a x = 0) x
  · exact isClosed_eq ((f.gnsStarAlgHom a).continuous) continuous_const
  · intro b
    simp only [Representations.gnsVector_apply, mul_one]
    exact hv b


theorem exists_irreducible_annihilating (hI : I ≠ ⊤) :
    ∃ ρ : IrreducibleRepresentation A, ∀ a ∈ I, ρ.representation a = 0 := by
  obtain ⟨φ, hp, hφ⟩ := exists_pure_annihilating I hI
  exact ⟨Representations.pureRepresentation φ hp,
    fun a ha => pureRepresentation_annihilates I φ hp hφ a ha⟩

end PrimitiveSeparation
end KirchbergRordam.GenericRW

namespace KirchbergRordam.GenericRW.Fullness
variable {A : Type*} [CStarAlgebra A]


def closedIdeal (I : TwoSidedIdeal A) : Ideal A := I.asIdeal.topologicalClosure

instance closedIdeal_twoSided (I : TwoSidedIdeal A) : (closedIdeal I).IsTwoSided where
  mul_mem_of_left := by
    intro a b ha
    exact (show Set.MapsTo (fun x : A => x * b) (I : Set A) (I : Set A) from
      fun x hx => I.mul_mem_right x b hx).closure (continuous_mul_const b) ha

instance closedIdeal_isClosed (I : TwoSidedIdeal A) : IsClosed (closedIdeal I : Set A) :=
  isClosed_closure

lemma eq_top_of_closedIdeal_eq_top (I : TwoSidedIdeal A) (hI : closedIdeal I = ⊤) : I = ⊤ := by
  have h1 : (1 : A) ∈ closure (I : Set A) := by
    change (1 : A) ∈ closedIdeal I
    rw [hI]
    trivial
  obtain ⟨x, hx, hnear⟩ := Metric.mem_closure_iff.mp h1 1 zero_lt_one
  have hu : IsUnit x := by
    have hnorm : ‖1 - x‖ < 1 := by simpa only [dist_eq_norm] using hnear
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have ht := I.asIdeal.eq_top_of_isUnit_mem hx hu
  apply le_antisymm le_top
  intro x _
  change x ∈ I.asIdeal
  rw [ht]
  trivial


def IsFull (a : A) : Prop := TwoSidedIdeal.span {a} = ⊤

lemma full_iff_closed (a : A) : IsFull a ↔ closedIdeal (TwoSidedIdeal.span {a}) = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro x hx
    apply subset_closure
    rw [show TwoSidedIdeal.span {a} = ⊤ from h]
    trivial
  · exact eq_top_of_closedIdeal_eq_top _

lemma full_of_survives [Nontrivial A]
    (a : A) (h : ∀ π : IrreducibleRepresentation A, π.representation a ≠ 0) : IsFull a := by
  let := CStarAlgebra.spectralOrder A
  let := CStarAlgebra.spectralOrderedRing A
  apply (full_iff_closed a).mpr
  by_contra hn
  obtain ⟨π, hπ⟩ := PrimitiveSeparation.exists_irreducible_annihilating
    (closedIdeal (TwoSidedIdeal.span {a})) hn
  exact h π (hπ a (subset_closure (TwoSidedIdeal.subset_span rfl)))

lemma full_ne_zero [Nontrivial A] {a : A} (ha : IsFull a) : a ≠ 0 := by
  intro he
  subst a
  have h : (1 : A) ∈ TwoSidedIdeal.span {0} := by
    rw [show TwoSidedIdeal.span {(0 : A)} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hh : TwoSidedIdeal.span ({0} : Set A) ≤ ⊥ := TwoSidedIdeal.span_le.mpr (by simp)
  exact one_ne_zero ((TwoSidedIdeal.mem_bot _).mp (hh h))

lemma full_survives {B : Type*} [CStarAlgebra B] [Nontrivial B]
    {a : A} (ha : IsFull a) (φ : A →⋆ₐ[ℂ] B) : φ a ≠ 0 := by
  intro hz
  have hk : TwoSidedIdeal.span {a} ≤ TwoSidedIdeal.ker φ.toRingHom :=
    TwoSidedIdeal.span_le.mpr (Set.singleton_subset_iff.mpr ((TwoSidedIdeal.mem_ker _).mpr hz))
  have h1 : (1 : A) ∈ TwoSidedIdeal.span {a} := by
    rw [show TwoSidedIdeal.span {a} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hz1 := (TwoSidedIdeal.mem_ker _).mp (hk h1)
  exact one_ne_zero (by simpa only [map_one] using hz1)

lemma bridges_span_one {a b : A} (ha : IsFull a) (hb : IsFull b) :
    TwoSidedIdeal.span (Set.range (fun d : A => a * d * b)) = ⊤ := by
  let J := TwoSidedIdeal.span (Set.range (fun d : A => a * d * b))
  have hmul {x : A} (hx : x ∈ TwoSidedIdeal.span {a}) : ∀ d : A, x * d * b ∈ J := by
    induction hx using TwoSidedIdeal.span_induction with
    | mem x hx => subst x; intro d; exact TwoSidedIdeal.subset_span ⟨d, rfl⟩
    | zero => intro d; simp only [zero_mul]; exact J.zero_mem
    | add x y hx hy ihx ihy =>
      intro d
      simpa only [add_mul] using J.add_mem (ihx d) (ihy d)
    | neg x hx ih =>
      intro d
      simpa only [neg_mul] using J.neg_mem (ih d)
    | left_absorb c x hx ih =>
      intro d
      simpa only [mul_assoc] using J.mul_mem_left c _ (ih d)
    | right_absorb c x hx ih =>
      intro d
      simpa only [mul_assoc] using ih (c * d)
  have h1 : (1 : A) ∈ TwoSidedIdeal.span {a} := by
    rw [show TwoSidedIdeal.span {a} = ⊤ from ha]
    exact TwoSidedIdeal.mem_top A
  have hbJ : b ∈ J := by simpa using hmul h1 1
  have hk : TwoSidedIdeal.span {b} ≤ J := TwoSidedIdeal.span_le.mpr (by simpa)
  apply top_unique
  rwa [hb] at hk

lemma mem_span_finite {s : Set A} {x : A} (hx : x ∈ TwoSidedIdeal.span s) :
    ∃ t : Finset A, ↑t ⊆ s ∧ x ∈ TwoSidedIdeal.span (t : Set A) := by
  classical
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx => exact ⟨{x}, by simpa, TwoSidedIdeal.subset_span (by simp)⟩
  | zero => exact ⟨∅, by simp, TwoSidedIdeal.zero_mem _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨t, ht, hxt⟩ := ihx
    obtain ⟨u, hu, hyu⟩ := ihy
    refine ⟨t ∪ u, ?_, TwoSidedIdeal.add_mem _ ?_ ?_⟩
    · simpa using Set.union_subset ht hu
    · exact TwoSidedIdeal.span_mono (by simp) hxt
    · exact TwoSidedIdeal.span_mono (by simp) hyu
  | neg x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.neg_mem _ hx⟩
  | left_absorb a x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.mul_mem_left _ _ _ hx⟩
  | right_absorb b x hx ih =>
    obtain ⟨t, ht, hx⟩ := ih
    exact ⟨t, ht, TwoSidedIdeal.mul_mem_right _ _ _ hx⟩

end KirchbergRordam.GenericRW.Fullness
end

end OAI
