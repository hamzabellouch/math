import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedFreeRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.StableResolutionIdentity

namespace OAI

/-! # Norms on projective integral representations of finite groups

Every invariant vector in a free representation is a norm. Splitting the
normalized free cover extends this to projective representations. Consequently,
a scalar endomorphism of the trivial representation factors through a projective
representation exactly when the group order divides that scalar.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem freeRepresentation_action_coeff {α : Type} (g : G)
    (x : α →₀ ℤ[G]) (a : α) (h : G) :
    (Representation.free ℤ G α g x a).coeff h = (x a).coeff (g⁻¹ * h) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, MonoidAlgebra.coeff_add, hx, hy]
  | single b z =>
    simp only [Representation.free, Representation.finsupp_single]
    by_cases hab : b = a
    · subst b
      simp [Representation.leftRegular, Representation.coeff_ofMulAction]
    · simp [hab]

variable [Fintype G]

theorem freeRepresentation_invariant_is_norm {α : Type} (x : Rep.free ℤ G α)
    (hx : ∀ g : G, (Rep.free ℤ G α).ρ g x = x) :
    ∃ y : Rep.free ℤ G α, (Rep.norm (Rep.free ℤ G α)).hom y = x := by
  classical
  have hc (a : α) (g : G) : (x a).coeff g = (x a).coeff 1 := by
    have he := congrArg (fun z : Rep.free ℤ G α => (z a).coeff g) (hx g)
    simpa only [freeRepresentation_action_coeff, inv_mul_cancel] using he.symm
  let y : Rep.free ℤ G α := x.mapRange (fun z => MonoidAlgebra.single 1 (z.coeff 1)) (by simp)
  refine ⟨y, ?_⟩
  ext a h
  change (Representation.norm (Representation.free ℤ G α) y a).coeff h = (x a).coeff h
  calc
    _ = ∑ g : G, (Representation.free ℤ G α g y a).coeff h := by
      simp [Representation.norm]
    _ = ∑ g : G, (y a).coeff (g⁻¹ * h) := by
      apply Finset.sum_congr rfl
      intro g _
      exact freeRepresentation_action_coeff g y a h
    _ = (x a).coeff h := by
      simp [y, MonoidAlgebra.coeff_single, Finsupp.single_apply, eq_comm, inv_mul_eq_one, hc]

theorem projectiveRepresentation_invariant_is_norm (P : Rep.{0} ℤ G) [Projective P]
    (x : P) (hx : ∀ g : G, P.ρ g x = x) :
    ∃ y : P, (Rep.norm P).hom y = x := by
  let s := Projective.factorThru (𝟙 P) (normalizedFreeAugmentation P)
  have hs : s ≫ normalizedFreeAugmentation P = 𝟙 P := Projective.factorThru_comp _ _
  have hxs (g : G) : (normalizedFreeRepresentation P).ρ g (s.hom x) = s.hom x := by
    rw [← Rep.hom_comm_apply, hx]
  obtain ⟨y, hy⟩ := freeRepresentation_invariant_is_norm (s.hom x) hxs
  refine ⟨(normalizedFreeAugmentation P).hom y, ?_⟩
  have hn := ConcreteCategory.congr_hom (Rep.norm_comm (normalizedFreeAugmentation P)) y
  change (Rep.norm P).hom ((normalizedFreeAugmentation P).hom y) =
    (normalizedFreeAugmentation P).hom ((Rep.norm (normalizedFreeRepresentation P)).hom y) at hn
  change (Rep.norm (normalizedFreeRepresentation P)).hom y = s.hom x at hy
  rw [hy] at hn
  exact hn.trans (ConcreteCategory.congr_hom hs x)

theorem projective_trivial_factor_divisible (P : Rep.{0} ℤ G) [Projective P]
    (u : trivialIntegral G ⟶ P) (v : P ⟶ trivialIntegral G) :
    (Fintype.card G : ℤ) ∣ v.hom (u.hom 1) := by
  have hu (g : G) : P.ρ g (u.hom 1) = u.hom 1 := by
    rw [← Rep.hom_comm_apply]
    rfl
  obtain ⟨y, hy⟩ := projectiveRepresentation_invariant_is_norm P (u.hom 1) hu
  refine ⟨v.hom y, ?_⟩
  have hn := ConcreteCategory.congr_hom (Rep.norm_comm v) y
  change (Rep.norm (trivialIntegral G)).hom (v.hom y) = v.hom ((Rep.norm P).hom y) at hn
  rw [hy] at hn
  simpa [Rep.norm, Representation.norm, trivialIntegral, nsmul_eq_mul] using hn.symm

theorem stableTrivialScalar_eq_zero_iff (m : ℤ) :
    stableRepresentationClass (trivialIntegral G) (trivialIntegral G)
      (m • 𝟙 (trivialIntegral G)) = 0 ↔ (Fintype.card G : ℤ) ∣ m := by
  rw [stableRepresentationClass_eq_zero_iff_projective_factor]
  constructor
  · rintro ⟨P, hP, u, v, huv⟩
    let := hP
    have h := projective_trivial_factor_divisible P u v
    have he := ConcreteCategory.congr_hom huv (1 : ℤ)
    change v.hom (u.hom 1) = m * 1 at he
    simpa only [he, mul_one] using h
  · rintro ⟨k, rfl⟩
    let A := trivialIntegral G
    let F := normalizedFreeRepresentation A
    let e : F := normalizedFreeGenerator A 1
    let u : A ⟶ F := Rep.ofHom
      ⟨{ toFun := fun z => z • (Rep.norm F).hom e
         map_add' := fun x y => add_smul x y _
         map_smul' := fun r z => by
           simp only [RingHom.id_apply, smul_eq_mul]
           exact @mul_smul ℤ F _ F.hV2.toSemigroupAction r z ((Rep.norm F).hom e) },
       fun g => by
         apply LinearMap.ext
         intro z
         change z • (Rep.norm F).hom e = F.ρ g (z • (Rep.norm F).hom e)
         rw [map_smul]
         congr 1
         exact (Representation.self_norm_apply F.ρ g e).symm⟩
    refine ⟨F, inferInstance, u, k • normalizedFreeAugmentation A, ?_⟩
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change k • (normalizedFreeAugmentation A).hom (z • (Rep.norm F).hom e) =
      ((Fintype.card G : ℤ) * k) • z
    rw [map_smul]
    have hn := ConcreteCategory.congr_hom (Rep.norm_comm (normalizedFreeAugmentation A)) e
    change (Rep.norm A).hom ((normalizedFreeAugmentation A).hom e) =
      (normalizedFreeAugmentation A).hom ((Rep.norm F).hom e) at hn
    rw [← hn]
    have he : (normalizedFreeAugmentation A).hom e = 1 :=
      normalizedFreeAugmentation_generator A 1
    rw [he]
    simp [A, Rep.norm, Representation.norm, trivialIntegral]
    ring

end PolycyclicRecognition

end

end OAI
