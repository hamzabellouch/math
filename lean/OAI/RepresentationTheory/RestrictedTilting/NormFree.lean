import OAI.RepresentationTheory.RestrictedTilting.NormMaps

namespace OAI

namespace FiberFunctorProof
open Representation
universe u
variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
variable (I : Type u)

 

noncomputable def freeNormRepresentative :
    (I →₀ MonoidAlgebra k G) →ₗ[k] (I →₀ MonoidAlgebra k G) :=
  Finsupp.mapRange.linearMap
    ((MonoidAlgebra.lsingle 1).comp
      ((Finsupp.lapply 1).comp (MonoidAlgebra.coeffLinearEquiv k).toLinearMap))

omit [Fintype G] in
@[simp] lemma freeNormRepresentative_apply (x : I →₀ MonoidAlgebra k G) (i : I) :
    freeNormRepresentative I x i = MonoidAlgebra.single 1 ((x i).coeff 1) := rfl

omit [Fintype G] in
lemma free_action_apply (g : G) (x : I →₀ MonoidAlgebra k G) (i : I) :
    Representation.free k G I g x i = Representation.leftRegular k G g (x i) := by
  classical
  have H : (Finsupp.lapply i).comp (Representation.free k G I g) =
      (Representation.leftRegular k G g).comp (Finsupp.lapply i) := by
    apply Finsupp.lhom_ext
    intro j v
    simp only [LinearMap.comp_apply, Representation.finsupp_single, Finsupp.lapply_apply]
    by_cases h : j = i
    · subst j; simp
    · simp [Ne.symm h]
  exact congr($(H) x)

lemma free_norm_apply (x : I →₀ MonoidAlgebra k G) (i : I) :
    (Representation.free k G I).norm x i = (Representation.leftRegular k G).norm (x i) := by
  classical
  simp only [Representation.norm, LinearMap.sum_apply, Finsupp.finsetSum_apply, free_action_apply]

lemma free_normRepresentative_invariant (x : I →₀ MonoidAlgebra k G)
    (hx : ∀ g, Representation.free k G I g x = x) :
    (Representation.free k G I).norm (freeNormRepresentative I x) = x := by
  apply Finsupp.ext
  intro i
  rw [free_norm_apply, freeNormRepresentative_apply]
  have hxi (g : G) : Representation.leftRegular k G g (x i) = x i := by
    have hi := congrArg (fun v : I →₀ MonoidAlgebra k G => v i) (hx g)
    simpa only [free_action_apply] using hi
  have heq : MonoidAlgebra.single (1:G) ((x i).coeff 1) =
      (x i).coeff 1 • MonoidAlgebra.single 1 (1 : k) := by simp
  rw [heq, map_smul]
  exact (regular_invariant_eq (x i) hxi).symm

lemma free_normRepresentative_coinvariant :
    (Coinvariants.mk (Representation.free k G I)).comp
      ((freeNormRepresentative I).comp (Representation.free k G I).norm) =
      Coinvariants.mk (Representation.free k G I) := by
  classical
  ext i g
  have hn : (Representation.free k G I).norm (Finsupp.single i (MonoidAlgebra.single g (1:k))) =
      Finsupp.single i ((Representation.leftRegular k G).norm (MonoidAlgebra.single g 1)) := by
    simp only [Representation.norm, LinearMap.sum_apply, Representation.finsupp_single]
    exact (map_sum (Finsupp.lsingle i : MonoidAlgebra k G →ₗ[k] (I →₀ MonoidAlgebra k G))
      (fun h => Representation.leftRegular k G h (MonoidAlgebra.single g 1)) Finset.univ).symm
  have hone : ((Representation.leftRegular k G).norm (MonoidAlgebra.single g (1:k))).coeff 1 = 1 := by
    rw [Representation.leftRegular_norm_apply]
    simp [regular_norm_single_coeff]
  have hrep : freeNormRepresentative I
      (Finsupp.single i ((Representation.leftRegular k G).norm (MonoidAlgebra.single g (1:k)))) =
      Finsupp.single i (MonoidAlgebra.single 1 1) := by
    simp [freeNormRepresentative, hone]
  change Coinvariants.mk _ (freeNormRepresentative I ((Representation.free k G I).norm
      (Finsupp.single i (MonoidAlgebra.single g 1)))) = _
  rw [hn, hrep]
  simpa [Representation.free_single_single] using
    (Coinvariants.mk_self_apply (Representation.free k G I) g
      (Finsupp.single i (MonoidAlgebra.single 1 (1:k)))).symm

 

theorem free_norm_bijective : Function.Bijective
    (coinvariantNorm (Representation.free k G I)) := by
  constructor
  · intro a b hab
    obtain ⟨x,rfl⟩ := Coinvariants.mk_surjective _ a
    obtain ⟨y,rfl⟩ := Coinvariants.mk_surjective _ b
    have hn := congrArg Subtype.val hab
    have hx := congr($(free_normRepresentative_coinvariant (k:=k) (G:=G) I) x)
    have hy := congr($(free_normRepresentative_coinvariant (k:=k) (G:=G) I) y)
    dsimp only [LinearMap.comp_apply] at hx hy
    rw [← hx, ← hy]
    exact congrArg (fun z => Coinvariants.mk _ (freeNormRepresentative I z)) hn
  · apply (coinvariantNorm_surjective_iff _).2
    intro x hx
    exact ⟨freeNormRepresentative I x, free_normRepresentative_invariant I x hx⟩
end FiberFunctorProof

end OAI
