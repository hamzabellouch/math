import Mathlib
import OAI.Analysis.Commutator.FreeWordTensor

namespace OAI

noncomputable section

noncomputable section

namespace Kadison.FreeMoments

attribute [local instance] Classical.propDecidable

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable {S τ}

variable (hstar : ∀ a : A, τ (star a) = star (τ a))

variable (h1 : τ 1 = 1)

end Kadison.FreeMoments

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A)

attribute [instance] Space.normed Space.inner

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree

end Kadison.FreeWordTensor

open scoped InnerProductSpace Topology

noncomputable section

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Kadison

namespace Kadison.FreeWordTensor

open scoped InnerProductSpace Topology

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

end Kadison.FreeWordTensor

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

end Kadison.FreeCreation

namespace Kadison.FreeCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

end Kadison.FreeCorner

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

end Kadison.FreeCreation

namespace Kadison.FreeExpectation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

lemma centered_mem {i : ι} {a : A} (ha : a ∈ S i) :
    a - t.functional a • (1 : A) ∈ S i :=
  sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i)))

lemma centered_zero (a : A) : t.functional (a - t.functional a • (1 : A)) = 0 := by
  simp [map_sub, map_smul, t.normalized]

include hfree in
lemma free_two {i j : ι} (hij : i ≠ j) {a b : A} (ha : a ∈ S i) (hb : b ∈ S j)
    (ha0 : t.functional a = 0) (hb0 : t.functional b = 0) :
    t.functional (a*b) = 0 := by
  let x : Letter S t.functional.toLinearMap := ⟨i, a, ha, ha0⟩
  let y : Letter S t.functional.toLinearMap := ⟨j, b, hb, hb0⟩
  have h := hfree [x, y] (by simpa [Reduced, List.isChain_cons_cons, x, y]) (by simp)
  simpa [word, x, y] using h

include hfree in
lemma free_three {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i)
    (ha0 : t.functional a = 0) (hb0 : t.functional b = 0) (hc0 : t.functional c = 0) :
    t.functional (a*b*c) = 0 := by
  let x : Letter S t.functional.toLinearMap := ⟨i, a, ha, ha0⟩
  let y : Letter S t.functional.toLinearMap := ⟨j, b, hb, hb0⟩
  let z : Letter S t.functional.toLinearMap := ⟨i, c, hc, hc0⟩
  have h := hfree [x, y, z]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, mul_assoc] using h

include hfree in
lemma free_four {i j : ι} (hij : i ≠ j) {a b c d : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (ha0 : t.functional a = 0) (hb0 : t.functional b = 0)
    (hc0 : t.functional c = 0) (hd0 : t.functional d = 0) :
    t.functional (a*b*c*d) = 0 := by
  let x : Letter S t.functional.toLinearMap := ⟨i, a, ha, ha0⟩
  let y : Letter S t.functional.toLinearMap := ⟨j, b, hb, hb0⟩
  let z : Letter S t.functional.toLinearMap := ⟨i, c, hc, hc0⟩
  let w : Letter S t.functional.toLinearMap := ⟨j, d, hd, hd0⟩
  have h := hfree [x, y, z, w]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, w, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, w, mul_assoc] using h

include hfree in
lemma centered_mul_zero {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (ha0 : t.functional a = 0) :
    t.functional (a*b) = 0 := by
  have h := free_two t S hfree hij ha (centered_mem t S hb) ha0 (centered_zero t b)
  simpa [mul_sub, mul_smul_comm, map_sub, map_smul, ha0] using h

include hfree in
lemma mul_centered_zero {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hb0 : t.functional b = 0) :
    t.functional (a*b) = 0 := by
  have h := free_two t S hfree hij (centered_mem t S ha) hb (centered_zero t a) hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hb0] using h

include hfree in
lemma centered_middle_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : t.functional a = 0) (hb0 : t.functional b = 0) :
    t.functional (c*a*b) = 0 := by
  have h := free_three t S hfree hij.symm (centered_mem t S hc) ha hb
    (centered_zero t c) ha0 hb0
  have hab := free_two t S hfree hij ha hb ha0 hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab, mul_assoc] using h

include hfree in
lemma centered_sandwich_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : t.functional a = 0) (hb0 : t.functional b = 0) :
    t.functional (c*a*b*a) = 0 := by
  have h := free_four t S hfree hij.symm (centered_mem t S hc) ha hb ha
    (centered_zero t c) ha0 hb0 ha0
  have hab := free_three t S hfree hij ha hb ha ha0 hb0 ha0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab] using h

include hfree in
theorem free_compression_pairing {i j : ι} (hij : i ≠ j) {e b c : A}
    (he : e ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j) (hb0 : t.functional b = 0) :
    t.functional (c * (e*b*e)) = (t.functional e)^2 * t.functional (c*b) := by
  let a := e - t.functional e • (1 : A)
  have ha : a ∈ S i := centered_mem t S he
  have ha0 : t.functional a = 0 := centered_zero t e
  have h1 := centered_sandwich_pairing t S hfree hij ha hb hc ha0 hb0
  have h2 := centered_middle_pairing t S hfree hij ha hb hc ha0 hb0
  have h3 := mul_centered_zero t S hfree hij.symm (mul_mem hc hb) ha ha0
  have hid : c * (e*b*e) = c*a*b*a + t.functional e • (c*a*b) +
      t.functional e • (c*b*a) + ((t.functional e)^2) • (c*b) := by
    dsimp [a]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one,
      smul_sub, smul_smul, pow_two]
    noncomm_ring
  rw [hid]
  simp only [map_add, map_smul, h1, h2, h3, smul_eq_mul, mul_zero, zero_add]

def factorSpace (j : ι) : Submodule ℂ t.functional.GNS :=
  (Submodule.map ((UniformSpace.Completion.toComplₗᵢ :
      t.functional.PreGNS →ₗᵢ[ℂ] t.functional.GNS).toLinearMap.comp
      t.functional.toPreGNS.toLinearMap) (S j).toSubmodule).topologicalClosure

instance (j : ι) : IsClosed (factorSpace t S j : Set t.functional.GNS) :=
  Submodule.isClosed_topologicalClosure _

lemma vector_mem_factorSpace {j : ι} {b : A} (hb : b ∈ S j) :
    (t.functional.toPreGNS b : t.functional.GNS) ∈ factorSpace t S j :=
  Submodule.le_topologicalClosure _ ⟨b, hb, rfl⟩

include hfree in
lemma compression_error_orthogonal {i j : ι} (hij : i ≠ j) {e b : A}
    (he : e ∈ S i) (hb : b ∈ S j) (hb0 : t.functional b = 0) :
    (t.functional.toPreGNS (e*b*e) : t.functional.GNS) -
      (t.functional e)^2 • (t.functional.toPreGNS b : t.functional.GNS) ∈
        (factorSpace t S j)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro x hx
  apply closure_minimal (s := (Submodule.map ((UniformSpace.Completion.toComplₗᵢ :
      t.functional.PreGNS →ₗᵢ[ℂ] t.functional.GNS).toLinearMap.comp
      t.functional.toPreGNS.toLinearMap) (S j).toSubmodule : Set _)) ?_
      (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hx
  rintro _ ⟨c, hc, rfl⟩
  change inner ℂ (t.functional.toPreGNS c : t.functional.GNS) _ = 0
  rw [inner_sub_right, inner_smul_right, Completion.inner_coe, Completion.inner_coe]
  change t.functional (star c * (e*b*e)) - (t.functional e)^2 *
    t.functional (star c*b) = 0
  rw [free_compression_pairing t S hfree hij he hb (star_mem hc) hb0, sub_self]

include hfree in
theorem free_compression_projection {i j : ι} (hij : i ≠ j) {e b : A}
    (he : e ∈ S i) (hb : b ∈ S j) (hb0 : t.functional b = 0) :
    (factorSpace t S j).starProjection (t.functional.toPreGNS (e*b*e) : t.functional.GNS) =
      (t.functional e)^2 • (t.functional.toPreGNS b : t.functional.GNS) := by
  have h := compression_error_orthogonal t S hfree hij he hb hb0
  have hp := (factorSpace t S j).orthogonalProjectionOnto_apply_of_mem_orthogonal h
  have heq : (factorSpace t S j).starProjection
      ((t.functional.toPreGNS (e*b*e) : t.functional.GNS) -
        (t.functional e)^2 • (t.functional.toPreGNS b : t.functional.GNS)) = 0 :=
    congrArg (fun x : factorSpace t S j => (x : t.functional.GNS)) hp
  exact (sub_eq_zero.mp (by simpa only [map_sub, map_smul,
    Submodule.starProjection_eq_self_iff.mpr (vector_mem_factorSpace t S hb)] using heq))

end Kadison.FreeExpectation
end
end
end

end OAI
