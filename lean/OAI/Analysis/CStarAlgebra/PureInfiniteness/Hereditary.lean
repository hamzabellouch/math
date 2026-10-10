import Mathlib

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra ComplexOrder InnerProductSpace

namespace MainGap

variable {A : Type*} [NonUnitalCStarAlgebra A]

def sandwichAlgebra (h : A) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range (fun a : A => h * a * star h)
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp [mul_add, add_mul]⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * star h * h * b, by simp only [mul_assoc]⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    exact ⟨c • a, by simp only [mul_smul_comm, smul_mul_assoc]⟩
  star_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨star a, by simp only [star_mul, star_star, mul_assoc]⟩

def Her (h : A) : NonUnitalStarSubalgebra ℂ A := (sandwichAlgebra h).topologicalClosure

lemma mem_Her_iff {h a : A} : a ∈ Her h ↔
    a ∈ closure (Set.range (fun b : A => h * b * star h)) := Iff.rfl

lemma isClosed_Her (h : A) : IsClosed (Her h : Set A) := isClosed_closure

instance (h : A) : IsClosed (Her h : Set A) := isClosed_Her h

lemma sandwich_mem_Her (h a : A) : h * a * star h ∈ Her h :=
  subset_closure ⟨a, rfl⟩

instance (h : A) : CompleteSpace (Her h) := (isClosed_Her h).completeSpace_coe

def sandwichMap (h : A) : A →ₗ[ℂ] Her h where
  toFun a := ⟨h * a * star h, sandwich_mem_Her h a⟩
  map_add' a b := Subtype.ext (by
    change h * (a + b) * star h = h * a * star h + h * b * star h
    simp only [mul_add, add_mul])
  map_smul' c a := Subtype.ext (by
    change h * (c • a) * star h = c • (h * a * star h)
    simp only [mul_smul_comm, smul_mul_assoc])

@[simp] lemma sandwichMap_val (h a : A) : (sandwichMap h a : A) = h * a * star h := rfl

lemma sandwichMap_dense (h : A) : DenseRange (sandwichMap h) := by
  intro a
  rw [closure_subtype]
  have heq : Subtype.val '' Set.range (sandwichMap h) =
      Set.range (fun b : A => h * b * star h) := by
    ext b
    constructor
    · rintro ⟨k, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨sandwichMap h c, ⟨c, rfl⟩, rfl⟩
  rw [heq]
  exact a.property

lemma norm_mul_eq_of_star_mul_eq {z h : A} (hzh : star z * z = star h * h) (a : A) :
    ‖z * a‖ = ‖h * a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two, ← CStarRing.norm_star_mul_self, star_mul]
  congr 1
  calc
    star a * star z * (z * a) = star a * (star z * z) * a := by noncomm_ring
    _ = star a * (star h * h) * a := by rw [hzh]
    _ = star a * star h * (h * a) := by noncomm_ring

def carrierNumerator (z h : A) : A →ₗ[ℂ] A where
  toFun a := z * a * star h
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

def carrier (z h : A) : Her h →L[ℂ] A :=
  (carrierNumerator z h).extendOfNorm (sandwichMap h)

lemma carrier_on_sandwich {z h : A} (hzh : star z * z = star h * h) (a : A) :
    carrier z h (sandwichMap h a) = z * a * star h := by
  apply LinearMap.extendOfNorm_eq (sandwichMap_dense h)
  refine ⟨1, fun b => ?_⟩
  change ‖z * b * star h‖ ≤ 1 * ‖h * b * star h‖
  rw [one_mul, mul_assoc, mul_assoc, norm_mul_eq_of_star_mul_eq hzh]

lemma carrier_norm {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    ‖carrier z h k‖ = ‖(k : A)‖ := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [carrier_on_sandwich hzh, sandwichMap_val, mul_assoc, mul_assoc,
    norm_mul_eq_of_star_mul_eq hzh]

lemma carrier_inner {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    star (carrier z h k) * carrier z h l = star (k : A) * (l : A) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  simp only [carrier_on_sandwich hzh, sandwichMap_val, star_mul, star_star]
  calc
    h * (star a * star z) * (z * b * star h) =
        h * star a * (star z * z) * b * star h := by noncomm_ring
    _ = h * star a * (star h * h) * b * star h := by rw [hzh]
    _ = h * (star a * star h) * (h * b * star h) := by noncomm_ring

lemma carrier_mul {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    carrier z h (k * l) = carrier z h k * (l : A) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have heq : sandwichMap h a * sandwichMap h b =
      sandwichMap h (a * star h * h * b) := Subtype.ext (by
        change (h * a * star h) * (h * b * star h) =
          h * (a * star h * h * b) * star h
        simp only [mul_assoc])
  rw [heq, carrier_on_sandwich hzh, carrier_on_sandwich hzh, sandwichMap_val]
  simp only [mul_assoc]

lemma norm_mul_star_eq_of_star_mul_eq {z h : A} (hzh : star z * z = star h * h) (a : A) :
    ‖a * star z‖ = ‖a * star h‖ := by
  calc
    ‖a * star z‖ = ‖star (a * star z)‖ := (norm_star _).symm
    _ = ‖z * star a‖ := by rw [star_mul, star_star]
    _ = ‖h * star a‖ := norm_mul_eq_of_star_mul_eq hzh _
    _ = ‖star (a * star h)‖ := by rw [star_mul, star_star]
    _ = ‖a * star h‖ := norm_star _

lemma norm_sandwich_eq {z h : A} (hzh : star z * z = star h * h) (a : A) :
    ‖z * a * star z‖ = ‖h * a * star h‖ := by
  rw [norm_mul_star_eq_of_star_mul_eq hzh, mul_assoc, mul_assoc,
    norm_mul_eq_of_star_mul_eq hzh]

def conjugationNumerator (z : A) : A →ₗ[ℂ] A where
  toFun a := z * a * star z
  map_add' a b := by simp only [mul_add, add_mul]
  map_smul' c a := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

def conjugation (z h : A) : Her h →L[ℂ] A :=
  (conjugationNumerator z).extendOfNorm (sandwichMap h)

lemma conjugation_on_sandwich {z h : A} (hzh : star z * z = star h * h) (a : A) :
    conjugation z h (sandwichMap h a) = z * a * star z := by
  apply LinearMap.extendOfNorm_eq (sandwichMap_dense h)
  refine ⟨1, fun b => ?_⟩
  change ‖z * b * star z‖ ≤ 1 * ‖h * b * star h‖
  rw [one_mul, norm_sandwich_eq hzh]

lemma conjugation_norm {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    ‖conjugation z h k‖ = ‖(k : A)‖ := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  rw [conjugation_on_sandwich hzh, sandwichMap_val, norm_sandwich_eq hzh]

lemma conjugation_mem {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    conjugation z h k ∈ Her z := by
  refine (sandwichMap_dense h).induction_on k
    ((isClosed_Her z).preimage (conjugation z h).continuous) ?_
  intro a
  rw [conjugation_on_sandwich hzh]
  exact sandwich_mem_Her z a

lemma conjugation_mul {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    conjugation z h (k * l) = conjugation z h k * conjugation z h l := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have heq : sandwichMap h a * sandwichMap h b =
      sandwichMap h (a * star h * h * b) := Subtype.ext (by
        change (h * a * star h) * (h * b * star h) =
          h * (a * star h * h * b) * star h
        simp only [mul_assoc])
  rw [heq, conjugation_on_sandwich hzh, conjugation_on_sandwich hzh,
    conjugation_on_sandwich hzh]
  calc
    z * (a * star h * h * b) * star z = z * a * (star h * h) * b * star z := by
      noncomm_ring
    _ = z * a * (star z * z) * b * star z := by rw [hzh]
    _ = (z * a * star z) * (z * b * star z) := by noncomm_ring

lemma carrier_outer {z h : A} (hzh : star z * z = star h * h) (k l : Her h) :
    carrier z h k * star (carrier z h l) = conjugation z h (k * star l) := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  refine (sandwichMap_dense h).induction_on l (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro b
  have heq : sandwichMap h a * star (sandwichMap h b) =
      sandwichMap h (a * star h * h * star b) := Subtype.ext (by
        change (h * a * star h) * star (h * b * star h) =
          h * (a * star h * h * star b) * star h
        simp only [star_mul, star_star, mul_assoc])
  rw [heq, carrier_on_sandwich hzh, carrier_on_sandwich hzh, conjugation_on_sandwich hzh]
  simp only [star_mul, star_star, mul_assoc]

lemma conjugation_star {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    conjugation z h (star k) = star (conjugation z h k) := by
  refine (sandwichMap_dense h).induction_on k
    (isClosed_eq ((conjugation z h).continuous.comp continuous_star)
      (continuous_star.comp (conjugation z h).continuous)) ?_
  intro a
  have heq : star (sandwichMap h a) = sandwichMap h (star a) := Subtype.ext (by
    change star (h * a * star h) = h * star a * star h
    simp only [star_mul, star_star, mul_assoc])
  rw [heq, conjugation_on_sandwich hzh, conjugation_on_sandwich hzh]
  simp only [star_mul, star_star, mul_assoc]

def transportHom {z h : A} (hzh : star z * z = star h * h) : Her h →⋆ₙₐ[ℂ] A :=
  { (conjugation z h).toLinearMap with
    map_zero' := map_zero (conjugation z h)
    map_mul' := conjugation_mul hzh
    map_star' := conjugation_star hzh }

lemma transportHom_injective {z h : A} (hzh : star z * z = star h * h) :
    Function.Injective (transportHom hzh) := by
  intro k l heq
  apply sub_eq_zero.mp
  apply Subtype.val_injective
  apply norm_eq_zero.mp
  rw [← conjugation_norm hzh]
  change ‖transportHom hzh (k - l)‖ = 0
  rw [map_sub, heq, sub_self, norm_zero]

lemma transport_represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) {z h : A} (hzh : star z * z = star h * h) (k : Her h) :
    ‖π (transportHom hzh k)‖ = ‖π (k : A)‖ := by
  refine (sandwichMap_dense h).induction_on k (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  change ‖π (conjugation z h (sandwichMap h a))‖ = ‖π (h * a * star h)‖
  rw [conjugation_on_sandwich hzh]
  simp only [map_mul, map_star]
  apply norm_sandwich_eq
  simpa only [map_mul, map_star] using congrArg π hzh

lemma Her_sandwich {h k : A} (hk : k ∈ Her h) (a : A) : k * a * star k ∈ Her h := by
  let k' : Her h := ⟨k, hk⟩
  change (k' : A) * a * star (k' : A) ∈ Her h
  refine (sandwichMap_dense h).induction_on k'
    ((isClosed_Her h).preimage (by fun_prop)) ?_
  intro b
  change (h * b * star h) * a * star (h * b * star h) ∈ Her h
  convert sandwich_mem_Her h (b * star h * a * h * star b) using 1
  simp only [star_mul, star_star, mul_assoc]

lemma Her_mono_of_mem {h k : A} (hk : k ∈ Her h) : Her k ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  exact Her_sandwich hk a

lemma Her_mul_le (h k : A) : Her (h * k) ≤ Her h := by
  apply closure_minimal _ (isClosed_Her h)
  rintro _ ⟨a, rfl⟩
  change (h * k) * a * star (h * k) ∈ Her h
  convert sandwich_mem_Her h (k * a * star k) using 1
  simp only [star_mul, mul_assoc]

structure RegularTransport (h v : A) where
  carrier : Her h →L[ℂ] A
  hom : Her h →⋆ₙₐ[ℂ] A
  inner : ∀ k l : Her h, star (carrier k) * carrier l = star (k : A) * (l : A)
  outer : ∀ k l : Her h, carrier k * star (carrier l) = hom (k * star l)
  mul : ∀ k l : Her h, carrier (k * l) = carrier k * (l : A)
  image : ∀ k : Her h, hom k ∈ Her v

namespace RegularTransport
variable {h v : A} (T : RegularTransport h v)

def restrict {k : A} (T : RegularTransport k v) (hle : Her h ≤ Her k) :
    RegularTransport h v := by
  let ι : Her h →⋆ₙₐ[ℂ] Her k := NonUnitalStarSubalgebra.inclusion hle
  let i : Her h →L[ℂ] Her k := {
    toFun := ι
    map_add' := map_add ι
    map_smul' := map_smul ι
    cont := by fun_prop }
  exact {
    carrier := T.carrier.comp i
    hom := T.hom.comp ι
    inner := fun a b => T.inner (ι a) (ι b)
    outer := fun a b => by
      change T.carrier (ι a) * star (T.carrier (ι b)) = T.hom (ι (a * star b))
      rw [map_mul, map_star]
      exact T.outer (ι a) (ι b)
    mul := fun a b => by
      change T.carrier (ι (a * b)) = T.carrier (ι a) * (b : A)
      rw [map_mul]
      exact T.mul (ι a) (ι b)
    image := fun a => T.image (ι a) }

lemma carrier_represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) (k : Her h) : ‖π (T.carrier k)‖ = ‖π (k : A)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [pow_two, ← CStarRing.norm_star_mul_self, ← map_star, ← map_mul, T.inner]

lemma represented_norm {B : Type*} [NonUnitalCStarAlgebra B]
    (π : A →⋆ₙₐ[ℂ] B) (k : Her h) : ‖π (T.hom k)‖ = ‖π (k : A)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  calc
    ‖π (T.hom k)‖ ^ 2 = ‖π (T.hom (star k * k))‖ := by
      simp only [map_mul, map_star, CStarRing.norm_star_mul_self, pow_two]
    _ = ‖π (T.carrier (star k) * star (T.carrier (star k)))‖ := by
      rw [T.outer, star_star]
    _ = ‖π (T.carrier (star k))‖ ^ 2 := by
      simp only [map_mul, map_star, CStarRing.norm_self_mul_star, pow_two]
    _ = ‖π (star (k : A))‖ ^ 2 := by
      rw [T.carrier_represented_norm, StarMemClass.coe_star]
    _ = ‖π (k : A)‖ ^ 2 := by rw [map_star, norm_star]

lemma norm_hom (k : Her h) : ‖T.hom k‖ = ‖(k : A)‖ :=
  T.represented_norm (NonUnitalStarAlgHom.id ℂ A) k

lemma injective : Function.Injective T.hom := by
  intro k l hkl
  apply sub_eq_zero.mp
  apply Subtype.val_injective
  apply norm_eq_zero.mp
  rw [← T.norm_hom, map_sub, hkl, sub_self, norm_zero]

end RegularTransport

section Order
variable [PartialOrder A] [StarOrderedRing A]

lemma mul_star_mem_Her (h : A) : h * star h ∈ Her h := by
  apply (isClosed_Her h).mem_of_tendsto
    (((CStarAlgebra.increasingApproximateUnit A).tendsto_mul_left h).mul_const (star h))
  exact Filter.Eventually.of_forall (sandwich_mem_Her h)

lemma sqrt_mem_Her {h k : A} (hk : k ∈ Her h) (hkpos : 0 ≤ k) : CFC.sqrt k ∈ Her h := by
  rw [CFC.sqrt_eq_real_sqrt k hkpos]
  exact cfcₙ_mem (𝕜' := ℂ) Real.sqrt hk

lemma self_mem_Her {h : A} (hh : 0 ≤ h) : h ∈ Her h := by
  have hm : h * h ∈ Her h := by
    simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using mul_star_mem_Her h
  simpa only [CFC.sqrt_mul_self h hh] using
    sqrt_mem_Her hm (by simpa only [IsSelfAdjoint.of_nonneg hh |>.star_eq] using
      star_mul_self_nonneg h)

lemma sqrt_Her_eq {h : A} (hh : 0 ≤ h) : Her (CFC.sqrt h) = Her h := by
  apply le_antisymm
  · exact Her_mono_of_mem (sqrt_mem_Her (self_mem_Her hh) hh)
  · apply Her_mono_of_mem
    have ht := self_mem_Her (CFC.sqrt_nonneg h)
    have hm : CFC.sqrt h * CFC.sqrt h ∈ Her (CFC.sqrt h) := (Her (CFC.sqrt h)).mul_mem ht ht
    rwa [CFC.sqrt_mul_sqrt_self h hh] at hm

def twoSidedRemainder (e a : A) : A := a - e * a - a * e + e * a * e

lemma twoSidedRemainder_as_square {e a : A} (he : IsSelfAdjoint e) (ha : 0 ≤ a) :
    twoSidedRemainder e a =
      (CFC.sqrt a - e * CFC.sqrt a) * star (CFC.sqrt a - e * CFC.sqrt a) := by
  have hs : star (CFC.sqrt a) = CFC.sqrt a := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg a)).star_eq
  simp only [star_sub, star_mul, he.star_eq, hs]
  calc
    twoSidedRemainder e a = a - e * a - a * e + e * a * e := rfl
    _ = (CFC.sqrt a * CFC.sqrt a) - e * (CFC.sqrt a * CFC.sqrt a) -
        (CFC.sqrt a * CFC.sqrt a) * e + e * (CFC.sqrt a * CFC.sqrt a) * e := by
      rw [CFC.sqrt_mul_sqrt_self a ha]
    _ = _ := by noncomm_ring

lemma twoSidedRemainder_nonneg {e a : A} (he : IsSelfAdjoint e) (ha : 0 ≤ a) :
    0 ≤ twoSidedRemainder e a := by
  rw [twoSidedRemainder_as_square he ha]
  exact mul_star_self_nonneg _

lemma twoSidedRemainder_mono {e a b : A} (he : IsSelfAdjoint e) (hab : a ≤ b) :
    twoSidedRemainder e a ≤ twoSidedRemainder e b := by
  apply sub_nonneg.mp
  convert twoSidedRemainder_nonneg he (sub_nonneg.mpr hab) using 1
  simp only [twoSidedRemainder]
  noncomm_ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_twoSidedRemainder_le {e : A} (he : ‖e‖ ≤ 1) (b : A) :
    ‖twoSidedRemainder e b‖ ≤ 2 * ‖b - e * b‖ := by
  have heq : twoSidedRemainder e b = (b - e * b) - (b - e * b) * e := by
    simp only [twoSidedRemainder]
    noncomm_ring
  rw [heq]
  calc
    ‖(b - e * b) - (b - e * b) * e‖ ≤ ‖b - e * b‖ + ‖(b - e * b) * e‖ := norm_sub_le _ _
    _ ≤ ‖b - e * b‖ + ‖b - e * b‖ * ‖e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 2 * ‖b - e * b‖ := by nlinarith [norm_nonneg (b - e * b)]

lemma norm_sqrt_remainder_sq_le {e a b : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 ≤ 2 * ‖b - e * b‖ := by
  calc
    ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 = ‖twoSidedRemainder e a‖ := by
      rw [twoSidedRemainder_as_square he ha, CStarRing.norm_self_mul_star, pow_two]
    _ ≤ ‖twoSidedRemainder e b‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg (twoSidedRemainder_mono he hab)
        (twoSidedRemainder_nonneg he ha)
    _ ≤ 2 * ‖b - e * b‖ := norm_twoSidedRemainder_le hen b

lemma norm_compression_error_le {e a : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) :
    ‖a - e * a * e‖ ≤ 2 * ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖ := by
  have ha' : IsSelfAdjoint a := .of_nonneg ha
  have hstar : ‖a - a * e‖ = ‖a - e * a‖ := by
    rw [← norm_star (a - a * e), star_sub, star_mul, he.star_eq, ha'.star_eq]
  have heq : a - e * a * e = (a - e * a) + e * (a - a * e) := by noncomm_ring
  have hbound : ‖a - e * a‖ ≤ ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖ := by
    calc
      ‖a - e * a‖ = ‖(CFC.sqrt a - e * CFC.sqrt a) * CFC.sqrt a‖ := by
        rw [sub_mul, mul_assoc e, CFC.sqrt_mul_sqrt_self a ha]
      _ ≤ _ := norm_mul_le _ _
  calc
    ‖a - e * a * e‖ = ‖(a - e * a) + e * (a - a * e)‖ := congrArg norm heq
    _ ≤ ‖a - e * a‖ + ‖e * (a - a * e)‖ := norm_add_le _ _
    _ ≤ ‖a - e * a‖ + ‖e‖ * ‖a - a * e‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ 2 * ‖a - e * a‖ := by rw [hstar]; nlinarith [norm_nonneg (a - e * a)]
    _ ≤ _ := by nlinarith

lemma norm_compression_error_sq_le {e a b : A} (he : IsSelfAdjoint e) (hen : ‖e‖ ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ‖a - e * a * e‖ ^ 2 ≤ 8 * ‖a‖ * ‖b - e * b‖ := by
  have hsa : IsSelfAdjoint (CFC.sqrt a) := .of_nonneg (CFC.sqrt_nonneg _)
  have hsq : ‖CFC.sqrt a‖ ^ 2 = ‖a‖ := by
    rw [← hsa.norm_mul_self, CFC.sqrt_mul_sqrt_self a ha]
  calc
    ‖a - e * a * e‖ ^ 2 ≤
        (2 * ‖CFC.sqrt a - e * CFC.sqrt a‖ * ‖CFC.sqrt a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr (norm_compression_error_le he hen ha)
    _ = 4 * ‖a‖ * ‖CFC.sqrt a - e * CFC.sqrt a‖ ^ 2 := by rw [← hsq]; ring
    _ ≤ 4 * ‖a‖ * (2 * ‖b - e * b‖) := by
      gcongr
      exact norm_sqrt_remainder_sq_le he hen ha hab
    _ = _ := by ring

lemma Her_exists_approx_unit {b : A} (hb : 0 ≤ b) {δ : ℝ} (hδ : 0 < δ) :
    ∃ e : A, e ∈ Her b ∧ IsSelfAdjoint e ∧ ‖e‖ ≤ 1 ∧ ‖b - e * b‖ < δ := by
  let b' : Her b := ⟨b, self_mem_Her hb⟩
  let : PartialOrder (Her b) := CStarAlgebra.spectralOrder (Her b)
  let : StarOrderedRing (Her b) := CStarAlgebra.spectralOrderedRing (Her b)
  have hunit := CStarAlgebra.increasingApproximateUnit (Her b)
  have ht : Tendsto (fun e : Her b => ‖b' - e * b'‖)
      (CStarAlgebra.approximateUnit (Her b)) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := b')).sub (hunit.tendsto_mul_right b')).norm
  have hsmall : ∀ᶠ e : Her b in CStarAlgebra.approximateUnit (Her b), ‖b' - e * b'‖ < δ :=
    ht.eventually (Iio_mem_nhds hδ)
  obtain ⟨e, hn, hp, hs⟩ := (hunit.eventually_norm.and (hunit.eventually_nonneg.and hsmall)).exists
  refine ⟨e, e.property, ?_, hn, hs⟩
  change star (e : A) = (e : A)
  have he := congrArg (fun x : Her b => (x : A)) (IsSelfAdjoint.of_nonneg hp |>.star_eq)
  exact he

lemma mem_Her_of_nonneg_le {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : a ∈ Her b := by
  have hb : 0 ≤ b := ha.trans hab
  have hc : a ∈ closure (Her b : Set A) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hden : 0 < 8 * ‖a‖ + 1 := by positivity
    have hδ : 0 < ε ^ 2 / (8 * ‖a‖ + 1) := div_pos (sq_pos_of_pos hε) hden
    obtain ⟨e, he, hesa, hen, hesmall⟩ := Her_exists_approx_unit hb hδ
    refine ⟨e * a * e, ?_, ?_⟩
    · change e * a * e ∈ Her b
      simpa only [hesa.star_eq] using Her_sandwich he a
    · rw [dist_eq_norm]
      have hsq := norm_compression_error_sq_le hesa hen ha hab
      have hp : (8 * ‖a‖ + 1) * ‖b - e * b‖ < ε ^ 2 := by
        have ht := mul_lt_mul_of_pos_left hesmall hden
        rwa [mul_div_cancel₀ _ (ne_of_gt hden)] at ht
      have hfinal : ‖a - e * a * e‖ ^ 2 < ε ^ 2 := by
        nlinarith [norm_nonneg (b - e * b)]
      exact (sq_lt_sq₀ (norm_nonneg _) hε.le).mp hfinal
  rwa [(isClosed_Her b).closure_eq] at hc

lemma Her_mono {a b : A} (ha : 0 ≤ a) (hab : a ≤ b) : Her a ≤ Her b :=
  Her_mono_of_mem (mem_Her_of_nonneg_le ha hab)

omit [PartialOrder A] [StarOrderedRing A] in
lemma real_smul_mem_Her {h a : A} (ha : a ∈ Her h) (r : ℝ) : r • a ∈ Her h := by
  change r • a ∈ (Her h).toSubmodule
  simpa only [Complex.coe_smul] using (Her h).smul_mem (r : ℂ) ha

lemma smul_Her_eq {h : A} (hh : 0 ≤ h) {r : ℝ} (hr : 0 < r) :
    Her (r • h) = Her h := by
  apply le_antisymm
  · exact Her_mono_of_mem (real_smul_mem_Her (self_mem_Her hh) r)
  · apply Her_mono_of_mem
    have hm := real_smul_mem_Her (self_mem_Her (smul_nonneg hr.le hh)) r⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hr), one_smul] using hm

lemma square_Her_eq {h : A} (hh : 0 ≤ h) : Her (h * h) = Her h := by
  have hm : 0 ≤ h * h := by
    simpa only [(IsSelfAdjoint.of_nonneg hh).star_eq] using star_mul_self_nonneg h
  simpa only [CFC.sqrt_mul_self h hh] using (sqrt_Her_eq hm).symm

lemma Her_eq_of_order_bounds {a b : A} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hl : r • a ≤ b) (hu : b ≤ R • a) :
    Her b = Her a := by
  apply le_antisymm
  · simpa only [smul_Her_eq ha hR] using Her_mono hb hu
  · simpa only [smul_Her_eq ha hr] using Her_mono (smul_nonneg hr.le ha) hl

def cut (d : A) (ε : ℝ) : A := cfcₙ (fun t : ℝ => max (t - ε) 0) d

lemma cut_nonneg (d : A) (ε : ℝ) : 0 ≤ cut d ε := by
  exact cfcₙ_nonneg (fun _ _ => le_max_right _ _)

lemma cut_mem_Her {d : A} (hd : 0 ≤ d) (ε : ℝ) : cut d ε ∈ Her d := by
  exact cfcₙ_mem (𝕜' := ℂ) _ (self_mem_Her hd)

lemma cut_sandwich_lower {d : A} (hd : IsSelfAdjoint d) {ε : ℝ} (hε : 0 ≤ ε) :
    ε • (cut d ε * cut d ε) ≤ cut d ε * d * cut d ε := by
  let f : ℝ → ℝ := fun t => max (t - ε) 0
  have hf : Continuous f := (continuous_id.sub continuous_const).max continuous_const
  have hf0 : f 0 = 0 := by simp [f, max_eq_right (neg_nonpos.mpr hε)]
  have hid : cfcₙ (fun t : ℝ => t) d = d := cfcₙ_id ℝ d hd
  have hl : cfcₙ (fun t => ε * (f t * f t)) d = ε • (cut d ε * cut d ε) := by
    rw [cfcₙ_const_mul ε (fun t => f t * f t) d (hf.mul hf).continuousOn
      (by simp [hf0]), cfcₙ_mul f f d hf.continuousOn hf0 hf.continuousOn hf0]
    rfl
  have hu : cfcₙ (fun t => f t * t * f t) d = cut d ε * d * cut d ε := by
    rw [cfcₙ_mul (fun t => f t * t) f d (hf.mul continuous_id).continuousOn
      (by simp [hf0]) hf.continuousOn hf0,
      cfcₙ_mul f (fun t => t) d hf.continuousOn hf0 continuousOn_id rfl, hid]
    rfl
  rw [← hl, ← hu]
  apply (cfcₙ_le_iff _ _ d (continuous_const.mul (hf.mul hf)).continuousOn
    ((hf.mul continuous_id).mul hf).continuousOn (by simp [hf0]) (by simp [hf0]) hd).mpr
  intro t _
  by_cases ht : ε ≤ t
  · calc
      ε * (f t * f t) ≤ t * (f t * f t) :=
        mul_le_mul_of_nonneg_right ht (mul_self_nonneg _)
      _ = f t * t * f t := by ring
  · simp [f, max_eq_right (by linarith : t - ε ≤ 0)]

lemma cut_transport_lower {d v s : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (ε - ‖d - star s * v * s‖) • (cut d ε * cut d ε) ≤
      cut d ε * (star s * v * s) * cut d ε := by
  let h := cut d ε
  have hh : IsSelfAdjoint h := .of_nonneg (cut_nonneg d ε)
  have hb : IsSelfAdjoint (d - star s * v * s) :=
    (IsSelfAdjoint.of_nonneg hd).sub (.of_nonneg (star_left_conjugate_nonneg hv s))
  have hbound : h * d * h - h * (star s * v * s) * h ≤
      ‖d - star s * v * s‖ • (h * h) := by
    simpa only [hh.star_eq, mul_sub, sub_mul] using
      CStarAlgebra.star_left_conjugate_le_norm_smul h (d - star s * v * s) hb
  calc
    (ε - ‖d - star s * v * s‖) • (h * h) =
        ε • (h * h) - ‖d - star s * v * s‖ • (h * h) := sub_smul _ _ _
    _ ≤ h * d * h - ‖d - star s * v * s‖ • (h * h) :=
      sub_le_sub_right (cut_sandwich_lower (.of_nonneg hd) hε) _
    _ ≤ h * (star s * v * s) * h := (sub_le_comm).mp hbound

theorem regularTransport_of_approx {d v s : A} (hd : 0 ≤ d) (hv : 0 ≤ v)
    {ε : ℝ} (hε : 0 < ε) (hs : ‖d - star s * v * s‖ < ε) :
    Nonempty (RegularTransport (cut d ε) v) := by
  let h := cut d ε
  let z := CFC.sqrt v * s * h
  have hhpos : 0 ≤ h := cut_nonneg d ε
  have hh : IsSelfAdjoint h := .of_nonneg hhpos
  have hvroot : IsSelfAdjoint (CFC.sqrt v) := .of_nonneg (CFC.sqrt_nonneg v)
  have hzz : star z * z = h * (star s * v * s) * h := by
    simp only [z, star_mul, hh.star_eq, hvroot.star_eq]
    calc
      h * (star s * CFC.sqrt v) * (CFC.sqrt v * s * h) =
          h * (star s * (CFC.sqrt v * CFC.sqrt v) * s) * h := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self v hv]
  have hspos : 0 ≤ star s * v * s := star_left_conjugate_nonneg hv s
  have hh2pos : 0 ≤ h * h := by simpa only [hh.star_eq] using star_mul_self_nonneg h
  have hl : (ε - ‖d - star s * v * s‖) • (h * h) ≤ star z * z := by
    rw [hzz]
    exact cut_transport_lower hd hv hε.le
  have hu : star z * z ≤ (‖star s * v * s‖ + 1) • (h * h) := by
    rw [hzz]
    calc
      h * (star s * v * s) * h ≤ ‖star s * v * s‖ • (h * h) := by
        simpa only [hh.star_eq] using
          CStarAlgebra.star_left_conjugate_le_norm_smul h (star s * v * s) (.of_nonneg hspos)
      _ ≤ _ := smul_le_smul_of_nonneg_right (by linarith) hh2pos
  have heq : Her (star z * z) = Her h := by
    rw [Her_eq_of_order_bounds hh2pos (star_mul_self_nonneg z)
      (sub_pos.mpr hs) (by positivity) hl hu, square_Her_eq hhpos]
  let q := CFC.sqrt (star z * z)
  have hq : star z * z = star q * q := by
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (star z * z))).star_eq]
    exact (CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg z)).symm
  have hqHer : Her q = Her h := (sqrt_Her_eq (star_mul_self_nonneg z)).trans heq
  have hrange : Her z ≤ Her v := by
    calc
      Her z = Her (CFC.sqrt v * (s * h)) := by simp only [z, mul_assoc]
      _ ≤ Her (CFC.sqrt v) := Her_mul_le _ _
      _ = Her v := sqrt_Her_eq hv
  let T : RegularTransport q v := {
    carrier := carrier z q
    hom := transportHom hq
    inner := carrier_inner hq
    outer := carrier_outer hq
    mul := carrier_mul hq
    image := fun k => hrange (conjugation_mem hq k) }
  exact ⟨T.restrict hqHer.ge⟩

end Order

end MainGap

end

end OAI
