import OAI.GroupTheory.FiniteLattice.LeastImage
import OAI.GroupTheory.FiniteLattice.RetainedCore

namespace OAI

/-! Normality of least preimages under compatible local extensions. -/
namespace FiniteLattice.CommonCore

variable {M H D : Type*} [Group M] [Group H] [Group D]

/-- A least preimage computed inside a normal covering subgroup agrees with
that computed in its ambient group, for the prescribed normal image J. -/
theorem least_image_inside_normal_eq
    (f : M →* H) (J : Subgroup H) [J.Normal]
    (Q : Subgroup M) [Q.Normal] (hQ : Q.map f = J)
    (hminQ : ∀ B : Subgroup M, B.Normal → J ≤ B.map f → Q ≤ B)
    (C : Subgroup M) [C.Normal] (hC : J ≤ C.map f)
    (B : Subgroup C) [B.Normal] (hB : B.map (f.comp C.subtype) = J)
    (hminB : ∀ A : Subgroup C, A.Normal → J ≤ A.map (f.comp C.subtype) → B ≤ A) :
    B.map C.subtype = Q := by
  have hBN : (B.map C.subtype).Normal := by
    refine ⟨?_⟩
    intro x hx r
    obtain ⟨b, hb, rfl⟩ := hx
    let a : C ≃* C := C.normalizerMonoidHom
      ⟨r, by rw [Subgroup.normalizer_eq_top]; trivial⟩
    have hc : ∀ z : C,
        (f.comp C.subtype) (a z) = (MulAut.conj (f r)) ((f.comp C.subtype) z) := by
      intro z
      change f (r * (z : M) * r⁻¹) = f r * f (z : M) * (f r)⁻¹
      simp only [map_mul, map_inv]
    have hj : ∀ y ∈ J, MulAut.conj (f r) y ∈ J :=
      fun y hy => (inferInstance : J.Normal).conj_mem y hy (f r)
    refine ⟨a b, least_image_stable (f.comp C.subtype) J B hB hminB
      a (MulAut.conj (f r)) hj hc b hb, ?_⟩
    rfl
  have hBimage : (B.map C.subtype).map f = J := by
    rw [Subgroup.map_map]
    exact hB
  have hQB : Q ≤ B.map C.subtype := hminQ _ hBN hBimage.ge
  have hQC : Q ≤ C := hminQ C inferInstance hC
  have hcover : J ≤ (Q.comap C.subtype).map (f.comp C.subtype) := by
    intro y hy
    rw [← hQ] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hQC hx⟩, hx, hxy⟩
  have hBQ := hminB (Q.comap C.subtype) inferInstance hcover
  exact le_antisymm (by rintro _ ⟨b, hb, rfl⟩; exact hBQ hb) hQB

/-- A local extension normalizes the least preimage when a normal subgroup
covering the prescribed image is also normal in the ambient group. -/
theorem least_image_normal_of_local_extension
    (A : Subgroup D) [Finite A] (f : A →* H) (beta : D →* H)
    (hext : ∀ a : A, beta a = f a)
    (J : Subgroup H) [J.Normal] [Group.IsPerfect J]
    (Q : Subgroup A) [Q.Normal] (hQ : Q.map f = J)
    (hminQ : ∀ B : Subgroup A, B.Normal → J ≤ B.map f → Q ≤ B)
    (C : Subgroup A) [C.Normal] [(C.map A.subtype).Normal]
    (hC : J ≤ C.map f) : (Q.map A.subtype).Normal := by
  have hrange : J ≤ (f.comp C.subtype).range := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hC hy
    exact ⟨⟨x, hx⟩, hxy⟩
  obtain ⟨B, hBN, hB, hminB⟩ :=
    FiniteLattice.exists_least_normal_perfect_preimage (f.comp C.subtype) J hrange
  let : B.Normal := hBN
  have hBQ : B.map C.subtype = Q :=
    least_image_inside_normal_eq f J Q hQ hminQ C hC B hB hminB
  refine ⟨?_⟩
  intro x hx d
  obtain ⟨q, hq, rfl⟩ := hx
  rw [← hBQ] at hq
  obtain ⟨b, hb, rfl⟩ := hq
  let a : C ≃* C := FiniteLattice.RetainedCore.embeddedConj C A.subtype
    Subtype.val_injective d (by rw [Subgroup.normalizer_eq_top]; trivial)
  have ha (z : C) : A.subtype (a z : A) =
      d * A.subtype (z : A) * d⁻¹ :=
    FiniteLattice.RetainedCore.embeddedConj_val C A.subtype
      Subtype.val_injective d _ z
  have hc : ∀ z : C, (f.comp C.subtype) (a z) =
      MulAut.conj (beta d) ((f.comp C.subtype) z) := by
    intro z
    change f (a z : A) = beta d * f (z : A) * (beta d)⁻¹
    rw [← hext (a z : A), ← hext (z : A)]
    change beta (A.subtype (a z : A)) =
      beta d * beta (A.subtype (z : A)) * (beta d)⁻¹
    rw [ha]
    simp only [map_mul, map_inv]
  have hj : ∀ y ∈ J, MulAut.conj (beta d) y ∈ J :=
    fun y hy => (inferInstance : J.Normal).conj_mem y hy (beta d)
  have hab : a b ∈ B := least_image_stable (f.comp C.subtype) J B hB hminB
    a (MulAut.conj (beta d)) hj hc b hb
  refine ⟨(a b : A), ?_, ha b⟩
  rw [← hBQ]
  exact ⟨a b, hab, rfl⟩

/-- The least preimage is normal in the ambient group when the relative core
covers the prescribed image. -/
theorem least_image_normal_of_core
    (A : Subgroup D) [Finite A] (f : A →* H) (beta : D →* H)
    (hext : ∀ a : A, beta a = f a)
    (J : Subgroup H) [J.Normal] [Group.IsPerfect J]
    (Q : Subgroup A) [Q.Normal] (hQ : Q.map f = J)
    (hminQ : ∀ B : Subgroup A, B.Normal → J ≤ B.map f → Q ≤ B)
    (hcore : J ≤ (A.normalCore.comap A.subtype).map f) :
    (Q.map A.subtype).Normal := by
  let C : Subgroup A := A.normalCore.comap A.subtype
  have hCmap : C.map A.subtype = A.normalCore := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact ha
    · intro x hx
      exact ⟨⟨x, A.normalCore_le hx⟩, hx, rfl⟩
  let : (C.map A.subtype).Normal := by
    rw [hCmap]
    infer_instance
  exact least_image_normal_of_local_extension A f beta hext J Q hQ hminQ C hcore

/-- Intersecting a subgroup with the kernel of a restricted homomorphism
commutes with its inclusion into the ambient group. -/
theorem local_kernel_image_eq
    (A : Subgroup D) (f : A →* H) (beta : D →* H)
    (hext : ∀ a : A, beta a = f a) (Q : Subgroup A) :
    (Q ⊓ f.ker).map A.subtype = Q.map A.subtype ⊓ beta.ker := by
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    change beta (a : D) = 1
    rw [hext]
    exact ha.2
  · rintro x ⟨⟨a, ha, rfl⟩, hk⟩
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    change f a = 1
    rw [← hext]
    exact hk

/-- The intersection with the kernel is normal in the ambient group whenever
the subgroup is normal and the homomorphism extends to that group. -/
theorem local_kernel_normal
    (A : Subgroup D) (f : A →* H) (beta : D →* H)
    (hext : ∀ a : A, beta a = f a) (Q : Subgroup A)
    [(Q.map A.subtype).Normal] : ((Q ⊓ f.ker).map A.subtype).Normal := by
  rw [local_kernel_image_eq A f beta hext Q]
  infer_instance

end FiniteLattice.CommonCore

end OAI
