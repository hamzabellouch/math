import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace OAI

/-! # Splitting an extension using a bijective twisted-difference map

A central quotient element with bijective Lang map on the kernel selects a
unique commuting lift in every quotient fiber. These lifts form a subgroup.
-/

noncomputable section
namespace PolycyclicRecognition
variable {N G Q : Type*} [Group N] [Group G] [Group Q]
  (S : GroupExtension N G Q) (t : G)

/-- The twisted difference on the kernel, with the order needed for correcting
left coset representatives. -/
def extensionLangMap (n : N) : N := n⁻¹ * S.conjAct t n

@[simp] theorem extensionLangMap_one : extensionLangMap S t 1 = 1 := by
  simp [extensionLangMap]

def centralizerProjection : Subgroup.centralizer ({t} : Set G) →* Q :=
  S.rightHom.comp (Subgroup.centralizer ({t} : Set G)).subtype

theorem centralizerProjection_surjective
    (ht : ∀ q : Q, Commute (S.rightHom t) q)
    (hLang : Function.Surjective (extensionLangMap S t)) :
    Function.Surjective (centralizerProjection S t) := by
  intro q
  obtain ⟨g, hg⟩ := S.rightHom_surjective q
  have hdmem : t * g * t⁻¹ * g⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [(ht (S.rightHom g)).eq]
    group
  obtain ⟨d, hd⟩ := hdmem
  obtain ⟨n, hn⟩ := hLang d⁻¹
  have hn' : S.conjAct t n = n * d⁻¹ := inv_mul_eq_iff_eq_mul.mp hn
  have htg : t * g = S.inl d * g * t := by rw [hd]; group
  have hcomm : t * (S.inl n * g) = (S.inl n * g) * t := by
    calc
      _ = (t * S.inl n * t⁻¹) * (t * g) := by group
      _ = S.inl (S.conjAct t n) * (S.inl d * g * t) := by
        rw [S.inl_conjAct_comm, htg]
      _ = _ := by rw [hn', map_mul, map_inv]; group
  refine ⟨⟨S.inl n * g, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩, ?_⟩
  change S.rightHom (S.inl n * g) = q
  rw [map_mul, S.rightHom_inl, one_mul, hg]

theorem centralizerProjection_injective
    (hLang : Function.Injective (extensionLangMap S t)) :
    Function.Injective (centralizerProjection S t) := by
  intro a b hab
  have hab' : S.rightHom (a : G) = S.rightHom (b : G) := hab
  have hx : (a : G) * (b : G)⁻¹ ∈ S.inl.range := by
    rw [S.range_inl_eq_ker_rightHom, MonoidHom.mem_ker, map_mul, map_inv, hab', mul_inv_cancel]
  obtain ⟨n, hn⟩ := hx
  have hcomm : t * S.inl n = S.inl n * t := by
    rw [hn]
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      ((Subgroup.centralizer ({t} : Set G)).mul_mem a.property
        ((Subgroup.centralizer ({t} : Set G)).inv_mem b.property))).symm
  have hfix : S.conjAct t n = n := by
    apply S.inl_injective
    rw [S.inl_conjAct_comm, hcomm, mul_inv_cancel_right]
  have hn0 : n = 1 := hLang (by
    rw [extensionLangMap, hfix, inv_mul_cancel, extensionLangMap_one])
  have he : (a : G) * (b : G)⁻¹ = 1 := by rw [← hn, hn0, map_one]
  exact Subtype.ext (mul_inv_eq_one.mp he)

/-- The centralizer provides an actual homomorphic section of the extension. -/
def centralizerSplitting
    (ht : ∀ q : Q, Commute (S.rightHom t) q)
    (hLang : Function.Bijective (extensionLangMap S t)) : S.Splitting := by
  let e : Subgroup.centralizer ({t} : Set G) ≃* Q :=
    MulEquiv.ofBijective (centralizerProjection S t)
      ⟨centralizerProjection_injective S t hLang.1,
        centralizerProjection_surjective S t ht hLang.2⟩
  let f := (Subgroup.centralizer ({t} : Set G)).subtype.comp e.symm.toMonoidHom
  exact { f with rightInverse_rightHom := fun q => e.apply_symm_apply q }

end PolycyclicRecognition

end

end OAI
