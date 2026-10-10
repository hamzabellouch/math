import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

namespace OAI

/-! Conjugation actions on normal sections and uniqueness on generated groups. -/
namespace FiniteLattice.CommonCore

variable {K M T : Type*} [Group K] [Group M] [Group T]

/-- An action preserving a normal subgroup descends to the quotient. -/
def quotientAction (a : K →* MulAut M) (L : Subgroup M) [L.Normal]
    (hL : ∀ k, L.map (a k).toMonoidHom = L) : K →* MulAut (M ⧸ L) where
  toFun k := QuotientGroup.congr L L (a k) (hL k)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L x
    change QuotientGroup.mk' L (a 1 x) = QuotientGroup.mk' L x
    rw [map_one, MulAut.one_apply]
  map_mul' k l := by
    apply MulEquiv.ext
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective L x
    change QuotientGroup.mk' L (a (k * l) x) =
      QuotientGroup.mk' L (a k (a l x))
    rw [map_mul, MulAut.mul_apply]

/-- An isomorphism transports an automorphism action. -/
def transportAction (a : K →* MulAut M) (e : M ≃* T) : K →* MulAut T where
  toFun k := (e.symm.trans (a k)).trans e
  map_one' := by
    apply MulEquiv.ext
    intro t
    change e (a 1 (e.symm t)) = t
    rw [map_one, MulAut.one_apply, e.apply_symm_apply]
  map_mul' k l := by
    apply MulEquiv.ext
    intro t
    change e (a (k * l) (e.symm t)) =
      e (a k (e.symm (e (a l (e.symm t)))))
    rw [e.symm_apply_apply, map_mul, MulAut.mul_apply]

/-- An ambient normal subgroup is preserved by conjugation on a normal subgroup. -/
theorem normal_section_invariant (Q L : Subgroup K) [Q.Normal] [L.Normal]
    (k : K) :
    (L.subgroupOf Q).map (MulAut.conjNormal (H := Q) k).toMonoidHom =
      L.subgroupOf Q := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    change ((MulAut.conjNormal (H := Q) k q : Q) : K) ∈ L
    rw [MulAut.conjNormal_apply]
    exact (inferInstance : L.Normal).conj_mem q.val hq k
  · intro q hq
    refine ⟨(MulAut.conjNormal (H := Q) k).symm q, ?_,
      (MulAut.conjNormal (H := Q) k).apply_symm_apply q⟩
    change (((MulAut.conjNormal (H := Q) k).symm q : Q) : K) ∈ L
    rw [MulAut.conjNormal_symm_apply]
    simpa only [inv_inv] using (inferInstance : L.Normal).conj_mem q.val hq k⁻¹

/-- Conjugation on `Q / (Q ∩ L)` transported through `theta`. -/
def normalSectionAction (Q L : Subgroup K) [Q.Normal] [L.Normal]
    (theta : (Q ⧸ L.subgroupOf Q) ≃* T) : K →* MulAut T :=
  transportAction
    (quotientAction (MulAut.conjNormal (H := Q)) (L.subgroupOf Q)
      (normal_section_invariant Q L)) theta

/-- The transported action on a quotient representative. -/
theorem normalSectionAction_apply (Q L : Subgroup K) [Q.Normal] [L.Normal]
    (theta : (Q ⧸ L.subgroupOf Q) ≃* T) (k : K) (q : Q) :
    normalSectionAction Q L theta k (theta (QuotientGroup.mk' _ q)) =
      theta (QuotientGroup.mk' _ (MulAut.conjNormal (H := Q) k q)) := by
  change theta (QuotientGroup.congr (L.subgroupOf Q) (L.subgroupOf Q)
    (MulAut.conjNormal (H := Q) k) (normal_section_invariant Q L k)
    (theta.symm (theta (QuotientGroup.mk' _ q)))) = _
  rw [theta.symm_apply_apply]
  rfl

/-- Agreement on quotient representatives determines the transported automorphism. -/
theorem normalSectionAction_eq_of_representatives
    (Q L : Subgroup K) [Q.Normal] [L.Normal]
    (theta : (Q ⧸ L.subgroupOf Q) ≃* T) (k : K) (b : MulAut T)
    (h : ∀ q : Q,
      theta (QuotientGroup.mk' _ (MulAut.conjNormal (H := Q) k q)) =
        b (theta (QuotientGroup.mk' _ q))) :
    normalSectionAction Q L theta k = b := by
  apply MulEquiv.ext
  intro t
  obtain ⟨x, rfl⟩ := theta.surjective t
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (L.subgroupOf Q) x
  rw [normalSectionAction_apply]
  exact h q

/-- Homomorphisms agreeing on a generating family of subgroups are equal. -/
theorem generated_hom_unique {H : Type*} [Group H] {ι : Type*}
    (U : ι → Subgroup K) (hgen : (⨆ i, U i) = ⊤)
    (f g : K →* H) (h : ∀ i, ∀ x : U i, f x = g x) : f = g := by
  let B : Subgroup K :=
    { carrier := {x | f x = g x}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        change f (x * y) = g (x * y)
        rw [map_mul, map_mul, hx, hy]
      inv_mem' := by
        intro x hx
        change f x⁻¹ = g x⁻¹
        rw [map_inv, map_inv, hx] }
  have hUB : ∀ i, U i ≤ B := fun i x hx => h i ⟨x, hx⟩
  have htop : (⊤ : Subgroup K) ≤ B := by
    rw [← hgen]
    exact iSup_le hUB
  apply MonoidHom.ext
  intro x
  exact htop (show x ∈ (⊤ : Subgroup K) from trivial)

end FiniteLattice.CommonCore

end OAI
