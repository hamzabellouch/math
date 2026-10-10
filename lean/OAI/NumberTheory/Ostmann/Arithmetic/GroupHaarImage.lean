import OAI.NumberTheory.Ostmann.Arithmetic.ResidueHaar

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.GroupHaarImage
open scoped BigOperators
open ResidueHaar

local instance subgroupFintype {H : Type*} [Group H] [Fintype H]
    (S : Subgroup H) : Fintype S := Fintype.ofFinite S

def homProductEquiv {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) : G ≃ H × f.ker where
  toFun x := (f x,⟨(Classical.choose (hf (f x)))⁻¹*x, by
    simp [MonoidHom.mem_ker,Classical.choose_spec (hf (f x))]⟩)
  invFun z := Classical.choose (hf z.1) * z.2.val
  left_inv x := by simp
  right_inv z := by
    have hk : f z.2.val = 1 := z.2.property
    have hr : f (Classical.choose (hf z.1)) = z.1 := Classical.choose_spec (hf z.1)
    apply Prod.ext
    · simp [map_mul,hr,hk]
    · apply Subtype.ext
      simp [map_mul,hr,hk]

theorem average_surjective {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f)
    (F : H → ℂ) : average (fun x => F (f x)) = average F := by
  classical
  let e := homProductEquiv f hf
  have h := average_equiv e (fun z : H × f.ker => F z.1)
  change average (fun x => F (f x)) = average (fun z : H × f.ker => F z.1) at h
  have hk : average (fun _ : f.ker => (1:ℂ)) = 1 := by
    have hc : (Fintype.card f.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [average,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    exact inv_mul_cancel₀ hc
  calc
    _ = average (fun z : H × f.ker => F z.1 * 1) := by
      simpa only [mul_one] using h
    _ = average F * average (fun _ : f.ker => (1:ℂ)) := average_product F (fun _ : f.ker => (1:ℂ))
    _ = _ := by rw [hk,mul_one]

theorem average_range {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (F : f.range → ℂ) :
    average (fun x => F (f.rangeRestrict x)) = average F := by
  classical
  exact @average_surjective G f.range _ _ _ (subgroupFintype f.range)
    f.rangeRestrict f.rangeRestrict_surjective F

end Ostmann.Arithmetic.GroupHaarImage

end

end OAI
