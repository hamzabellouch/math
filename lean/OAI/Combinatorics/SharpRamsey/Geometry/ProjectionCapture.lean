import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.Projection

namespace OAI

section
namespace SharpLogRamsey.Projection
open Finset Incidence
open scoped Classical BigOperators
noncomputable section
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

lemma projected_liftCap (S : Finset (Projectivization K V)) (z : Projectivization K V)
    (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    projected (liftCap S z W) z=projected S z∩W := by
  ext b
  constructor
  · intro hb
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hb
    have hh := (mem_liftCap S z p.val W).mp (mem_subtype.mp hp)
    obtain ⟨hS,hn,hW⟩ := hh
    exact mem_inter.mpr ⟨mem_image.mpr ⟨p,mem_subtype.mpr hS,rfl⟩,hW⟩
  · intro hb
    obtain ⟨hs,hw⟩ := mem_inter.mp hb
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hs
    exact mem_image.mpr ⟨p,mem_subtype.mpr ((mem_liftCap _ _ _ _).mpr
      ⟨mem_subtype.mp hp,p.property,hw⟩),rfl⟩

lemma projected_card_le (S : Finset (Projectivization K V)) (z : Projectivization K V) :
    (projected S z).card≤S.card := by
  exact card_image_le.trans (by rw [card_subtype]; exact card_filter_le _ _)

lemma inter_liftCap (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    S∩liftCap U z W=liftCap S z W := by
  ext p
  simp only [mem_inter,mem_liftCap]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hSU h.1,h.2⟩⟩

theorem original_support_loss (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule))) :
    (S\liftCap U z W).card ≤ (projected S z\W).card+orderedCollisions S z+1 := by
  have hc := projected_card_le (liftCap S z W) z
  rw [projected_liftCap] at hc
  have he : (S\liftCap U z W).card+(S∩liftCap U z W).card=S.card :=
    card_sdiff_add_card_inter S (liftCap U z W)
  rw [inter_liftCap S U hSU] at he
  have hi : (projected S z\W).card+(projected S z∩W).card=(projected S z).card :=
    card_sdiff_add_card_inter _ _
  have hp := projection_loss S z
  omega

theorem original_support_loss_real (S U : Finset (Projectivization K V)) (hSU : S⊆U)
    (z : Projectivization K V) (W : Finset (Projectivization K (V ⧸ z.submodule)))
    (ε δ : ℝ) (hε : 0≤ε)
    (hcap : (projected S z\W).card≤ε*(projected S z).card)
    (hcol : (orderedCollisions S z:ℝ)+1≤δ*S.card) :
    ((S\liftCap U z W).card:ℝ)≤(ε+δ)*S.card := by
  have h := original_support_loss S U hSU z W
  have hr : ((S\liftCap U z W).card:ℝ)≤(projected S z\W).card+orderedCollisions S z+1 := by
    exact_mod_cast h
  have hp : ((projected S z).card:ℝ)≤S.card := by exact_mod_cast projected_card_le S z
  have hpc := mul_le_mul_of_nonneg_left hp hε
  linarith

end
end SharpLogRamsey.Projection

end

end OAI
