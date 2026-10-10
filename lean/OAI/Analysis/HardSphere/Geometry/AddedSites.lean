import Mathlib
import OAI.Analysis.HardSphere.Geometry.TorusNear

namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace HardSphere.Lattice

def addedSites {K : ℕ} (H : Finset (DiscreteTorus K)) : Finset (DiscreteTorus K) :=
  H.biUnion fun c ↦ ((torusOffsets 1).erase 0).image (fun d ↦ c+torusProjection K d)

lemma torus_unit_offsets_card : ((torusOffsets 1).erase 0).card=26 := by
  rw [Finset.card_erase_of_mem (by simp [torusOffsets,Fintype.mem_piFinset]),torusOffsets_card]
  norm_num

lemma addedSites_card {K : ℕ} (H : Finset (DiscreteTorus K)) : (addedSites H).card≤26*H.card := by
  calc
    _ ≤ ∑ c∈H, (((torusOffsets 1).erase 0).image (fun d ↦ c+torusProjection K d)).card := Finset.card_biUnion_le
    _ ≤ ∑ _c∈H, 26 := by
      apply Finset.sum_le_sum
      intro c _
      exact Finset.card_image_le.trans torus_unit_offsets_card.le
    _ = 26*H.card := by simp [Nat.mul_comm]

lemma mem_addedSites {K : ℕ} {H : Finset (DiscreteTorus K)} {c x : DiscreteTorus K}
    (hc : c∈H) (hne : c≠x) (hcx : torusNear K 1 c x) : x∈addedSites H := by
  obtain ⟨d,hd,he⟩ := hcx
  apply Finset.mem_biUnion.mpr
  refine ⟨c,hc,Finset.mem_image.mpr ⟨d,Finset.mem_erase.mpr ⟨?_,?_⟩,?_⟩⟩
  · intro heq
    apply hne
    ext i
    have h := he i
    simp only [heq,Pi.zero_apply,Int.cast_zero,add_zero] at h
    exact h.symm
  · simpa only [torusOffsets,Fintype.mem_piFinset,Finset.mem_Icc,← abs_le] using hd
  · ext i; exact (he i).symm

end HardSphere.Lattice

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace HardSphere.Lattice
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]

def encounterSet (e : V → V → Prop) (P Q : Finset V) : Finset (V×V) :=
  (P×ˢQ).filter fun z ↦ e z.1 z.2

omit [Fintype V] [DecidableEq V] in
lemma mem_encounterSet (e : V → V → Prop) (P Q : Finset V) (x y : V) :
    (x,y)∈encounterSet e P Q ↔ x∈P ∧ y∈Q ∧ e x y := by
  simp only [encounterSet,Finset.mem_filter,Finset.mem_product]
  tauto

lemma encounterSet_card_le (e : V → V → Prop) (D : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D) (P Q : Finset V) :
    (encounterSet e P Q).card≤P.card*D := by
  have hsub : encounterSet e P Q ⊆
      P.biUnion (fun x ↦ (Finset.univ.filter (e x)).image (fun y ↦ (x,y))) := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,_,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    exact Finset.mem_biUnion.mpr ⟨x,hx,Finset.mem_image.mpr ⟨y,by simp [he],rfl⟩⟩
  calc
    _ ≤ (P.biUnion (fun x ↦ (Finset.univ.filter (e x)).image (fun y ↦ (x,y)))).card := Finset.card_le_card hsub
    _ ≤ ∑ x∈P, ((Finset.univ.filter (e x)).image (fun y ↦ (x,y))).card := Finset.card_biUnion_le
    _ ≤ ∑ _x∈P, D := by
      apply Finset.sum_le_sum
      intro x _
      exact Finset.card_image_le.trans (hdeg x)
    _ = P.card*D := by simp

lemma encounterSet_card_le_right (e : V → V → Prop) (hsym : ∀ x y, e x y → e y x) (D : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D) (P Q : Finset V) :
    (encounterSet e P Q).card≤Q.card*D := by
  have hsub : encounterSet e P Q ⊆ (encounterSet e Q P).image Prod.swap := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    exact Finset.mem_image.mpr ⟨(y,x),(mem_encounterSet e Q P y x).mpr ⟨hy,hx,hsym x y he⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (encounterSet_card_le e D hdeg Q P))

theorem encounter_charge_bound {H : Type v} [DecidableEq H]
    (e : V → V → Prop) (hsym : ∀ x y, e x y → e y x) (D b : ℕ)
    (hdeg : ∀ x, (Finset.univ.filter (e x)).card≤D)
    (Γ Γ' P Q : Finset V) (Hs : Finset H) (added : H → Finset V) (size : H → ℕ)
    (hsize : ∀ h∈Hs, (added h).card≤b*size h)
    (hcharge : ∀ x∈P, ∀ y∈Q, e x y →
      (x∈Γ ∧ y∈Γ') ∨ ∃ h∈Hs, x∈added h ∨ y∈added h) :
    (encounterSet e P Q).card ≤ (encounterSet e Γ Γ').card+(2*b*D)*∑ h∈Hs, size h := by
  let A := Hs.biUnion (fun h ↦ encounterSet e (added h) Q ∪ encounterSet e P (added h))
  have hsubset : encounterSet e P Q ⊆ encounterSet e Γ Γ' ∪ A := by
    rintro ⟨x,y⟩ hxy
    obtain ⟨hx,hy,he⟩ := (mem_encounterSet e P Q x y).mp hxy
    rcases hcharge x hx y hy he with hnom|⟨h,hh,hadd⟩
    · exact Finset.mem_union_left A ((mem_encounterSet e Γ Γ' x y).mpr ⟨hnom.1,hnom.2,he⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨h,hh,?_⟩
      rcases hadd with hadd|hadd
      · exact Finset.mem_union_left _ ((mem_encounterSet e (added h) Q x y).mpr ⟨hadd,hy,he⟩)
      · exact Finset.mem_union_right _ ((mem_encounterSet e P (added h) x y).mpr ⟨hx,hadd,he⟩)
  have hA : A.card ≤ (2*b*D)*∑ h∈Hs, size h := by
    calc
      _ ≤ ∑ h∈Hs, (encounterSet e (added h) Q ∪ encounterSet e P (added h)).card := Finset.card_biUnion_le
      _ ≤ ∑ h∈Hs, (2*b*D)*size h := by
        apply Finset.sum_le_sum
        intro h hh
        calc
          _ ≤ (encounterSet e (added h) Q).card+(encounterSet e P (added h)).card := Finset.card_union_le _ _
          _ ≤ (added h).card*D+(added h).card*D :=
            Nat.add_le_add (encounterSet_card_le e D hdeg _ _) (encounterSet_card_le_right e hsym D hdeg _ _)
          _ ≤ (b*size h)*D+(b*size h)*D := Nat.add_le_add
            (Nat.mul_le_mul_right D (hsize h hh)) (Nat.mul_le_mul_right D (hsize h hh))
          _ = (2*b*D)*size h := by ring
      _ = (2*b*D)*∑ h∈Hs, size h := by rw [Finset.mul_sum]
  exact (Finset.card_le_card hsubset).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hA _))

end HardSphere.Lattice

namespace HardSphere.Lattice

def torusContact {K : ℕ} (R : ℕ) (H Γ : Finset (DiscreteTorus K)) : Prop :=
  ∃ c∈H, ∃ z∈Γ, torusNear K R c z

def shellAttachment {K : ℕ} [NeZero K] (R : ℕ) (B Γ : Finset (DiscreteTorus K))
    (x : DiscreteTorus K) : Prop :=
  ∃ c∈B, torusNear K 1 c x ∧
    ∃ z∈Γ, z∈badComponent (torusRangeGraph K (R+2)) B c

lemma near_badComponent_eq {K R : ℕ} [NeZero K] (B : Finset (DiscreteTorus K))
    {c d : DiscreteTorus K} (hc : c∈B) (hd : d∈B) (hcd : torusNear K R c d) :
    badComponent (torusRangeGraph K R) B c=badComponent (torusRangeGraph K R) B d := by
  by_cases he : c=d
  · rw [he]
  · apply badComponent_eq_of_reachable
    exact (show (badGraph (torusRangeGraph K R) B).Adj c d from ⟨hc,hd,he,hcd⟩).reachable

lemma shell_encounter_charge {K R : ℕ} [NeZero K]
    (B Γ Γ' : Finset (DiscreteTorus K)) {x y : DiscreteTorus K}
    (hxgood : x∉B) (hxattach : shellAttachment R B Γ x)
    (hy : y∈Γ' ∨ shellAttachment R B Γ' y) (hxy : torusNear K R x y) :
    ∃ H∈badComponents (torusRangeGraph K (R+2)) B,
      torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ' ∧ x∈addedSites H := by
  obtain ⟨c,hc,hcx,z,hz,hzc⟩ := hxattach
  let H := badComponent (torusRangeGraph K (R+2)) B c
  have hcH : c∈H := mem_own_badComponent _ _ hc
  refine ⟨H,Finset.mem_image.mpr ⟨c,hc,rfl⟩,?_,?_,?_⟩
  · exact ⟨z,hzc,z,hz,torusNear_refl _ _ _⟩
  · rcases hy with hy|hy
    · exact ⟨c,hcH,y,hy,torusNear_mono (by omega) (torusNear_add hcx hxy)⟩
    · obtain ⟨d,hd,hdy,w,hw,hwd⟩ := hy
      have hcd : torusNear K (R+2) c d := by
        convert torusNear_add (torusNear_add hcx hxy) (torusNear_symm hdy) using 1; omega
      have he := near_badComponent_eq B hc hd hcd
      have hwH : w∈H := by dsimp [H]; rw [he]; exact hwd
      exact ⟨w,hwH,w,hw,torusNear_refl _ _ _⟩
  · exact mem_addedSites hcH (fun he ↦ hxgood (he ▸ hc)) hcx

theorem torus_detour_charge {K : ℕ} [NeZero K] (R : ℕ)
    (B Γ Γ' P Q : Finset (DiscreteTorus K))
    (hP : ∀ x∈P, x∉B ∧ (x∈Γ ∨ shellAttachment R B Γ x))
    (hQ : ∀ y∈Q, y∉B ∧ (y∈Γ' ∨ shellAttachment R B Γ' y)) :
    (encounterSet (torusNear K R) P Q).card ≤
      (encounterSet (torusNear K R) Γ Γ').card+
      (52*(2*R+1)^3)*∑ H∈(badComponents (torusRangeGraph K (R+2)) B).filter
        (fun H ↦ torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ'), H.card := by
  apply encounter_charge_bound (torusNear K R) (fun _ _ h ↦ torusNear_symm h)
    ((2*R+1)^3) 26 (torusNear_ball_card R) Γ Γ' P Q
    ((badComponents (torusRangeGraph K (R+2)) B).filter
      (fun H ↦ torusContact (R+2) H Γ ∧ torusContact (R+2) H Γ')) addedSites Finset.card
  · intro H _
    exact addedSites_card H
  · intro x hx y hy hxy
    have hx' := hP x hx
    have hy' := hQ y hy
    rcases hx'.2 with hxnom|hxattach
    · rcases hy'.2 with hynom|hyattach
      · exact Or.inl ⟨hxnom,hynom⟩
      · obtain ⟨H,hH,hHΓ',hHΓ,hyH⟩ := shell_encounter_charge B Γ' Γ hy'.1 hyattach
          (Or.inl hxnom) (torusNear_symm hxy)
        exact Or.inr ⟨H,Finset.mem_filter.mpr ⟨hH,hHΓ,hHΓ'⟩,Or.inr hyH⟩
    · obtain ⟨H,hH,hHΓ,hHΓ',hxH⟩ := shell_encounter_charge B Γ Γ' hx'.1 hxattach hy'.2 hxy
      exact Or.inr ⟨H,Finset.mem_filter.mpr ⟨hH,hHΓ,hHΓ'⟩,Or.inl hxH⟩

end HardSphere.Lattice

end

end OAI
