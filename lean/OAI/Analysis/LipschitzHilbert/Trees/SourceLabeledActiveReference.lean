import OAI.Analysis.LipschitzHilbert.Trees.SourceLabeledMainRestriction

namespace OAI

/-! The narrow main reference family retains only labels active at the
frozen direction. Inactive labels contribute exactly zero, so neither
the square nor the masked variation needs spectral assumptions there. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
  (t : ℝ) (b : ∀ j, P.labels j → κ → ℝ → ℂ)

def frozenActiveLabels (j : Fin N) : Finset (Label j) :=
  (P.labels j).filter (fun l => ∃ h : l ∈ P.labels j, ∃ k, b j ⟨l,h⟩ k t ≠ 0)

def frozenActiveOriginalLabel (j : Fin N) (l : P.frozenActiveLabels t b j) : P.labels j :=
  ⟨l.val,(Finset.mem_filter.mp l.property).1⟩

theorem frozenActiveLabel_nonzero (j : Fin N) (l : P.frozenActiveLabels t b j) :
    ∃ k, b j (P.frozenActiveOriginalLabel t b j l) k t ≠ 0 := by
  obtain ⟨h,k,hk⟩ := (Finset.mem_filter.mp l.property).2
  have heq : (⟨l.val,h⟩ : P.labels j) = P.frozenActiveOriginalLabel t b j l := Subtype.ext rfl
  exact ⟨k,by simpa only [heq] using hk⟩

theorem frozenActiveLabels_card_le (j : Fin N) :
    (P.frozenActiveLabels t b j).card ≤ (P.labels j).card :=
  Finset.card_le_card (Finset.filter_subset _ _)

def frozenActiveFamily : SourceLabeledLattice N κ Label Item where
  topLength := P.topLength
  width := P.width
  scale := P.scale
  ratioBound := P.ratioBound
  carrierBound := P.carrierBound
  profileBound := P.profileBound
  order := P.order
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  profileBound_pos := P.profileBound_pos
  order_ge_three := P.order_ge_three
  ratioBound_ge_one := P.ratioBound_ge_one
  scale_bound := P.scale_bound
  carrierBound_nonneg := P.carrierBound_nonneg
  labels := P.frozenActiveLabels t b
  originX := fun j l => P.originX j (P.frozenActiveOriginalLabel t b j l)
  originZ := fun j l => P.originZ j (P.frozenActiveOriginalLabel t b j l)
  rowSlope := fun j l => P.rowSlope j (P.frozenActiveOriginalLabel t b j l)
  frequency := P.frequency
  site := fun j l => P.site j (P.frozenActiveOriginalLabel t b j l)
  site_injective := fun j l => P.site_injective j (P.frozenActiveOriginalLabel t b j l)
  profile := fun j l => P.profile j (P.frozenActiveOriginalLabel t b j l)
  profile_bound := fun j l => P.profile_bound j (P.frozenActiveOriginalLabel t b j l)
  shear_bound := fun j l => P.shear_bound j (P.frozenActiveOriginalLabel t b j l)
  carrier_bound := fun j l => P.carrier_bound j (P.frozenActiveOriginalLabel t b j l)

@[simp] theorem frozenActiveFamily_constant : (P.frozenActiveFamily t b).constant = P.constant := rfl

def frozenActiveSelector : ∀ j, (P.frozenActiveFamily t b).labels j → κ → ℝ → ℂ :=
  fun j l => b j (P.frozenActiveOriginalLabel t b j l)

@[simp] theorem frozenActiveFamily_physicalPacket (s : ℝ) (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (k : κ) :
    (P.frozenActiveFamily t b).physicalPacket s j l u k =
      P.physicalPacket s j (P.frozenActiveOriginalLabel t b j l) u k := rfl

@[simp] theorem frozenActiveFamily_positiveEnvelope (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (y x : ℝ) :
    (P.frozenActiveFamily t b).positiveEnvelope j l u y x =
      P.positiveEnvelope j (P.frozenActiveOriginalLabel t b j l) u y x := rfl

@[simp] theorem frozenActiveFamily_raw (i : Fin 3) (j : Fin N)
    (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) (k : κ) (y : ℝ) :
    (P.frozenActiveFamily t b).raw i j l u k y =
      P.raw i j (P.frozenActiveOriginalLabel t b j l) u k y := rfl

@[simp] theorem frozenActiveFamily_alt_raw
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (i : Fin 3) (j : Fin N) (l : (P.frozenActiveFamily t b).labels j)
    (u : Item j l) (k : κ) (y : ℝ) :
    ((P.frozenActiveFamily t b).withProfile
      (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
      (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l))).raw i j l u k y =
      (P.withProfile alt hAlt).raw i j (P.frozenActiveOriginalLabel t b j l) u k y := rfl

theorem frozenActiveFamily_frozenCoefficient (a : ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (j : Fin N) (l : (P.frozenActiveFamily t b).labels j) (u : Item j l) :
    (P.frozenActiveFamily t b).physicalFrozenCenteredCoefficient t a
      (P.frozenActiveSelector t b) v g j l u =
        P.physicalFrozenCenteredCoefficient t a b v g j (P.frozenActiveOriginalLabel t b j l) u := rfl

def frozenActiveLabelsEquiv (j : Fin N) : P.frozenActiveLabels t b j ≃
    {l : P.labels j // ∃ k, b j l k t ≠ 0} where
  toFun := fun l => ⟨P.frozenActiveOriginalLabel t b j l,P.frozenActiveLabel_nonzero t b j l⟩
  invFun := fun l => ⟨l.val.val,Finset.mem_filter.mpr ⟨l.val.property,
    ⟨l.val.property,l.property⟩⟩⟩
  left_inv := fun _ => Subtype.ext rfl
  right_inv := fun _ => Subtype.ext (Subtype.ext rfl)

theorem sum_frozenActive_of_zero {E : Type*} [AddCommMonoid E] (j : Fin N)
    (f : ∀ l : P.labels j, Item j l → E)
    (hzero : ∀ l, (∀ k, b j l k t = 0) → ∀ u, f l u = 0) :
    (∑ l : P.frozenActiveLabels t b j, ∑ u : Item j l,
      f (P.frozenActiveOriginalLabel t b j l) u) =
        ∑ l : P.labels j, ∑ u : Item j l, f l u := by
  have heq := Equiv.sum_comp (P.frozenActiveLabelsEquiv t b j)
    (fun l => ∑ u : Item j l.val, f l.val u)
  have hz : (∑ l : {l : P.labels j // ¬∃ k, b j l k t ≠ 0},
      ∑ u : Item j l.val, f l.val u) = 0 := by
    apply Finset.sum_eq_zero
    intro l _
    apply Finset.sum_eq_zero
    intro u _
    exact hzero l.val (fun k => by
      by_contra hn
      exact l.property ⟨k,hn⟩) u
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun l : P.labels j => ∃ k, b j l k t ≠ 0)
    (fun l => ∑ u : Item j l, f l u)
  rw [hz,add_zero] at hsum
  exact heq.trans hsum

theorem physicalMainScale_eq_frozenActive (a : ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (j : Fin N) (y x : ℝ) :
    P.physicalMainScale t a b v g j y x =
      (P.frozenActiveFamily t b).physicalMainScale t a (P.frozenActiveSelector t b) v g j y x := by
  let f (l : P.labels j) (u : Item j l) :=
    ‖P.physicalFrozenCenteredCoefficient t a b v g j l u‖*P.positiveEnvelope j l u y x
  have hs := P.sum_frozenActive_of_zero t b (E := ℝ) j f (fun l hz u => by
    dsimp only [f]
    rw [P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz,norm_zero,zero_mul])
  exact hs.symm

theorem physicalMainSquare_eq_frozenActive (a : ℝ)
    (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ) (y x : ℝ) :
    P.physicalMainSquare t a b v g y x =
      (P.frozenActiveFamily t b).physicalMainSquare t a (P.frozenActiveSelector t b) v g y x := by
  unfold physicalMainSquare
  simp_rw [P.physicalMainScale_eq_frozenActive t b a v g]

theorem physicalCenteredMaskedBand_eq_frozenActive
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y : ℝ) (j : Fin N) (x : ℝ) :
    P.physicalCenteredMaskedBand alt hAlt t a b v g T L A y j x =
      (P.frozenActiveFamily t b).physicalCenteredMaskedBand
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l)) t a
        (P.frozenActiveSelector t b) v g
        (fun j l => T j (P.frozenActiveOriginalLabel t b j l)) L A y j x := by
  ext k
  let f (l : P.labels j) (u : Item j l) : ℂ :=
    P.physicalFrozenCenteredCoefficient t a b v g j l u k*
      ((T j l u).mask L A (x,y+t*x):ℂ)*
      (P.withProfile alt hAlt).physicalPacket t j l u k (x,y+t*x)
  have hs := P.sum_frozenActive_of_zero t b (E := ℂ) j f (fun l hz u => by
    have hc := congrArg (fun c : EuclideanSpace ℂ κ => c k)
      (P.physicalFrozenCenteredCoefficient_eq_zero t a b v g j l u hz)
    dsimp only [f]
    rw [hc]
    simp)
  exact hs.symm

theorem physicalCenteredMaskedVariation_eq_frozenActive
    (alt : ∀ j (l : P.labels j), Item j l → κ → SchwartzMap (ℝ×ℝ) ℂ)
    (hAlt : ∀ j l u k, planarProfileConstant (alt j l u k) (2*P.order) ≤ P.profileBound)
    (a : ℝ) (v : ℝ×ℝ → ℝ) (g : ℝ×ℝ → EuclideanSpace ℂ κ)
    (T : ∀ j (l : P.labels j), Item j l → SlopeBox) (L A y x : ℝ) :
    P.physicalCenteredMaskedVariation alt hAlt t a b v g T L A y x =
      (P.frozenActiveFamily t b).physicalCenteredMaskedVariation
        (fun j l => alt j (P.frozenActiveOriginalLabel t b j l))
        (fun j l => hAlt j (P.frozenActiveOriginalLabel t b j l)) t a
        (P.frozenActiveSelector t b) v g
        (fun j l => T j (P.frozenActiveOriginalLabel t b j l)) L A y x := by
  unfold physicalCenteredMaskedVariation
  congr 2
  funext j
  exact P.physicalCenteredMaskedBand_eq_frozenActive t b alt hAlt a v g T L A y j x

end LipschitzHilbert.SourceLabeledLattice

end

end OAI
