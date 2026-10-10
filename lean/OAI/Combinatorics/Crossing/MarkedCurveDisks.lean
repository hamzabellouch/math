import OAI.Combinatorics.Crossing.RoundDiskClearance

namespace OAI

noncomputable section
namespace Zarankiewicz

theorem closedRoundDisk_mono (z : Plane) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    closedRoundDisk z r ⊆ closedRoundDisk z s := by
  intro x hx
  change squaredLength (x-z) ≤ r^2 at hx
  change squaredLength (x-z) ≤ s^2
  nlinarith

theorem finite_curve_mark_isolation {E M : Type*} [Fintype E] [Fintype M] [DecidableEq M]
    (γ : E → unitInterval → Plane) (hγ : ∀ e, Continuous (γ e))
    (mark : M → Plane) (hm : Function.Injective mark)
    (O : E → M → Set unitInterval) (hO : ∀ e k, IsOpen (O e k))
    (hvisit : ∀ e k t, γ e t=mark k → t ∈ O e k) :
    ∃ r : ℝ, 0 < r ∧
      (∀ k l, k ≠ l → Disjoint (closedRoundDisk (mark k) r) (closedRoundDisk (mark l) r)) ∧
      (∀ e k t, γ e t ∈ closedRoundDisk (mark k) r → t ∈ O e k) := by
  let K : E × M → Set Plane := fun ek => γ ek.1 '' (O ek.1 ek.2)ᶜ
  have hK (ek : E × M) : IsCompact (K ek) :=
    (hO ek.1 ek.2).isClosed_compl.isCompact.image (hγ ek.1)
  have hnot (ek : E × M) : mark ek.2 ∉ K ek := by
    rintro ⟨t,ht,he⟩
    exact ht (hvisit ek.1 ek.2 t he)
  obtain ⟨ρ,hρ,hclear⟩ := exists_round_disk_clearance (fun ek : E × M => mark ek.2) K hK hnot
  obtain ⟨σ,hσ,hdisjoint⟩ := exists_disjoint_round_disks mark hm
  refine ⟨min ρ σ,lt_min hρ hσ,?_,?_⟩
  · intro k l hkl
    exact (hdisjoint k l hkl).mono
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
      (closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_right _ _))
  · intro e k t ht
    by_contra hn
    have hd : γ e t ∈ closedRoundDisk (mark k) ρ :=
      closedRoundDisk_mono _ (le_of_lt (lt_min hρ hσ)) (min_le_left _ _) ht
    exact Set.disjoint_left.mp (hclear (e,k)) hd ⟨t,hn,rfl⟩

end Zarankiewicz

end

end OAI
