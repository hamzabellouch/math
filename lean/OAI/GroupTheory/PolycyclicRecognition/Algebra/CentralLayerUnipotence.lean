import OAI.GroupTheory.PolycyclicRecognition.Algebra.UpperCentralLayerMap

namespace OAI

/-! # Lifting unipotence from rational central layers to the original group -/

noncomputable section
namespace PolycyclicRecognition

variable {G : Type} [Group G] (F : Subgroup G) [F.Normal] [Group.IsNilpotent F]

theorem relativeCommutatorSeries_upperCentral_le (hF : HasNoNontrivialTorsion F)
    (K : Subgroup G) (i c : ℕ)
    (hc : linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    relativeCommutatorSeries K (ambientUpperCentralSeries F (i + 1)) c ≤
      ambientUpperCentralSeries F i := by
  have h := relativeCommutatorSeries_le_kernel_of_linearFiltration K
    (ambientUpperCentralSeries F (i + 1)) (rationalUpperCentralAction F i)
    (rationalUpperCentralMap F i) (rationalUpperCentralMap_equivariant F i) c hc
  rwa [rationalUpperCentralMap_kernel F hF i] at h

theorem exists_relativeCommutatorSeries_eq_bot_of_central_layers
    (hF : HasNoNontrivialTorsion F) (K : Subgroup G)
    (hc : ∀ i, i < Group.nilpotencyClass F → ∃ c, linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    ∃ c, relativeCommutatorSeries K F c = ⊥ := by
  have hi (i : ℕ) (hi : i ≤ Group.nilpotencyClass F) :
      ∃ c, relativeCommutatorSeries K (ambientUpperCentralSeries F i) c = ⊥ := by
    induction i with
    | zero => exact ⟨0, ambientUpperCentralSeries_zero F⟩
    | succ i ih =>
      obtain ⟨c, hci⟩ := hc i (by omega)
      obtain ⟨d, hd⟩ := ih (by omega)
      refine ⟨c + d, eq_bot_iff.mpr ?_⟩
      rw [relativeCommutatorSeries_add]
      exact (relativeCommutatorSeries_mono K
        (relativeCommutatorSeries_upperCentral_le F hF K i c hci) d).trans_eq hd
  simpa only [ambientUpperCentralSeries_top] using hi (Group.nilpotencyClass F) le_rfl

theorem nilpotent_of_unipotent_central_layers (hF : HasNoNontrivialTorsion F)
    (K : Subgroup G) [K.Normal]
    (hcent : Subgroup.centralizer (F : Set G) ≤ F)
    (hc : ∀ i, i < Group.nilpotencyClass F → ∃ c, linearActionFiltration
      (fun g : K => (rationalUpperCentralAction F i g).toLinearMap - 1) c = ⊥) :
    Group.IsNilpotent K := by
  obtain ⟨c, hc⟩ := exists_relativeCommutatorSeries_eq_bot_of_central_layers F hF K hc
  exact nilpotent_of_relativeCommutatorSeries K F c hc hcent

end PolycyclicRecognition

end

end OAI
