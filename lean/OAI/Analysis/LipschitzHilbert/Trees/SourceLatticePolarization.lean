import OAI.Analysis.LipschitzHilbert.Packets.SourceLatticePacket
import OAI.Analysis.LipschitzHilbert.Estimates.PlanarProfilePolarization

namespace OAI

/-! Unit-phase profile combinations construct genuine source packet
families on the same lattice with a factor-two change in the raw constant. -/

noncomputable section
namespace LipschitzHilbert

theorem planarProfileJet_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (ratio : ℝ) (i : Fin 3) :
    planarProfileJet (f + c • g) ratio i =
      planarProfileJet f ratio i + c • planarProfileJet g ratio i := by
  simp only [planarProfileJet_eq, planarVerticalJet_add, planarVerticalJet_smul,
    smul_add, smul_smul, mul_comm]

theorem modulatedPlanarJet_add_smul (f g : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    modulatedPlanarJet (f + c • g) a cy l W delta frequency scale y hl i =
      modulatedPlanarJet f a cy l W delta frequency scale y hl i +
        c • modulatedPlanarJet g a cy l W delta frequency scale y hl i := by
  ext x
  simp only [modulatedPlanarJet, modulatedPlanarSlice_apply, planarProfileJet_add_smul,
    add_apply, smul_apply, smul_eq_mul]
  ring

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (alt : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ)
  (hAlt : ∀ j u k, planarProfileConstant (alt j u k) (2 * P.order) ≤ P.profileBound)

/-- Change the profiles, retaining every site, center, carrier and scale. -/
def withProfile : SourceLatticePacket N κ ι :=
  { P with profile := alt, profile_bound := hAlt }

/-- A polarization family retains all geometry and twice the profile bound. -/
def polarize (c : ℂ) (hc : ‖c‖ = 1) : SourceLatticePacket N κ ι :=
  { P with
    profileBound := 2 * P.profileBound
    profileBound_pos := mul_pos (by norm_num) P.profileBound_pos
    profile := fun j u k => P.profile j u k + c • alt j u k
    profile_bound := fun j u k => planarProfileConstant_polarization_bound
      (P.profile j u k) (alt j u k) c hc (2 * P.order) P.profileBound
      (P.profile_bound j u k) (hAlt j u k) }

@[simp] theorem withProfile_length (j : Fin N) :
    (P.withProfile alt hAlt).length j = P.length j := rfl

@[simp] theorem withProfile_actualX (j : Fin N) (u : ι j) :
    (P.withProfile alt hAlt).actualX j u = P.actualX j u := rfl

@[simp] theorem withProfile_actualZ (j : Fin N) (u : ι j) :
    (P.withProfile alt hAlt).actualZ j u = P.actualZ j u := rfl

@[simp] theorem withProfile_constant : (P.withProfile alt hAlt).constant = P.constant := rfl

@[simp] theorem polarize_length (c : ℂ) (hc : ‖c‖ = 1) (j : Fin N) :
    (P.polarize alt hAlt c hc).length j = P.length j := rfl

@[simp] theorem polarize_actualX (c : ℂ) (hc : ‖c‖ = 1) (j : Fin N) (u : ι j) :
    (P.polarize alt hAlt c hc).actualX j u = P.actualX j u := rfl

@[simp] theorem polarize_actualZ (c : ℂ) (hc : ‖c‖ = 1) (j : Fin N) (u : ι j) :
    (P.polarize alt hAlt c hc).actualZ j u = P.actualZ j u := rfl

@[simp] theorem polarize_snappedSite (c : ℂ) (hc : ‖c‖ = 1) (j : Fin N) (u : ι j) :
    (P.polarize alt hAlt c hc).snappedSite j u = P.snappedSite j u := rfl

/-- Every raw covariant jet polarizes on the original geometry. -/
theorem polarize_raw (c : ℂ) (hc : ‖c‖ = 1)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (P.polarize alt hAlt c hc).raw i j u k y =
      P.raw i j u k y + c • (P.withProfile alt hAlt).raw i j u k y := by
  change modulatedPlanarJet (P.profile j u k + c • alt j u k)
      (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j)
      (P.frequency k) P.scale y (P.length_pos j).ne' i = _
  exact modulatedPlanarJet_add_smul (P.profile j u k) (alt j u k) c
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j)
    (P.frequency k) P.scale y (P.length_pos j).ne' i

theorem polarize_constant (c : ℂ) (hc : ‖c‖ = 1) :
    (P.polarize alt hAlt c hc).constant = 2 * P.constant := by
  dsimp [constant, amplitude, polarize]
  ring

theorem polarize_family_wave (c : ℂ) (hc : ‖c‖ = 1)
    (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (P.polarize alt hAlt c hc).family.wave j u k y =
      P.family.wave j u k y + c • (P.withProfile alt hAlt).family.wave j u k y :=
  P.polarize_raw alt hAlt c hc 0 j u k y

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
