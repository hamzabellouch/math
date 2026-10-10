import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticePolarizationSpectrum

namespace OAI

/-! Frozen selector values multiply the original Schwartz profiles.
They preserve the common seminorm bound, geometry and physical spectrum;
no new packet or concentration assumption is introduced. -/

noncomputable section
namespace LipschitzHilbert

theorem planarEnvelopeConstant_smul_le (f : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    planarEnvelopeConstant (c • f) n ≤ planarEnvelopeConstant f n := by
  let W := SchwartzMap.smulLeftCLM ℂ (fun z : ℝ × ℝ => (planarPolynomialWeight n z : ℂ))
  let p := SchwartzMap.seminorm ℂ (E := ℝ × ℝ) (F := ℂ) 0 0
  change p (W (c • f)) + 1 ≤ p (W f) + 1
  rw [map_smul, map_smul_eq_mul]
  have h := mul_le_of_le_one_left (apply_nonneg p (W f)) hc
  linarith

theorem planarProfileConstant_smul_le (f : SchwartzMap (ℝ × ℝ) ℂ)
    (c : ℂ) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    planarProfileConstant (c • f) n ≤ planarProfileConstant f n := by
  simp only [planarProfileConstant, planarVerticalJet_smul,
    planarHorizontalDerivative_smul, planarVerticalDerivative_smul]
  apply Finset.sum_le_sum
  intro i _
  exact add_le_add (add_le_add
    (planarEnvelopeConstant_smul_le _ c hc n)
    (planarEnvelopeConstant_smul_le _ c hc n))
    (planarEnvelopeConstant_smul_le _ c hc n)

theorem modulatedPlanarJet_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a cy l W delta frequency scale y : ℝ) (hl : l ≠ 0) (i : Fin 3) :
    modulatedPlanarJet (c • f) a cy l W delta frequency scale y hl i =
      c • modulatedPlanarJet f a cy l W delta frequency scale y hl i := by
  ext x
  simp only [modulatedPlanarJet,modulatedPlanarSlice_apply,planarProfileJet_eq,
    planarVerticalJet_smul,smul_smul,smul_apply,smul_eq_mul]
  ring

theorem physicalPlanarPacket_smul (f : SchwartzMap (ℝ × ℝ) ℂ) (c : ℂ)
    (a b l W theta frequency : ℝ) (hl : l ≠ 0) (hW : W ≠ 0) :
    physicalPlanarPacket (c • f) a b l W theta frequency hl hW =
      c • physicalPlanarPacket f a b l W theta frequency hl hW := by
  ext z
  simp only [physicalPlanarPacket_apply,smul_apply,smul_eq_mul]
  ring

namespace SourceLatticePacket
variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]
variable (P : SourceLatticePacket N κ ι)
  (c : ∀ j, ι j → κ → ℂ) (hc : ∀ j u k, ‖c j u k‖ ≤ 1)

def frozenProfile : SourceLatticePacket N κ ι :=
  { P with
    profile := fun j u k => c j u k • P.profile j u k
    profile_bound := fun j u k =>
      (planarProfileConstant_smul_le _ _ (hc j u k) _).trans (P.profile_bound j u k) }

@[simp] theorem frozenProfile_constant : (P.frozenProfile c hc).constant = P.constant := rfl

@[simp] theorem frozenProfile_raw (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (P.frozenProfile c hc).raw i j u k y = c j u k • P.raw i j u k y := by
  exact modulatedPlanarJet_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j)
    (P.frequency k) P.scale y (P.length_pos j).ne' i

@[simp] theorem frozenProfile_physicalPacket (t : ℝ) (j : Fin N) (u : ι j) (k : κ) :
    (P.frozenProfile c hc).physicalPacket t j u k = c j u k • P.physicalPacket t j u k := by
  exact physicalPlanarPacket_smul (P.profile j u k) (c j u k)
    (P.actualX j u) (P.actualZ j u+t*P.actualX j u) (P.length j) P.width
    (t+P.rowSlope j) (P.frequency k) (P.length_pos j).ne' P.width_pos.ne'

theorem frozenProfile_physicalFourier (t : ℝ) (j : Fin N) (u : ι j) (k : κ) (xi eta : ℝ) :
    planarAngularFourier ((P.frozenProfile c hc).physicalPacket t j u k) (xi,eta) =
      c j u k * planarAngularFourier (P.physicalPacket t j u k) (xi,eta) := by
  rw [P.frozenProfile_physicalPacket]
  exact planarFourier_smul _ _ _

theorem frozenProfile_spectrum (t w cStar cEta CEta : ℝ)
    (h : ∀ j u k xi eta, planarAngularFourier (P.physicalPacket t j u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta) :
    ∀ j u k xi eta, planarAngularFourier ((P.frozenProfile c hc).physicalPacket t j u k) (xi,eta) ≠ 0 →
      |xi+(t+P.rowSlope j)*eta| ≤ cStar/P.length j ∧ cEta ≤ w*eta ∧ w*eta ≤ CEta := by
  intro j u k xi eta hn
  apply h j u k xi eta
  intro hz
  apply hn
  rw [P.frozenProfile_physicalFourier, hz, mul_zero]

end SourceLatticePacket
end LipschitzHilbert

end

end OAI
