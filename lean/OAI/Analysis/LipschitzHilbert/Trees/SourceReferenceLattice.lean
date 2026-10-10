import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeSpectrum

namespace OAI

/-! Change the reference direction of an actual translated source
lattice. Profiles, sites and physical packets are preserved exactly.
The reference-cone and width hypotheses imply the new shear and carrier
bounds; the absolute raw envelope is independent of the carrier bound. -/

noncomputable section
open scoped FourierTransform
namespace LipschitzHilbert.SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def changeReference (delta M : ℝ) (hM : 0 ≤ M)
    (hshear : ∀ j, |(P.rowSlope j+delta)*P.length j/P.width| ≤ 1)
    (hcarrier : ∀ j k, |P.frequency k*(P.rowSlope j+delta)*P.length j| ≤ M) :
    SourceLatticePacket N κ ι :=
  { P with
    carrierBound := M
    carrierBound_nonneg := hM
    originZ := fun j => P.originZ j+delta*P.originX j
    rowSlope := fun j => P.rowSlope j+delta
    shear_bound := hshear
    carrier_bound := hcarrier }

variable (delta M : ℝ) (hM : 0 ≤ M)
  (hshear : ∀ j, |(P.rowSlope j+delta)*P.length j/P.width| ≤ 1)
  (hcarrier : ∀ j k, |P.frequency k*(P.rowSlope j+delta)*P.length j| ≤ M)

@[simp] theorem changeReference_length (j : Fin N) :
    (P.changeReference delta M hM hshear hcarrier).length j = P.length j := rfl

@[simp] theorem changeReference_actualX (j : Fin N) (u : ι j) :
    (P.changeReference delta M hM hshear hcarrier).actualX j u = P.actualX j u := rfl

theorem changeReference_actualZ (j : Fin N) (u : ι j) :
    (P.changeReference delta M hM hshear hcarrier).actualZ j u =
      P.actualZ j u+delta*P.actualX j u := by
  dsimp [actualZ,actualX,changeReference,length]
  ring

/-- The new reference slope is `t`; the old one is `t+delta`.
There is no change to the original two-dimensional packet. -/
theorem changeReference_physicalPacket (t : ℝ) (j : Fin N) (u : ι j) (k : κ) :
    (P.changeReference delta M hM hshear hcarrier).physicalPacket t j u k =
      P.physicalPacket (t+delta) j u k := by
  ext z
  simp only [physicalPacket,physicalPlanarPacket_apply]
  rw [P.changeReference_actualX delta M hM hshear hcarrier,
    P.changeReference_actualZ delta M hM hshear hcarrier]
  have hc : P.actualZ j u+delta*P.actualX j u+t*P.actualX j u =
      P.actualZ j u+(t+delta)*P.actualX j u := by ring
  have hs : t+(P.rowSlope j+delta) = (t+delta)+P.rowSlope j := by ring
  change Complex.exp (((P.frequency k *
    ((z.2-(P.actualZ j u+delta*P.actualX j u+t*P.actualX j u))-
      (t+(P.rowSlope j+delta))*(z.1-P.actualX j u))):ℝ)*Complex.I) *
    P.profile j u k ((z.1-P.actualX j u)/P.length j,
      ((z.2-(P.actualZ j u+delta*P.actualX j u+t*P.actualX j u))-
      (t+(P.rowSlope j+delta))*(z.1-P.actualX j u))/P.width) = _
  rw [hc,hs]

theorem changeReference_raw_slice (t : ℝ) (i : Fin 3) (j : Fin N) (u : ι j)
    (k : κ) (y : ℝ) :
    (P.changeReference delta M hM hshear hcarrier).raw i j u k y =
      planarSchwartzSlice (planarCovariantJet (P.physicalPacket (t+delta) j u k)
        (P.frequency k) P.scale i) y t := by
  rw [(P.changeReference delta M hM hshear hcarrier).raw_eq_physical_slice i j u k y t]
  change planarSchwartzSlice (planarCovariantJet
    ((P.changeReference delta M hM hshear hcarrier).physicalPacket t j u k)
    (P.frequency k) P.scale i) y t = _
  rw [P.changeReference_physicalPacket delta M hM hshear hcarrier]

/-- The cone needed for reference-line packets implies both analytic
dimensionless bounds, using only the original width and frequency scale. -/
theorem reference_cone_bounds {delta H F w : ℝ} (hw : 0 < w)
    (_hH : 0 ≤ H) (hF : 0 ≤ F) (hwide : H*w ≤ P.width)
    (hcone : ∀ j, |P.rowSlope j+delta| ≤ H*w/P.length j)
    (hfrequency : ∀ k, |P.frequency k| ≤ F/w) :
    (∀ j, |(P.rowSlope j+delta)*P.length j/P.width| ≤ 1) ∧
      ∀ j k, |P.frequency k*(P.rowSlope j+delta)*P.length j| ≤ F*H := by
  have hr (j : Fin N) : |P.rowSlope j+delta| * P.length j ≤ H*w :=
    (le_div_iff₀ (P.length_pos j)).mp (hcone j)
  constructor
  · intro j
    rw [abs_div,abs_mul,abs_of_pos (P.length_pos j),abs_of_pos P.width_pos]
    exact (div_le_one P.width_pos).mpr ((hr j).trans hwide)
  · intro j k
    rw [abs_mul,abs_mul,abs_of_pos (P.length_pos j),mul_assoc]
    calc
      _ ≤ (F/w)*(H*w) := mul_le_mul (hfrequency k) (hr j)
        (mul_nonneg (abs_nonneg _) (P.length_pos j).le) (div_nonneg hF hw.le)
      _ = F*H := by field_simp

/-- Unlike derivative bounds, the raw absolute envelope has no carrier
factor, even when the reference cone is much wider than a main annulus. -/
theorem raw_absolute_envelope (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤
      ((2^P.order*P.profileBound)*P.ratioBound^2)*
        (lineEnvelope (P.actualX j u) (P.length j) P.order x*
          lineEnvelope (P.actualZ j u) P.width P.order y) := by
  let C := P.ratioBound^2*P.profileBound
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) P.profileBound_pos.le
  have hprofile : ∀ z, ‖planarProfileJet (P.profile j u k) (P.scale/P.width) i z‖ ≤ C*
      (lineEnvelope 0 1 (2*P.order) z.1*lineEnvelope 0 1 (2*P.order) z.2) := by
    intro z
    exact (planar_profile_envelope (P.profile j u k) (2*P.order) (P.scale/P.width)
      P.ratioBound P.ratioBound_ge_one P.scale_bound i z).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (P.profile_bound j u k) (sq_nonneg _))
        (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)))
  have h := modulatedPlanarSlice_envelope (planarProfileJet (P.profile j u k) (P.scale/P.width) i)
    (P.actualX j u) (P.actualZ j u) (P.length j) P.width (-P.rowSlope j) (P.frequency k)
    y C (P.length_pos j).ne' P.order hC (P.raw_shear_bound j) hprofile x
  convert h using 1 <;> simp only [raw,modulatedPlanarJet,div_eq_mul_inv,C]
  ring

/-- Fourier annuli on the new reference line follow from the spectrum
of the unchanged original physical packet, including all three jets. -/
theorem changeReference_fourier_cutoffs (t w cStar cEta CEta cb Cb : ℝ)
    (hw : 0 < w) (hcEta : 0 < cEta) (hcb : 0 ≤ cb) (hCb : 0 ≤ Cb)
    (hspectrum : ∀ j u k ξ η, planarAngularFourier (P.physicalPacket (t+delta) j u k) (ξ,η) ≠ 0 →
      |ξ+((t+delta)+P.rowSlope j)*η| ≤ cStar/P.length j ∧
        cEta ≤ w*η ∧ w*η ≤ CEta)
    (hselector : ∀ j (_u : ι j), cb*w/P.length j ≤ |P.rowSlope j+delta| ∧
      |P.rowSlope j+delta| ≤ Cb*w/P.length j)
    (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    (∀ ξ, |ξ| < (((cEta*cb-cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val →
      𝓕 ((P.changeReference delta M hM hshear hcarrier).raw i j u k y) ξ = 0) ∧
    (∀ ξ, (((CEta*Cb+cStar)/(2*Real.pi))/P.topLength)*(2:ℝ)^j.val < |ξ| →
      𝓕 ((P.changeReference delta M hM hshear hcarrier).raw i j u k y) ξ = 0) := by
  apply (P.changeReference delta M hM hshear hcarrier).raw_fourier_cutoffs t w cStar cEta CEta cb Cb
    hw hcEta hcb hCb _ hselector i j u k y
  intro j u k ξ η hξ
  rw [P.changeReference_physicalPacket delta M hM hshear hcarrier] at hξ
  have h := hspectrum j u k ξ η hξ
  have hs : t+(P.rowSlope j+delta) = (t+delta)+P.rowSlope j := by ring
  simpa only [changeReference,changeReference_length,length,hs] using h

end LipschitzHilbert.SourceLatticePacket

end

end OAI
