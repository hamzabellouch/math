import OAI.Analysis.LipschitzHilbert.Estimates.UniformPlanarRawBounds
import OAI.Analysis.LipschitzHilbert.Packets.PlanarPacketFamily
import OAI.Analysis.LipschitzHilbert.Estimates.SnappedLattice
import OAI.Analysis.LipschitzHilbert.Fourier.PhysicalPlanarJet

namespace OAI

/-! Actual general planar packets on translated sheared lattices form
the canonical planar packet family. Only the bookkeeping sites are
quantized: the raw waves retain their original centers and profiles. -/

noncomputable section

open MeasureTheory

namespace LipschitzHilbert

/-- Concrete local packet data. These are geometric, seminorm and
dimensionless scale bounds, with no coefficient or concentration premise. -/
structure SourceLatticePacket (N : ℕ) (κ : Type) (ι : Fin N → Type)
    [Fintype κ] [∀ j, Fintype (ι j)] where
  topLength : ℝ
  width : ℝ
  scale : ℝ
  ratioBound : ℝ
  carrierBound : ℝ
  profileBound : ℝ
  order : ℕ
  topLength_pos : 0 < topLength
  width_pos : 0 < width
  profileBound_pos : 0 < profileBound
  order_ge_three : 3 ≤ order
  ratioBound_ge_one : 1 ≤ ratioBound
  scale_bound : |scale / width| ≤ ratioBound
  carrierBound_nonneg : 0 ≤ carrierBound
  originX : Fin N → ℝ
  originZ : Fin N → ℝ
  /-- Physical packet slope minus the reference-line slope. -/
  rowSlope : Fin N → ℝ
  frequency : κ → ℝ
  site : ∀ j, ι j → ℤ × ℤ
  site_injective : ∀ j, Function.Injective (site j)
  profile : ∀ j, ι j → κ → SchwartzMap (ℝ × ℝ) ℂ
  profile_bound : ∀ j u k, planarProfileConstant (profile j u k) (2 * order) ≤ profileBound
  shear_bound : ∀ j, |rowSlope j * (topLength / (2 : ℝ) ^ j.val) / width| ≤ 1
  carrier_bound : ∀ j k,
    |frequency k * rowSlope j * (topLength / (2 : ℝ) ^ j.val)| ≤ carrierBound

namespace SourceLatticePacket

variable {N : ℕ} {κ : Type} {ι : Fin N → Type}
  [Fintype κ] [∀ j, Fintype (ι j)]

variable (P : SourceLatticePacket N κ ι)

def length (j : Fin N) : ℝ := P.topLength / (2 : ℝ) ^ j.val

theorem length_pos (j : Fin N) : 0 < P.length j :=
  div_pos P.topLength_pos (pow_pos (by norm_num) _)

def actualX (j : Fin N) (u : ι j) : ℝ :=
  P.originX j + P.length j * (P.site j u).1

def actualZ (j : Fin N) (u : ι j) : ℝ :=
  P.originZ j + P.rowSlope j * P.length j * (P.site j u).1 + P.width * (P.site j u).2

def snappedSite (j : Fin N) (u : ι j) : ℤ × ℤ :=
  snappedLatticeSite (P.originX j) (P.originZ j) (P.length j) P.width (P.rowSlope j)
    (P.site j u)

theorem snappedSite_injective (j : Fin N) : Function.Injective (P.snappedSite j) :=
  (snappedLatticeSite_injective _ _ _ _ _).comp (P.site_injective j)

def raw (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y : ℝ) : SchwartzMap ℝ ℂ :=
  modulatedPlanarJet (P.profile j u k) (P.actualX j u) (P.actualZ j u)
    (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale y (P.length_pos j).ne' i

/-- The center drift is `theta-t`, whereas the modulation along the
reference line has shear `t-theta`. This identifies every actual raw
jet with the corresponding restriction of the physical planar packet. -/
theorem raw_eq_physical_slice (i : Fin 3) (j : Fin N) (u : ι j) (k : κ)
    (y t : ℝ) :
    P.raw i j u k y = planarSchwartzSlice
      (planarCovariantJet (physicalPlanarPacket (P.profile j u k)
        (P.actualX j u) (P.actualZ j u + t * P.actualX j u)
        (P.length j) P.width (t + P.rowSlope j) (P.frequency k)
        (P.length_pos j).ne' P.width_pos.ne') (P.frequency k) P.scale i) y t := by
  have h := physicalPlanarPacket_jet_slice (P.profile j u k) (P.actualX j u)
    (P.actualZ j u + t * P.actualX j u) (P.length j) P.width
    (t + P.rowSlope j) (P.frequency k) P.scale y t
    (P.length_pos j).ne' P.width_pos.ne' i
  have hc : P.actualZ j u + t * P.actualX j u - t * P.actualX j u = P.actualZ j u := by
    ring
  have hd : t - (t + P.rowSlope j) = -P.rowSlope j := by ring
  simpa only [hc, hd, raw] using h.symm

def amplitude : ℝ :=
  (2 ^ P.order * P.profileBound) * (P.carrierBound + 2) * P.ratioBound ^ 2

def constant : ℝ := P.amplitude * 3 ^ (2 * P.order)

theorem amplitude_pos : 0 < P.amplitude := by
  have hR : 0 < P.ratioBound := lt_of_lt_of_le (by norm_num) P.ratioBound_ge_one
  have hM : 0 < P.carrierBound + 2 := by linarith [P.carrierBound_nonneg]
  exact mul_pos (mul_pos (mul_pos (pow_pos (by norm_num) _) P.profileBound_pos) hM)
    (sq_pos_of_pos hR)

theorem constant_pos : 0 < P.constant :=
  mul_pos P.amplitude_pos (pow_pos (by norm_num) _)

theorem raw_shear_bound (j : Fin N) : |(-P.rowSlope j) * P.length j / P.width| ≤ 1 := by
  simpa only [length, neg_mul, neg_div, abs_neg] using P.shear_bound j

theorem raw_carrier_bound (j : Fin N) (k : κ) :
    |P.frequency k * (-P.rowSlope j) * P.length j| ≤ P.carrierBound := by
  simpa only [length, mul_neg, neg_mul, abs_neg] using P.carrier_bound j k

theorem raw_bound_actual (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.amplitude *
      (lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y) := by
  exact (uniform_planar_raw_bounds (P.profile j u k) P.order P.profileBound
    (P.profile_bound j u k) (P.actualX j u) (P.actualZ j u) (P.length j) P.width
    (-P.rowSlope j) (P.frequency k) P.scale P.ratioBound P.carrierBound
    (P.length_pos j) P.ratioBound_ge_one P.scale_bound P.carrierBound_nonneg
    (P.raw_shear_bound j) (P.raw_carrier_bound j k) i y x).1

theorem raw_derivative_bound_actual (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.amplitude / P.length j) *
      (lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y) := by
  exact (uniform_planar_raw_bounds (P.profile j u k) P.order P.profileBound
    (P.profile_bound j u k) (P.actualX j u) (P.actualZ j u) (P.length j) P.width
    (-P.rowSlope j) (P.frequency k) P.scale P.ratioBound P.carrierBound
    (P.length_pos j) P.ratioBound_ge_one P.scale_bound P.carrierBound_nonneg
    (P.raw_shear_bound j) (P.raw_carrier_bound j k) i y x).2

theorem snapped_envelope (j : Fin N) (u : ι j) (y x : ℝ) :
    lineEnvelope (P.actualX j u) (P.length j) P.order x *
        lineEnvelope (P.actualZ j u) P.width P.order y ≤
      3 ^ (2 * P.order) *
        (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
          lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  have h := snappedLatticeSite_envelope (P.originX j) (P.originZ j) (P.length j)
    P.width (P.rowSlope j) x y (P.length_pos j) P.width_pos (P.site j u) P.order P.order
  have hp : (3 : ℝ) ^ P.order * 3 ^ P.order = 3 ^ (2 * P.order) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [actualX, actualZ, snappedSite, hp] using h

theorem raw_bound (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_bound_actual i j u k y x).trans
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x) P.amplitude_pos.le
  simpa only [constant, mul_assoc] using h

theorem raw_derivative_bound (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖deriv (P.raw i j u k y) x‖ ≤ (P.constant / P.length j) *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) P.order x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width P.order y) := by
  apply (P.raw_derivative_bound_actual i j u k y x).trans
  have h := mul_le_mul_of_nonneg_left (P.snapped_envelope j u y x)
    (div_nonneg P.amplitude_pos.le (P.length_pos j).le)
  convert h using 1
  dsimp [constant]
  ring

theorem raw_bound_three (i : Fin 3) (j : Fin N) (u : ι j) (k : κ) (y x : ℝ) :
    ‖P.raw i j u k y x‖ ≤ P.constant *
      (lineEnvelope (P.length j * (P.snappedSite j u).1) (P.length j) 3 x *
        lineEnvelope (P.width * (P.snappedSite j u).2) P.width 3 y) := by
  apply (P.raw_bound i j u k y x).trans
  apply mul_le_mul_of_nonneg_left _ P.constant_pos.le
  exact mul_le_mul (lineEnvelope_antitone _ _ _ P.order_ge_three)
    (lineEnvelope_antitone _ _ _ P.order_ge_three) (lineEnvelope_nonneg _ _ _ _)
    (lineEnvelope_nonneg _ _ _ _)

/-- Canonical sites with base coordinates zero, carrying the original
raw waves at their actual translated sheared lattice centers. -/
def family : PlanarPacketFamily N κ ι where
  baseX := 0
  baseZ := 0
  topLength := P.topLength
  width := P.width
  constant := P.constant
  topLength_pos := P.topLength_pos
  width_pos := P.width_pos
  constant_pos := P.constant_pos
  site := P.snappedSite
  site_injective := P.snappedSite_injective
  wave := P.raw 0
  wave_measurable := by
    intro j u k
    exact (modulatedPlanarJet_continuous (P.profile j u k) (P.actualX j u) (P.actualZ j u)
      (P.length j) P.width (-P.rowSlope j) (P.frequency k) P.scale
      (P.length_pos j).ne' 0).measurable
  wave_bound := by
    intro j u k y x
    simpa only [zero_add, length] using P.raw_bound_three 0 j u k y x

@[simp] theorem family_length (j : Fin N) : P.family.length j = P.length j := rfl

@[simp] theorem family_wave (j : Fin N) (u : ι j) (k : κ) (y : ℝ) :
    P.family.wave j u k y = P.raw 0 j u k y := rfl

@[simp] theorem family_centerX (j : Fin N) (u : ι j) :
    P.family.centerX j u = P.length j * (P.snappedSite j u).1 := by
  simp only [PlanarPacketFamily.centerX, family_length]
  exact zero_add _

@[simp] theorem family_centerZ (j : Fin N) (u : ι j) :
    P.family.centerZ j u = P.width * (P.snappedSite j u).2 := by
  exact zero_add _

end SourceLatticePacket

end LipschitzHilbert

end

end OAI
