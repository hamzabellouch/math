import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.Model

namespace OAI

/-! Exact finite encodings and continuum promise problems of both main
theorems. Nuclear coordinates and positive charges are binary, electrons are
unary, and the threshold separation is at least one. Energies are the full
spinful antisymmetric weak-H¹ infima, with no finite-orbital restriction. -/

namespace ContinuumCoulomb
open BinaryEncoding

structure BinaryPosition where
  x : BinaryRational
  y : BinaryRational
  z : BinaryRational
  deriving DecidableEq, Repr

def BinaryPosition.value (p : BinaryPosition) : Fin 3 → ℚ := ![p.x.value, p.y.value, p.z.value]

def BinaryPosition.Valid (p : BinaryPosition) : Prop :=
  0 < p.x.denominator ∧ 0 < p.y.denominator ∧ 0 < p.z.denominator

def binaryPositionEquiv : BinaryPosition ≃ (BinaryRational × (BinaryRational × BinaryRational)) where
  toFun p := (p.x, p.y, p.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv p := by cases p; rfl
  right_inv p := by rcases p with ⟨x, y, z⟩; rfl

def binaryPositionCodec : Codec BinaryPosition := BinaryEncoding.equiv
  (pair binaryRationalCodec (pair binaryRationalCodec binaryRationalCodec)) binaryPositionEquiv

structure BinaryCoulomb where
  nuclei : List (BinaryPosition × ℕ)
  electrons : ℕ
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def binaryCoulombEquiv : BinaryCoulomb ≃
    (List (BinaryPosition × ℕ) × (ℕ × (BinaryRational × BinaryRational))) where
  toFun d := (d.nuclei, d.electrons, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨ns, n, a, b⟩; rfl

def binaryCoulombCodec : Codec BinaryCoulomb := BinaryEncoding.equiv
  (pair (BinaryEncoding.list (pair binaryPositionCodec natural))
    (pair unary (pair binaryRationalCodec binaryRationalCodec))) binaryCoulombEquiv

structure BinaryCoulomb.Valid (d : BinaryCoulomb) : Prop where
  nuclei_pos : 0 < d.nuclei.length
  electrons_pos : 0 < d.electrons
  positions : ∀ a : Fin d.nuclei.length, (d.nuclei.get a).1.Valid
  distinct : Function.Injective (fun a : Fin d.nuclei.length => (d.nuclei.get a).1.value)
  charge_pos : ∀ a : Fin d.nuclei.length, 0 < (d.nuclei.get a).2
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : 1 ≤ d.upper.value - d.lower.value

def BinaryCoulomb.toData (d : BinaryCoulomb) (h : d.Valid) : NuclearData where
  nuclei := d.nuclei.length
  nuclei_pos := h.nuclei_pos
  position a := (d.nuclei.get a).1.value
  distinct := h.distinct
  charge a := (d.nuclei.get a).2
  charge_pos := h.charge_pos
  electrons := d.electrons
  electrons_pos := h.electrons_pos

structure UnitCoulomb where
  nuclei : List BinaryPosition
  electrons : ℕ
  lower : BinaryRational
  upper : BinaryRational
  deriving DecidableEq, Repr

def unitCoulombEquiv : UnitCoulomb ≃ (List BinaryPosition × (ℕ × (BinaryRational × BinaryRational))) where
  toFun d := (d.nuclei, d.electrons, d.lower, d.upper)
  invFun d := ⟨d.1, d.2.1, d.2.2.1, d.2.2.2⟩
  left_inv d := by cases d; rfl
  right_inv d := by rcases d with ⟨ns, n, a, b⟩; rfl

def unitCoulombCodec : Codec UnitCoulomb := BinaryEncoding.equiv
  (pair (BinaryEncoding.list binaryPositionCodec)
    (pair unary (pair binaryRationalCodec binaryRationalCodec))) unitCoulombEquiv

structure UnitCoulomb.Valid (d : UnitCoulomb) : Prop where
  nuclei_pos : 0 < d.nuclei.length
  electrons_pos : 0 < d.electrons
  positions : ∀ a : Fin d.nuclei.length, (d.nuclei.get a).Valid
  distinct : Function.Injective (fun a : Fin d.nuclei.length => (d.nuclei.get a).value)
  lower_denominator : 0 < d.lower.denominator
  upper_denominator : 0 < d.upper.denominator
  gap : 1 ≤ d.upper.value - d.lower.value

def UnitCoulomb.toData (d : UnitCoulomb) (h : d.Valid) : UnitNuclearData where
  nuclei := d.nuclei.length
  nuclei_pos := h.nuclei_pos
  position a := (d.nuclei.get a).value
  distinct := h.distinct
  electrons := d.electrons
  electrons_pos := h.electrons_pos

noncomputable section

def binaryCoulombPromise : PromiseProblem BinaryCoulomb where
  yes := {d | ∃ h : d.Valid, groundEnergy (d.toData h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, ((d.upper.value : ℝ) : EReal) ≤ groundEnergy (d.toData h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, hyes⟩ ⟨h', hno⟩
    have hgap : d.lower.value < d.upper.value := by linarith [h.gap]
    have hgap' : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by exact_mod_cast hgap
    exact (not_le_of_gt hgap') (hno.trans hyes)

def unitCoulombPromise : PromiseProblem UnitCoulomb where
  yes := {d | ∃ h : d.Valid, unitGroundEnergy (d.toData h) ≤ ((d.lower.value : ℝ) : EReal)}
  no := {d | ∃ h : d.Valid, ((d.upper.value : ℝ) : EReal) ≤ unitGroundEnergy (d.toData h)}
  disjoint := by
    apply Set.disjoint_left.mpr
    rintro d ⟨h, hyes⟩ ⟨h', hno⟩
    have hgap : d.lower.value < d.upper.value := by linarith [h.gap]
    have hgap' : ((d.lower.value : ℝ) : EReal) < ((d.upper.value : ℝ) : EReal) := by exact_mod_cast hgap
    exact (not_le_of_gt hgap') (hno.trans hyes)

end
end ContinuumCoulomb

end OAI
