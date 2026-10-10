import OAI.NumberTheory.Ostmann.Characters.FrequencyExposureLeaves
import OAI.NumberTheory.Ostmann.Characters.TemplateFrequencyConstraint

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
open BinaryExposure FrequencyExposure
attribute [local instance] Classical.propDecidable

abbrev KnownStates (k R:ℕ) := (j:ℕ)→(schedule k j).Slot→ZMod (R^(j+2))
abbrev PairedKnownStates (k R:ℕ) := KnownStates k R×KnownStates k R

theorem frequency_dvd_precision (R:ℕ) (j:ℕ) {s:ℤ} (hs:s.natAbs∣R) : s.natAbs∣R^(j+2) :=
  dvd_trans hs (dvd_pow_self R (by omega))

def ambientData (K R:ℕ) (d:Data R) : Data (R^(K+2)) where
  s:=d.s
  s':=d.s'
  v:=d.v
  w:=d.w
  v':=d.v'
  w':=d.w'
  divides:=frequency_dvd_precision R K d.divides
  divides':=frequency_dvd_precision R K d.divides'

def knownCoefficient (k R j:ℕ) (b:Bool) (s:ℤ) (hs:s.natAbs∣R) (C:KnownStates k R) :
    (ZMod s.natAbs)ˣ :=
  unitConvention (ZMod.castHom (frequency_dvd_precision R (j+1) hs) (ZMod s.natAbs)
    (blockProduct k j b (C (j+1))))

def exposureConstraint (k K R:ℕ) (d:List Bool→Data R)
    (j:ℕ) (h:List Bool×PairedKnownStates k R) (t x:(ZMod (R^(K+2)))ˣ) : Prop :=
  rawSplitConstraint (d h.1).s.natAbs (d h.1).v (d h.1).w
    (knownCoefficient k R j true (d h.1).s (d h.1).divides h.2.1)
    (knownCoefficient k R j false (d h.1).s (d h.1).divides h.2.1)
    (ZMod.unitsMap (ambientData K R (d h.1)).divides t)
    (ZMod.unitsMap (ambientData K R (d h.1)).divides x) ∧
  rawSplitConstraint (d h.1).s'.natAbs (d h.1).v' (d h.1).w'
    (knownCoefficient k R j true (d h.1).s' (d h.1).divides' h.2.2)
    (knownCoefficient k R j false (d h.1).s' (d h.1).divides' h.2.2)
    (ZMod.unitsMap (ambientData K R (d h.1)).divides' t)
    (ZMod.unitsMap (ambientData K R (d h.1)).divides' x)

def exposureStep (k K R:ℕ) (d:List Bool→Data R) (b:Bool) (j:ℕ)
    (h:List Bool×PairedKnownStates k R) (t x:(ZMod (R^(K+2)))ˣ) :
    List Bool×PairedKnownStates k R :=
  (b::h.1,if hj:j<K then
    let red := ZMod.castHom (pow_dvd_pow R (by omega : j+3≤K+2)) (ZMod (R^(j+3)))
    let XL := red (x:ZMod (R^(K+2)))
    let XR := red ((x⁻¹*t:(ZMod (R^(K+2)))ˣ):ZMod (R^(K+2)))
    (Function.update h.2.1 j
      (knownChild (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega)) k j (!b)
        (d h.1).s (d h.1).v (d h.1).w (h.2.1 (j+1)) XL XR),
     Function.update h.2.2 j
      (knownChild (R^(j+3)) (R^(j+2)) (pow_dvd_pow R (by omega)) k j (!b)
        (d h.1).s' (d h.1).v' (d h.1).w' (h.2.2 (j+1)) XL XR))
  else h.2)

theorem actual_residue_leaf_count (ε:ℝ) (hε:0<ε) :
    ∃ C:NNReal, 0<C ∧ ∀ k K R:ℕ, ∀ [NeZero R], ∀ d:List Bool→Data R,
      ∀ j p (h:PairedKnownStates k R),
      (Nat.card {z:BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ j //
        leafAdmissible (exposureConstraint k K R d)
          (exposureStep k K R d false) (exposureStep k K R d true) j (p,h) z}:ℝ)/
        Nat.card (BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ j) ≤
      ((budget C ε (fun p=>ambientData K R (d p)) j p).value:ℝ) := by
  obtain ⟨C,hC,hlocal⟩ := paired_frequency_split_probability_le_rpow ε hε
  let C' : NNReal := ⟨C,hC.le⟩
  refine ⟨C',hC,?_⟩
  intro k K R _ d j p h
  apply leaf_count_le_tree
  have hc : ∀j p h t,
      Controlled (exposureConstraint k K R d)
        (exposureStep k K R d false) (exposureStep k K R d true) j (p,h) t
        (budget C' ε (fun p=>ambientData K R (d p)) j p) := by
    intro j
    induction j with
    | zero => intros; trivial
    | succ j ih =>
      intro p h t
      constructor
      · exact hlocal (R^(K+2)) (d p).s (d p).s' (d p).v (d p).w (d p).v' (d p).w'
          (ambientData K R (d p)).divides (ambientData K R (d p)).divides'
          (knownCoefficient k R j true (d p).s (d p).divides h.1)
          (knownCoefficient k R j false (d p).s (d p).divides h.1)
          (knownCoefficient k R j true (d p).s' (d p).divides' h.2)
          (knownCoefficient k R j false (d p).s' (d p).divides' h.2) t
      · intro x
        exact ⟨ih _ _ _,ih _ _ _⟩
  intro t
  exact hc j p h t

end Ostmann.Characters.Template

end

end OAI
