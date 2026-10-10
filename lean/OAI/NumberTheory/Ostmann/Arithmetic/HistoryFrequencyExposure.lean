import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyContext

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Characters FrequencyExposure BinaryExposure

structure FixedFactors where
  plus : ℕ
  minus : ℕ
  compensation : ℕ

abbrev PairedContext (R : ℕ) := ℕ × (KnownGiants R × KnownGiants R)

def exposureCoefficients (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (p : List Bool) :
    Coefficients (PairedContext R) (Template.ambientData K R (d p)) where
  A h _ := knownCoefficient R h.1 (d p).s (d p).divides (f p).1.plus (h.2.1 h.1).1
  B h _ := knownCoefficient R h.1 (d p).s (d p).divides (f p).1.minus (h.2.1 h.1).2
  A' h _ := knownCoefficient R h.1 (d p).s' (d p).divides' (f p).2.plus (h.2.2 h.1).1
  B' h _ := knownCoefficient R h.1 (d p).s' (d p).divides' (f p).2.minus (h.2.2 h.1).2

def exposureStep (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) (b : Bool)
    (p : List Bool) (h : PairedContext R) (t x : (ZMod (R^(K+2)))ˣ) : PairedContext R :=
  let j := h.1-1
  (j,if hj:j<K then
    let red := ZMod.castHom (pow_dvd_pow R (by omega : j+3≤K+2)) (ZMod (R^(j+3)))
    let XL := red (x:ZMod (R^(K+2)))
    let XR := red ((x⁻¹*t:(ZMod (R^(K+2)))ˣ):ZMod (R^(K+2)))
    (childGiants R j (d p).s (d p).v (d p).w
      (f p).1.plus (f p).1.minus (f p).1.compensation h.2.1 XL XR b,
     childGiants R j (d p).s' (d p).v' (d p).w'
      (f p).2.plus (f p).2.minus (f p).2.compensation h.2.2 XL XR b)
   else h.2)

def exposureConstraint (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) :=
  constraint (fun p => Template.ambientData K R (d p)) (exposureCoefficients K R d f)

theorem exposure_leaf_count (ε : ℝ) (hε : 0<ε) :
    ∃ C:NNReal,0<C ∧ ∀ K R:ℕ,∀[NeZero R],∀d:List Bool→Data R,
      ∀f:List Bool→FixedFactors×FixedFactors,∀l p (h:PairedContext R),
      (Nat.card {z:BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l //
        leafAdmissible (exposureConstraint K R d f)
          (update false (exposureStep K R d f false))
          (update true (exposureStep K R d f true)) l (p,h) z}:ℝ)/
        Nat.card (BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l) ≤
      ((budget C ε (fun p=>Template.ambientData K R (d p)) l p).value:ℝ) := by
  obtain ⟨C,hC,hcount⟩ := paired_frequency_leaf_count ε hε
  refine ⟨C,hC,?_⟩
  intro K R _ d f l p h
  exact hcount (R^(K+2)) (PairedContext R) (fun p=>Template.ambientData K R (d p))
    (exposureCoefficients K R d f) (exposureStep K R d f false)
    (exposureStep K R d f true) l p h

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
