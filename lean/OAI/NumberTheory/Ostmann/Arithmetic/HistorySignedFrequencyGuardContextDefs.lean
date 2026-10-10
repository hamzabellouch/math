import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyLeaves
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryFrequencyRealizationMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyGuardContextBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryFrequencyResidues
open Construction Characters FrequencyExposure BinaryExposure

def knownPairFrequencyUnits (K R : ℕ) (d : List Bool → Data R)
    (f : List Bool → FixedFactors × FixedFactors) :
    {l : ℕ} → History l → History l → List Bool → PairedContext R →
      BinaryHaar.Leaves (ZMod (R^(K+2)))ˣ l → Prop
  | _,h@(.leaf _),h'@(.leaf _),_,c,_ =>
    knownRootFrequencyUnits R c.1 h.frequencies c.2.1 ∧
      knownRootFrequencyUnits R c.1 h'.frequencies c.2.2
  | _,h@(.node _ _ _ _ _ left right),h'@(.node _ _ _ _ _ left' right'),path,c,z =>
    knownRootFrequencyUnits R c.1 h.frequencies c.2.1 ∧
      knownRootFrequencyUnits R c.1 h'.frequencies c.2.2 ∧
      knownPairFrequencyUnits K R d f left left' (false::path)
        (exposureStep K R d f false path c
          (BinaryHaar.product z.1*BinaryHaar.product z.2) (BinaryHaar.product z.1)) z.1 ∧
      knownPairFrequencyUnits K R d f right right' (true::path)
        (exposureStep K R d f true path c
          (BinaryHaar.product z.1*BinaryHaar.product z.2) (BinaryHaar.product z.1)) z.2

def initialResidueGiants (K R : ℕ)
    (z : ZMod (R^(K+2)) × ZMod (R^(K+2))) : KnownGiants R := fun j=>
  if hj:j≤K then
    let red := ZMod.castHom (pow_dvd_pow R (by omega : j+2≤K+2)) (ZMod (R^(j+2)))
    (red z.1,red z.2)
  else (0,0)

theorem initialResidueGiants_matches (K R j : ℕ) (hj : j≤K) (Xp Xm : ℤ) :
    SignedGiantsMatch R j (initialResidueGiants K R (Xp,Xm)) Xp Xm := by
  simp only [SignedGiantsMatch,initialResidueGiants,dite_eq_left hj,map_intCast]
  exact ⟨trivial,trivial⟩

def pairedFiniteFrequencyUnits (K : ℕ) {l : ℕ} (h h' : History l)
    (z : ZMod ((pairedFrequencyProduct h h')^(K+2)) ×
      ZMod ((pairedFrequencyProduct h h')^(K+2))) : Prop :=
  knownPairFrequencyUnits K (pairedFrequencyProduct h h') (frequencySchedule h h')
    (fixedFactorSchedule h h') h h' []
    (l,initialResidueGiants K (pairedFrequencyProduct h h') z,
      initialResidueGiants K (pairedFrequencyProduct h h') z)
    (frequencyLeaves ((pairedFrequencyProduct h h')^(K+2)) h)

end Ostmann.Arithmetic.HistoryFrequencyResidues

end

end OAI
