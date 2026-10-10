import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HydrogenInput
import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.NuclearPromise

namespace OAI

/-! Fixed one-electron outputs for the decidable one-spin source branch.
The only spectral input is the precisely stated published hydrogen bottom. -/

noncomputable section
namespace ContinuumCoulomb
open MeasureTheory

theorem oneElectron_antisymmetric (w : Coulomb.H1Vector 1) : Coulomb.Antisymmetric w := by
  intro p s
  have hp : p=1 := Subsingleton.elim _ _
  subst p
  filter_upwards [] with x
  have hx : Coulomb.permute (1 : Equiv.Perm (Fin 1)) x=x := by ext i; rfl
  simp [hx]

def atomicData : UnitNuclearData where
  nuclei := 1
  nuclei_pos := by decide
  position := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  electrons := 1
  electrons_pos := by decide

theorem atomic_form (w : FormState 1) : unitCoulombForm atomicData w = hydrogenForm 0 w.val := by
  have ha (y : Position) : Coulomb.attraction atomicData.toNuclearData.toNuclei y =
      Coulomb.coulombKernel y := by
    unfold Coulomb.attraction
    erw [Fin.sum_univ_one]
    have hr : realPosition (0 : Fin 3 → ℚ)=0 := by ext i; simp [realPosition]
    simp only [atomicData,UnitNuclearData.toNuclearData,NuclearData.toNuclei,
      Nat.cast_one,hr,sub_zero,one_mul]
  have hp : Coulomb.pairEnergy w.val=0 := by simp [Coulomb.pairEnergy]
  change Coulomb.kinetic w.val-Coulomb.nuclearEnergy atomicData.toNuclearData.toNuclei w.val+
    Coulomb.pairEnergy w.val = hydrogenForm 0 w.val
  simp only [hp,add_zero,Coulomb.nuclearEnergy,ha,Fin.sum_univ_one,
    hydrogenForm,singlePoleEnergy,sub_zero]

theorem atomic_ground : unitGroundEnergy atomicData = hydrogenEnergy 0 := by
  unfold unitGroundEnergy hydrogenEnergy oneElectronEnergy
  congr 1
  ext e
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨w.val,hw,congrArg (fun t : ℝ => (t:EReal)) (atomic_form w)⟩
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨w,oneElectron_antisymmetric w⟩,hw,
      congrArg (fun t : ℝ => (t:EReal)) (atomic_form ⟨w,oneElectron_antisymmetric w⟩).symm⟩

def atomicOutput (yes : Bool) : UnitCoulomb where
  nuclei := [⟨BinaryRational.ofRat 0,BinaryRational.ofRat 0,BinaryRational.ofRat 0⟩]
  electrons := 1
  lower := BinaryRational.ofRat (if yes then 0 else -2)
  upper := BinaryRational.ofRat (if yes then 1 else -1)

theorem atomicOutput_valid (yes : Bool) : (atomicOutput yes).Valid := by
  refine ⟨by change 0<1; decide,by change 0<1; decide,?_,?_,?_,?_,?_⟩
  · intro i
    change Fin 1 at i
    fin_cases i
    change (0:ℕ)<1 ∧ (0:ℕ)<1 ∧ (0:ℕ)<1
    decide
  · intro i j _
    apply Fin.ext
    have hi : i.val<1 := i.isLt
    have hj : j.val<1 := j.isLt
    omega
  · cases yes <;> decide
  · cases yes <;> decide
  · cases yes <;> norm_num [atomicOutput]

theorem atomicOutput_data (yes : Bool) (h : (atomicOutput yes).Valid) :
    (atomicOutput yes).toData h = atomicData := by
  cases yes <;> unfold UnitCoulomb.toData atomicOutput atomicData <;>
    congr 1 <;> funext i <;> fin_cases i <;>
    ext j <;> fin_cases j <;> norm_num [atomicOutput,UnitCoulomb.toData,atomicData,BinaryPosition.value]

theorem atomicOutput_yes (hh : PublishedHydrogenBottom) : atomicOutput true ∈ unitCoulombPromise.yes := by
  refine ⟨atomicOutput_valid true,?_⟩
  rw [atomicOutput_data,atomic_ground,hh]
  simp only [atomicOutput,BinaryRational.value_ofRat,ite_true,Rat.cast_zero]
  change ((-1/2:ℝ):EReal) ≤ ((0:ℝ):EReal)
  exact EReal.coe_le_coe (by norm_num)

theorem atomicOutput_no (hh : PublishedHydrogenBottom) : atomicOutput false ∈ unitCoulombPromise.no := by
  refine ⟨atomicOutput_valid false,?_⟩
  rw [atomicOutput_data,atomic_ground,hh]
  simp only [atomicOutput,BinaryRational.value_ofRat,Bool.false_eq_true,ite_false,Rat.cast_neg,Rat.cast_one]
  change ((-1:ℝ):EReal) ≤ ((-1/2:ℝ):EReal)
  exact EReal.coe_le_coe (by norm_num)

end ContinuumCoulomb

end

end OAI
