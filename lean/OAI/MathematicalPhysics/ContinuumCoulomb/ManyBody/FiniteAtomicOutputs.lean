import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.AtomicOutputs

namespace OAI

/-! Fixed YES and NO instances need only finiteness of the atomic energy.
No hydrogen spectral formula is needed for this branch of the reduction. -/

noncomputable section
namespace ContinuumCoulomb

/-- A fixed one-electron unit nucleus with adjacent integer thresholds. -/
def atomicThresholdOutput (z : ℤ) : UnitCoulomb where
  nuclei := [⟨BinaryRational.ofRat 0,BinaryRational.ofRat 0,BinaryRational.ofRat 0⟩]
  electrons := 1
  lower := BinaryRational.ofRat z
  upper := BinaryRational.ofRat (z+1)

theorem atomicThresholdOutput_valid (z : ℤ) : (atomicThresholdOutput z).Valid := by
  refine ⟨by change 0<1; decide,by change 0<1; decide,?_,?_,?_,?_,?_⟩
  · intro i
    change Fin 1 at i
    fin_cases i
    change (0:ℕ)<1 ∧ (0:ℕ)<1 ∧ (0:ℕ)<1
    decide
  · intro i j _
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    change i.val<1 at hi
    change j.val<1 at hj
    omega
  · exact Rat.den_pos _
  · exact Rat.den_pos _
  · simp only [atomicThresholdOutput,BinaryRational.value_ofRat]
    norm_num

theorem atomicThresholdOutput_data (z : ℤ) (h : (atomicThresholdOutput z).Valid) :
    (atomicThresholdOutput z).toData h = atomicData := by
  unfold UnitCoulomb.toData atomicThresholdOutput atomicData
  congr 1
  funext i
  fin_cases i
  ext j
  fin_cases j <;> norm_num [BinaryPosition.value]

theorem exists_atomic_yes_no : ∃ y z : UnitCoulomb,
    y ∈ unitCoulombPromise.yes ∧ z ∈ unitCoulombPromise.no := by
  let E := (hydrogenEnergy 0).toReal
  have hE : (E : EReal)=hydrogenEnergy 0 :=
    EReal.coe_toReal (hydrogenEnergy_finite 0).1 (hydrogenEnergy_finite 0).2
  refine ⟨atomicThresholdOutput ⌈E⌉,atomicThresholdOutput (⌊E⌋-1),?_,?_⟩
  · refine ⟨atomicThresholdOutput_valid _,?_⟩
    rw [atomicThresholdOutput_data,atomic_ground,← hE]
    simpa only [atomicThresholdOutput,BinaryRational.value_ofRat,Rat.cast_intCast] using
      EReal.coe_le_coe (Int.le_ceil E)
  · refine ⟨atomicThresholdOutput_valid _,?_⟩
    rw [atomicThresholdOutput_data,atomic_ground,← hE]
    have hfloor : (⌊E⌋:ℝ)-1+1 ≤ E := by linarith [Int.floor_le E]
    simpa only [atomicThresholdOutput,BinaryRational.value_ofRat,Rat.cast_intCast,
      Rat.cast_add,Rat.cast_sub,Rat.cast_one,Int.cast_sub,Int.cast_one] using EReal.coe_le_coe hfloor

end ContinuumCoulomb

end

end OAI
