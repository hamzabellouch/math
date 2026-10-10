import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PrefactorSourceContactProgram

namespace OAI

/-! The prefactor-aware program retains the exact final graph enumeration,
and calibrates its original weights at the physical unit-charge scale. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

def weights (a : ℚ) (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    GlobalEdge (SourceMetadataProgram.geometricSource s d hd) → ℚ :=
  fun e => PrefactorCalibration.adjustedWeight a (SourceContactProgram.weights s d hd e)

theorem electron_count (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    (SourcePositiveProgram.output s d).vertices =
      Fintype.card (GlobalSite (SourceMetadataProgram.geometricSource s d hd)) := by
  rw [SourcePositiveProgram.vertices_eq s d hd]
  simp only [GlobalSite,Fintype.card_fin]
  rfl

theorem electron_count_positive (s : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    0 < (SourcePositiveProgram.output s d).vertices := by
  rw [electron_count s d hd,globalSite_card]
  have hp := (SourceMetadataProgram.geometricSource s d hd).vertices_pos
  omega

theorem input_eq_graphInput (a : ℚ) (C s p h : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    input a C s p h d = CalibratedContactProgram.graphInput
      (SourceMetadataProgram.geometricSource s d hd)
      (CalibrationMesh.base (SourceContactProgram.size d))
      (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
      (SourceContactProgram.size d ^ h) (weights a s d hd) := by
  unfold input CalibratedContactProgram.graphInput
  rw [SourceContactProgram.coordinates_eq s d hd,SourceContactProgram.signedBonds_eq s d hd,
    SourceContactProgram.weights_eq s d hd,List.map_ofFn]
  rfl

theorem value_eq_array (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p h k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid) :
    value rho a C ε c s p h k A B d = List.ofFn (fun x =>
      ContactCalibratedGeometry.position (SourceMetadataProgram.geometricSource s d hd)
        (SourceContactProgram.size d ^ h)
        (AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)))
        (CalibratedContactProgram.graphLengths rho ε c k A B
          (CalibrationMesh.base (SourceContactProgram.size d))
          (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
          (SourceMetadataProgram.geometricSource s d hd) (weights a s d hd)) x) := by
  unfold value
  rw [input_eq_graphInput]
  exact CalibratedContactProgram.value_graphInput _ _ _ _ _ _ _ _ _ _ _

theorem source_weight_range (s : ℕ) : ∃ A : ℕ, 0 < A ∧
    ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
    ∀ e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd),
      ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
        SourceContactProgram.weights s d hd e ∧
      (SourceContactProgram.weights s d hd e:ℝ) ≤
        (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A := by
  obtain ⟨A,hA,hweight⟩ := SourceMetadataProgram.geometricSource_weight_range s
  refine ⟨A,hA,fun d hd hp e => ?_⟩
  obtain ⟨hlo,hhi⟩ := hweight d hd hp e
  have hn : (1:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast (show 1 ≤ SourceContactProgram.size d from
      le_trans (by decide : 1 ≤ 2) (SourceContactProgram.size_ge_two d))
  have hbase : (SourceContactProgram.size d:ℝ) ≤
      CalibrationMesh.base (SourceContactProgram.size d) := by
    simp only [CalibrationMesh.base,Nat.cast_pow]
    exact le_self_pow₀ hn (by decide)
  have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ SourceContactProgram.size d) hbase A
  have hsize : (SourceContactProgram.size d:ℝ) =
      (binaryHeisenbergCodec.encode d).length + 2 := by
    simp only [SourceContactProgram.size,SourceMetadataProgram.size,Nat.cast_add,Nat.cast_one]
    ring
  have hlo' : ((SourceContactProgram.size d:ℝ)^A)⁻¹ ≤
      (SourceContactProgram.weights s d hd e:ℝ) := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hlo
  have hhi' : (SourceContactProgram.weights s d hd e:ℝ) ≤
      (SourceContactProgram.size d:ℝ)^A := by
    simpa only [hsize,SourceContactProgram.weights,SourcePositiveProgram.sourceBound] using hhi
  refine ⟨?_,hhi'.trans hpow⟩
  have hpos : (0:ℝ) < (SourceContactProgram.size d:ℝ)^A := by positivity
  have hinv : ((CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A)⁻¹ ≤
      ((SourceContactProgram.size d:ℝ)^A)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hpos hpow
  exact hinv.trans hlo'

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
