import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorSourceContactCorrectness

namespace OAI

/-! Uniform, executable nominal calibration for the actual positive
three-stage graph, with precisely the amplification of the nuclear mesh. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

def nominalDistance (rho : ℕ) (a : ℚ) (C : ℕ) (ε c : ℚ)
    (s p k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) : ℚ :=
  PrefactorCalibration.value rho a C ε c k A B
    (CalibrationMesh.base (SourceContactProgram.size d),
      (SourceContactProgram.size d ^ p,SourceContactProgram.weights s d hd e))

theorem graphLengths_scale (rho : ℕ) (a : ℚ) (C : ℕ) (ε : ℚ)
    {c : ℚ} (hc : 0 < c) (s p k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd)) :
    (AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)):ℝ) *
      CalibratedContactProgram.graphLengths rho ε c k A B
        (CalibrationMesh.base (SourceContactProgram.size d))
        (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
        (SourceMetadataProgram.geometricSource s d hd) (weights a s d hd) e =
      nominalDistance rho a C ε c s p k A B d hd e := by
  exact CalibratedContactProgram.graphLengths_scale rho ε hc k A B
    (CalibrationMesh.base (SourceContactProgram.size d))
    (PrefactorCalibration.precision C (SourceContactProgram.size d ^ p))
    (by have h := CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d); omega)
    (SourceMetadataProgram.geometricSource s d hd) (weights a s d hd) e

theorem exists_nominal_calibration (rho : ℕ) (hrho : 0 < rho)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (s B : ℕ) (kmin : ℝ) :
    ∃ (C A : ℕ) (c : ℚ) (k : ℕ), 0 < C ∧ 0 < c ∧ 0 < k ∧ kmin ≤ (k:ℝ) ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s → ∀ p : ℕ,
      ∀ e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd),
        let r := nominalDistance rho (CalibrationMesh.prefactor rho) C ε c s p k A B d hd e
        let N := CalibrationMesh.base (SourceContactProgram.size d)
        let D := (k:ℝ)*Real.log N
        (1-(ε:ℝ))*D ≤ r ∧ (r:ℝ) ≤ (1+(ε:ℝ))*D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0-
              localizedCoulombProfile (GaussianFrequency.frequency rho) r ∧
          |(CalibrationMesh.amplification rho (SourceContactProgram.size d) k:ℝ)*planarHopping r-
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
              (SourceContactProgram.weights s d hd e) r| ≤
            ((SourceContactProgram.size d:ℝ)^p+1)⁻¹ := by
  obtain ⟨A,hA,hweights⟩ := source_weight_range s
  obtain ⟨C,L,c,k,hC,hL,hc,hk,hkmin,hcal⟩ := PrefactorCalibration.exists_calibration
    rho hrho (CalibrationMesh.prefactor rho) (CalibrationMesh.prefactor_positive hrho)
    ε hε hε1 A B kmin
  refine ⟨C,A+L,c,k,hC,hc,hk,hkmin,fun d hd hp p e => ?_⟩
  obtain ⟨hlo,hhi⟩ := hweights d hd hp e
  have hm := hcal (CalibrationMesh.base (SourceContactProgram.size d))
    (SourceContactProgram.size d ^ p) (SourceContactProgram.weights s d hd e)
    (CalibrationMesh.base_ge_two (SourceContactProgram.size_ge_two d)) hlo hhi
  simpa only [nominalDistance,CalibrationMesh.amplification,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Nat.cast_pow] using hm

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
