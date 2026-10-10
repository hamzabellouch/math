import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorSourceCalibration
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PrefactorSpacing

namespace OAI

/-! One fixed calibration retains both the source edge residuals and the
uniform shared spacing, including for source graphs with no retained edges. -/

noncomputable section
namespace ContinuumCoulomb.PrefactorSourceContactProgram
open ContactMediator

theorem exists_source_calibration (rho : ℕ) (hrho : 0 < rho)
    (eps : ℚ) (heps : 0 < eps) (hepsSmall : eps ≤ 1/1000)
    (s B : ℕ) (kmin : ℝ) :
    ∃ (C A : ℕ) (c : ℚ) (k : ℕ), 0 < C ∧ 0 < c ∧ 0 < k ∧ kmin ≤ (k:ℝ) ∧
      ∀ (d : BinaryHeisenberg) (hd : d.Valid), d.PolynomialPromise s →
      ((59/2:ℝ)*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤
        AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)) ∧
        (AutomaticCalibration.spacing c k (CalibrationMesh.base (SourceContactProgram.size d)):ℝ) ≤
          31*(k:ℝ)*Real.log (SourceContactProgram.size d)) ∧
      ∀ (p : ℕ) (e : GlobalEdge (SourceMetadataProgram.geometricSource s d hd)),
        let r := nominalDistance rho (CalibrationMesh.prefactor rho) C eps c s p k A B d hd e
        let N := CalibrationMesh.base (SourceContactProgram.size d)
        let D := (k:ℝ)*Real.log N
        (1-(eps:ℝ))*D ≤ r ∧ (r:ℝ) ≤ (1+(eps:ℝ))*D ∧
          localizedGramConstant (GaussianFrequency.frequency rho) ≤
            localizedCoulombProfile (GaussianFrequency.frequency rho) 0-
              localizedCoulombProfile (GaussianFrequency.frequency rho) r ∧
          |(CalibrationMesh.amplification rho (SourceContactProgram.size d) k:ℝ)*planarHopping r-
            coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^B)⁻¹
              (SourceContactProgram.weights s d hd e) r| ≤
            ((SourceContactProgram.size d:ℝ)^p+1)⁻¹ := by
  have heps1 : eps < 1 := lt_of_le_of_lt hepsSmall (by norm_num)
  obtain ⟨A,hA,hweights⟩ := source_weight_range s
  obtain ⟨C,L,c,k,hC,_hL,hc,hk,hkmin,hcal⟩ := PrefactorCalibration.exists_calibration
    rho hrho (CalibrationMesh.prefactor rho) (CalibrationMesh.prefactor_positive hrho)
    eps heps heps1 A B kmin
  refine ⟨C,A+L,c,k,hC,hc,hk,hkmin,fun d hd hp => ?_⟩
  have hN := SourceContactProgram.size_ge_two d
  have hbase := CalibrationMesh.base_ge_two hN
  have hpwr : (1:ℝ) ≤ (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^A :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ CalibrationMesh.base (SourceContactProgram.size d) by omega))
  have hone := hcal (CalibrationMesh.base (SourceContactProgram.size d)) 0 1 hbase
    (by simpa only [Rat.cast_one] using inv_le_one_of_one_le₀ hpwr)
    (by simpa only [Rat.cast_one] using hpwr)
  refine ⟨PrefactorCalibration.spacing_bounds rho (CalibrationMesh.prefactor rho) C
    heps.le hepsSmall hc k (A+L) B (SourceContactProgram.size d) 0 hN ⟨hone.1,hone.2.1⟩,?_⟩
  intro p e
  obtain ⟨hlo,hhi⟩ := hweights d hd hp e
  have hm := hcal (CalibrationMesh.base (SourceContactProgram.size d))
    (SourceContactProgram.size d^p) (SourceContactProgram.weights s d hd e) hbase hlo hhi
  simpa only [nominalDistance,CalibrationMesh.amplification,Rat.cast_mul,Rat.cast_pow,
    Rat.cast_natCast,Nat.cast_pow] using hm

end ContinuumCoulomb.PrefactorSourceContactProgram

end

end OAI
