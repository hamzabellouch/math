import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceContactTransport
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.RationalContactBudget
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGridGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ManufacturedFrequency

namespace OAI

/-! The literal source sites and literal source graph satisfy the full
matrix hypothesis used by the continuum cloud comparison. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram SourcePositiveProgram ContactMediator HubbardGlobal

theorem exists_indexed_matrix_offsets (rho : ℕ) (hrho : 0 < rho) :
    ∃ qN qC : ℕ, 1 ≤ qN ∧ 1 ≤ qC ∧
    ∀ (C s pc h k A B aK p : ℕ) (eps c : ℚ) (d : BinaryHeisenberg) (hd : d.Valid),
    d.PolynomialPromise s → 0 ≤ eps → 0 < c → (eps:ℝ)/2 ≤ contactLengthTolerance →
    1100 ≤ k → 13 ≤ h →
    qN+(s+k/100+13)+p+1 ≤ 5*k → qC+30*k+aK+(s+k/100+13)+p+2 ≤ h → p+2 ≤ pc →
    5 ≤ 25*(k:ℝ)*Real.log (SourceContactProgram.size d) →
    ((59/2:ℝ)*(k:ℝ)*Real.log (SourceContactProgram.size d) ≤ contactSpacing c k d ∧
      (contactSpacing c k d:ℝ) ≤ 31*(k:ℝ)*Real.log (SourceContactProgram.size d)) →
    2*localLeakageBound (GaussianFrequency.frequency rho)
      (25*(k:ℝ)*Real.log (SourceContactProgram.size d)) ≤
        localDualMass (GaussianFrequency.frequency rho)/2 →
    (∀ e : GlobalEdge (geometricSource s d hd),
      0 ≤ (SourceContactProgram.weights s d hd e:ℝ) ∧
      (SourceContactProgram.weights s d hd e:ℝ) ≤ (SourceContactProgram.size d:ℝ)^aK) →
    (∀ e : GlobalEdge (geometricSource s d hd),
      let r := PrefactorSourceContactProgram.nominalDistance rho (CalibrationMesh.prefactor rho)
        C eps c s pc k A B d hd e
      |(amplification rho k d:ℝ)*planarHopping r-
        coulombHoppingTarget (GaussianFrequency.frequency rho)
          ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e) r| ≤
        ((SourceContactProgram.size d:ℝ)^pc+1)⁻¹) →
    ∀ (m : ℕ) (hm : (output s d).vertices=m+1),
    let F := indexedGraph s d hd hm
    let u := fun i => PlanarForcingProgram.position (indexedCoordinates rho C eps c s pc h k A B d hd hm i)
    let τ := ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹
    ∀ i j : Fin (m+1),
      ‖(((amplification rho k d:ℝ)*planarHoppingMatrix u i j:ℝ):ℂ)-
        graphHoppingMatrix m F.left F.right
          (fun e => (-(coulombHoppingTarget (GaussianFrequency.frequency rho) τ (F.weight e)
            ‖u (F.left e)-u (F.right e)‖):ℝ)) i j‖ ≤ ((SourceContactProgram.size d:ℝ)^p)⁻¹ := by
  have ha : (0:ℝ) < 8/(rho:ℝ) := div_pos (by norm_num) (by exact_mod_cast hrho)
  have hf := manufactured_frequency_positive hrho
  obtain ⟨qN,qC,hqN,hqC,hbound⟩ := ContactCalibratedGeometry.exists_full_matrix_offsets ha hf
  refine ⟨qN,qC,hqN,hqC,?_⟩
  intro C s pc h k A B aK p eps c d hd hp heps hc htol hk hh hkn hkh hpc hD hspacing hleak hweights hcal m hm
  dsimp only
  let N := SourceContactProgram.size d
  let σ := indexedSites s d hd hm
  let ell := contactLengths rho C eps c s pc k A B d hd
  have hN : 2 ≤ N := SourceContactProgram.size_ge_two d
  have hNR : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le (by norm_num) hNR
  have hN1 : (1:ℝ) ≤ N := le_trans (by norm_num) hNR
  have hx : 0 ≤ (k:ℝ)*Real.log N := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hN1)
  have hfar : 2 ≤ 35*(k:ℝ)*Real.log N := by nlinarith only [hD,hx]
  have hDq : 25*(k:ℝ)*Real.log N ≤ (9/10:ℝ)*contactSpacing c k d := by nlinarith [hspacing.1]
  have hfarq : 35*(k:ℝ)*Real.log N ≤ (6/5:ℝ)*contactSpacing c k d := by nlinarith [hspacing.1]
  have hP : 7200 ≤ N^h := ContactCalibratedGeometry.precision_ge_7200 hN hh
  have hell := contactLengths_near_one rho C heps hc htol s pc k A B d hd
  have hQ := contactSpacing_positive hc k d
  have hQS : (contactSpacing c k d:ℝ) ≤ (N:ℝ)^(k/100+s+13) :=
    ContactCalibratedGeometry.spacing_polynomial (s := s) hN hk hspacing.2
  have hdiam := raw_diameter_bound rho C heps hc htol s pc h k A B d hd hp hk hP hspacing.2
  have hres (e : GlobalEdge (geometricSource s d hd)) :
      |((8/(rho:ℝ))*((N:ℝ)^k)^30)*planarHopping ((contactSpacing c k d:ℝ)*ell e)-
        coulombHoppingTarget (GaussianFrequency.frequency rho) ((N:ℝ)^(30*B))⁻¹
          (SourceContactProgram.weights s d hd e) ((contactSpacing c k d:ℝ)*ell e)| ≤
            1/((N:ℝ)^pc+1) := by
    simpa only [one_div] using nominal_residual_transport rho C eps hc s pc k A B d hd e (hcal e)
  have hqS : (contactSpacing c k d:ℝ) ≤ (N:ℝ)^(s+k/100+13) := by
    simpa only [Nat.add_comm (k/100) s] using hQS
  have hs := hbound N k aK (s+k/100+13) p pc h hN hkn hkh hpc (geometricSource s d hd)
    (sourceBound s d) (size d^s) m σ (contactSpacing c k d) hQ hqS ell hP hell
    (25*(k:ℝ)*Real.log N) (35*(k:ℝ)*Real.log N) ((N:ℝ)^(30*B))⁻¹
    hD hfar le_rfl hDq hfarq hleak
    (inv_nonneg.mpr (pow_nonneg hN0.le _)) (inv_le_one_of_one_le₀ (one_le_pow₀ hN1))
    (fun e => (SourceContactProgram.weights s d hd e:ℝ))
    (fun e => (hweights e).1) (fun e => (hweights e).2) hdiam hres
  exact matrix_bound_transport rho C eps c s pc h k A B d hd hm hs

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
