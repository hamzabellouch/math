import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceIndexedGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceGridGeometry
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.FockGraphEntries

namespace OAI

/-! Exact transport of nominal distances and hopping matrices to the
literal source's common vertex order. -/

noncomputable section
namespace ContinuumCoulomb.SourceNuclearProgram
open SourceMetadataProgram SourcePositiveProgram ContactMediator HubbardGlobal

theorem amplification_calibration (rho k : ℕ) (d : BinaryHeisenberg) :
    amplification rho k d=CalibrationMesh.amplification rho (SourceContactProgram.size d) k := by
  rw [amplification,CalibrationMesh.amplification_eq_mesh]
  rfl

theorem calibration_base_power (B : ℕ) (d : BinaryHeisenberg) :
    (CalibrationMesh.base (SourceContactProgram.size d):ℝ)^B=
      (SourceContactProgram.size d:ℝ)^(30*B) := by
  simp only [CalibrationMesh.base,Nat.cast_pow,← pow_mul]

theorem nominal_residual_transport (rho C : ℕ) (eps : ℚ) {c : ℚ} (hc : 0 < c)
    (s pc k A B : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (e : GlobalEdge (geometricSource s d hd)) {err : ℝ}
    (hcal : let r := PrefactorSourceContactProgram.nominalDistance rho (CalibrationMesh.prefactor rho) C eps c s pc k A B d hd e
      |(amplification rho k d:ℝ)*planarHopping r-
        coulombHoppingTarget (GaussianFrequency.frequency rho)
          ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e) r| ≤ err) :
    |((8/(rho:ℝ))*((SourceContactProgram.size d:ℝ)^k)^30)*
        planarHopping ((contactSpacing c k d:ℝ)*contactLengths rho C eps c s pc k A B d hd e)-
      coulombHoppingTarget (GaussianFrequency.frequency rho)
        ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e)
          ((contactSpacing c k d:ℝ)*contactLengths rho C eps c s pc k A B d hd e)| ≤ err := by
  rw [lengths_scale rho C eps hc s pc k A B d hd e]
  simpa only [amplification_real] using hcal

theorem matrix_bound_transport (rho C : ℕ) (eps c : ℚ) (s pc h k A B : ℕ)
    (d : BinaryHeisenberg) (hd : d.Valid) {m : ℕ} (hm : (output s d).vertices=m+1)
    {err : ℝ}
    (hraw :
      let σ := indexedSites s d hd hm
      let F := MediatorIteration.finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)
      let u := fun i => ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
        (contactSpacing c k d) (contactLengths rho C eps c s pc k A B d hd) (σ.symm i)
      ∀ i j, ‖(((8/(rho:ℝ))*((SourceContactProgram.size d:ℝ)^k)^30*planarHoppingMatrix u i j:ℝ):ℂ)-
        graphHoppingMatrix m (fun e => σ (F.left e)) (fun e => σ (F.right e))
          (fun e => (-(coulombHoppingTarget (GaussianFrequency.frequency rho)
            ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e)
              ‖u (σ (F.left e))-u (σ (F.right e))‖):ℝ)) i j‖ ≤ err) :
    let F := indexedGraph s d hd hm
    let u := fun i => PlanarForcingProgram.position (indexedCoordinates rho C eps c s pc h k A B d hd hm i)
    ∀ i j, ‖(((amplification rho k d:ℝ)*planarHoppingMatrix u i j:ℝ):ℂ)-
      graphHoppingMatrix m F.left F.right
        (fun e => (-(coulombHoppingTarget (GaussianFrequency.frequency rho)
          ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (F.weight e)
            ‖u (F.left e)-u (F.right e)‖):ℝ)) i j‖ ≤ err := by
  dsimp only
  let σ := indexedSites s d hd hm
  let F := indexedGraph s d hd hm
  let rawF := MediatorIteration.finalGraph (geometricSource s d hd).bonds (sourceBound s d) (size d^s)
  let u := fun i => PlanarForcingProgram.position (indexedCoordinates rho C eps c s pc h k A B d hd hm i)
  have hleft : (fun e => σ (rawF.left e))=F.left := by
    funext e
    exact (indexedGraph_left s d hd hm e).symm
  have hright : (fun e => σ (rawF.right e))=F.right := by
    funext e
    exact (indexedGraph_right s d hd hm e).symm
  have hu : (fun x => ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
      (contactSpacing c k d) (contactLengths rho C eps c s pc k A B d hd) (σ.symm x))=u := by
    funext i
    exact (indexed_position rho C eps c s pc h k A B d hd hm i).symm
  intro i j
  have hij := hraw i j
  dsimp only at hij
  change ‖(((8/(rho:ℝ))*((SourceContactProgram.size d:ℝ)^k)^30*planarHoppingMatrix _ i j:ℝ):ℂ)-_‖ ≤ _ at hij
  rw [hu,hleft,hright] at hij
  have hup (a) : ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
      (contactSpacing c k d) (contactLengths rho C eps c s pc k A B d hd) (σ.symm a)=u a := congrFun hu a
  have hleftp (e) : σ (rawF.left e)=F.left e := congrFun hleft e
  have hrightp (e) : σ (rawF.right e)=F.right e := congrFun hright e
  have hcoef :
      (fun e : GlobalEdge (geometricSource s d hd) =>
        ((-coulombHoppingTarget (GaussianFrequency.frequency rho)
          ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e)
          ‖ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
              (contactSpacing c k d) (contactLengths rho C eps c s pc k A B d hd) (σ.symm (σ (rawF.left e)))-
            ContactCalibratedGeometry.point (geometricSource s d hd) (SourceContactProgram.size d^h)
              (contactSpacing c k d) (contactLengths rho C eps c s pc k A B d hd) (σ.symm (σ (rawF.right e)))‖:ℝ):ℂ)) =
      (fun e : GlobalEdge (geometricSource s d hd) =>
        ((-coulombHoppingTarget (GaussianFrequency.frequency rho)
          ((SourceContactProgram.size d:ℝ)^(30*B))⁻¹ (SourceContactProgram.weights s d hd e)
          ‖u (F.left e)-u (F.right e)‖:ℝ):ℂ)) := by
    funext e
    rw [hup,hup,hleftp,hrightp]
  rw [hcoef] at hij
  rw [amplification_real,indexedGraph_weight]
  exact hij

end ContinuumCoulomb.SourceNuclearProgram

end

end OAI
