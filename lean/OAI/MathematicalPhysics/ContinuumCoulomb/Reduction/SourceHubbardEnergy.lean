import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePhysicalPromise
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.TargetHubbardParameters

namespace OAI

/-! Exact finite-spin and scalar-offset identities for the literal source
bond list. These identify the Hubbard center with the computed threshold center. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb
open MediatorIteration HubbardGlobal

theorem source_graph_bottom {m r : ℕ} (s : ℕ) (d : BinaryHeisenberg)
    (F : Bonds (m+1) r)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : F.toList = (SourcePositiveProgram.output s d).bonds) (τ : ℝ) :
    graphSourceBottom m F.left F.right (fun e => τ^2*(F.weight e : ℝ)) =
      τ^2*(SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
        (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ)) := by
  rw [graphSourceBottom_bonds_smul F (sq_nonneg τ)]
  have hm : sourceMatrixBottom (m+1) F.matrix =
      SourcePositiveProgram.energy (SourcePositiveProgram.output s d) := by
    unfold SourcePositiveProgram.energy
    rw [hvertices,← hbonds,Bonds.matrix_toList]
  have hs : (∑ e, (F.weight e : ℝ)) =
      (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ) := by
    rw [← hbonds]
    simp only [Bonds.toList,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  rw [hm,hs]

namespace SourcePhysicalThreshold

def exactHubbardEnergy (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (F : Bonds (m+1) r) (t : Fin r → ℝ) : ℝ :=
  let x := input rho C eps c s p h k A B q d
  CenteredPhysicalThreshold.actualOffset rho x.1 +
    (SourceNuclearProgram.amplification rho k d : ℝ)*
      (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
      CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)

theorem hubbard_center_error (rho C : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s p h k A B q : ℕ) (d : BinaryHeisenberg) {m r : ℕ}
    (u : Fin (m+1) → CoulombPairSum.Point) (F : Bonds (m+1) r) (t : Fin r → ℝ)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : F.toList = (SourcePositiveProgram.output s d).bonds)
    {δ : ℝ}
    (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
      graphSourceBottom m F.left F.right (fun e =>
        ((((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2)*(F.weight e : ℝ))| ≤ δ) :
    |exactHubbardEnergy rho C eps c s p h k A B q d u F t -
      exactSourceEnergy rho C eps c s p h k A B q d
        (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u)| ≤
      (SourceNuclearProgram.amplification rho k d : ℝ)*δ := by
  have ha : 0 ≤ (SourceNuclearProgram.amplification rho k d : ℝ) :=
    (CenteredPhysicalThreshold.amplification_bound rho (SourcePhysicalThreshold.mesh k d) hrho).1
  rw [source_graph_bottom s d F hvertices hbonds] at hfinite
  have he : exactHubbardEnergy rho C eps c s p h k A B q d u F t -
      exactSourceEnergy rho C eps c s p h k A B q d
        (CoulombPairSum.exactTotal (GaussianFrequency.frequency rho) u) =
    (SourceNuclearProgram.amplification rho k d : ℝ) *
      (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
        (((SourceContactProgram.size d^(30*B) : ℕ) : ℝ)⁻¹)^2 *
          (SourcePositiveProgram.energy (SourcePositiveProgram.output s d) -
            (((SourcePositiveProgram.output s d).bonds.map (fun e => e.2.2)).sum : ℝ))) := by
    simp only [exactHubbardEnergy,exactSourceEnergy,input,SourceNuclearProgram.amplification,
      Rat.cast_inv,Rat.cast_natCast,Rat.cast_list_sum,List.map_map,Function.comp_def]
    ring
  rw [he,abs_mul,abs_of_nonneg ha]
  exact mul_le_mul_of_nonneg_left hfinite ha

theorem exactHubbardEnergy_eq (rho C : ℕ) (eps c : ℚ) (s p h k A B q : ℕ)
    (d : BinaryHeisenberg) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (F : Bonds (m+1) r) (t : Fin r → ℝ)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1) :
    exactHubbardEnergy rho C eps c s p h k A B q d u F t =
      (SourceNuclearProgram.amplification rho k d : ℝ)^2*(m+1:ℝ)*
        (slabPotential rho (slabHorizontal k d) (slabVertical k d) 0+
          ((-1/2:ℝ)+GaussianFrequency.frequency rho/2)) +
      (SourceNuclearProgram.amplification rho k d : ℝ)*
        (hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
          (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
            (fun i => PlanarForcingProgram.position (u i))) F.left F.right t -
          (1/2:ℝ)*∑ i, ∑ j, localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
            (fun i => PlanarForcingProgram.position (u i)) i j) := by
  simp only [exactHubbardEnergy,CenteredPhysicalThreshold.actualOffset,
    CenteredPhysicalThreshold.actualReference,input,SourceNuclearProgram.amplification,
    hvertices,Nat.cast_add,Nat.cast_one,CoulombPairSum.exactTotal,localizedOffsiteCoulomb,
    slabHorizontal,slabVertical]
  ring

end SourcePhysicalThreshold
end ContinuumCoulomb

end

end OAI
