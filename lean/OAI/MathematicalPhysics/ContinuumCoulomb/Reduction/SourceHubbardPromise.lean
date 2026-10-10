import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourceHubbardEnergy
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.SourcePromiseBudget

namespace OAI

/-! End-to-end promise accounting from a Hubbard interval for the literal
source output. All errors use the actual fixed-power precision schedules. -/

noncomputable section
namespace ContinuumCoulomb.SourceUnitCoulomb
open HubbardGlobal MediatorIteration

theorem promise_of_hubbard_interval (rho C U F K : ℕ) (hrho : 0 < rho) (eps c : ℚ)
    (s pc h k A B q ap p g : ℕ) (d : BinaryHeisenberg) (hd : d.Valid)
    (hp : d.PolynomialPromise s) {m r : ℕ} (u : Fin (m+1) → CoulombPairSum.Point)
    (hu : Function.Injective u)
    (hsites : SourceNuclearProgram.sites rho C eps c s pc h k A B d = List.ofFn u)
    (graph : Bonds (m+1) r)
    (hvertices : (SourcePositiveProgram.output s d).vertices = m+1)
    (hbonds : graph.toList = (SourcePositiveProgram.output s d).bonds) (t : Fin r → ℝ)
    (ho : (value rho C U F K eps c s pc h k A B q ap d).Valid)
    (hscale : 1 ≤ (SourceNuclearProgram.amplification rho k d:ℝ))
    (hpowers : 60*B+s+14 ≤ p) (hgpowers : s+14 ≤ g) (hqpowers : 60*B+s+14 ≤ q)
    (hfinite : |hubbardFermionBottom m (localizedCoulombProfile (GaussianFrequency.frequency rho) 0)
        (localizedOffsiteCoulomb (GaussianFrequency.frequency rho)
          (fun i => PlanarForcingProgram.position (u i))) graph.left graph.right t -
      graphSourceBottom m graph.left graph.right (fun e =>
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2*(graph.weight e:ℝ))| ≤
      ((SourceContactProgram.size d:ℝ)^g)⁻¹*
        (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
    (hground :
      ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t -
        (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal) ≤
        unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ∧
      unitGroundEnergy ((value rho C U F K eps c s pc h k A B q ap d).toData ho) ≤
        ((SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t +
          (SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹:ℝ):EReal)) :
    (realSourceGroundEnergy (d.toSource hd) ≤ d.lower.value →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.yes) ∧
    ((d.upper.value:ℝ) ≤ realSourceGroundEnergy (d.toSource hd) →
      value rho C U F K eps c s pc h k A B q ap d ∈ unitCoulombPromise.no) := by
  have hN : (2:ℝ) ≤ SourceContactProgram.size d := by
    exact_mod_cast SourceContactProgram.size_ge_two d
  have hM : (1:ℝ) ≤ SourceMetadataProgram.size d := by
    exact_mod_cast SourceMetadataProgram.size_pos d
  have hMN : (SourceMetadataProgram.size d:ℝ) ≤ SourceContactProgram.size d := by
    simp only [SourceContactProgram.size,Nat.cast_add,Nat.cast_one]
    linarith
  have hbudget := physical_promise_error_budget hN hM hMN hscale s B p g q hpowers hgpowers hqpowers
  have hcenter := SourcePhysicalThreshold.hubbard_center_error rho C hrho eps c s pc h k A B q d
    u graph t hvertices hbonds hfinite
  obtain ⟨hy,hn⟩ := promise_transfer rho C U F K hrho eps c s pc h k A B q ap d hd hp u hu hsites ho
    (SourcePhysicalThreshold.exactHubbardEnergy rho C eps c s pc h k A B q d u graph t)
    ((SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^p)⁻¹)
    ((SourceNuclearProgram.amplification rho k d:ℝ)*((SourceContactProgram.size d:ℝ)^g)⁻¹*
      (((SourceContactProgram.size d^(30*B):ℕ):ℝ)⁻¹)^2)
    hground (by simpa only [mul_assoc] using hcenter)
    (by simpa only [Nat.cast_pow] using hbudget)
  exact ⟨fun h => ⟨ho,hy h⟩,fun h => ⟨ho,hn h⟩⟩

end ContinuumCoulomb.SourceUnitCoulomb

end

end OAI
