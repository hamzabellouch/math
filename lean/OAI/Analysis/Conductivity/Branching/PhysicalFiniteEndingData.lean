import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalAttachedGreen
import OAI.Analysis.Conductivity.Branching.PhysicalRankTransport

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus

structure PhysicalFiniteEndingData (s : Fin 3 → ℝ) where
  p : Fin 2 → centralEnergySpace s
  mean_zero : ∀ j,centralM s (p j)=0
  variational : ∀ j,CentralVariationalEquation s (centralBasisSlopes j) (p j)
  harmonic : ∀ j,WeaklyHarmonicOn
    (centralWholeL2 (centralAmbientComponent s 0 (p j).val)) centralHarmonicRegion
  ending : ∀ i : Fin 3,TorusEndingData s
    (branchNormalize i (fun j => torusSpectralSynthesis s (centralT s i (p j))))

lemma physicalFiniteEndingData_nonempty {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (hres : ∀ h l : Fin 2 → ℤ,torusQuadratic s h=torusQuadratic s l → l=h ∨ l= -h) :
    Nonempty (PhysicalFiniteEndingData s) := by
  obtain ⟨p,hm,hv,hw,_⟩ := central_pair_regular_exists s
  have he (i : Fin 3) := torusEndingData_nonempty hs hres
    (branchNormalize i (fun j => torusSpectralSynthesis s (centralT s i (p j))))
  exact ⟨⟨p,hm,hv,hw,fun i => Classical.choice (he i)⟩⟩

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def traces (i : Fin 3) (j : Fin 2) : TorusL2 := torusSpectralSynthesis s (centralT s i (z.p j))

def compression (i : Fin 3) : ℝ :=
  if i=0 then -((z.ending i).R+1)/centralThickness else ((z.ending i).R+1)/centralThickness

lemma ending_R_pos (i : Fin 3) : 0<(z.ending i).R := by
  linarith [(z.ending i).d_pos,(z.ending i).e_pos,(z.ending i).overlap_lt]

lemma compression_parent : z.compression 0<0 := by
  rw [compression,ite_eq_left rfl]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (by linarith [z.ending_R_pos 0]))
    (by norm_num [centralThickness])

lemma compression_child (k : Fin 2) : 0<z.compression k.succ := by
  rw [compression,ite_eq_right (Fin.succ_ne_zero k)]
  exact div_pos (by linarith [z.ending_R_pos k.succ]) (by norm_num [centralThickness])

lemma compression_ne (i : Fin 3) : z.compression i≠0 :=
  Fin.cases z.compression_parent.ne (fun k => (z.compression_child k).ne') i

lemma end_length (i : Fin 3) : physicalEndLength z.compression i=(z.ending i).R+1 := by
  unfold physicalEndLength compression
  split_ifs <;>
    rw [abs_div,abs_of_pos (show 0<centralThickness by norm_num [centralThickness])]
  · rw [abs_neg,abs_of_pos (by linarith [z.ending_R_pos i])]
    exact div_mul_cancel₀ _ (by norm_num [centralThickness])
  · rw [abs_of_pos (by linarith [z.ending_R_pos i])]
    exact div_mul_cancel₀ _ (by norm_num [centralThickness])

def correctedEndJet (j : Fin 2) (i : Fin 3) (x : R3) : JetFiber :=
  attachedPhysicalJet s z.compression (centralBasisSlopes j) (z.p j) i x+
    periodicCorrectionJet (branchCorrection i (z.ending i) j) (z.compression i) i x

lemma correction_initial_zero (i : Fin 3) (j : Fin 2) {x : Coord3} (hx : x 0<(z.ending i).d) :
    branchCorrection i (z.ending i) j x=0 := by
  unfold branchCorrection torusEndingCorrection axialZeroExtension
  split_ifs with h
  · linarith [(z.ending i).e_pos]
  · rfl

theorem corrected_pair_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ u w : Fin 2 → H1,
      (∀ j,u j∈H10 ∧ w j∈H10) ∧
      (∀ j,H1JetOn (u j) centralPhysical (centralFullJetCLM s (z.p j).val) ∧
        H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (u j) (physicalEndRegion i)
        (attachedPhysicalJet s z.compression (centralBasisSlopes j) (z.p j) i) ∧
        H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      ∀ j v,(∫ y in physicalBlockRegion,originalPiGradient (u j) y ⬝ᵥ
        (physicalBlockTensor s z.compression y*ᵥoriginalPiGradient v y))=
        physicalTerminalFluxCLM s z.compression (centralBasisSlopes j) z.compression_ne
          (fun i => centralT s i (z.p j)) v := by
  have hu (j : Fin 2) := complete_physical_attachment s hs z.compression (centralBasisSlopes j)
    z.compression_parent z.compression_child (z.p j)
  choose u hu0 huc hue using hu
  have hd (j : Fin 2) := triplePeriodicCorrection_exists
    (fun i => branchCorrection i (z.ending i) j)
    (fun i => branchCorrection_periodic i (z.ending i) j)
    (fun i => (branchCorrection_C2 i (z.ending i) hs j).of_le (by norm_num))
    (fun i => (z.ending i).d) z.compression (fun i => (z.ending i).d_pos)
    (fun i x hx => z.correction_initial_zero i j hx) z.compression_parent z.compression_child
  choose d hd0 hdc hde using hd
  refine ⟨u,fun j => u j+d j,fun j => ⟨hu0 j,H10.add_mem (hu0 j) (hd0 j)⟩,
    fun j => ⟨huc j,(huc j).add_zero (hdc j)⟩,
    fun j i => ⟨hue j i,(hue j i).add (hde j i)⟩,?_⟩
  intro j v
  exact physical_block_green_extension s z.compression (centralBasisSlopes j) hs z.compression_ne
    (fun i => centralT s i (z.p j)) (u j)
    (fun _ hφ => attached_block_smooth_green s z.compression (centralBasisSlopes j) hs
      z.compression_parent z.compression_child (z.p j) (z.variational j) (u j) (huc j) (hue j) hφ) v

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
