import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicPacketPoints
import OAI.NumberTheory.PrimePackets.PacketMoments

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set
namespace PrimeDegreePackets.Adelic

lemma mem_packetSupport_iff_diagonal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K) (x : X (d+1)) :
    x ∈ packetSupport M σ ↔ ∃ N : FullLattice (d+1) K, LocallyHomothetic M N ∧
      ∃ D : G (d+1), (∀ i j, i ≠ j → D.val i j = 0) ∧ x = rightAction (latticePoint N σ) D := by
  constructor
  · intro hx
    obtain ⟨O,hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨N,hN,w,hw,hO⟩ := O.property
    rw [hO] at hx
    obtain ⟨u,rfl⟩ := hx
    refine ⟨N,hN,w * diagonalFlow u,?_,?_⟩
    · intro i j hij
      change (w.val * Matrix.diagonal _ : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j = 0
      rw [Matrix.mul_diagonal,hw.1 i j hij,zero_mul]
    · simp only [orbitMap,rightAction_mul]
  · rintro ⟨N,hN,D,hD,rfl⟩
    obtain ⟨w,hw,u,rfl⟩ := diagonal_eq_sign_mul_flow D hD
    refine Set.mem_iUnion.mpr ⟨⟨diagonalOrbit (rightAction (latticePoint N σ) w),N,hN,w,hw,rfl⟩,?_⟩
    refine ⟨u,?_⟩
    simp only [orbitMap,rightAction_mul]

lemma adelic_translate_eq_latticePoint {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1) (b : Basis (Fin (d+1)) ℚ K)
    (σ : OrderedEmbeddings (d+1) K) (g : GL (Fin (d+1)) RationalFiniteAdeles)
    (t : (TensorAdeles K)ˣ) (D : G (d+1))
    (hD : SpecialLinearGroup.toPGL D = ProjGenLinGroup.mk (diagonalUnits (d+1) ((ideleEquiv σ hn t).1))) :
    DoubleCoset.mk (rationalProjectiveGroup (d+1)) (finiteProjectiveIntegral (d+1))
      (adelicRegular b t * (ProjGenLinGroup.mk (realBasisGL hn b σ),ProjGenLinGroup.mk g)) =
      ambientEquiv hodd hn b (rightAction
        (latticePoint (matrixFullLattice hn b (finiteRegular b ((ideleEquiv σ hn t).2) * g)) σ) D) := by
  rw [adelicRegular_translate]
  change adelicMatrixPoint _ _ = _
  rw [adelicMatrixPoint_basis_reduction,ambientEquiv_latticePoint_rightAction]
  apply realMatrixPoint_eq_of_projective_eq
  rw [map_mul,map_mul,← hD]
  rfl

theorem adelic_packet_support_eq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (hodd : Odd (d+1)) (hn : finrank ℚ K = d+1)
    (b : Basis (Fin (d+1)) ℚ K) (σ : OrderedEmbeddings (d+1) K)
    (g : GL (Fin (d+1)) RationalFiniteAdeles) :
    ambientEquiv hodd hn b '' packetSupport (matrixFullLattice hn b g) σ =
      adelicPacketSupport hn b σ g := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨M,hM,D,hD,rfl⟩ := (mem_packetSupport_iff_diagonal _ σ x).mp hx
    obtain ⟨tf,htf⟩ := finiteIdele_realizes_local_homothety hn b g M hM
    obtain ⟨z,hz⟩ := diagonalUnits_of_SL D hD
    let t := (ideleEquiv σ hn).symm (z,tf)
    have ht : ideleEquiv σ hn t = (z,tf) := (ideleEquiv σ hn).apply_symm_apply _
    refine ⟨t,?_⟩
    have he := adelic_translate_eq_latticePoint hodd hn b σ g t D (by rw [ht]; exact congrArg ProjGenLinGroup.mk hz)
    rw [ht,Prod.snd] at he
    rw [latticePoint_eq_of_carrier_eq _ M σ hn hodd htf] at he
    exact he
  · rintro ⟨t,rfl⟩
    obtain ⟨D,hD,hDz⟩ := specialLinear_diagonal_preimage hodd ((ideleEquiv σ hn t).1)
    let M := matrixFullLattice hn b (finiteRegular b ((ideleEquiv σ hn t).2) * g)
    refine ⟨rightAction (latticePoint M σ) D,?_,?_⟩
    · apply (mem_packetSupport_iff_diagonal _ σ _).mpr
      exact ⟨M,matrixFullLattice_finiteRegular_locallyHomothetic hn b _ g,D,hD,rfl⟩
    · exact (adelic_translate_eq_latticePoint hodd hn b σ g t D hDz).symm

end PrimeDegreePackets.Adelic

end

end OAI
