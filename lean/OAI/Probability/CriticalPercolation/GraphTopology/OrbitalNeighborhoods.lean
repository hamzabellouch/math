import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.GraphGeometry.OrbitalScales
import OAI.Probability.CriticalPercolation.Growth.SparseDoubling

namespace OAI

section
noncomputable section
open Set
open scoped Classical Pointwise

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def orbitBall (o : V) (r : ℕ) : Set V :=
  MulAction.orbit G.Aut o ∩ G.vertexBall o r

def displacementBall (o : V) (r : ℕ) : Set G.Aut :=
  {φ | φ • o ∈ G.vertexBall o r}

lemma orbitBall_finite (hl : G.LocallyFinite) (o : V) (r : ℕ) :
    (G.orbitBall o r).Finite := (G.vertexBall_finite hl o r).subset Set.inter_subset_right

lemma mem_orbitBall_self (o : V) (r : ℕ) : o ∈ G.orbitBall o r :=
  ⟨MulAction.mem_orbit_self o,G.mem_vertexBall_self o r⟩

lemma orbitBall_mono (o : V) : Monotone (G.orbitBall o) :=
  fun _ _ hrs _ hv => ⟨hv.1,G.vertexBall_mono o hrs hv.2⟩

lemma orbitBall_ncard_pos (hl : G.LocallyFinite) (o : V) (r : ℕ) :
    0<(G.orbitBall o r).ncard :=
  (Set.ncard_pos (G.orbitBall_finite hl o r)).mpr ⟨o,G.mem_orbitBall_self o r⟩

lemma Aut.orbitBall_mem (φ : G.Aut) (o v : V) (r : ℕ) :
    φ • v ∈ G.orbitBall (φ • o) r ↔ v ∈ G.orbitBall o r := by
  change (φ • v ∈ MulAction.orbit G.Aut (φ • o) ∧
    φ.vertex v ∈ G.vertexBall (φ.vertex o) r) ↔ _
  rw [Aut.vertexBall_mem]
  refine and_congr ?_ Iff.rfl
  rw [MulAction.orbit_smul]
  constructor
  · rintro ⟨ψ,hψ⟩
    refine ⟨φ⁻¹*ψ,?_⟩
    change (φ⁻¹*ψ) • o=v
    change ψ • o=φ • v at hψ
    rw [mul_smul,hψ,inv_smul_smul]
  · rintro ⟨ψ,rfl⟩
    exact ⟨φ*ψ,mul_smul _ _ _⟩

lemma Aut.orbitBall_image (φ : G.Aut) (o : V) (r : ℕ) :
    φ.vertex '' G.orbitBall o r = G.orbitBall (φ • o) r := by
  ext v
  obtain ⟨w,rfl⟩ := φ.vertex.surjective v
  simp only [Set.mem_image,φ.vertex.injective.eq_iff,exists_eq_right]
  change w∈G.orbitBall o r ↔ φ • w∈G.orbitBall (φ • o) r
  exact (Aut.orbitBall_mem G φ o w r).symm

lemma Aut.orbitBall_ncard (φ : G.Aut) (o : V) (r : ℕ) :
    (G.orbitBall (φ • o) r).ncard=(G.orbitBall o r).ncard := by
  rw [←Aut.orbitBall_image G φ,Set.ncard_image_of_injective _ φ.vertex.injective]

lemma orbitBall_ncard_of_mem_orbit {o u : V} (hu : u∈MulAction.orbit G.Aut o) (r : ℕ) :
    (G.orbitBall u r).ncard=(G.orbitBall o r).ncard := by
  obtain ⟨φ,rfl⟩ := hu
  exact Aut.orbitBall_ncard G φ o r

lemma orbitBall_add {o u : V} {r : ℕ} (hu : u∈G.orbitBall o r) (s : ℕ) :
    G.orbitBall u s ⊆ G.orbitBall o (r+s) := by
  intro v hv
  refine ⟨?_,G.vertexBall_add hu.2 s hv.2⟩
  obtain ⟨φ,rfl⟩ := hu.1
  simpa only [MulAction.orbit_smul] using hv.1

lemma one_mem_displacementBall (o : V) (r : ℕ) : 1∈G.displacementBall o r := by
  simpa only [displacementBall,Set.mem_ofPred_eq,one_smul] using G.mem_vertexBall_self o r

lemma inv_mem_displacementBall {o : V} {r : ℕ} {φ : G.Aut} :
    φ⁻¹∈G.displacementBall o r ↔ φ∈G.displacementBall o r := by
  change φ⁻¹ • o∈G.vertexBall o r ↔ φ • o∈G.vertexBall o r
  have hh := Aut.vertexBall_mem G φ o (φ⁻¹ • o) r
  change φ • (φ⁻¹ • o)∈G.vertexBall (φ • o) r ↔ φ⁻¹ • o∈G.vertexBall o r at hh
  rw [smul_inv_smul] at hh
  exact hh.symm.trans G.vertexBall_comm.symm

lemma displacementBall_mul_subset (o : V) (r s : ℕ) :
    G.displacementBall o r * G.displacementBall o s ⊆ G.displacementBall o (r+s) := by
  rintro φ ⟨ψ,hψ,η,hη,rfl⟩
  change (ψ*η) • o∈G.vertexBall o (r+s)
  rw [mul_smul]
  exact G.vertexBall_add hψ s ((Aut.vertexBall_mem G ψ o (η • o) s).mpr hη)

lemma orbitBall_polynomial_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∀ R : ℕ, ∃ n≥R, (G.orbitBall o n).ncard≤n^(d+1) := by
  obtain ⟨C,hC⟩ := G.orbit_density_radius hc hq o
  intro R
  obtain ⟨N,hN,x,hx⟩ := hpoly (C+1*(max R ((C+2*1)^d)+1))
  obtain ⟨φ,hφ⟩ := hC x
  have ha := polynomial_scale_arithmetic C 1 d R N (by omega) hN
  simp only [Nat.div_one,Nat.one_mul] at ha
  refine ⟨N-C,ha.1,?_⟩
  calc
    (G.orbitBall o (N-C)).ncard ≤ (G.vertexBall o (N-C)).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right (G.vertexBall_finite hl o _)
    _ = (G.vertexBall (φ.vertex o) (N-C)).ncard := (Aut.vertexBall_ncard G φ o _).symm
    _ ≤ (G.vertexBall x N).ncard := Set.ncard_le_ncard
      (fun _ hv => G.vertexBall_mono x ha.2.1 (G.vertexBall_add hφ (N-C) hv))
      (G.vertexBall_finite hl x N)
    _ ≤ N^d := hx
    _ ≤ (N-C)^(d+1) := ha.2.2

lemma orbitBall_doubling_scales (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V) (d : ℕ)
    (hpoly : ∀ R : ℕ, ∃ n≥R, ∃ v : V, (G.vertexBall v n).ncard≤n^d) :
    ∀ R : ℕ, ∃ n≥R, (G.orbitBall o (5*n)).ncard≤5^(d+2)*(G.orbitBall o n).ncard := by
  apply CriticalPercolation.sparse_polynomial_doubling_scales
    (fun n => (G.orbitBall o n).ncard)
  · intro n m hnm
    exact Set.ncard_le_ncard (G.orbitBall_mono o hnm) (G.orbitBall_finite hl o m)
  · intro n
    exact G.orbitBall_ncard_pos hl o n
  · exact G.orbitBall_polynomial_scales hc hl hq o d hpoly

end CriticalPercolation.BondGraph
end
end

end OAI
