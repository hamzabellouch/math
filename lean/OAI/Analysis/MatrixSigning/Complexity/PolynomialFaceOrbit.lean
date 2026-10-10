import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialMatrixFold
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies
import OAI.Analysis.MatrixSigning.Realization.VarianceRealization
import OAI.Analysis.MatrixSigning.Complexity.StoredBits
import OAI.Analysis.MatrixSigning.Complexity.GlobalCounts
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFaceQuery
import OAI.Analysis.MatrixSigning.Complexity.PolynomialVariance

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalSDP Hermitian
open scoped BigOperators MatrixOrder

structure FaceParams.GoodAtoms (p : FaceParams) : Prop where
  d_ne : p.d≠0
  N_ne : p.N≠0
  positive : ∀i,rationalAtoms p.coords i∈psdCone p.d
  nonzero : ∀i,rationalAtoms p.coords i≠0
  rank : ∀i,(rationalAtoms p.coords i : Mat p.d).rank≤1
  trace : ∑i,Hermitian.realTrace (rationalAtoms p.coords i)=1

def FaceParams.normal (p : FaceParams) : FaceParams :=
  {p with nu := RationalSDP.varianceQuery p.coords,lam := Schedule.penaltyParameter p.N (RationalSDP.varianceQuery p.coords)}
def FaceParams.orbit (p : FaceParams) (k : ℕ) : FaceParams :=
  FaceParams.next^[k] p.normal.start
lemma orbit_eq (p : FaceParams) (k : ℕ) :
    p.orbit k={p.normal with base := (Descent.run
      (RationalFace.transition p.coords p.normal.nu p.normal.lam) k
      (RationalFace.freezeAll (p.normal.lam^2/p.normal.nu) 0))} := by
  unfold FaceParams.orbit
  rw [next_iterate]
  rfl
lemma orbit_count_le (p : FaceParams) (k : ℕ) : (p.orbit k).n≤p.N := by
  rw [orbit_eq]
  exact RationalFace.activeIndices_length_le _
lemma normal_fuel_bound (p : FaceParams) (h : p.GoodAtoms) :
    Descent.fuel (RationalFace.uniformDrop p.d p.N p.normal.nu p.normal.lam)≤
      Schedule.iterationP.eval (p.d+p.N) := by
  let : NeZero p.d := ⟨h.d_ne⟩
  let : NeZero p.N := ⟨h.N_ne⟩
  exact RationalFace.normalized_fuel_polynomial p.coords h.positive h.rank h.trace
lemma orbit_query_bounds (p : FaceParams) (h : p.GoodAtoms) (k : ℕ) (hn : (p.orbit k).n≠0) :
    (p.orbit k).stencilCount≤(valueScanP Schedule.queryPrecisionP).eval (p.d+p.N) ∧
    (p.orbit k).scoreCount≤(valueScanP Schedule.queryPrecisionP).eval (p.d+p.N) := by
  let : NeZero p.d := ⟨h.d_ne⟩
  let : NeZero p.N := ⟨h.N_ne⟩
  have hb := normalized_query_search_iterations p.coords h.positive h.rank h.trace
    (Nat.pos_of_ne_zero hn) (orbit_count_le p k)
  have h1 := hb _ (List.mem_cons_self ..)
  have h2 := hb _ (by simp only [List.mem_cons,List.not_mem_nil,or_false];exact Or.inr rfl)
  rw [orbit_eq] at *
  exact ⟨h1,h2⟩
lemma qparts_bitSize (q : ℚ) : QParts (RationalGridSize.bitSize q) q := by
  constructor
  · exact (Nat.lt_size_self q.num.natAbs).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _))
  · exact (Nat.lt_size_self q.den).le.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _))
lemma faceCode_base_bound (p : FaceParams) (v : Fin p.N → ℚ) :
    (faceCode {p with base := v}).length≤(faceCode p).length+2*(vectorCode (List.ofFn v)).length := by
  simp only [faceCode,FaceParams.data,faceDataCode,prodCode_length]
  omega
lemma orbit_wire_bound : ∃ q : NaturalPolynomial,∀p : FaceParams,p.GoodAtoms →∀k,
    (faceCode (p.orbit k)).length≤(faceCode p.normal).length+
      p.N*(2*(4*q.eval (p.d+p.N)+7)+1)*2 := by
  obtain ⟨q,hq⟩ := RationalFace.normalized_stored_bits_polynomial
  refine ⟨q,?_⟩
  intro p hp k
  let : NeZero p.d := ⟨hp.d_ne⟩
  let : NeZero p.N := ⟨hp.N_ne⟩
  rw [orbit_eq]
  apply (faceCode_base_bound p.normal _).trans
  apply Nat.add_le_add_left
  rw [Nat.mul_comm 2]
  apply Nat.mul_le_mul_right
  calc
    _≤(List.ofFn (Descent.run (RationalFace.transition p.coords p.normal.nu p.normal.lam) k
      (RationalFace.freezeAll (p.normal.lam^2/p.normal.nu) 0))).length*(2*(4*q.eval (p.d+p.N)+7)+1) := by
      apply listCode_length_bound
      intro x hx
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
      exact ((qparts_bitSize _).mono (hq p.d p.N p.coords hp.positive hp.nonzero hp.rank hp.trace k i)).length
    _=_ := by rw [List.length_ofFn]

variable {ι : Type*} {L : ι → ℕ}
lemma isPoly_face_dimensions (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) :
    IsPoly L (fun i => (a i).d+(a i).N) := by
  have hd := (RunsPoly.of_poly fD a ha).output
  have hn := (RunsPoly.of_poly (fBase.then (lengthList ratCode)) a ha).output
  have h := hd.add hn
  simp only [natCode,List.length_replicate,List.length_ofFn] at h
  exact h
lemma isPoly_face_orbit (a : ι → FaceParams)
    (ha : IsPoly L (fun i => (faceCode (a i)).length)) (hg : ∀i,(a i).GoodAtoms) :
    IsPoly (fun s : ι×ℕ => L s.1) (fun s => (faceCode ((a s.1).orbit s.2)).length) := by
  obtain ⟨q,hq⟩ := orbit_wire_bound
  have hdim := isPoly_face_dimensions a ha
  have hn : IsPoly L (fun i => (faceCode (a i).normal).length) :=
    (RunsPoly.of_poly faceNormalized a ha).output
  have h := hn.add ((hdim.mul ((((isPoly_const L 4).mul (hdim.eval q)).add
    (isPoly_const L 7)).mul (isPoly_const L 2) |>.add (isPoly_const L 1))).mul (isPoly_const L 2))
  apply (h.reindex Prod.fst).mono
  intro s
  apply (hq (a s.1) (hg s.1) s.2).trans
  dsimp only [Function.comp_apply]
  have hb : (a s.1).N≤(a s.1).d+(a s.1).N := Nat.le_add_left _ _
  nlinarith
end CurrentKS.Realization

end OAI
