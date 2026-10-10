import OAI.Geometry.BundleTests.Multiplicities
import OAI.Geometry.ComplexBundle.ProjectionBundle
import Mathlib.Topology.VectorBundle.Constructions

namespace OAI

/-! The compact bundle-test base, prefix dimensions, and retained multiplicities. -/

noncomputable section
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky

def testProjectiveDimension (m R : ℕ) (i : Fin R) : ℕ :=
  320 * m^2 * 4^(2*i.val) * (4^(R-i.val)-1)

theorem testProjectiveDimension_pos {m R : ℕ} (hm : 0 < m) (i : Fin R) :
    0 < testProjectiveDimension m R i := by
  have hn : R-i.val ≠ 0 := by omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have hp : 0 < 4^k := pow_pos (by omega) _
  have hh : 0 < 4^(R-i.val)-1 := by rw [hk, pow_succ]; omega
  unfold testProjectiveDimension
  positivity

/-- A concrete basepoint in every projective factor. -/
def coordinateLineProjection (k : ℕ) : projectionSpace (k+1) 1 := by
  let f : Fin (k+1) → ℂ := fun j => if j = 0 then 1 else 0
  refine ⟨Matrix.diagonal f, ?_, ?_, ?_⟩
  · apply Matrix.isHermitian_diagonal_of_self_adjoint
    funext j
    simp [f]
  · rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    simp [f]
  · simp [Matrix.trace_diagonal, f]

abbrev BundleTestBase (m R : ℕ) := ∀ i : Fin R,
  projectionSpace (testProjectiveDimension m R i + 1) 1

instance (m R : ℕ) : CompactSpace (BundleTestBase m R) := inferInstance

def bundleTestBasePoint (m R : ℕ) : BundleTestBase m R :=
  fun i => coordinateLineProjection (testProjectiveDimension m R i)

instance (m R : ℕ) : Nonempty (BundleTestBase m R) := ⟨bundleTestBasePoint m R⟩

def bundleTestProjection (m R : ℕ) (i : Fin R) :
    C(BundleTestBase m R, projectionSpace (testProjectiveDimension m R i + 1) 1) :=
  ⟨fun y => y i, continuous_apply i⟩

abbrev TestTautologicalLine (m R : ℕ) (i : Fin R) :=
  (bundleTestProjection m R i) *ᵖ (projectionLineCore (testProjectiveDimension m R i + 1)).Fiber

instance (m R : ℕ) (i : Fin R) : FiberBundle ℂ (TestTautologicalLine m R i) := inferInstance
instance (m R : ℕ) (i : Fin R) : VectorBundle ℂ ℂ (TestTautologicalLine m R i) := inferInstance

theorem testTautologicalLine_finrank (m R : ℕ) (i : Fin R) (y : BundleTestBase m R) :
    Module.finrank ℂ (TestTautologicalLine m R i y) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

/-- The actual dual hyperplane-line candidate on the projection product. -/
abbrev TestHyperplaneLine (m R : ℕ) (i : Fin R) :=
  (bundleTestProjection m R i) *ᵖ (projectionDualLineCore (testProjectiveDimension m R i + 1)).Fiber

instance (m R : ℕ) (i : Fin R) : FiberBundle ℂ (TestHyperplaneLine m R i) := inferInstance
instance (m R : ℕ) (i : Fin R) : VectorBundle ℂ ℂ (TestHyperplaneLine m R i) := inferInstance

theorem testHyperplaneLine_finrank (m R : ℕ) (i : Fin R) (y : BundleTestBase m R) :
    Module.finrank ℂ (TestHyperplaneLine m R i y) = 1 := by
  change Module.finrank ℂ ℂ = 1
  exact Module.finrank_self ℂ

end Kaplansky

end

namespace Kaplansky
open scoped BigOperators

theorem three_sum_pow_four (n : ℕ) : 3*(∑ i : Fin n,4^i.val)+1=4^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc,pow_succ]
    simp only [Fin.val_castSucc,Fin.val_last]
    omega

theorem testProjectiveDimension_bound (m R : ℕ) (i : Fin R) :
    testProjectiveDimension m R i ≤ 5*m*testRank m R 0*4^i.val := by
  have h := Nat.mul_le_mul_left (320*m^2*4^(2*i.val)) (Nat.sub_le (4^(R-i.val)) 1)
  change testProjectiveDimension m R i ≤ _ at h
  have he : 2*i.val+(R-i.val)=R+i.val := by omega
  calc
    _ ≤ 320*m^2*4^(2*i.val)*4^(R-i.val) := h
    _ = 320*m^2*4^(R+i.val) := by rw [mul_assoc,← pow_add,he]
    _ = _ := by rw [testRank_eq]; simp only [Nat.add_zero,pow_add]; ring

/-- Exact prefix dimensions, retaining every later occurrence through R. -/
def testPrefixDimension (m R j : ℕ) (hj : j<R) : ℕ :=
  ∑ i : Fin (j+1), testProjectiveDimension m R (i.castLE hj)

theorem testPrefixDimension_margin {m R j : ℕ} (hm : 0<m) (hj : j<R) :
    3*testPrefixDimension m R j hj < 20*m*testRank m R j := by
  have h : testPrefixDimension m R j hj ≤
      5*m*testRank m R 0*(∑ i : Fin (j+1),4^i.val) := by
    unfold testPrefixDimension
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => testProjectiveDimension_bound m R (i.castLE hj))
  have hg := three_sum_pow_four (j+1)
  have hd : 0<testRank m R 0 := by unfold testRank; positivity
  have he : testRank m R j = testRank m R 0*4^j := by
    simp only [testRank,pow_zero,one_mul]
    ring
  rw [pow_succ] at hg
  rw [he]
  nlinarith [Nat.mul_le_mul_left 3 h,
    congrArg (fun n : ℕ => 5*m*testRank m R 0*n) hg]

/-- Count all copies of L_(i+1) in m copies of E_0⊕...⊕E_R.
The stages are enumerated in descending order. -/
def retainedHyperplaneMultiplicity (m R : ℕ) (i : Fin R) : ℕ :=
  m * ∑ t : Fin (R-i.val), testMultiplicity m R (R-t.val) ⟨i.val+1,by omega⟩

theorem retainedHyperplaneMultiplicity_eq (m R : ℕ) (i : Fin R) :
    retainedHyperplaneMultiplicity m R i = testProjectiveDimension m R i := by
  have ht : ∀ t : Fin (R-i.val),
      testMultiplicity m R (R-t.val) ⟨i.val+1,by omega⟩ =
        960*m*4^(2*i.val)*4^t.val := by
    intro t
    unfold testMultiplicity
    rw [ite_eq_right (by simp)]
    have he : R+2*(i.val+1)-(R-t.val)-2=2*i.val+t.val := by omega
    dsimp only
    rw [he,pow_add]
    ring
  unfold retainedHyperplaneMultiplicity
  simp_rw [ht]
  rw [← Finset.mul_sum]
  have hg : 3*(∑ t : Fin (R-i.val),4^t.val)=4^(R-i.val)-1 := by
    have h := three_sum_pow_four (R-i.val)
    omega
  unfold testProjectiveDimension
  rw [← hg]
  ring

/-- The exact rank of the retained trivial block, in descending stage order. -/
def retainedTrivialMultiplicity (m R : ℕ) : ℕ :=
  m * ∑ t : Fin (R+1), testMultiplicity m R (R-t.val) 0

theorem retainedTrivialMultiplicity_eq (m R : ℕ) :
    retainedTrivialMultiplicity m R = 64*m^2*(∑ t : Fin (R+1),4^t.val) := by
  have ht : ∀ t : Fin (R+1), testMultiplicity m R (R-t.val) 0=64*m*4^t.val := by
    intro t
    change 64*m*4^(R-(R-t.val))=64*m*4^t.val
    have he : R-(R-t.val)=t.val := by omega
    rw [he]
  unfold retainedTrivialMultiplicity
  simp_rw [ht]
  rw [← Finset.mul_sum]
  ring

theorem retainedTrivialMultiplicity_bound {m R : ℕ} (hm : 0<m) :
    retainedTrivialMultiplicity m R < 2*m*testRank m R 0 := by
  rw [retainedTrivialMultiplicity_eq,testRank_eq]
  have h := three_sum_pow_four (R+1)
  rw [pow_succ] at h
  have hp : 0<64*m^2 := by positivity
  have hsum : (∑ t : Fin (R+1),4^t.val)<2*4^R := by omega
  have hh := Nat.mul_lt_mul_of_pos_left hsum hp
  simpa only [Nat.add_zero] using (show 64*m^2*(∑ t : Fin (R+1),4^t.val)<2*m*(64*m*4^R) from by nlinarith [hh])

end Kaplansky

end OAI
