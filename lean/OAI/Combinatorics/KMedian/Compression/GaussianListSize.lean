import Mathlib
import OAI.Combinatorics.KMedian.Compression.GaussianStates
import OAI.Combinatorics.KMedian.Compression.GaussianListMachine

namespace OAI


                                        
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function

def rowBound (N H : ℕ) := N*(2*(3*H+10)+1)
def matrixBound (R N H : ℕ) := R*(2*rowBound N H+1)
def frameBound (N H : ℕ) := 2*(N+1)+1+rowBound N H
def framesBound (R N H : ℕ) := R*(2*frameBound N H+1)
def stateBound (R N H K : ℕ) := 4*N+2*matrixBound R N H+2*rowBound N K+2*framesBound R N H+10

def FrameValid (N H : ℕ) (f : Frame) : Prop :=
  f.1  ≤  N ∧ f.2.length  ≤  N ∧ ∀ q∈f.2, HasHeight q H
def FramesValid (N H : ℕ) (fs : Frames) : Prop := ∀ f∈fs, FrameValid N H f

def kernelList (r n : ℕ) (A : RatMatrix r n) : Row :=
  List.ofFn (fun j : Fin n => (kernelVector r n A)[j.val])

def Audit (R N H K r n : ℕ) (A : RatMatrix r n) : Prop :=
  ∀ B∈kernelStates r n A, B.rows ≤ R ∧ B.cols ≤ N ∧
    (∀ i j,HasHeight (values B.data i j) H) ∧
    (∀ j : Fin B.cols,HasHeight ((kernelVector B.rows B.cols B.data)[j.val]) K)

 theorem slots_size (n : ℕ) : (eslots (List.replicate n ())).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,EncodedList.cons_length,eu,List.length_nil,ih]; omega

 theorem row_size (row : Row) (N H : ℕ) (hn : row.length ≤ N) (hh : ∀ q∈row, HasHeight q H) :
    (er row).length ≤ rowBound N H := by
  exact (EncodedList.length_bound Ratio.encode row (3*H+10) (fun q hq => Ratio.length_height (hh q hq))).trans
    (Nat.mul_le_mul_right _ hn)

 theorem frame_size (N H : ℕ) (f : Frame) (h : FrameValid N H f) :
    (ef f).length ≤ frameBound N H := by
  have hp := NatBinary.length_le_height (h.1.trans (Nat.lt_two_pow_self (n:=N)).le)
  have hr := row_size f.2 N H h.2.1 h.2.2
  simp only [ef,encodePair_length,frameBound]
  omega

 theorem frames_size (R N H : ℕ) (fs : Frames) (hR : fs.length ≤ R) (h : FramesValid N H fs) :
    (efs fs).length ≤ framesBound R N H :=
  (EncodedList.length_bound ef fs (frameBound N H) (fun f hf => frame_size N H f (h f hf))).trans
    (Nat.mul_le_mul_right _ hR)

 theorem matrix_size {r n : ℕ} (A : Fin r → Fin n → ℚ) (R N H : ℕ)
    (hr : r ≤ R) (hn : n ≤ N) (hh : ∀ i j,HasHeight (A i j) H) :
    (ers (matrix A)).length ≤ matrixBound R N H := by
  apply (EncodedList.length_bound er (matrix A) (rowBound N H) ?_).trans
  · simpa only [matrix,List.length_ofFn,matrixBound] using Nat.mul_le_mul_right (2*rowBound N H+1) hr
  · intro row hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
    apply row_size _ N H (by simpa only [List.length_ofFn] using hn)
    intro q hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact hh i j

 theorem desc_size {r n : ℕ} (A : Fin r → Fin n → ℚ) (fs : Frames) (R N H K : ℕ)
    (hr : r ≤ R) (hn : n ≤ N) (hh : ∀ i j,HasHeight (A i j) H)
    (hf : fs.length ≤ R) (hv : FramesValid N H fs) :
    (eState (.inl ((List.replicate n (),matrix A),fs))).length ≤ stateBound R N H K := by
  have ha := matrix_size A R N H hr hn hh
  have hf := frames_size R N H fs hf hv
  simp only [eState,encodeLoop,List.length_cons,ed,edata,encodePair_length,slots_size,stateBound]
  omega

 theorem up_size {n : ℕ} (z : Fin n → ℚ) (fs : Frames) (R N H K : ℕ)
    (hn : n ≤ N) (hz : ∀ j,HasHeight (z j) K)
    (hf : fs.length ≤ R) (hv : FramesValid N H fs) :
    (eState (.inr (List.ofFn z,fs))).length ≤ stateBound R N H K := by
  have hf := frames_size R N H fs hf hv
  have hz := row_size (List.ofFn z) N K (by simpa only [List.length_ofFn] using hn)
    (fun q hq => by obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq; exact hz j)
  simp only [eState,encodeLoop,List.length_cons,eUp,encodePair_length,stateBound]
  omega

 theorem audit_head {R N H K r n : ℕ} {A : RatMatrix r n} (h : Audit R N H K r n A) :
    r ≤ R ∧ n ≤ N ∧ (∀ i j,HasHeight (values A i j) H) ∧
    (∀ j : Fin n,HasHeight ((kernelVector r n A)[j.val]) K) := by
  apply h ⟨r,n,A⟩
  cases r with
  | zero => simp only [kernelStates,List.mem_singleton]
  | succ r => cases n <;> simp only [kernelStates,List.mem_cons,true_or]
end MetricKMedian.Gaussian.ListOperation
end

end OAI
