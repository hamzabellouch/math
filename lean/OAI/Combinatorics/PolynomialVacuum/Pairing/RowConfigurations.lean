import OAI.Combinatorics.PolynomialVacuum.Pairing.TransferMatrix

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical

 
def incomingStream {N : ℕ} (a : Spin) (r : Fin N → Spin) (j : Fin N) : Spin :=
  (Fin.cons a r : Fin (N+1) → Spin) j.castSucc

def streamEndpoint {N : ℕ} (a : Spin) (r : Fin N → Spin) : Spin :=
  (Fin.cons a r : Fin (N+1) → Spin) (Fin.last N)

@[simp] theorem incomingStream_zero {N : ℕ} (a h : Spin) (r : Fin N → Spin) :
    incomingStream a (Fin.cons h r) 0=a := rfl
@[simp] theorem incomingStream_succ {N : ℕ} (a h : Spin) (r : Fin N → Spin) (j : Fin N) :
    incomingStream a (Fin.cons h r) j.succ=incomingStream h r j := rfl
@[simp] theorem streamEndpoint_cons {N : ℕ} (a h : Spin) (r : Fin N → Spin) :
    streamEndpoint a (Fin.cons h r)=streamEndpoint h r := rfl

noncomputable def rowConfigurationWeight {N : ℕ} (out inp : Fin N → Spin)
    (a b : Spin) (r k : Fin N → Spin) : ℂ :=
  if streamEndpoint a r=b then ∏j : Fin N,
    honeycombPiece (out j,r j) (incomingStream a r j,inp j) (k j) else 0

theorem honeycombKernel_stream (N : ℕ) (out inp : Fin N → Spin) (a b : Spin) :
    honeycombKernel N out inp a b = ∑ r : Fin N → Spin,
      if streamEndpoint a r=b then ∏j : Fin N,
        honeycombEntry (out j,r j) (incomingStream a r j,inp j) else 0 := by
  induction N generalizing a b with
  | zero => simp [honeycombKernel,streamEndpoint,eq_comm]
  | succ N ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (N+1) => Spin)).sum_comp,Fintype.sum_prod_type]
    change _ = ∑ h : Spin,∑ r : Fin N → Spin,
      if streamEndpoint a (Fin.cons h r)=b then ∏j : Fin (N+1),
        honeycombEntry (out j,(Fin.cons h r : Fin (N+1) → Spin) j) (incomingStream a (Fin.cons h r) j,inp j) else 0
    simp only [streamEndpoint_cons,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,
      incomingStream_zero,incomingStream_succ,honeycombKernel,ih]
    apply Finset.sum_congr rfl
    intro h _
    simp only [honeycombEntry,← Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    split_ifs <;> simp [Fin.tail]

theorem honeycombKernel_configurations (N : ℕ) (out inp : Fin N → Spin) (a b : Spin) :
    honeycombKernel N out inp a b=∑ r : Fin N → Spin,∑ k : Fin N → Spin,
      rowConfigurationWeight out inp a b r k := by
  rw [honeycombKernel_stream]
  apply Finset.sum_congr rfl
  intro r _
  unfold rowConfigurationWeight
  split_ifs with h
  · simp_rw [honeycombEntry]
    exact Fintype.prod_sum _
  · simp

 

theorem physicalTransfer_configurations (N : ℕ) (κ : ℂ) (out inp : Fin N → Spin) :
    physicalTransfer N κ out inp=∑ a : Spin,∑ r : Fin N → Spin,∑ k : Fin N → Spin,
      κ^charge a*rowConfigurationWeight out inp a a r k := by
  simp [physicalTransfer,honeycombKernel_configurations,Finset.mul_sum]

end PolynomialVacuumAlgebra

end OAI
