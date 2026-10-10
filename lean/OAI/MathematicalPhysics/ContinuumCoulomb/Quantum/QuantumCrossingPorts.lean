import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedSharedEdge

namespace OAI

/-! Every nonvertex meeting has four distinct lattice ports, two on each route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

theorem qmaPath_interior_ports {u v z : ℕ × ℕ} (P : qmaSquareGrid.Path u v)
    (hz : z ∈ P.val.support) (hzu : z ≠ u) (hzv : z ≠ v) :
    ∃ a b, a ≠ b ∧ s(z,a) ∈ P.val.edges ∧ s(z,b) ∈ P.val.edges := by
  obtain ⟨k,hk,hkle⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hz
  have hk0 : 0 < k := by
    by_contra h
    have he : k = 0 := by omega
    exact hzu (hk.symm.trans (by simp [he]))
  have hkL : k < P.val.length := by
    by_contra h
    have he : k = P.val.length := by omega
    exact hzv (hk.symm.trans (by simp [he]))
  refine ⟨P.val.getVert (k-1),P.val.getVert (k+1),?_,?_,?_⟩
  · intro he
    have hn := P.property.getVert_injOn (show k-1 ≤ P.val.length by omega)
      (show k+1 ≤ P.val.length by omega) he
    omega
  · apply (P.val.mk_mem_edges_iff_exists).mpr
    refine ⟨k-1,by omega,?_⟩
    rw [show k-1+1 = k by omega,hk]
    exact Sym2.eq_swap
  · apply (P.val.mk_mem_edges_iff_exists).mpr
    exact ⟨k,hkL,by rw [hk]⟩

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

theorem buffered_crossing_ports (hA : 0 < A)
    (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) {e f : M.Term} (hef : e ≠ f)
    {z : ℕ × ℕ} (hv : ∀ v, z ≠ M.placedVertex v)
    (he : z ∈ (M.bufferedPath hd e).val.support)
    (hf : z ∈ (M.bufferedPath hd f).val.support) :
    ∃ port : Fin 4 → ℕ × ℕ, Function.Injective port ∧
      (∀ i, qmaSquareGrid.Adj z (port i)) ∧
      s(z,port 0) ∈ (M.bufferedPath hd e).val.edges ∧
      s(z,port 1) ∈ (M.bufferedPath hd e).val.edges ∧
      s(z,port 2) ∈ (M.bufferedPath hd f).val.edges ∧
      s(z,port 3) ∈ (M.bufferedPath hd f).val.edges := by
  obtain ⟨a,b,hab,hea,heb⟩ := qmaPath_interior_ports (M.bufferedPath hd e) he (hv _) (hv _)
  obtain ⟨c,d,hcd,hfc,hfd⟩ := qmaPath_interior_ports (M.bufferedPath hd f) hf (hv _) (hv _)
  have hac : a ≠ c := by
    intro h
    exact M.bufferedPath_no_shared_edge hA hd hef hea (h.symm ▸ hfc)
  have had : a ≠ d := by
    intro h
    exact M.bufferedPath_no_shared_edge hA hd hef hea (h.symm ▸ hfd)
  have hbc : b ≠ c := by
    intro h
    exact M.bufferedPath_no_shared_edge hA hd hef heb (h.symm ▸ hfc)
  have hbd : b ≠ d := by
    intro h
    exact M.bufferedPath_no_shared_edge hA hd hef heb (h.symm ▸ hfd)
  refine ⟨![a,b,c,d],?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i
    fin_cases i
    · exact (M.bufferedPath hd e).val.adj_of_mem_edges hea
    · exact (M.bufferedPath hd e).val.adj_of_mem_edges heb
    · exact (M.bufferedPath hd f).val.adj_of_mem_edges hfc
    · exact (M.bufferedPath hd f).val.adj_of_mem_edges hfd
  · exact hea
  · exact heb
  · exact hfc
  · exact hfd

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
