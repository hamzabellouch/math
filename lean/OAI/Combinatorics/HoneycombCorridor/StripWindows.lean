import Mathlib
import OAI.Combinatorics.HoneycombCorridor.StripDecay

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def vertexWindow (h M : ℕ) : Finset Vertex :=
  ((Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h)).biUnion
    fun p => {Vertex.up p.1 p.2,Vertex.down p.1 p.2}

theorem mem_vertexWindow (h M : ℕ) (v : Vertex) : v ∈ vertexWindow h M ↔
    -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 ≤ M ∧ InStrip h v := by
  cases v <;>
    simp [vertexWindow,Finset.mem_biUnion,Finset.mem_Icc,
      Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton,InStrip,boxIndex,
      Vertex.up.injEq,Vertex.down.injEq] <;> aesop

theorem vertexWindow_card_le (h M : ℕ) : (vertexWindow h M).card ≤ 2*(2*M+1)*h := by
  have hc := Finset.card_biUnion_le (s := (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h))
    (t := fun p => {Vertex.up p.1 p.2,Vertex.down p.1 p.2})
  change (vertexWindow h M).card ≤ _ at hc
  have hs : (∑ p ∈ (Finset.Icc (-(M : ℤ)) M).product (Finset.Ico (0 : ℤ) h),
      ({Vertex.up p.1 p.2,Vertex.down p.1 p.2} : Finset Vertex).card) = 2*(2*M+1)*h := by
    have hcast : ((M : ℤ) + 1 + M).toNat = 2*M+1 := by omega
    simp [Finset.card_product,Int.card_Icc,Int.card_Ico,hcast]
    ring
  exact hc.trans_eq hs

theorem bounded_position_mem_window (h n : ℕ) (v : Vertex) (hv : InStrip h v)
    (hx : |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    v ∈ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
  have hi := strip_index_bounds h v hv
  have hi0 : (boxIndex v 1 : ℝ) ≤ (boxIndex v 2 : ℝ) := by exact_mod_cast hi.1
  have hi1 : (boxIndex v 2 : ℝ) ≤ (boxIndex v 1 : ℝ) + h := by exact_mod_cast hi.2
  have hab := abs_lt.mp hx
  rw [position_index] at hab
  apply (mem_vertexWindow _ _ _).mpr
  refine ⟨?_,?_,hv⟩
  · have : -(((2*(n+1)+1)*(h+1) : ℕ) : ℝ) ≤ (boxIndex v 1 : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this
  · have : (boxIndex v 1 : ℝ) ≤ (((2*(n+1)+1)*(h+1) : ℕ) : ℝ) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) h]
    exact_mod_cast this

theorem strip_shell_card_le (h n : ℕ) (D : Finset Vertex)
    (hstrip : ∀ v ∈ D, InStrip h v) (S : Finset Vertex) (hSD : S ⊆ D)
    (hS : ∀ v ∈ S, |(position v).1| < 2*((n : ℝ)+1)*(h+1)) :
    (S.card : ℝ) ≤ 20*((n : ℝ)+1)*((h : ℝ)+1)^2 := by
  have hsub : S ⊆ vertexWindow h ((2*(n+1)+1)*(h+1)) := by
    intro v hv
    exact bounded_position_mem_window h n v (hstrip v (hSD hv)) (hS v hv)
  have hc := (Finset.card_le_card hsub).trans (vertexWindow_card_le h _)
  have hc' : (S.card : ℝ) ≤ (2*(2*((2*(n+1)+1)*(h+1))+1)*h : ℕ) := by exact_mod_cast hc
  push_cast at hc'
  nlinarith [Nat.cast_nonneg (α := ℝ) h,Nat.cast_nonneg (α := ℝ) n,
    sq_nonneg ((h : ℝ)+1),mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (sq_nonneg (h : ℝ))]



theorem vertexWindow_convex (h M : ℕ) : AdmissiblyConvex (vertexWindow h M) := by
  apply admissiblyConvex_of_box _
    (fun k => if k = 0 then 0 else -(M : ℤ))
    (fun k => if k = 0 then h else if k = 1 then M+1 else M+h+1)
  intro v
  rw [mem_vertexWindow]
  constructor
  · rintro ⟨hlo,hhi,hstrip⟩ k
    have hb := strip_index_bounds h v hstrip
    fin_cases k <;> simp only [Fin.zero_eta,ite_true,Fin.reduceEq,ite_false]
    · exact hstrip
    · change -(M : ℤ) ≤ boxIndex v 1 ∧ boxIndex v 1 < (M : ℤ)+1
      omega
    · change -(M : ℤ) ≤ boxIndex v 2 ∧ boxIndex v 2 < (M : ℤ)+h+1
      omega
  · intro hv
    have h0 := hv 0
    have h1 := hv 1
    simp only [Fin.reduceEq,ite_false,ite_true] at h0 h1
    exact ⟨h1.1,by omega,h0⟩

theorem bottomSource_mem_window (h M : ℕ) (hh : 1 ≤ h) :
    bottomSource.1 ∈ vertexWindow h M := by
  rw [mem_vertexWindow]
  simp only [bottomSource,boxIndex,Fin.reduceEq,ite_false,ite_true,InStrip]
  omega

theorem vertexWindow_strip (h M : ℕ) : ∀ v ∈ vertexWindow h M, InStrip h v := by
  intro v hv
  exact ((mem_vertexWindow _ _ _).mp hv).2.2

theorem finite_vertices_in_window (h : ℕ) (S : Finset Vertex)
    (hs : ∀ v ∈ S, InStrip h v) : ∃ M : ℕ, S ⊆ vertexWindow h M := by
  let M := S.sup (fun v => (boxIndex v 1).natAbs)
  refine ⟨M,?_⟩
  intro v hv
  have ha : (boxIndex v 1).natAbs ≤ M := Finset.le_sup (f := fun v => (boxIndex v 1).natAbs) hv
  have ha' : (|(boxIndex v 1)| : ℤ) ≤ (M : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ha
  have hab := abs_le.mp ha'
  exact (mem_vertexWindow _ _ _).mpr ⟨hab.1,hab.2,hs v hv⟩

end PolynomialVacuumBridge.Corridor

end

end OAI
