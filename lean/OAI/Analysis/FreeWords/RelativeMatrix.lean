import Mathlib
import OAI.Analysis.FreeWords.EntryWords
import OAI.Analysis.FreeWords.RelativeMatrixDefinitions
import OAI.Analysis.FreeWords.ScalarFreeApprox

namespace OAI

noncomputable section

namespace KKRelativeMatrix

open KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem entryWord_trace_bound {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    {n : ℕ} (u : ℤ → ConcreteAlgebra M)
    (w : List (ℤ × Matrix (Fin n) (Fin n) (ConcreteAlgebra M)))
    (i j : Fin n) (δ : ℝ)
    (h : ∀ v∈entryWords w i j, ‖τ.map (scalarWord u v)‖≤δ) :
    ‖τ.map (matrixWord u w i j)‖ ≤ (entryWords w i j).length*δ := by
  rw [entryWords_sum, map_list_sum, List.map_map]
  calc
    _ ≤ (((entryWords w i j).map (fun v => τ.map (scalarWord u v))).map norm).sum := norm_list_sum_le _
    _ ≤ ((entryWords w i j).map (fun _ => δ)).sum := by
      rw [List.map_map]
      exact List.sum_le_sum h
    _ = _ := by rw [List.map_const',List.sum_replicate]; simp only [nsmul_eq_mul]

theorem finite_relative_matrix_independence : FiniteRelativeMatrixIndependence (H := H) := by
  classical
  intro M τ hF hD n K F hFne hcenter ε hε
  let S : Finset (List (ℤ × ConcreteAlgebra M)) :=
    F.biUnion fun w => Finset.univ.biUnion fun i : Fin n =>
      Finset.univ.biUnion fun j : Fin n => (entryWords w i j).toFinset
  have hS (w) (hw : w∈F) (i j : Fin n) (v) (hv : v∈entryWords w i j) : v∈S := by
    exact Finset.mem_biUnion.mpr ⟨w,hw,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,List.mem_toFinset.mpr hv⟩⟩⟩
  have hSdata (v) (hv : v∈S) : ∃ w∈F, ∃ i j : Fin n, v∈entryWords w i j := by
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i,_,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨j,_,hv⟩ := Finset.mem_biUnion.mp hv
    exact ⟨w,hw,i,j,List.mem_toFinset.mp hv⟩
  have hSne : ∀ v∈S, v≠[] := by
    intro v hv hv0
    obtain ⟨w,hw,i,j,hv⟩ := hSdata v hv
    have hl := entryWords_length hv
    rw [hv0,List.length_nil] at hl
    exact hFne w hw (List.eq_nil_of_length_eq_zero hl.symm)
  have hSc : ∀ v∈S, ∀ y∈v, y.1≠0 ∧ τ.map y.2=0 := by
    intro v hv y hy
    obtain ⟨w,hw,i,j,hv⟩ := hSdata v hv
    obtain ⟨z,hz,a,b,rfl⟩ := entryWords_letters hv y hy
    exact ⟨(hcenter w hw z hz).1,(hcenter w hw z hz).2 a b⟩
  let T : ℕ := ∑ w∈F, ∑ i : Fin n, ∑ j : Fin n, (entryWords w i j).length
  have hT (w) (hw : w∈F) (i j : Fin n) : (entryWords w i j).length≤T := by
    calc
      _ ≤ ∑ j : Fin n, (entryWords w i j).length :=
        Finset.single_le_sum (f := fun j : Fin n => (entryWords w i j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin n, ∑ j : Fin n, (entryWords w i j).length :=
        Finset.single_le_sum (f := fun i : Fin n => ∑ j : Fin n, (entryWords w i j).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ ≤ T := by
        dsimp only [T]
        exact Finset.single_le_sum (f := fun w => ∑ i : Fin n, ∑ j : Fin n, (entryWords w i j).length) (fun _ _ => Nat.zero_le _) hw
  let δ : ℝ := ε/(T+1)
  have hden : 0<(T:ℝ)+1 := by positivity
  have hδ : 0<δ := div_pos hε hden
  have hδle : δ≤ε := div_le_self hε.le (le_add_of_nonneg_left (Nat.cast_nonneg T))
  obtain ⟨u,huK,huS⟩ := KKLocalPatching.finite_scalar_free_approximation M τ hF hD K S hSne hSc δ hδ
  refine ⟨u,fun k hk hk0 => (huK k hk hk0).trans_le hδle,?_⟩
  intro w hw i j
  have hb := entryWord_trace_bound τ (fun k => (u^k).val) w i j δ
    (fun v hv => (huS v (hS w hw i j v hv)).le)
  have hmul : (entryWords w i j).length*δ≤(T:ℝ)*δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hT w hw i j) hδ.le
  have hstrict : (T:ℝ)*δ<ε := by
    dsimp only [δ]
    rw [← mul_div_assoc,div_lt_iff₀ hden]
    nlinarith
  exact hb.trans_lt (hmul.trans_lt hstrict)

end

end KKRelativeMatrix
end

end OAI
