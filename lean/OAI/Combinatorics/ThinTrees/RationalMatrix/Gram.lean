import Mathlib
import OAI.Combinatorics.ThinTrees.RationalMatrix.Squares

namespace OAI

/-! Rational gram. -/

section

namespace AlgorithmicThinTrees.RationalGram
open Matrix CurrentKS.RationalBits
variable {n : ℕ}

def factorColumns : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → List (Fin n → ℚ)
  | 0,_ => []
  | n+1,A => (scalarFactors (A 0 0)⁻¹).map (fun a i => a*A i 0) ++
      (factorColumns n (KS.W17.schurTail A)).map (Fin.cons 0)

lemma sum_scaled_outer (L : List ℚ) (u : Fin n → ℚ) (i j : Fin n) :
    (L.map (fun a => (a*u i)*(a*u j))).sum =
      (L.map (fun a => a^2)).sum*(u i*u j) := by
  rw [← List.sum_map_mul_right]
  congr 2
  funext a
  ring

lemma zero_pivot_row {A : Matrix (Fin n) (Fin n) ℚ}
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosSemidef) (i j : Fin n)
    (hi : A i i=0) : A i j=0 := by
  have h := CurrentKS.Covariance.entry_eq_zero_of_diag_eq_zero hA i j (by simp [hi])
  simpa only [Matrix.map_apply,Rat.cast_eq_zero] using h

lemma factorColumns_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    (A.map (fun q : ℚ => (q:ℝ))).PosSemidef → ∀ i j,
      ((factorColumns n A).map (fun v => v i*v j)).sum=A i j := by
  intro n
  induction n with
  | zero => intro A hA i;exact Fin.elim0 i
  | succ n ih =>
    intro A hA i j
    have hsym := KS.W07.rational_isSymm_of_cast_posSemidef hA
    have hdiag : 0 ≤ A 0 0 := by
      have hh := hA.diag_nonneg (i:=0)
      simp only [Matrix.map_apply] at hh
      exact_mod_cast hh
    have hp := scalarFactors_sum (A 0 0)⁻¹ (inv_nonneg.mpr hdiag)
    have ht := ih (KS.W17.schurTail A) (KS.W07.fin_schurTail_posSemidef A hA)
    simp only [factorColumns,List.map_append,List.sum_append,List.map_map,Function.comp_def]
    rw [sum_scaled_outer (u := fun i => A i 0),hp]
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · simp [hz]
        · field_simp
      · simp only [Fin.cons_zero,zero_mul,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · simp [hz,zero_pivot_row hA 0 j.succ hz]
        · rw [show A j.succ 0=A 0 j.succ from hsym.apply _ _]
          field_simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero,mul_zero,List.map_const',List.sum_replicate,nsmul_zero,add_zero]
        by_cases hz : A 0 0=0
        · have hrow := zero_pivot_row hA 0 i.succ hz
          rw [←hsym.apply 0 i.succ] at hrow
          simp [hz,hrow]
        · field_simp
      · simp only [Fin.cons_succ]
        rw [ht,KS.W17.schurTail,show A j.succ 0=A 0 j.succ from hsym.apply _ _]
        ring

def factorMatrix (A : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin (factorColumns n A).length) ℚ :=
  fun i j => (factorColumns n A).get j i

lemma factorMatrix_correct (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    factorMatrix A*(factorMatrix A)ᵀ=A := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑k, (factorColumns n A).get k i*(factorColumns n A).get k j)=A i j
  rw [← List.sum_ofFn]
  have hh : (List.ofFn fun k => (factorColumns n A).get k i*(factorColumns n A).get k j) =
      (factorColumns n A).map (fun v => v i*v j) := by
    change List.ofFn ((fun (v : Fin n → ℚ) => v i*v j) ∘ (factorColumns n A).get) = _
    rw [← List.map_ofFn,List.ofFn_get]
  rw [hh]
  exact factorColumns_correct n A hA i j

lemma trace_parts {N k t : ℕ} {M : Matrix (Fin N) (Fin N) ℚ}
    {p : Fin k → Fin N} {r : Fin t → Fin N} {S : Matrix (Fin t) (Fin t) ℚ}
    (h : KS.W07.PivotTrace M p r S) {b : ℕ} (hM : ∀ i j, Parts b (M i j)) :
    ∀ i j, Parts (KS.W30.inverseBitBound N b) (S i j) := by
  intro i j
  have hh := h.entry_parts_size_le b (fun i j => (hM i j).1) (fun i j => (hM i j).2) i j
  exact ⟨(Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hh.1),
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hh.2)⟩

lemma trace_factor_bounds {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ)
    (hPSD : (M.map (fun q : ℚ => (q:ℝ))).PosSemidef)
    {b : ℕ} (hM : ∀ i j, Parts b (M i j)) :
    ∀ {t k : ℕ} {p : Fin k → Fin N} {r : Fin t → Fin N}
      {S : Matrix (Fin t) (Fin t) ℚ}, KS.W07.PivotTrace M p r S →
      (factorColumns t S).length ≤ 3*t*(2*KS.W30.inverseBitBound N b+1) ∧
      ∀ v ∈ factorColumns t S, ∀ i, Parts (4*KS.W30.inverseBitBound N b+1) (v i) := by
  intro t
  induction t with
  | zero => intro k p r S h; simp [factorColumns]
  | succ t ih =>
    intro k p r S h
    let B := KS.W30.inverseBitBound N b
    have hp := h.state_posSemidef hPSD
    have hd : 0 ≤ S 0 0 := by
      have hh := hp.diag_nonneg (i:=0)
      simp only [Matrix.map_apply] at hh
      exact_mod_cast hh
    have hs : ∃k', ∃p' : Fin k' → Fin N,
        KS.W07.PivotTrace M p' (fun i => r i.succ) (KS.W17.schurTail S) := by
      by_cases hz : S 0 0=0
      · exact ⟨k,p,h.zero hz⟩
      · exact ⟨k+1,Fin.snoc p (r 0),h.positive (lt_of_le_of_ne hd (Ne.symm hz))⟩
    obtain ⟨k',p',hs⟩ := hs
    obtain ⟨hlen,hparts⟩ := ih hs
    have hS := trace_parts h hM
    have hb : Parts B (S 0 0)⁻¹ := (hS 0 0).inv
    have hlen' := scalarFactors_length hb
    constructor
    · simp only [factorColumns,List.length_append,List.length_map]
      change (scalarFactors (S 0 0)⁻¹).length+(factorColumns t (KS.W17.schurTail S)).length ≤
        3*(t+1)*(2*B+1)
      change (factorColumns t (KS.W17.schurTail S)).length ≤ 3*t*(2*B+1) at hlen
      nlinarith only [hlen,hlen']
    · intro v hv i
      simp only [factorColumns,List.mem_append,List.mem_map] at hv
      rcases hv with ⟨a,ha,rfl⟩|⟨u,hu,rfl⟩
      · have hq := (scalarFactors_parts hb ha).mul (hS i 0)
        change Parts (4*B+1) (a*S i 0)
        convert hq using 1
        omega
      · refine Fin.cases ?_ (fun j => hparts u hu j) i
        change Parts (4*B+1) 0
        simp [Parts,Nat.one_le_two_pow]

lemma factorColumns_bounds (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosSemidef)
    {b : ℕ} (hb : ∀ i j, Parts b (A i j)) :
    (factorColumns n A).length ≤ 3*n*(2*KS.W30.inverseBitBound n b+1) ∧
      ∀ v ∈ factorColumns n A, ∀ i, Parts (4*KS.W30.inverseBitBound n b+1) (v i) :=
  trace_factor_bounds A hA hb KS.W07.PivotTrace.initial

end AlgorithmicThinTrees.RationalGram
end

end OAI
