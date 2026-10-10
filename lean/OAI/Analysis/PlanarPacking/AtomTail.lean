import OAI.Analysis.PlanarPacking.CanonicalRows

namespace OAI

namespace SharpPlanar
open IntegerBasis
noncomputable def atomBase : Fin 7 → ℝ := ![1/10000,469/1000000,7279/1000000,59165/1000000,219974/1000000,494744/1000000,828986/1000000]
lemma atomBase_pos (j : Fin 7) : 0<atomBase j := by fin_cases j <;> norm_num [atomBase]
lemma atomBase_lt_one (j : Fin 7) : atomBase j<1 := by fin_cases j <;> norm_num [atomBase]
lemma atomBase_contains (j : Fin 7) : Real.exp (-(314159/100000:ℝ)*dampingCap j) ≤ atomBase j := by
  have hp := Real.sum_le_exp_of_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤314159/100000) (dampingCap_pos j).le) 30
  rw [neg_mul,Real.exp_neg]
  apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
  have ht : 1 ≤ atomBase j*(∑ i ∈ Finset.range 30,((314159/100000:ℝ)*dampingCap j)^i/(i.factorial:ℝ)) := by
    fin_cases j <;> norm_num [atomBase,dampingCap,Finset.sum_range_succ]
  exact ht.trans (mul_le_mul_of_nonneg_left hp (atomBase_pos j).le)
lemma decay_atomBase (j : Fin 7) (n : ℕ) :
    Real.exp (-Real.pi*dampingCap j*n) ≤ atomBase j^n := by
  have he : Real.exp (-Real.pi*dampingCap j)≤atomBase j :=
    (Real.exp_le_exp.mpr (by nlinarith [pi_fine,dampingCap_pos j])).trans (atomBase_contains j)
  rw [mul_comm _ (n:ℝ),Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_pos _).le he n
noncomputable def atomRowFactor (j : Fin 7) (n : ℕ) : ℝ := (1+|D n|+Real.pi*zCap j)/Q n
noncomputable def atomRow (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomRowFactor j n*atomL j n else 0
noncomputable def atomRowTable (N : ℕ) : ℝ :=
  ∑ j : Fin 7, (∑ a : Fin 12, atomRow j (N+1+a.val))/(1-Real.exp (-12*Real.pi*dampingCap j))
lemma atomRowFactor_nonneg (j : Fin 7) (n : ℕ) : 0≤atomRowFactor j n := by
  unfold atomRowFactor
  have hz := zCap_nonneg j
  exact div_nonneg (by positivity) (Q_pos n).le
lemma atomRow_nonneg (j : Fin 7) (n : ℕ) : 0≤atomRow j n := by
  unfold atomRow; split_ifs
  · exact mul_nonneg (atomRowFactor_nonneg _ _) (atomL_nonneg _ _)
  · rfl
lemma atomRow_period (j : Fin 7) (n k : ℕ) :
    atomRow j (n+12*k)=(Real.exp (-12*Real.pi*dampingCap j))^k*atomRow j n := by
  have hmod : (n+12*k)%12=n%12 := by omega
  have hfac : atomRowFactor j (n+12*k)=atomRowFactor j n := by simp [atomRowFactor,Q,D,hmod]
  unfold atomRow
  rw [hmod]
  split_ifs
  · rw [hfac]
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [atomL_shift]
    have he : Real.exp (-Real.pi*dampingCap j*(12*(k:ℝ)))=(Real.exp (-12*Real.pi*dampingCap j))^k := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [he]; ring
  · simp
lemma atomRow_tail_sum (j : Fin 7) (N : ℕ) :
    Summable (fun n : ℕ => atomRow j (N+1+n)) ∧
    (∑' n : ℕ, atomRow j (N+1+n)) ≤
      (∑ a : Fin 12,atomRow j (N+1+a.val))/(1-Real.exp (-12*Real.pi*dampingCap j)) := by
  apply periodic_geometric_sum (fun _ => atomRow_nonneg j _) (Real.exp_pos _).le
  · apply Real.exp_lt_one_iff.mpr
    nlinarith [Real.pi_pos,dampingCap_pos j,mul_pos Real.pi_pos (dampingCap_pos j)]
  · intro a k
    convert (atomRow_period j (N+1+a.val) k).le using 1; congr 1; omega
noncomputable def atomFactorRat (j : Fin 7) (n : ℕ) : ℝ := (1+rowDUpper n+(31416/10000:ℝ)*zCap j)/rowQLower n
noncomputable def atomRowRat (j : Fin 7) (n : ℕ) : ℝ :=
  if n%12∈residues then atomFactorRat j n*(atomMass j*lambdaCap j*atomBase j^n) else 0
noncomputable def atomTableRat (N : ℕ) : ℝ := ∑ j : Fin 7,(∑ a : Fin 12,atomRowRat j (N+1+a.val))/(1-atomBase j^12)
lemma atomFactorRat_nonneg (j : Fin 7) (n : ℕ) : 0≤atomFactorRat j n := by
  have hq : 0≤rowQLower n := by unfold rowQLower; split_ifs <;> norm_num
  have hd : 0≤rowDUpper n := by unfold rowDUpper; split_ifs <;> norm_num
  have hz := zCap_nonneg j
  unfold atomFactorRat
  positivity
lemma atomRowFactor_le (j : Fin 7) (n : ℕ) (hn : n%12∈residues) : atomRowFactor j n≤atomFactorRat j n := by
  unfold atomRowFactor atomFactorRat
  have hq := rowQLower_bound n hn
  have hd := rowDUpper_bound n hn
  have hz := zCap_nonneg j
  have hd0 := (abs_nonneg (D n)).trans hd.le
  apply div_le_div₀ (by positivity)
  · exact add_le_add (add_le_add le_rfl hd.le) (mul_le_mul_of_nonneg_right pi_fine.2.le hz)
  · exact hq.1
  · exact hq.2.le
lemma atomRow_le (j : Fin 7) (n : ℕ) : atomRow j n≤atomRowRat j n := by
  unfold atomRow atomRowRat
  split_ifs with hn
  · apply mul_le_mul (atomRowFactor_le j n hn)
    · exact mul_le_mul_of_nonneg_left (decay_atomBase j n) (by fin_cases j <;> norm_num [atomMass,lambdaCap])
    · exact atomL_nonneg j n
    · exact atomFactorRat_nonneg j n
  · rfl
lemma atomRowTable_le (N : ℕ) : atomRowTable N≤atomTableRat N := by
  unfold atomRowTable atomTableRat
  apply Finset.sum_le_sum
  intro j _
  have hd : 0<1-atomBase j^12 := sub_pos.mpr (pow_lt_one₀ (atomBase_pos j).le (atomBase_lt_one j) (by norm_num))
  apply div_le_div₀
  · exact Finset.sum_nonneg (fun a _ => (atomRow_nonneg j _).trans (atomRow_le j _))
  · exact Finset.sum_le_sum (fun a _ => atomRow_le j _)
  · exact hd
  · have he := decay_atomBase j 12
    have heq : Real.exp (-Real.pi*dampingCap j*(12:ℕ))=Real.exp (-12*Real.pi*dampingCap j) := by congr 1; push_cast; ring
    rw [heq] at he
    exact sub_le_sub_left he 1
lemma atomTableRat_hundred : atomTableRat 100<(32:ℝ)/10^9 := by
  norm_num [atomTableRat,atomRowRat,atomFactorRat,atomBase,atomMass,rowDUpper,rowQLower,lambdaCap,zCap,residues,Fin.sum_univ_succ]
lemma atomRowTable_hundred : atomRowTable 100<(32:ℝ)/10^9 :=
  (atomRowTable_le 100).trans_lt atomTableRat_hundred
end SharpPlanar

end OAI
