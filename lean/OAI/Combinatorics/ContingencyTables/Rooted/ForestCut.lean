import OAI.Combinatorics.ContingencyTables.Rooted.MaximumForest
import OAI.Combinatorics.ContingencyTables.Transport.RowColumnPenalties

namespace OAI

/-!
# Signed cut equations for the actual physical table views

Small row and column views may disagree. Their two incidences therefore
remain separate in the cut formula. Large cells have a single physical
value at both endpoints, so every internal large-cell contribution cancels.
-/

namespace ContingencyTables.ForestCut

open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

def indicator (s : Bool) : ℝ := if s then 1 else 0

omit [Fintype I] [Fintype J] in
lemma abs_indicator_sub {a b : Bool} (h : a≠b) : |indicator a-indicator b|=1 := by
  cases a <;> cases b <;> simp_all [indicator]

noncomputable def rowDifference (small : I → J → Bool) (x z X : I → J → ℝ) (i : I) : ℝ :=
  ∑ j, if small i j then x i j-X i j else z i j-X i j

noncomputable def columnDifference (small : I → J → Bool) (q z X : I → J → ℝ) (j : J) : ℝ :=
  ∑ i, if small i j then q i j-X i j else z i j-X i j

noncomputable def cutTerm (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) : ℝ :=
  if small i j then indicator (rowU i)*(x i j-X i j)-indicator (colU j)*(q i j-X i j)
  else (indicator (rowU i)-indicator (colU j))*(z i j-X i j)

/-- Literal signed summation of the nonroot margin differences. -/
theorem signed_cut_identity (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) :
    (∑ i, indicator (rowU i)*rowDifference small x z X i)-
      (∑ j, indicator (colU j)*columnDifference small q z X j) =
      ∑ i, ∑ j, cutTerm small rowU colU x q z X i j := by
  unfold rowDifference columnDifference cutTerm
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm (f := fun j i => indicator (colU j)*
    (if small i j then q i j-X i j else z i j-X i j))]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  cases small i j <;> simp [sub_mul]

/-- When U avoids roots, all selected nonroot equations hold, giving
the source's cut cancellation even on unbalanced small profiles. -/
theorem cut_sum_zero (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ)
    (hr : ∀ i, rowU i=true → rowDifference small x z X i=0)
    (hc : ∀ j, colU j=true → columnDifference small q z X j=0) :
    (∑ i, ∑ j, cutTerm small rowU colU x q z X i j)=0 := by
  rw [← signed_cut_identity]
  have hrow : ∀ i, indicator (rowU i)*rowDifference small x z X i=0 := by
    intro i
    cases hi : rowU i
    · simp [indicator]
    · simp [indicator,hr i hi]
  have hcol : ∀ j, indicator (colU j)*columnDifference small q z X j=0 := by
    intro j
    cases hj : colU j
    · simp [indicator]
    · simp [indicator,hc j hj]
  simp only [hrow,hcol,Finset.sum_const_zero,sub_self]

omit [Fintype I] [Fintype J] in
lemma small_term_bound (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) (b B : ℝ)
    (hs : small i j=true) (hb : b≤B)
    (hx : 0≤x i j ∧ x i j≤b) (hq : 0≤q i j ∧ q i j≤b)
    (hX : 0≤X i j ∧ X i j≤b) :
    |cutTerm small rowU colU x q z X i j|≤2*B := by
  simp only [cutTerm,hs,ite_true]
  have hmul : ∀ s : Bool, ∀ a : ℝ, |indicator s*a|≤|a| := by
    intro s a
    cases s <;> simp [indicator]
  have hx' : |x i j-X i j|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hX.1,hX.2]
  have hq' : |q i j-X i j|≤b := by
    apply abs_le.mpr
    constructor <;> linarith [hq.1,hq.2,hX.1,hX.2]
  calc
    _≤|indicator (rowU i)*(x i j-X i j)|+|indicator (colU j)*(q i j-X i j)| := abs_sub _ _
    _≤|x i j-X i j|+|q i j-X i j| := add_le_add (hmul _ _) (hmul _ _)
    _≤2*B := by linarith

omit [Fintype I] [Fintype J] in
lemma free_term_bound (small : I → J → Bool) (rowU : I → Bool) (colU : J → Bool)
    (x q z X : I → J → ℝ) (i : I) (j : J) (b B : ℝ)
    (hs : small i j=false) (hB : 1≤B)
    (hcap : rowU i≠colU j → b≤B)
    (hz : 0≤z i j ∧ z i j≤b+1) (hX : 0≤X i j ∧ X i j≤b) :
    |cutTerm small rowU colU x q z X i j|≤2*B := by
  by_cases hc : rowU i=colU j
  · simp [cutTerm,hs,hc]
    linarith
  · have hb := hcap hc
    have hdiff : |z i j-X i j|≤2*B := by
      apply abs_le.mpr
      constructor <;> linarith [hz.1,hz.2,hX.1,hX.2]
    simp only [cutTerm,hs,Bool.false_eq_true,ite_false,abs_mul,abs_indicator_sub hc,one_mul]
    exact hdiff

/-- Isolating the sole crossing tree edge in the actual signed cut
equations gives the forest displacement bound. Small cells retain both
incidences, so the statement covers every unbalanced small profile. -/
theorem displacement_bound (small tree : I → J → Bool)
    (rowU : I → Bool) (colU : J → Bool) (x q z X b : I → J → ℝ)
    (i₀ : I) (j₀ : J) (d : ℝ)
    (hd : (Fintype.card I*Fintype.card J : ℕ)≤d)
    (hB : 1≤b i₀ j₀) (hs₀ : small i₀ j₀=false)
    (hcross : rowU i₀≠colU j₀)
    (hr : ∀ i, rowU i=true → rowDifference small x z X i=0)
    (hc : ∀ j, colU j=true → columnDifference small q z X j=0)
    (hX : ∀ i j, 0≤X i j ∧ X i j≤b i j)
    (hsmall : ∀ i j, small i j=true →
      b i j≤b i₀ j₀ ∧ (0≤x i j ∧ x i j≤b i j) ∧ (0≤q i j ∧ q i j≤b i j))
    (htree : ∀ i j, tree i j=true → (i,j)≠(i₀,j₀) → rowU i=colU j)
    (hfree : ∀ i j, small i j=false → tree i j=false →
      (0≤z i j ∧ z i j≤b i j+1) ∧ (rowU i≠colU j → b i j≤b i₀ j₀)) :
    |z i₀ j₀-X i₀ j₀|≤4*d*b i₀ j₀ := by
  let f : I×J → ℝ := fun a => cutTerm small rowU colU x q z X a.1 a.2
  have hsum : (∑ a, f a)=0 := by
    simpa only [Fintype.sum_prod_type,f] using cut_sum_zero small rowU colU x q z X hr hc
  have hrest : ∀ a∈(Finset.univ.erase (i₀,j₀) : Finset (I×J)), |f a|≤2*b i₀ j₀ := by
    rintro ⟨i,j⟩ ha
    have hne : (i,j)≠(i₀,j₀) := (Finset.mem_erase.mp ha).1
    by_cases hs : small i j=true
    · exact small_term_bound small rowU colU x q z X i j (b i j) (b i₀ j₀)
        hs (hsmall i j hs).1 (hsmall i j hs).2.1 (hsmall i j hs).2.2 (hX i j)
    · have hs' : small i j=false := Bool.eq_false_iff.mpr hs
      by_cases ht : tree i j=true
      · have he := htree i j ht hne
        simp [f,cutTerm,hs',he]
        linarith
      · have ht' : tree i j=false := Bool.eq_false_iff.mpr ht
        exact free_term_bound small rowU colU x q z X i j (b i j) (b i₀ j₀)
          hs' hB (hfree i j hs' ht').2 (hfree i j hs' ht').1 (hX i j)
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset (I×J)))
    (a := (i₀,j₀)) f (Finset.mem_univ _)
  have hisolate : f (i₀,j₀)=-(∑ a∈Finset.univ.erase (i₀,j₀), f a) := by
    rw [hsum] at hsplit
    linarith
  have htarget : |f (i₀,j₀)|=|z i₀ j₀-X i₀ j₀| := by
    simp only [f,cutTerm,hs₀,Bool.false_eq_true,ite_false,abs_mul,
      abs_indicator_sub hcross,one_mul]
  have hbound : |f (i₀,j₀)|≤(Fintype.card I*Fintype.card J:ℕ)*(2*b i₀ j₀) := by
    rw [hisolate,abs_neg]
    calc
      |∑ a∈Finset.univ.erase (i₀,j₀), f a|≤
        ∑ a∈Finset.univ.erase (i₀,j₀), |f a| := Finset.abs_sum_le_sum_abs _ _
      _≤∑ _a∈(Finset.univ.erase (i₀,j₀) : Finset (I×J)), 2*b i₀ j₀ :=
        Finset.sum_le_sum hrest
      _≤(Fintype.card I*Fintype.card J:ℕ)*(2*b i₀ j₀) := by
        simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ,Fintype.card_prod,nsmul_eq_mul]
        have hn : (Fintype.card I*Fintype.card J-1:ℕ)≤Fintype.card I*Fintype.card J := Nat.sub_le _ _
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  rw [htarget] at hbound
  have hdb : 0≤d := le_trans (Nat.cast_nonneg _) hd
  have hn : (Fintype.card I*Fintype.card J:ℕ)* (2*b i₀ j₀)≤2*d*b i₀ j₀ := by
    nlinarith
  exact hbound.trans (hn.trans (by nlinarith))

/-- The interval bound needed in the equality-softening count argument
follows from the proved cut displacement estimate, with ample slack. -/
lemma physical_interval_of_displacement (d b X z : ℝ) (hd : 1 ≤ d) (hb : 0 ≤ b)
    (hX : 0 ≤ X ∧ X ≤ b) (hz : |z-X| ≤ 4*d*b) :
    -10*d*b ≤ z ∧ z ≤ 10*d*b := by
  have h := abs_le.mp hz
  have hdb : 0 ≤ d*b := mul_nonneg (by linarith) hb
  have hbdb : b ≤ d*b := by nlinarith
  constructor <;> nlinarith

end ContingencyTables.ForestCut

end OAI
