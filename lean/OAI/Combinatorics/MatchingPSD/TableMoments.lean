import OAI.Combinatorics.MatchingPSD.TypeProbabilities

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace MatchingSmoothing
open Matrix
section TableKernel
variable {H : Type u_1} {C : Type u_2} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq C] in

lemma weighted_common_fiber_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (σ : Equiv.Perm (H × Bool)) :
    (Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2 ≤
      ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  classical
  calc
    _ = ∑ f : H × Bool → C, if P f ∧ P (f ∘ σ) then w ^ 2 else 0 := by
      rw [← sum_indicator_card]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs with hf
      · rw [hw f hf.1, hw (f ∘ σ) hf.2, pow_two]
      · exact mul_nonneg (pairWeight_nonneg A hA f) (pairWeight_nonneg A hA (f ∘ σ))

omit [DecidableEq C] in
lemma weighted_table_kernel_bound (A : Matrix C C ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L)
    (σ : Equiv.Perm (H × Bool)) :
    Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} ≤
      L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ) := by
  have hc := weighted_common_fiber_bound A hA P w hw σ
  have hd : 0 < D ^ 2 := sq_pos_of_pos hD
  have hz' : Z / D ^ 2 ≤ w ^ 2 * L := (div_le_iff₀ hd).mpr (by nlinarith [hz])
  calc
    _ ≤ (w ^ 2 * L) * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} :=
      mul_le_mul_of_nonneg_right hz' (Nat.cast_nonneg _)
    _ = L * ((Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)} : ℝ) * w ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc hL

lemma weighted_table_kernel_moment (A : Matrix C C ℝ)
    (hs : A.IsHermitian) (hA : ∀ i j, 0 ≤ A i j)
    (v : C → ℝ) (hv : ∀ i, 0 < v i) (hAv : A *ᵥ v = v)
    (P : (H × Bool → C) → Prop) [DecidablePred P]
    (w Z D L : ℝ) (hw : ∀ f, P f → pairWeight A f = w)
    (hZ : 0 ≤ Z) (hD : 0 < D) (hL : 0 ≤ L) (hz : Z ≤ D ^ 2 * w ^ 2 * L) :
    (∑ σ : Equiv.Perm (H × Bool),
      (Z / D ^ 2 * Fintype.card {f : H × Bool → C // P f ∧ P (f ∘ σ)}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * L ^ 2 *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2) := by
  calc
    _ ≤ ∑ σ : Equiv.Perm (H × Bool),
        (L * ∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro σ _
      apply pow_le_pow_left₀ (by positivity)
      exact weighted_table_kernel_bound A hA P w Z D L hw hD hL hz σ
    _ = L ^ 2 * ∑ σ : Equiv.Perm (H × Bool),
        (∑ f : H × Bool → C, pairWeight A f * pairWeight A (f ∘ σ)) ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ L ^ 2 * (Fintype.card (Equiv.Perm (H × Bool)) *
        (Fintype.card H + 1 : ℝ) ^ (Fintype.card C ^ 2)) :=
      mul_le_mul_of_nonneg_left (pairWeight_overlap_square_moment A hs hA v hv hAv) (sq_nonneg L)
    _ = _ := by ring

end TableKernel
end MatchingSmoothing

namespace MatchingSmoothing
open Matrix

def threeEdgeType (p : Fin 3 × Fin 3) : Fin 6 :=
  (![![0, 1, 2], ![1, 3, 4], ![2, 4, 5]] : Fin 3 → Fin 3 → Fin 6) p.1 p.2

def typeMultiplicity : Fin 6 → ℕ := ![1, 2, 2, 1, 2, 1]

lemma threeEdgeType_surjective : Function.Surjective threeEdgeType := by decide

lemma card_threeEdgeType_fiber (t : Fin 6) :
    Fintype.card {a : Fin 3 × Fin 3 // threeEdgeType a = t} = typeMultiplicity t := by
  fin_cases t <;> decide

lemma threeEdgeType_symm (a b : Fin 3) : threeEdgeType (a,b) = threeEdgeType (b,a) := by
  fin_cases a <;> fin_cases b <;> rfl

lemma typeMultiplicity_pos (t : Fin 6) : 0 < typeMultiplicity t := by
  fin_cases t <;> decide

lemma endpoint_type_identity (a b i : Fin 3) :
    (∑ j : Fin 3, (if threeEdgeType (a,b) = threeEdgeType (i,j) then (1 : ℝ) else 0) /
      typeMultiplicity (threeEdgeType (i,j))) =
      ((if a = i then (1 : ℝ) else 0) + (if b = i then 1 else 0)) / 2 := by
  have h0 : typeMultiplicity 0 = 1 := by decide
  have h1 : typeMultiplicity 1 = 2 := by decide
  have h2 : typeMultiplicity 2 = 2 := by decide
  have h3 : typeMultiplicity 3 = 1 := by decide
  have h4 : typeMultiplicity 4 = 2 := by decide
  have h5 : typeMultiplicity 5 = 1 := by decide
  fin_cases a <;> fin_cases b <;> fin_cases i <;>
    norm_num [threeEdgeType, Fin.sum_univ_succ, Fin.ext_iff, h0, h1, h2, h3, h4, h5]

section ThreeTables
variable {H : Type u_3} [Fintype H] [DecidableEq H]

noncomputable def pairColorEquiv : (H × Bool → Fin 3) ≃ (H → Fin 3 × Fin 3) where
  toFun f i := (f (i,false), f (i,true))
  invFun k v := if v.2 then (k v.1).2 else (k v.1).1
  left_inv f := by funext ⟨i,b⟩; cases b <;> rfl
  right_inv k := by funext i; rfl

noncomputable def threeTable (f : H × Bool → Fin 3) : Fin 6 → ℕ :=
  histogram (threeEdgeType ∘ pairColorEquiv f)

noncomputable def tableGamma (f : H × Bool → Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ((threeTable f (threeEdgeType (i,j)) : ℝ) / Fintype.card H) /
    typeMultiplicity (threeEdgeType (i,j))

noncomputable def tablePi (f : H × Bool → Fin 3) : Fin 3 → ℝ :=
  fun i => (histogram f i : ℝ) / (2 * Fintype.card H)

omit [DecidableEq H] in
lemma histogram_cast_sum {V : Type u_4} {T : Type u_5} [Fintype V] [DecidableEq T] (f : V → T) (t : T) :
    (histogram f t : ℝ) = ∑ i, if f i = t then 1 else 0 := by
  classical
  simp only [histogram, Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

omit [DecidableEq H] in
lemma tableGamma_hermitian (f : H × Bool → Fin 3) : (tableGamma f).IsHermitian := by
  rw [Matrix.IsHermitian.ext_iff]
  intro i j
  simp only [star_trivial, tableGamma, threeEdgeType_symm j i]

omit [DecidableEq H] in
lemma tableGamma_nonneg (f : H × Bool → Fin 3) : ∀ i j, 0 ≤ tableGamma f i j := by
  intro i j
  unfold tableGamma
  positivity

omit [DecidableEq H] in
lemma tableGamma_rowsum (f : H × Bool → Fin 3) (i : Fin 3) :
    ∑ j, tableGamma f i j = tablePi f i := by
  have he (j : Fin 3) : tableGamma f i j =
      (∑ v : H, (if threeEdgeType (f (v,false),f (v,true)) = threeEdgeType (i,j)
        then (1 : ℝ) else 0) / typeMultiplicity (threeEdgeType (i,j))) / Fintype.card H := by
    simp only [tableGamma, threeTable, histogram_cast_sum, Function.comp_apply,
      pairColorEquiv, Equiv.coe_fn_mk, ← Finset.sum_div]
    ring
  simp_rw [he]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [endpoint_type_identity]
  rw [← Finset.sum_div, div_div]
  congr 1
  simp only [histogram_cast_sum, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.sum_add_distrib]
  ring

omit [DecidableEq H] in
lemma tablePi_pos (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf : ∀ i, 0 < histogram f i) : ∀ i, 0 < tablePi f i := by
  intro i
  exact div_pos (Nat.cast_pos.mpr (hf i)) (by positivity)

omit [DecidableEq H] in
lemma tablePi_sum (f : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    ∑ i, tablePi f i = 1 := by
  simp only [tablePi, ← Finset.sum_div, ← Nat.cast_sum, sum_histogram,
    Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
  field_simp

omit [DecidableEq H] in
lemma pairWeight_tableGamma_eq (f₀ f : H × Bool → Fin 3) :
    pairWeight (tableGamma f₀) f =
      ∏ t : Fin 6, (((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t) ^ threeTable f t := by
  exact prod_eq_prod_histogram (threeEdgeType ∘ pairColorEquiv f)
    (fun t => ((threeTable f₀ t : ℝ) / Fintype.card H) / typeMultiplicity t)

omit [DecidableEq H] in
lemma pairWeight_tableGamma_constant (f₀ f : H × Bool → Fin 3)
    (hf : threeTable f = threeTable f₀) :
    pairWeight (tableGamma f₀) f = pairWeight (tableGamma f₀) f₀ := by
  rw [pairWeight_tableGamma_eq, pairWeight_tableGamma_eq, hf]

lemma tableGamma_integer_mean_lower (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H) :
    1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
      ((Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) *
        pairWeight (tableGamma f₀) f₀) := by
  classical
  have hl := integer_mean_type_probability_lower threeEdgeType threeEdgeType_surjective
    (threeEdgeType ∘ pairColorEquiv f₀) hH
  simp only [Fintype.card_fin, card_threeEdgeType_fiber] at hl
  have he : (∑ f : H × Bool → Fin 3,
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f) =
      ∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i)) := by
    exact Fintype.sum_equiv pairColorEquiv _ _ (fun f => rfl)
  change 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 *
    (∑ k : H → Fin 3 × Fin 3,
      (if histogram (threeEdgeType ∘ k) = threeTable f₀ then (1 : ℝ) else 0) *
        ∏ i, ((threeTable f₀ (threeEdgeType (k i)) : ℝ) / Fintype.card H) /
          typeMultiplicity (threeEdgeType (k i))) at hl
  rw [← he] at hl
  have hc (f : H × Bool → Fin 3) :
      (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f =
        (if threeTable f = threeTable f₀ then (1 : ℝ) else 0) * pairWeight (tableGamma f₀) f₀ := by
    split_ifs with hf
    · rw [pairWeight_tableGamma_constant f₀ f hf]
    · simp
  simp_rw [hc] at hl
  rw [← Finset.sum_mul, sum_indicator_card] at hl
  exact hl

omit [DecidableEq H] in
lemma threeTable_histogram_eq {f g : H × Bool → Fin 3} (hH : 0 < Fintype.card H)
    (h : threeTable f = threeTable g) : histogram f = histogram g := by
  have hγ : tableGamma f = tableGamma g := by
    unfold tableGamma
    rw [h]
  funext i
  have he := (tableGamma_rowsum f i).symm.trans
    ((congrArg (fun A : Matrix (Fin 3) (Fin 3) ℝ => ∑ j, A i j) hγ).trans
      (tableGamma_rowsum g i))
  change (histogram f i : ℝ) / (2 * Fintype.card H) =
    (histogram g i : ℝ) / (2 * Fintype.card H) at he
  have hn : (2 * Fintype.card H : ℝ) ≠ 0 := by positivity
  exact_mod_cast (div_left_inj' hn).mp he

end ThreeTables

section Probability
variable {V : Type u_6} {C : Type u_7} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

lemma histogram_product_mass_le_one (π : C → ℝ) (hn : ∀ i, 0 ≤ π i)
    (hs : ∑ i, π i = 1) (f₀ : V → C) :
    (Fintype.card (Colorings V C (histogram f₀)) : ℝ) * (∏ v, π (f₀ v)) ≤ 1 := by
  classical
  calc
    _ = ∑ f : V → C, if histogram f = histogram f₀ then ∏ v, π (f v) else 0 := by
      have he (f : V → C) :
          (if histogram f = histogram f₀ then ∏ v, π (f v) else 0) =
          (if histogram f = histogram f₀ then (1 : ℝ) else 0) * ∏ v, π (f₀ v) := by
        split_ifs with hf
        · rw [one_mul, prod_eq_prod_histogram f, prod_eq_prod_histogram f₀, hf]
        · simp
      simp_rw [he]
      rw [← Finset.sum_mul, sum_indicator_card]
      congr 1
      exact congrArg Nat.cast (@Fintype.card_congr
        (Colorings V C (histogram f₀)) {f : V → C // histogram f = histogram f₀}
        (coloringsFintype _) (Subtype.fintype _) (Equiv.refl _))
    _ ≤ ∑ f : V → C, ∏ v, π (f v) := by
      apply Finset.sum_le_sum
      intro f _
      split_ifs
      · rfl
      · exact Finset.prod_nonneg (fun v _ => hn (f v))
    _ = ∏ _v : V, ∑ i, π i := Fintype.prod_sum (fun (_v : V) i => π i) |>.symm
    _ = 1 := by simp only [hs, Finset.prod_const_one]

omit [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma vertexSqrtWeight_sq (π : C → ℝ) (hn : ∀ i, 0 ≤ π i) (f : V → C) :
    (∏ v, Real.sqrt (π (f v))) ^ 2 = ∏ v, π (f v) := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl (fun v _ => Real.sq_sqrt (hn (f v)))

end Probability

section TableNormalization
variable {H : Type u_8} {C : Type u_9} [Fintype H] [Fintype C] [DecidableEq H] [DecidableEq C]

omit [DecidableEq H] [Fintype C] [DecidableEq C] in
lemma pairWeight_normalized (γ : Matrix C C ℝ) (π : C → ℝ) (f : H × Bool → C) :
    pairWeight (normalizedPairMatrix γ π) f =
      pairWeight γ f / (∏ v : H × Bool, Real.sqrt (π (f v))) := by
  simp only [pairWeight, normalizedPairMatrix, Finset.prod_div_distrib,
    Fintype.prod_prod_type, Fintype.prod_bool]
  congr 1
  exact Finset.prod_congr rfl (fun i _ => mul_comm _ _)

end TableNormalization

section ThreeTableMoment
variable {H : Type u_10} [Fintype H] [DecidableEq H]

lemma three_table_kernel_moment (f₀ : H × Bool → Fin 3) (hH : 0 < Fintype.card H)
    (hf₀ : ∀ i, 0 < histogram f₀ i) :
    (∑ σ : Equiv.Perm (H × Bool),
      ((Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀)) : ℝ) /
        (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ) ^ 2 *
        Fintype.card {f : H × Bool → Fin 3 //
          threeTable f = threeTable f₀ ∧ threeTable (f ∘ σ) = threeTable f₀}) ^ 2) ≤
      Fintype.card (Equiv.Perm (H × Bool)) * (Fintype.card H + 1 : ℝ) ^ 33 := by
  classical
  let γ := tableGamma f₀
  let π := tablePi f₀
  let A := normalizedPairMatrix γ π
  let Z : ℝ := Fintype.card (Colorings (H × Bool) (Fin 3) (histogram f₀))
  let D : ℝ := Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀}
  let Q := pairWeight γ f₀
  let S := ∏ v : H × Bool, Real.sqrt (π (f₀ v))
  have hπ : ∀ i, 0 < π i := tablePi_pos f₀ hH hf₀
  have hS : 0 < S := Finset.prod_pos (fun v _ => Real.sqrt_pos.mpr (hπ (f₀ v)))
  have hD : 0 < D := by
    change (0 : ℝ) < (Fintype.card {f : H × Bool → Fin 3 // threeTable f = threeTable f₀} : ℝ)
    exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨⟨f₀, rfl⟩⟩)
  have hQ : 0 ≤ Q := pairWeight_nonneg γ (tableGamma_nonneg f₀) f₀
  have hw (f : H × Bool → Fin 3) (ht : threeTable f = threeTable f₀) :
      pairWeight A f = Q / S := by
    rw [pairWeight_normalized, pairWeight_tableGamma_constant f₀ f ht]
    congr 1
    change (∏ v, (fun i => Real.sqrt (π i)) (f v)) =
      ∏ v, (fun i => Real.sqrt (π i)) (f₀ v)
    rw [prod_eq_prod_histogram f (fun i => Real.sqrt (π i)),
      prod_eq_prod_histogram f₀ (fun i => Real.sqrt (π i)), threeTable_histogram_eq hH ht]
  have hprob : Z * S ^ 2 ≤ 1 := by
    rw [show S ^ 2 = _ from vertexSqrtWeight_sq π (fun i => (hπ i).le) f₀]
    exact histogram_product_mass_le_one π (fun i => (hπ i).le) (tablePi_sum f₀ hH) f₀
  have hmean : 1 ≤ (Fintype.card H + 1 : ℝ) ^ 6 * (D * Q) :=
    tableGamma_integer_mean_lower f₀ hH
  have hb : (1 : ℝ) ≤ D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hmean 2
    calc
      (1 : ℝ) = 1 ^ 2 := by norm_num
      _ ≤ ((Fintype.card H + 1 : ℝ) ^ 6 * (D * Q)) ^ 2 := h
      _ = _ := by ring
  have hz : Z ≤ D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hS)).mp
    have he : (D ^ 2 * (Q / S) ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12) * S ^ 2 =
        D ^ 2 * Q ^ 2 * (Fintype.card H + 1 : ℝ) ^ 12 := by field_simp
    rw [he]
    linarith
  have hg := weighted_table_kernel_moment A
    (normalizedPairMatrix_hermitian γ π (tableGamma_hermitian f₀))
    (normalizedPairMatrix_nonneg γ π (tableGamma_nonneg f₀))
    (fun i => Real.sqrt (π i)) (fun i => Real.sqrt_pos.mpr (hπ i))
    (normalizedPairMatrix_fixed γ π hπ (tableGamma_rowsum f₀))
    (fun f => threeTable f = threeTable f₀) (Q / S) Z D
    ((Fintype.card H + 1 : ℝ) ^ 12) hw (Nat.cast_nonneg _) hD (by positivity) hz
  convert hg using 1
  norm_num [Fintype.card_fin]
  ring

end ThreeTableMoment
end MatchingSmoothing

end OAI
