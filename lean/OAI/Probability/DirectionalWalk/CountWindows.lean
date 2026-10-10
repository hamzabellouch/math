import OAI.Probability.DirectionalWalk.MarkedSums

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def countWindowLaw (k n : ℕ) : Measure ℕ :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, Measure.dirac (k+i)

instance countWindowLaw_probability (k n : ℕ) [NeZero n] : IsProbabilityMeasure (countWindowLaw k n) := by
  constructor
  simp only [countWindowLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,measure_univ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (by finiteness)

lemma countWindowLaw_atom (k n r : ℕ) : countWindowLaw k n {r} =
    (if k ≤ r ∧ r < k+n then (n : ℝ≥0∞)⁻¹ else 0) := by
  classical
  simp only [countWindowLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _),Set.indicator_apply,Set.mem_singleton_iff,Pi.one_apply]
  by_cases h : k ≤ r ∧ r < k+n
  · rw [ite_eq_left h]
    let i : Fin n := ⟨r-k,by omega⟩
    rw [Finset.sum_eq_single i]
    · simp only [show k+(i : ℕ) = r by dsimp [i];omega,ite_eq_left,mul_one]
    · intro j _ hji
      apply ite_eq_right
      intro hj
      apply hji
      apply Fin.ext
      change (j : ℕ) = r-k
      omega
    · simp
  · rw [ite_eq_right h]
    have hz : ∑ i : Fin n, (if k+(i : ℕ) = r then (1 : ℝ≥0∞) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply ite_eq_right
      intro hi
      exact h ⟨by omega,by omega⟩
    rw [hz,mul_zero]

lemma countWindowLaw_ae (k n : ℕ) : ∀ᵐ r ∂countWindowLaw k n, k ≤ r ∧ r < k+n := by
  filter_upwards [ae_atom_pos (countWindowLaw k n)] with r hr
  by_contra hn
  rw [countWindowLaw_atom,ite_eq_right hn] at hr
  exact hr rfl

lemma countWindowLaw_info (k n : ℕ) : atomInfo (countWindowLaw k n) =ᵐ[countWindowLaw k n]
    fun _ => Real.log n := by
  filter_upwards [countWindowLaw_ae k n] with r hr
  simp only [atomInfo,measureReal_def,countWindowLaw_atom,ite_eq_left hr,ENNReal.toReal_inv,
    ENNReal.toReal_natCast,Real.log_inv,neg_neg]

lemma countWindowLaw_entropy (k n : ℕ) [NeZero n] :
    Integrable (atomInfo (countWindowLaw k n)) (countWindowLaw k n) ∧
      discreteEntropy (countWindowLaw k n) = Real.log n := by
  constructor
  · exact (integrable_const _).congr (countWindowLaw_info k n).symm
  · change (∫ r, atomInfo (countWindowLaw k n) r ∂countWindowLaw k n) = _
    rw [integral_congr_ae (countWindowLaw_info k n)]
    simp

lemma convolution_ae_bounds (μ ν : Measure ℕ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (a b c d : ℕ) (hμ : ∀ᵐ x ∂μ, a ≤ x ∧ x ≤ b) (hν : ∀ᵐ y ∂ν, c ≤ y ∧ y ≤ d) :
    ∀ᵐ z ∂μ.conv ν, a+c ≤ z ∧ z ≤ b+d := by
  rw [Measure.conv,ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hμ] with x hx
  filter_upwards [hν] with y hy
  exact ⟨Nat.add_le_add hx.1 hy.1,Nat.add_le_add hx.2 hy.2⟩
section MarkedWindows
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]
  {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

lemma nthCommonLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (r : ℕ) :
    (nthCommonLaw ν L r).map (fun a => (listCommonCount L a,pairTotal D a)) =
      (sumLaw (commonGapLaw ν L D) r).map (fun x => (r,x)) := by
  have hc : ∀ᵐ a ∂nthCommonLaw ν L r, listCommonCount L a = r := by
    classical
    filter_upwards [ae_atom_pos (nthCommonLaw ν L r)] with a ha
    by_contra hn
    rw [nthCommonLaw_atom ν L hL he,ite_eq_right (fun h => hn h.2)] at ha
    exact ha rfl
  rw [← nthCommonLaw_pairTotal ν L hL he D r,Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [hc] with a ha
  exact Prod.ext ha rfl

lemma windowCommonLaw_marked (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (k n : ℕ) :
    (windowCommonLaw ν L k n).map (fun a => (listCommonCount L a,pairTotal D a)) =
      markedSumLaw (commonGapLaw ν L D) (countWindowLaw k n) := by
  simp only [windowCommonLaw,Measure.map_smul _ (measurable_of_countable _).aemeasurable]
  rw [Measure.map_finset_sum' (measurable_of_countable _).aemeasurable]
  simp_rw [nthCommonLaw_marked ν L hL he D]
  conv_rhs => unfold markedSumLaw countWindowLaw
  rw [Measure.compProd_smul_left]
  congr 1
  conv_rhs => rw [← Measure.sum_fintype,Measure.compProd_sum_left,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  apply Measure.ext
  intro s hs
  rw [Measure.dirac_compProd_apply hs,Measure.map_apply (measurable_of_countable _) hs]
  rfl
end MarkedWindows

end DirectionalZeroOne

end OAI
