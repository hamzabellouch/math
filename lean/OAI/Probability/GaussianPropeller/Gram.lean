import OAI.Probability.GaussianPropeller.Deletion

namespace OAI

universe uE uF uι

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace

open scoped RealInnerProductSpace

namespace GaussianPropeller.Gram

variable {ι : Type uι} {E : Type uE} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [Fintype ι] [DecidableEq ι] in

theorem independent_omit (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (i : ι) :
    LinearIndependent ℝ (fun j : {j : ι // j ≠ i} => z j) := by
  apply LinearMap.BilinForm.linearIndependent_of_pairwise_le_zero (innerₗ E)
    (fun x hx => real_inner_self_pos.mpr hx) (-(innerₗ E) (z i))
  · intro j
    change 0 < -⟪z i, z j⟫
    exact neg_pos.mpr (hneg (Ne.symm j.property))
  · intro j l hjl
    exact (hneg (fun h => hjl (Subtype.ext h))).le

theorem sum_omit_eq {F : Type uF} [AddCommMonoid F] (f : ι → F) (i : ι)
    (hi : f i = 0) : (∑ j : {j : ι // j ≠ i}, f j) = ∑ j, f j := by
  rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp) f]
  simpa [hi] using Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)

theorem coefficients_constant (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (a : ι → ℝ) (ha : ∑ i, a i • z i = 0) (i j : ι) : a j = a i := by
  have hrel : ∑ l, (a l - a i) • z l = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, hsum, ha,
      smul_zero, sub_self]
  have hrel' : ∑ l : {l : ι // l ≠ i}, (a l - a i) • z l = 0 := by
    rw [sum_omit_eq (fun l => (a l - a i) • z l) i (by simp)]
    exact hrel
  by_cases hji : j = i
  · rw [hji]
  · have hzero := (Fintype.linearIndependent_iff.mp (independent_omit z hneg i))
      (fun l => a l - a i) hrel' ⟨j, hji⟩
    exact sub_eq_zero.mp hzero

theorem affineIndependent (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0) :
    AffineIndependent ℝ z := by
  rw [affineIndependent_iff_of_fintype]
  intro a ha hrel i
  have hlin : ∑ j, a j • z j = 0 := by
    simpa only [Finset.weightedVSub_eq_linear_combination Finset.univ ha] using hrel
  have hconst : ∀ j, a j = a i := coefficients_constant z hneg hsum a hlin i
  have hc : (Fintype.card ι : ℝ) * a i = 0 := by
    simpa only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using ha
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    have : Nonempty ι := ⟨i⟩
    exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp hc).resolve_left hcard

theorem independent_differences (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : LinearIndependent ℝ (fun j : {j : ι // j ≠ i} => z j - z i) := by
  exact (affineIndependent_iff_linearIndependent_vsub ℝ z i).mp
    (affineIndependent z hneg hsum)

theorem span_omit_eq (z : ι → E) (hsum : ∑ i, z i = 0) (i : ι) :
    Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j)) =
      Submodule.span ℝ (Set.range z) := by
  classical
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨j, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hji : j ≠ i
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
    · have hji' : j = i := not_ne_iff.mp hji
      subst j
      let V := Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j))
      have hi : z i = -(∑ j ∈ Finset.univ.erase i, z j) := by
        have h := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
        rw [hsum] at h
        exact eq_neg_of_add_eq_zero_right h
      rw [hi]
      apply V.neg_mem
      apply V.sum_mem
      intro j hj
      exact Submodule.subset_span ⟨⟨j, (Finset.mem_erase.mp hj).1⟩, rfl⟩

theorem finrank_span (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : Module.finrank ℝ (Submodule.span ℝ (Set.range z)) =
      Fintype.card ι - 1 := by
  rw [← span_omit_eq z hsum i, finrank_span_eq_card (independent_omit z hneg i)]
  simp [Fintype.card_subtype_compl (fun j : ι => j = i)]

theorem span_differences_eq (z : ι → E) (hsum : ∑ i, z i = 0) (i : ι) :
    Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j - z i)) =
      Submodule.span ℝ (Set.range z) := by
  classical
  let W := Submodule.span ℝ (Set.range (fun j : {j : ι // j ≠ i} => z j - z i))
  have hdiff (j : ι) : z j - z i ∈ W := by
    by_cases hji : j = i
    · simp [hji]
    · exact Submodule.subset_span ⟨⟨j, hji⟩, rfl⟩
  have hi : z i ∈ W := by
    have hh : (∑ j, (z j - z i)) = -(Fintype.card ι : ℝ) • z i := by
      simp [Finset.sum_sub_distrib, hsum, ← Nat.cast_smul_eq_nsmul ℝ, neg_smul]
    have hm : -(Fintype.card ι : ℝ) • z i ∈ W := by
      rw [← hh]
      exact W.sum_mem (fun j _ => hdiff j)
    have hcard : -(Fintype.card ι : ℝ) ≠ 0 := by
      have : Nonempty ι := ⟨i⟩
      exact neg_ne_zero.mpr (by exact_mod_cast Fintype.card_ne_zero)
    exact (W.smul_mem_iff hcard).mp hm
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Submodule.sub_mem _ (Submodule.subset_span ⟨j, rfl⟩)
      (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change z j ∈ W
    have h := W.add_mem (hdiff j) hi
    simpa only [sub_add_cancel] using h

omit [Fintype ι] [DecidableEq ι] in

theorem exists_inner_values [FiniteDimensional ℝ E] (v : ι → E)
    (hv : LinearIndependent ℝ v) (a : ι → ℝ) :
    ∃ h ∈ Submodule.span ℝ (Set.range v), ∀ i, ⟪h, v i⟫ = a i := by
  let W := Submodule.span ℝ (Set.range v)
  let b := Module.Basis.span hv
  let L : StrongDual ℝ W := LinearMap.toContinuousLinearMap (b.constr ℝ a)
  let h : W := (InnerProductSpace.toDual ℝ W).symm L
  refine ⟨h, h.property, fun i => ?_⟩
  have hi : ⟪h, b i⟫ = a i := by
    rw [InnerProductSpace.toDual_symm_apply]
    exact b.constr_basis ℝ a i
  change ⟪(h : E), ((b i) : E)⟫ = a i at hi
  simpa only [b, Module.Basis.coe_span_apply] using hi

theorem exists_translation [FiniteDimensional ℝ E] (z : ι → E)
    (hneg : Pairwise (fun i j => ⟪z i, z j⟫ < 0)) (hsum : ∑ i, z i = 0)
    (i : ι) : ∃ h ∈ Submodule.span ℝ (Set.range z),
      (∀ j, j ≠ i → ⟪h, z i - z j⟫ = 1) ∧
        ⟪h, z i⟫ = ((Fintype.card ι : ℝ) - 1) / (Fintype.card ι : ℝ) := by
  obtain ⟨h, hh, hpair⟩ := exists_inner_values
    (fun j : {j : ι // j ≠ i} => z j - z i)
    (independent_differences z hneg hsum i) (fun _ => -1)
  have hpair' (j : ι) (hji : j ≠ i) : ⟪h, z i - z j⟫ = 1 := by
    have hp := hpair ⟨j, hji⟩
    simp only [inner_sub_right] at hp ⊢
    linarith
  refine ⟨h, ?_, hpair', ?_⟩
  · rwa [span_differences_eq z hsum i] at hh
  · have hsum' : ∑ j : {j : ι // j ≠ i}, ⟪h, z i - z j⟫ =
        (Fintype.card ι : ℝ) - 1 := by
      simp only [show ∀ j : {j : ι // j ≠ i}, ⟪h, z i - z j⟫ = 1 from
        fun j => hpair' j j.property, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
      have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
        simp [Fintype.card_subtype_compl (fun j : ι => j = i)]
      rw [hcard, Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨i⟩)]
      simp
    have hsum'' : (Fintype.card ι : ℝ) * ⟪h, z i⟫ =
        (Fintype.card ι : ℝ) - 1 := by
      rw [sum_omit_eq (fun j => ⟪h, z i - z j⟫) i (by simp)] at hsum'
      simpa only [inner_sub_right, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, ← inner_sum, hsum, inner_zero_right,
        sub_zero] using hsum'
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      have : Nonempty ι := ⟨i⟩
      exact_mod_cast Fintype.card_ne_zero
    exact (eq_div_iff hn).mpr (by simpa only [mul_comm] using hsum'')

end GaussianPropeller.Gram

end OAI
