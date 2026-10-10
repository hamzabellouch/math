import OAI.NumberTheory.DukePrimeDegree.Dynamics.RootShearing

namespace OAI

/-!
# A first scale for noncentral root shearing

Every matrix outside a root centralizer has a finite positive first time
at which its conjugation displacement reaches a prescribed size. Before
that time all matrix entries remain uniformly controlled. This is the
stopping-time normalization used for the polynomial shearing argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma continuous_first_level {f : ℝ → ℝ} (hf : Continuous f)
    {a T : ℝ} (hzero : f 0 < a) (hT : 0 ≤ T) (hlarge : a ≤ f T) :
    ∃ t : ℝ, 0 < t ∧ t ≤ T ∧ f t = a ∧ ∀ u ∈ Icc 0 t, f u ≤ a := by
  let S : Set ℝ := Icc 0 T ∩ {t | a ≤ f t}
  have hSc : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const hf)
  have hSne : S.Nonempty := ⟨T, ⟨⟨hT, le_rfl⟩, hlarge⟩⟩
  obtain ⟨t, ht, hmin⟩ := hSc.exists_isLeast hSne
  have ht0 : 0 < t := lt_of_le_of_ne ht.1.1 (by
    intro he
    have h := ht.2
    rw [← he] at h
    exact hzero.not_ge h)
  obtain ⟨u, hu, hue⟩ := intermediate_value_Icc ht.1.1 hf.continuousOn
    ⟨hzero.le, ht.2⟩
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans ht.1.2⟩, hue.symm.le⟩
  have hut : u = t := le_antisymm hu.2 htu
  have hteq : f t = a := hut ▸ hue
  refine ⟨t, ht0, ht.1.2, hteq, ?_⟩
  intro u hu
  by_contra h
  have hau : a < f u := lt_of_not_ge h
  have htu : t ≤ u := hmin ⟨⟨hu.1, hu.2.trans ht.1.2⟩, hau.le⟩
  have hut : u = t := le_antisymm hu.2 htu
  simp only [hut, hteq, lt_self_iff_false] at hau

def rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) (t : ℝ) : ℝ :=
  ∑ r, ∑ s, |(Matrix.SpecialLinearGroup.transvection hij t * g *
    Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s|

lemma rootShearSize_zero {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    rootShearSize hij g 0 = 0 := by
  simp [rootShearSize]

lemma continuous_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) :
    Continuous (rootShearSize hij g) := by
  have hroot := continuous_rootTransvection hij
  have hconj : Continuous (fun t : ℝ =>
      Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)) :=
    (hroot.mul continuous_const).mul (hroot.comp continuous_neg)
  unfold rootShearSize
  apply continuous_finsetSum
  intro r _
  apply continuous_finsetSum
  intro s _
  exact ((((continuous_apply s).comp (continuous_apply r)).comp
    (continuous_subtype_val.comp hconj)).sub continuous_const).abs

lemma entry_sub_le_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      rootShearSize hij g t := by
  have hs : |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      ∑ u : Fin n, |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u| :=
    Finset.single_le_sum (f := fun u : Fin n =>
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u|)
      (fun u _ => abs_nonneg _) (Finset.mem_univ s)
  apply hs.trans
  exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n,
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 u v - g.1 u v|)
    (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    (Finset.mem_univ r)

/-- There is no bounded positive root-conjugation trajectory outside
the root centralizer. -/
theorem exists_large_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g) (a : ℝ) :
    ∃ t : ℝ, 0 ≤ t ∧ a ≤ rootShearSize hij g t := by
  by_contra h
  push Not at h
  let B : ℝ := ∑ r, ∑ s, |g.1 r s|
  have hentry (r s : Fin n) : |g.1 r s| ≤ B := by
    have hs : |g.1 r s| ≤ ∑ v : Fin n, |g.1 r v| :=
      Finset.single_le_sum (f := fun v : Fin n => |g.1 r v|)
        (fun v _ => abs_nonneg _) (Finset.mem_univ s)
    apply hs.trans
    exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n, |g.1 u v|)
      (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
      (Finset.mem_univ r)
  apply hnot
  apply commutes_root_of_bounded_conjugation hij g (a + B)
  intro t ht r s
  calc
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s| =
      |((Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s) + g.1 r s| :=
          by rw [sub_add_cancel]
    _ ≤ |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| + |g.1 r s| :=
      abs_add_le _ _
    _ ≤ a + B := add_le_add ((entry_sub_le_rootShearSize hij g t r s).trans (h t ht).le)
      (hentry r s)

/-- A normalized finite shearing interval exists at every positive
displacement scale for any noncentral matrix. -/
theorem exists_first_rootShearScale {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n)
    (hnot : ¬ ∀ t : ℝ, g * Matrix.SpecialLinearGroup.transvection hij t =
      Matrix.SpecialLinearGroup.transvection hij t * g)
    {a : ℝ} (ha : 0 < a) :
    ∃ t : ℝ, 0 < t ∧ rootShearSize hij g t = a ∧
      ∀ u ∈ Icc 0 t, rootShearSize hij g u ≤ a := by
  obtain ⟨T, hT, hlarge⟩ := exists_large_rootShearSize hij g hnot a
  obtain ⟨t, ht, _, heq, hsmall⟩ := continuous_first_level
    (continuous_rootShearSize hij g) (by simpa only [rootShearSize_zero] using ha) hT hlarge
  exact ⟨t, ht, heq, hsmall⟩

end DukePrimeDegree

end OAI
