import OAI.Analysis.ForestSpace.Paired

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section SegmentNorm
variable {V : Type} [PartialOrder V]

/-- All squared disjoint-segment tests. Quantifying over finite index types
is equivalent to families S₁,...,Sₘ; a zero-sized family
adds only zero to the set of test values. -/
def testValues (u : V → ℝ) : Set ℝ :=
  {r | ∃ (ι : Type) (_ : Fintype ι) (S : ι → Finset V),
    (∀ i, IsSegment (S i)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    r = ∑ i, segSum u (S i) ^ 2}

noncomputable def squareSup (u : V → ℝ) : ℝ := sSup (testValues u)

/-- Exactly the disjoint-segment norm, written as the square root of its
squared testing supremum. -/
noncomputable def rho (u : V → ℝ) : ℝ := Real.sqrt (squareSup u)

 theorem zero_mem_testValues (u : V → ℝ) : 0 ∈ testValues u := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, by simp, by simp [Pairwise], ?_⟩
  simp

 theorem TestBound.bddAbove {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
    BddAbove (testValues u) := by
  refine ⟨C, ?_⟩
  rintro r ⟨ι, inst, S, hs, hd, rfl⟩
  exact h ι inst S hs hd

 theorem TestBound.squareSup_le {u : V → ℝ} {C : ℝ} (h : TestBound u C) :
    squareSup u ≤ C := by
  apply csSup_le ⟨0, zero_mem_testValues u⟩
  rintro r ⟨ι, inst, S, hs, hd, rfl⟩
  exact h ι inst S hs hd

 theorem testBound_squareSup {u : V → ℝ} (hu : ∃ C, TestBound u C) :
    TestBound u (squareSup u) := by
  intro ι inst S hs hd
  exact le_csSup hu.choose_spec.bddAbove ⟨ι, inst, S, hs, hd, rfl⟩

 theorem squareSup_nonneg {u : V → ℝ} (hu : ∃ C, TestBound u C) : 0 ≤ squareSup u :=
  (testBound_squareSup hu).nonneg

 theorem rho_nonneg (u : V → ℝ) : 0 ≤ rho u := Real.sqrt_nonneg _

 theorem rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : rho u ^ 2 = squareSup u :=
  Real.sq_sqrt (squareSup_nonneg hu)

 theorem testBound_rho_sq {u : V → ℝ} (hu : ∃ C, TestBound u C) : TestBound u (rho u ^ 2) := by
  rw [rho_sq hu]
  exact testBound_squareSup hu

 theorem rho_le_of_testBound {u : V → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hu : TestBound u (C ^ 2)) : rho u ≤ C :=
  Real.sqrt_le_iff.mpr ⟨hC, hu.squareSup_le⟩

 theorem testBound_of_rho_le {u : V → ℝ} (hu : ∃ C, TestBound u C)
    {C : ℝ} (h : rho u ≤ C) : TestBound u (C ^ 2) :=
  (testBound_rho_sq hu).mono (by nlinarith [rho_nonneg u])

 theorem rho_add_le {u v : V → ℝ} (hu : ∃ C, TestBound u C) (hv : ∃ C, TestBound v C) :
    rho (u + v) ≤ rho u + rho v :=
  rho_le_of_testBound (add_nonneg (rho_nonneg u) (rho_nonneg v))
    ((testBound_rho_sq hu).add (testBound_rho_sq hv) (rho_nonneg u) (rho_nonneg v))

 theorem rho_smul_le {u : V → ℝ} (hu : ∃ C, TestBound u C) (a : ℝ) :
    rho (a • u) ≤ |a| * rho u := by
  apply rho_le_of_testBound (mul_nonneg (abs_nonneg a) (rho_nonneg u))
  have hh := (testBound_rho_sq hu).smul a
  simpa only [mul_pow, sq_abs] using hh

 theorem rho_zero : rho (0 : V → ℝ) = 0 := by
  apply le_antisymm _ (rho_nonneg _)
  apply rho_le_of_testBound (C := 0) (by norm_num)
  simpa using (TestBound.zero : TestBound (0 : V → ℝ) 0)

 theorem rho_smul {u : V → ℝ} (hu : ∃ C, TestBound u C) (a : ℝ) :
    rho (a • u) = |a| * rho u := by
  apply le_antisymm (rho_smul_le hu a)
  by_cases ha : a = 0
  · subst a
    simp [rho_zero]
  · have hb : ∃ C, TestBound (a • u) C := ⟨_, hu.choose_spec.smul a⟩
    have hh := rho_smul_le hb a⁻¹
    rw [inv_smul_smul₀ ha] at hh
    have hpos : 0 < |a| := abs_pos.mpr ha
    have ht := mul_le_mul_of_nonneg_left hh hpos.le
    simpa [abs_inv, ← mul_assoc, ne_of_gt hpos] using ht

 theorem coordinate_le_rho {u : V → ℝ} (hu : ∃ C, TestBound u C) (v : V) :
    |u v| ≤ rho u := by
  have hh := (testBound_rho_sq hu).single (isSegment_singleton v)
  simp only [segSum, sum_singleton] at hh
  exact (sq_le_sq₀ (abs_nonneg _) (rho_nonneg _)).mp (by simpa only [sq_abs] using hh)

noncomputable def l1size (u : V →₀ ℝ) : ℝ := ∑ v ∈ u.support, |u v|

omit [PartialOrder V] in
 theorem l1size_nonneg [PartialOrder V] (u : V →₀ ℝ) : 0 ≤ l1size u :=
  sum_nonneg (fun vertex _ => abs_nonneg (u vertex))

omit [PartialOrder V] in
 theorem finset_abs_sum_le_l1size [PartialOrder V] (u : V →₀ ℝ) (S : Finset V) :
    ∑ v ∈ S, |u v| ≤ l1size u := by
  have he : (∑ v ∈ S ∪ u.support, |u v|) = l1size u := by
    symm
    apply sum_subset subset_union_right
    intro v hv hn
    rw [Finsupp.notMem_support_iff.mp hn, abs_zero]
  rw [← he]
  exact sum_le_sum_of_subset_of_nonneg subset_union_left (fun v hv hn => abs_nonneg _)

 theorem testBound_l1size (u : V →₀ ℝ) : TestBound u (l1size u ^ 2) := by
  intro ι inst S hS hd
  have habs : (∑ i, |segSum u (S i)|) ≤ l1size u := by
    calc
      (∑ i, |segSum u (S i)|) ≤ ∑ i, ∑ v ∈ S i, |u v| :=
        sum_le_sum fun i hi => abs_sum_le_sum_abs _ _
      _ = ∑ v ∈ univ.biUnion S, |u v| :=
        (sum_biUnion (by intro i hi j hj hij; exact hd hij)).symm
      _ ≤ l1size u := finset_abs_sum_le_l1size u _
  have hsq := sum_sq_le_sq_sum_of_nonneg
    (s := (univ : Finset ι)) (f := fun i => |segSum u (S i)|) (fun i hi => abs_nonneg _)
  simp only [sq_abs] at hsq
  have hnonneg : 0 ≤ ∑ i, |segSum u (S i)| := sum_nonneg (fun i hi => abs_nonneg _)
  nlinarith [l1size_nonneg u]

 theorem finsupp_has_testBound (u : V →₀ ℝ) : ∃ C, TestBound u C := ⟨_, testBound_l1size u⟩

 theorem rho_le_l1size (u : V →₀ ℝ) : rho u ≤ l1size u :=
  rho_le_of_testBound (l1size_nonneg u) (testBound_l1size u)

 theorem finsupp_rho_eq_zero (u : V →₀ ℝ) : rho u = 0 ↔ u = 0 := by
  constructor
  · intro h
    ext v
    have hh := coordinate_le_rho (finsupp_has_testBound u) v
    rw [h] at hh
    exact abs_nonpos_iff.mp hh
  · rintro rfl
    exact rho_zero

end SegmentNorm

section SourceNormFidelity
variable {V : Type} [PartialOrder V]

/-- Nonempty finite convex chains are precisely the ancestral intervals.
This rules out a change in the allowed segment tests. -/
theorem nonempty_segment_iff_interval (hF : ForestOrder V) (S : Finset V) :
    IsSegment S ∧ S.Nonempty ↔
      ∃ a b : V, a ≤ b ∧ ∀ v, v ∈ S ↔ a ≤ v ∧ v ≤ b := by
  constructor
  · rintro ⟨hS,hne⟩
    obtain ⟨a,ha,b,hb,h⟩ := hS.endpoints hne
    exact ⟨a,b,(h b).mp hb |>.1,h⟩
  · rintro ⟨a,b,hab,h⟩
    constructor
    · constructor
      · intro v hv w hw
        exact hF v w b ((h v).mp hv).2 ((h w).mp hw).2
      · intro v hv w hw z hvz hzw
        exact (h z).mpr ⟨((h v).mp hv).1.trans hvz, hzw.trans ((h w).mp hw).2⟩
    · exact ⟨a,(h a).mpr ⟨le_rfl,hab⟩⟩

/-- The testing set with m≥1, nonempty
segments, and the square root taken before the supremum. -/
def sourceNormValues (u : V → ℝ) : Set ℝ :=
  {r | ∃ (m : ℕ), 0 < m ∧ ∃ S : Fin m → Finset V,
    (∀ i, IsSegment (S i) ∧ (S i).Nonempty) ∧
    Pairwise (fun i j => Disjoint (S i) (S j)) ∧
    r = Real.sqrt (∑ i, segSum u (S i)^2)}

theorem sourceNormValues_nonempty [Nonempty V] (u : V → ℝ) :
    (sourceNormValues u).Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  refine ⟨_,1,by norm_num,fun _ => {v},?_,?_,rfl⟩
  · intro i
    exact ⟨isSegment_singleton v, by simp⟩
  · intro i j hij
    exact (hij (Subsingleton.elim i j)).elim

theorem sourceNormValues_le_rho {u : V → ℝ} (hu : ∃ C, TestBound u C)
    {r : ℝ} (hr : r ∈ sourceNormValues u) : r ≤ rho u := by
  obtain ⟨m,hm,S,hS,hd,rfl⟩ := hr
  apply Real.sqrt_le_iff.mpr
  exact ⟨rho_nonneg u, testBound_rho_sq hu (Fin m) inferInstance S (fun i => (hS i).1) hd⟩

theorem sourceNormValues_bddAbove {u : V → ℝ} (hu : ∃ C, TestBound u C) :
    BddAbove (sourceNormValues u) :=
  ⟨rho u,fun _ h => sourceNormValues_le_rho hu h⟩

theorem sourceNormValues_sup_nonneg [Nonempty V] {u : V → ℝ}
    (hu : ∃ C, TestBound u C) : 0 ≤ sSup (sourceNormValues u) := by
  obtain ⟨r,hr⟩ := sourceNormValues_nonempty u
  have hr0 : 0 ≤ r := by
    obtain ⟨m,hm,S,hS,hd,rfl⟩ := hr
    exact Real.sqrt_nonneg _
  exact hr0.trans (le_csSup (sourceNormValues_bddAbove hu) hr)

/-- Erasing empty zero tests and enumerating the remaining finite family does
not alter its squared sum. -/
theorem testBound_from_source_sup [Nonempty V] {u : V → ℝ}
    (hu : ∃ C, TestBound u C) : TestBound u (sSup (sourceNormValues u)^2) := by
  classical
  intro ι inst S hS hd
  let I := {i : ι // (S i).Nonempty}
  by_cases hI : Nonempty I
  · let := hI
    let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
    let T : Fin (Fintype.card I) → Finset V := fun i => S (e i).val
    have hT : ∀ i, IsSegment (T i) ∧ (T i).Nonempty := fun i =>
      ⟨hS (e i).val,(e i).property⟩
    have hdT : Pairwise (fun i j => Disjoint (T i) (T j)) := by
      intro i j hij
      exact hd (fun h => hij (e.injective (Subtype.ext h)))
    have hsum : (∑ i, segSum u (T i)^2) = ∑ i, segSum u (S i)^2 := by
      rw [show (∑ i, segSum u (T i)^2) = ∑ i : I, segSum u (S i.val)^2 from
        e.sum_comp (fun i : I => segSum u (S i.val)^2)]
      have hz : (∑ i : {i : ι // ¬(S i).Nonempty}, segSum u (S i.val)^2) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have he : S i.val = ∅ := Finset.not_nonempty_iff_eq_empty.mp i.property
        simp [he]
      have hh := Fintype.sum_subtype_add_sum_subtype (fun i : ι => (S i).Nonempty)
        (fun i => segSum u (S i)^2)
      rw [hz,add_zero] at hh
      exact hh
    have hmem : Real.sqrt (∑ i, segSum u (S i)^2) ∈ sourceNormValues u := by
      refine ⟨Fintype.card I,Fintype.card_pos,T,hT,hdT,?_⟩
      rw [hsum]
    have hle := le_csSup (sourceNormValues_bddAbove hu) hmem
    exact (Real.sqrt_le_iff.mp hle).2
  · have hzero : ∑ i, segSum u (S i)^2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have he : S i = ∅ := Finset.not_nonempty_iff_eq_empty.mp (fun hi => hI ⟨⟨i,hi⟩⟩)
      simp [he]
    rw [hzero]
    exact sq_nonneg _

/-- Equality with the nonempty-segment definition, including the exclusion of empty
segments and zero-sized families and the order of supremum/square root. -/
theorem rho_eq_source_sup [Nonempty V] (u : V →₀ ℝ) :
    rho u = sSup (sourceNormValues u) := by
  have hu := finsupp_has_testBound u
  apply le_antisymm
  · exact rho_le_of_testBound (sourceNormValues_sup_nonneg hu) (testBound_from_source_sup hu)
  · exact csSup_le (sourceNormValues_nonempty u) (fun _ h => sourceNormValues_le_rho hu h)

end SourceNormFidelity

end

end ForestSpace

end OAI
