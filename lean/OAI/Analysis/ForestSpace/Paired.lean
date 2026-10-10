import OAI.Analysis.ForestSpace.FiniteGeometry

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePaired
variable {V : Type} [Fintype V] [PartialOrder V]

noncomputable def gateSigns (f k : V → ℝ) (s : ℝ) (g : V) : ℝ :=
  oppositeSign (segSum f (selectedHead f k s g))

 theorem gateSigns_sq (f k : V → ℝ) (s : ℝ) (g : V) : gateSigns f k s g ^ 2 = 1 :=
  oppositeSign_sq _

noncomputable def correctedTail (H : Set V) (f k : V → ℝ) (s τ : ℝ) : V → ℝ :=
  correction H k (gateSigns f k s) + τ • k

 theorem correctedTail_supported {H : Set V} {f k : V → ℝ}
    (hk : SupportedOn k Hᶜ) (s τ : ℝ) : SupportedOn (correctedTail H f k s τ) Hᶜ := by
  intro v hv
  change correction H k (gateSigns f k s) v + τ * k v = 0
  rw [correction_supported H k (gateSigns f k s) v hv, hk v hv]
  ring

 theorem correctedTail_testBound (hF : ForestOrder V) (H : Set V) (f k : V → ℝ)
    (hk : TestBound k 1) (s τ : ℝ) (hτ : |τ| ≤ 1) :
    TestBound (correctedTail H f k s τ) 4 := by
  have ht : τ ^ 2 ≤ 1 := by
    have := abs_le.mp hτ
    nlinarith [sq_abs τ]
  have hk' : TestBound (τ • k) 1 := (hk.smul τ).mono (by simpa using ht)
  have hc := correction_testBound hF hk (gateSigns_sq f k s) H
  have hh := TestBound.add (A := 1) (B := 1) (by simpa using hc) (by simpa using hk')
    zero_le_one zero_le_one
  convert hh using 1 <;> norm_num [correctedTail]

 theorem correctedTail_at_gate {H : Set V} (hH : IsLowerSet H) {f k : V → ℝ}
    (hk : SupportedOn k Hᶜ) {s τ : ℝ} (hτ : |τ| ≤ 1)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    segSum f (selectedHead f k s g) * segSum (correctedTail H f k s τ) S ≤ 0 ∧
    |segSum (correctedTail H f k s τ) S| ≤ 2 * mass k g := by
  have hd : |τ * segSum k S| ≤ mass k g := by
    rw [abs_mul]
    calc
      |τ| * |segSum k S| ≤ 1 * mass k g :=
        mul_le_mul hτ (tail_sum_le_mass hH hk hS hg hgs) (abs_nonneg _) zero_le_one
      _ = mass k g := one_mul _
  simp only [correctedTail, segSum_add, segSum_smul, correction_sum hS hg hgs, gateSigns]
  exact ⟨oppositeSign_cross hd, oppositeSign_tail_abs (mass_nonneg k g) hd⟩

 theorem gate_charge_le {H : Set V} {k : V → ℝ} {S : Finset V} {g : V}
    (hg : Gate H g) (hgs : g ∈ S) : mass k g ^ 2 ≤ ∑ v ∈ S, gateWeight H k v := by
  have hh := single_le_sum (f := gateWeight H k)
    (fun v hv => gateWeight_nonneg H k v) hgs
  simpa only [gateWeight, ite_eq_left hg] using hh

/-- The local choice of a suffix cut, including empty cuts for inexpensive terms. -/
 theorem segment_cut (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1)
    {S : Finset V} (hS : IsSegment S) :
    ∃ L : Finset V, L ⊆ S.filter (· ∈ H) ∧ IsSegment L ∧
      IsSegment (S.filter (· ∈ H) \ L) ∧
      (segSum f S + s * segSum (correctedTail H f k s τ) S) ^ 2 ≤
        (segSum f S - segSum f L) ^ 2 + segSum f L ^ 2 +
        8 * s ^ 2 * (∑ v ∈ S, gateWeight H k v) +
        s ^ 2 * segSum (correctedTail H f k s τ) S ^ 2 := by
  have hq : 0 ≤ ∑ v ∈ S, gateWeight H k v := sum_nonneg (fun v hv => gateWeight_nonneg H k v)
  have hcost : 0 ≤ 8 * s ^ 2 * (∑ v ∈ S, gateWeight H k v) := by positivity
  by_cases hcross : 0 < segSum f S * segSum (correctedTail H f k s τ) S
  · have hgex : ∃ g ∈ S, Gate H g := by
      by_contra hng
      have hz := cross_zero_of_no_gate hF hH hf (correctedTail_supported (f := f) hk s τ) hS hng
      linarith
    obtain ⟨g, hgs, hg⟩ := hgex
    have hinfo := correctedTail_at_gate (f := f) (s := s) hH hk hτ hS hg hgs
    have hcharge := gate_charge_le (k := k) hg hgs
    by_cases hsmall : |segSum f S| ≤ 2 * s * mass k g
    · refine ⟨∅, empty_subset _, isSegment_empty, by simpa using hS.head H hH, ?_⟩
      have hc := small_cross_bound hs (mass_nonneg k g) hsmall hinfo.2 hcharge
      simp only [segSum_empty, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
      nlinarith
    · have hp : ∃ a ∈ S, a ∈ H := by
        by_contra hn
        have hz := hf.segSum_eq_zero (S := S) (by simpa using hn)
        rw [hz, zero_mul] at hcross
        exact (lt_irrefl 0) hcross
      obtain ⟨a, hag, hhead⟩ := hS.head_eq_before hH hg hgs hp
      have he : segSum f (before a g) = segSum f S := by
        rw [← hhead]
        exact hf.segSum_filter S
      have ha : a ∈ largeStarts f k s g := mem_largeStarts.mpr
        ⟨hag, by rw [he]; exact le_of_lt (lt_of_not_ge hsmall)⟩
      refine ⟨selectedHead f k s g, ?_, selectedHead_segment hF f k s g, ?_, ?_⟩
      · rw [hhead]
        exact selectedHead_subset hF ha
      · rw [hhead]
        exact sdiff_selectedHead_segment (isSegment_before hF a g)
      · have hc := large_cross_bound hs (mass_nonneg k g) hcross hinfo.1
          (selectedHead_large ha) hinfo.2
        nlinarith
  · refine ⟨∅, empty_subset _, isSegment_empty, by simpa using hS.head H hH, ?_⟩
    have hc : 2 * s * (segSum f S * segSum (correctedTail H f k s τ) S) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hcross)
    simp only [segSum_empty, sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero]
    nlinarith

omit [Fintype V] [PartialOrder V] in
/-- All suffix cuts can be charged to one disjoint segment test of the head. -/
 theorem simultaneous_cut_bound [Fintype V] [PartialOrder V] {H : Set V} {f : V → ℝ}
    (hf : SupportedOn f H) (hf₁ : TestBound f 1)
    {ι : Type} [Fintype ι] (S L : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hL : ∀ i, L i ⊆ (S i).filter (· ∈ H))
    (hseg : ∀ i, IsSegment (L i))
    (hdiff : ∀ i, IsSegment ((S i).filter (· ∈ H) \ L i)) :
    (∑ i, ((segSum f (S i) - segSum f (L i)) ^ 2 + segSum f (L i) ^ 2)) ≤ 1 := by
  let P : ι → Finset V := fun i => (S i).filter (· ∈ H)
  let pieces : ι × Bool → Finset V := fun p => if p.2 then L p.1 else P p.1 \ L p.1
  have hpseg : ∀ p, IsSegment (pieces p) := by
    rintro ⟨i, b⟩
    cases b
    · exact hdiff i
    · exact hseg i
  have hpsub : ∀ p, pieces p ⊆ S p.1 := by
    rintro ⟨i, b⟩
    cases b
    · exact sdiff_subset.trans (filter_subset _ _)
    · exact (hL i).trans (filter_subset _ _)
  have hpdis : Pairwise (fun p q => Disjoint (pieces p) (pieces q)) := by
    rintro ⟨i,b⟩ ⟨j,c⟩ hne
    by_cases hij : i = j
    · subst j
      cases b <;> cases c
      · exact (hne rfl).elim
      · exact sdiff_disjoint
      · exact disjoint_sdiff
      · exact (hne rfl).elim
    · exact (hd hij).mono (hpsub (i,b)) (hpsub (j,c))
  have hb := hf₁ (ι × Bool) inferInstance pieces hpseg hpdis
  have he : ∀ i, segSum f (P i \ L i) = segSum f (S i) - segSum f (L i) := by
    intro i
    have ht : segSum f (P i \ L i) + segSum f (L i) = segSum f (P i) := sum_sdiff (hL i)
    have ht' : segSum f (P i) = segSum f (S i) := hf.segSum_filter (S i)
    linarith
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, pieces, Bool.false_eq_true,
    ↓reduceIte, he, add_comm] using hb

/-- The corrected tests have squared norm at most 1+12s², for either sign. -/
 theorem corrected_test_bound (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f k : V → ℝ} (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1)
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : |τ| ≤ 1) :
    TestBound (f + s • correctedTail H f k s τ) (1 + 12 * s ^ 2) := by
  intro ι inst S hS hd
  choose L hL hseg hdiff hlocal using (fun i => segment_cut hF hH hf hk hs hτ (hS i))
  have hhead := simultaneous_cut_bound hf hf₁ S L hd hL hseg hdiff
  have hcharge := gateWeight_family_le hF hk₁ H S hd
  have htail := correctedTail_testBound hF H f k hk₁ s τ hτ ι inst S hS hd
  have hnum := sum_le_sum (s := (univ : Finset ι)) (fun i hi => hlocal i)
  simp only [sum_add_distrib, ← mul_sum] at hnum
  have hcharge' := mul_le_mul_of_nonneg_left hcharge (show 0 ≤ 8 * s ^ 2 by positivity)
  have htail' := mul_le_mul_of_nonneg_left htail (sq_nonneg s)
  simp only [sum_add_distrib] at hhead
  simp only [segSum_add, segSum_smul]
  nlinarith

/-- Finite-support paired extension: the common correction cancels on averaging. -/

 theorem paired_finite_test_correction
    (hF : ForestOrder V) (H : Set V) (hH : IsLowerSet H) (f k : V → ℝ)
    (hf : ∀ v, v ∉ H → f v = 0) (hk : ∀ v, v ∈ H → k v = 0)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1)
    (s : ℝ) (hs : 0 < s) :
    ∃ c : V → ℝ, (∀ v, v ∈ H → c v = 0) ∧ TestBound c 1 ∧
      TestBound (f + s • (c + k)) (1 + 12 * s ^ 2) ∧
      TestBound (f + s • (c - k)) (1 + 12 * s ^ 2) := by
  have hk' : SupportedOn k Hᶜ := by
    intro v hv
    exact hk v (by simpa using hv)
  refine ⟨correction H k (gateSigns f k s), ?_,
    correction_testBound hF hk₁ (gateSigns_sq f k s) H, ?_, ?_⟩
  · intro v hv
    exact correction_supported H k (gateSigns f k s) v (by simpa using hv)
  · have hh := corrected_test_bound hF hH hf hk' hf₁ hk₁ hs.le (τ := 1) (by norm_num)
    simpa only [correctedTail, one_smul] using hh
  · have hh := corrected_test_bound hF hH hf hk' hf₁ hk₁ hs.le (τ := -1) (by norm_num)
    simpa only [correctedTail, neg_one_smul, sub_eq_add_neg] using hh

end FinitePaired

section FiniteRestriction
variable {V : Type} [PartialOrder V]

 theorem forestOrder_subtype (hF : ForestOrder V) (B : Set V) : ForestOrder B := by
  intro a b c hac hbc
  exact hF a b c hac hbc

 theorem IsSegment.subtype {S B : Finset V} (hS : IsSegment S) :
    IsSegment (S.subtype (· ∈ B)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_subtype.mp ha) b (mem_subtype.mp hb)
  · intro a ha b hb c hac hcb
    exact mem_subtype.mpr (hS.2 a (mem_subtype.mp ha) b (mem_subtype.mp hb) c hac hcb)

 theorem IsSegment.image_subtype {B : Finset V} (hB : IsLowerSet (B : Set V))
    {S : Finset B} (hS : IsSegment S) : IsSegment (S.image Subtype.val) := by
  constructor
  · intro a ha b hb
    obtain ⟨a, ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := mem_image.mp hb
    exact hS.1 a ha' b hb'
  · intro a ha b hb c hac hcb
    obtain ⟨a, ha', rfl⟩ := mem_image.mp ha
    obtain ⟨b, hb', rfl⟩ := mem_image.mp hb
    have hcB : c ∈ B := hB hcb b.property
    exact mem_image.mpr ⟨⟨c,hcB⟩, hS.2 a ha' b hb' ⟨c,hcB⟩ hac hcb, rfl⟩

omit [PartialOrder V] in
 theorem segSum_image_subtype [PartialOrder V] {B : Finset V} (u : V → ℝ) (S : Finset B) :
    segSum u (S.image Subtype.val) = segSum (fun v : B => u v) S := by
  exact sum_image (fun a ha b hb hab => Subtype.val_injective hab)

omit [PartialOrder V] in
 theorem segSum_subtype [PartialOrder V] {B S : Finset V} {u : V → ℝ} (hu : SupportedOn u (B : Set V)) :
    segSum (fun v : B => u v) (S.subtype (· ∈ B)) = segSum u S := by
  change (∑ v ∈ S.subtype (· ∈ B), u v) = ∑ v ∈ S, u v
  rw [sum_subtype_eq_sum_filter]
  exact sum_subset (filter_subset _ _) (by
    intro v hv hv'
    exact hu v (by change v ∉ B; simpa only [mem_filter, hv, true_and] using hv'))

 theorem TestBound.restrict_subtype {B : Finset V} (hB : IsLowerSet (B : Set V))
    {u : V → ℝ} {C : ℝ} (hu : TestBound u C) :
    TestBound (fun v : B => u v) C := by
  intro ι inst S hS hd
  have hh := hu ι inst (fun i => (S i).image Subtype.val)
    (fun i => (hS i).image_subtype hB) (by
      intro i j hij
      exact (Finset.disjoint_image Subtype.val_injective).mpr (hd hij))
  simpa only [segSum_image_subtype] using hh

 theorem TestBound.of_restrict {B : Finset V} {u : V → ℝ} {C : ℝ}
    (hu : SupportedOn u (B : Set V)) (hb : TestBound (fun v : B => u v) C) :
    TestBound u C := by
  intro ι inst S hS hd
  have hh := hb ι inst (fun i => (S i).subtype (· ∈ B))
    (fun i => (hS i).subtype) (by
      intro i j hij
      apply disjoint_left.mpr
      intro v hvi hvj
      exact disjoint_left.mp (hd hij) (mem_subtype.mp hvi) (mem_subtype.mp hvj))
  simpa only [segSum_subtype hu] using hh

/-- The finite ancestor assumption ensures that no node inserted between two
supported coordinates is lost when we use a finite test forest. -/
 theorem exists_finite_lower_hull (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (S : Finset V) : ∃ B : Finset V, S ⊆ B ∧ IsLowerSet (B : Set V) := by
  let A : Set V := ⋃ v ∈ (S : Set V), Set.Iic v
  have hA : A.Finite := S.finite_toSet.biUnion (fun v hv => hAnc v)
  refine ⟨hA.toFinset, ?_, ?_⟩
  · intro v hv
    exact hA.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨v,
      Set.mem_iUnion.mpr ⟨hv, le_rfl⟩⟩)
  · intro a b hab hb
    obtain ⟨v,hv,hbv⟩ := Set.mem_iUnion₂.mp (hA.mem_toFinset.mp hb)
    exact hA.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨v,hv,hab.trans hbv⟩)

/-- Extension by zero from a finite lower subforest. -/
noncomputable def finiteExtension (B : Finset V) (u : B → ℝ) : V →₀ ℝ :=
  Finsupp.onFinset B (fun v => if h : v ∈ B then u ⟨v,h⟩ else 0) (by
    intro v hv
    by_contra hn
    exact hv (dite_eq_right hn))

omit [PartialOrder V] in
@[simp] theorem finiteExtension_apply [PartialOrder V] {B : Finset V} (u : B → ℝ) (v : B) :
    finiteExtension B u v = u v := by simp [finiteExtension, v.property]

omit [PartialOrder V] in
 theorem finiteExtension_supported [PartialOrder V] (B : Finset V) (u : B → ℝ) :
    SupportedOn (finiteExtension B u) (B : Set V) := by
  intro v hv
  simp [finiteExtension, show v ∉ B from hv]

 theorem finiteExtension_testBound {B : Finset V} {u : B → ℝ} {C : ℝ}
    (hu : TestBound u C) : TestBound (finiteExtension B u) C := by
  apply TestBound.of_restrict (finiteExtension_supported B u)
  simpa only [finiteExtension_apply] using hu

/-- The finite-support corrected tests on an arbitrary finite-ancestor forest.
No assertion about the full dual having dense finite coordinates is used. -/
 theorem finsupp_paired_correction (hF : ForestOrder V)
    (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (H : Set V) (hH : IsLowerSet H) (f k : V →₀ ℝ)
    (hf : SupportedOn f H) (hk : SupportedOn k Hᶜ)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1) (s : ℝ) (hs : 0 < s) :
    ∃ c : V →₀ ℝ, SupportedOn c Hᶜ ∧ TestBound c 1 ∧
      TestBound (f + s • (c + k)) (1 + 12 * s ^ 2) ∧
      TestBound (f + s • (c - k)) (1 + 12 * s ^ 2) := by
  obtain ⟨B,hB,hBl⟩ := exists_finite_lower_hull hAnc (f.support ∪ k.support)
  have hfB : SupportedOn f (B : Set V) := by
    intro v hv
    by_contra hvf
    exact hv (hB (mem_union_left _ (Finsupp.mem_support_iff.mpr hvf)))
  have hkB : SupportedOn k (B : Set V) := by
    intro v hv
    by_contra hvk
    exact hv (hB (mem_union_right _ (Finsupp.mem_support_iff.mpr hvk)))
  let HB : Set B := {v | (v : V) ∈ H}
  have hHB : IsLowerSet HB := fun _ _ hab hb => hH hab hb
  obtain ⟨c,hcH,hc₁,hcp,hcm⟩ := paired_finite_test_correction
    (V := B) (fun a b c hac hbc => hF a b c hac hbc) HB hHB (fun v : B => f v) (fun v : B => k v)
    (fun v hv => hf v hv) (fun v hv => hk v (by
      exact not_not.mpr hv))
    (hf₁.restrict_subtype hBl) (hk₁.restrict_subtype hBl) s hs
  refine ⟨finiteExtension B c, ?_, finiteExtension_testBound hc₁, ?_, ?_⟩
  · intro v hv
    by_cases hvB : v ∈ B
    · have hh := hcH ⟨v,hvB⟩ (by
        change v ∈ H; simpa only [Set.mem_compl_iff, not_not] using hv)
      simpa [finiteExtension, hvB] using hh
    · exact finiteExtension_supported B c v hvB
  · apply TestBound.of_restrict (B := B)
      (u := (f + s • (finiteExtension B c + k) : V →₀ ℝ))
    · intro v hv
      simp [hfB v hv, hkB v hv, finiteExtension_supported B c v hv]
    · change TestBound (fun v : B => f v + s * (c v + k v)) (1 + 12 * s ^ 2) at hcp
      simpa only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, finiteExtension_apply] using hcp
  · apply TestBound.of_restrict (B := B)
      (u := (f + s • (finiteExtension B c - k) : V →₀ ℝ))
    · intro v hv
      simp [hfB v hv, hkB v hv, finiteExtension_supported B c v hv]
    · change TestBound (fun v : B => f v + s * (c v - k v)) (1 + 12 * s ^ 2) at hcm
      simpa only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_smul, Pi.add_apply,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul, finiteExtension_apply] using hcm

end FiniteRestriction

end

end ForestSpace

end OAI
