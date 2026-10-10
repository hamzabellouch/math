import OAI.Analysis.ForestSpace.Segments

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FiniteGeometry
variable {V : Type} [Fintype V] [PartialOrder V]

/-- The ancestral interval [a,g), ending immediately before g along its path. -/
noncomputable def before (a g : V) : Finset V := by
  classical
  exact univ.filter (fun v => a ≤ v ∧ v < g)

@[simp] theorem mem_before {a g v : V} : v ∈ before a g ↔ a ≤ v ∧ v < g := by
  classical
  simp [before]

 theorem isSegment_before (hF : ForestOrder V) (a g : V) : IsSegment (before a g) := by
  constructor
  · intro v hv w hw
    exact hF v w g (mem_before.mp hv).2.le (mem_before.mp hw).2.le
  · intro v hv w hw z hvz hzw
    exact mem_before.mpr ⟨(mem_before.mp hv).1.trans hvz,
      lt_of_le_of_lt hzw (mem_before.mp hw).2⟩

 theorem before_mono {a b g : V} (hab : a ≤ b) : before b g ⊆ before a g := by
  intro v hv
  exact mem_before.mpr ⟨hab.trans (mem_before.mp hv).1, (mem_before.mp hv).2⟩

 theorem before_subset_head {H : Set V} {g a : V} (hg : Gate H g) :
    ∀ v ∈ before a g, v ∈ H := by
  intro v hv
  exact hg.2 v (mem_before.mp hv).2

 theorem IsSegment.head_eq_before {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S)
    (hp : ∃ a ∈ S, a ∈ H) :
    ∃ a, a < g ∧ S.filter (· ∈ H) = before a g := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hS.endpoints ⟨g, hgs⟩
  have haH : a ∈ H := by
    obtain ⟨w, hw, hwH⟩ := hp
    exact hH ((hab w).mp hw).1 hwH
  have hag : a < g := lt_of_le_of_ne ((hab g).mp hgs).1
    (fun h => hg.1 (h ▸ haH))
  refine ⟨a, hag, ?_⟩
  ext v
  simp only [mem_filter, mem_before]
  constructor
  · rintro ⟨hv, hvH⟩
    refine ⟨((hab v).mp hv).1, ?_⟩
    have hvg : v ≤ g := (hS.1 v hv g hgs).resolve_right (fun h => hg.1 (hH h hvH))
    exact lt_of_le_of_ne hvg (fun he => hg.1 (he ▸ hvH))
  · rintro ⟨hav, hvg⟩
    exact ⟨hS.2 a ha g hgs v hav hvg.le, hg.2 v hvg⟩

/-- Removing a terminal suffix from any segment leaves a segment. -/
 theorem IsSegment.sdiff_before {S : Finset V} (hS : IsSegment S) {a b g : V}
    (hSa : S = before a g) : IsSegment (S \ before b g) := by
  classical
  subst S
  constructor
  · intro v hv w hw
    exact hS.1 v (mem_sdiff.mp hv).1 w (mem_sdiff.mp hw).1
  · intro v hv w hw z hvz hzw
    have hz := hS.2 v (mem_sdiff.mp hv).1 w (mem_sdiff.mp hw).1 z hvz hzw
    refine mem_sdiff.mpr ⟨hz, ?_⟩
    intro hzb
    apply (mem_sdiff.mp hw).2
    exact mem_before.mpr ⟨(mem_before.mp hzb).1.trans hzw,
      (mem_before.mp (mem_sdiff.mp hw).1).2⟩

/-- The closed ancestral interval [g,w]. -/
noncomputable def along (g w : V) : Finset V :=
  univ.filter (fun v => g ≤ v ∧ v ≤ w)

@[simp] theorem mem_along {g w v : V} : v ∈ along g w ↔ g ≤ v ∧ v ≤ w := by
  simp [along]

 theorem isSegment_along (hF : ForestOrder V) (g w : V) : IsSegment (along g w) := by
  constructor
  · intro a ha b hb
    exact hF a b w (mem_along.mp ha).2 (mem_along.mp hb).2
  · intro a ha b hb c hac hcb
    exact mem_along.mpr ⟨(mem_along.mp ha).1.trans hac, hcb.trans (mem_along.mp hb).2⟩

 theorem IsSegment.tail_eq_along {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S) {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    ∃ b, S.filter (· ∉ H) = along g b := by
  obtain ⟨a, ha, b, hb, hab⟩ := hS.endpoints ⟨g, hgs⟩
  refine ⟨b, ?_⟩
  ext v
  simp only [mem_filter, mem_along]
  constructor
  · rintro ⟨hv, hvH⟩
    refine ⟨?_, ((hab v).mp hv).2⟩
    rcases hS.1 g hgs v hv with hgv | hvg
    · exact hgv
    · by_contra hngv
      exact hvH (hg.2 v (lt_of_le_not_ge hvg hngv))
  · rintro ⟨hgv, hvb⟩
    exact ⟨hS.2 g hgs b hb v hgv hvb, fun hv => hg.1 (hH hgv hv)⟩

/-- Maximal initial-segment mass of a test inside the cone at g. -/
noncomputable def mass (k : V → ℝ) (g : V) : ℝ :=
  univ.sup' ⟨g, mem_univ g⟩ (fun w => |segSum k (along g w)|)

 theorem abs_segSum_along_le (k : V → ℝ) (g w : V) :
    |segSum k (along g w)| ≤ mass k g :=
  le_sup' (fun w => |segSum k (along g w)|) (mem_univ w)

 theorem mass_nonneg (k : V → ℝ) (g : V) : 0 ≤ mass k g :=
  (abs_nonneg _).trans (abs_segSum_along_le k g g)

 theorem mass_attained (k : V → ℝ) (g : V) :
    ∃ w, mass k g = |segSum k (along g w)| := by
  obtain ⟨w, hw, he⟩ := exists_mem_eq_sup' (⟨g, mem_univ g⟩ : (univ : Finset V).Nonempty)
    (fun w => |segSum k (along g w)|)
  exact ⟨w, he⟩

 theorem gate_mass_bound (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) : ∑ g : {g // Gate H g}, mass k g ^ 2 ≤ 1 := by
  choose w hw using (fun g : {g // Gate H g} => mass_attained k g)
  have hd : Pairwise (fun g h : {g // Gate H g} => Disjoint (along (g : V) (w g)) (along (h : V) (w h))) := by
    intro g h hne
    apply disjoint_left.mpr
    intro v hvg hvh
    have hcomp := hF g h v (mem_along.mp hvg).1 (mem_along.mp hvh).1
    apply hne
    apply Subtype.ext
    exact hcomp.elim (g.property.eq_of_le h.property) (fun hle => (h.property.eq_of_le g.property hle).symm)
  have hh := hk {g // Gate H g} inferInstance (fun g => along (g : V) (w g))
    (fun g => isSegment_along hF g (w g)) hd
  simpa only [hw, sq_abs] using hh

/-- Square mass at gates, and zero elsewhere. -/
noncomputable def gateWeight (H : Set V) (k : V → ℝ) (g : V) : ℝ :=
  if Gate H g then mass k g ^ 2 else 0

 theorem gateWeight_nonneg (H : Set V) (k : V → ℝ) (g : V) : 0 ≤ gateWeight H k g := by
  unfold gateWeight
  split_ifs <;> positivity

 theorem gateWeight_sum_le (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) : ∑ g, gateWeight H k g ≤ 1 := by
  have he : (∑ g, gateWeight H k g) = ∑ g : {g // Gate H g}, mass k g ^ 2 := by
    rw [← sum_subtype (p := Gate H) (univ.filter (Gate H)) (by simp)
      (fun g => mass k g ^ 2)]
    simp only [gateWeight, sum_filter]
  rw [he]
  exact gate_mass_bound hF hk H

omit [Fintype V] [PartialOrder V] in
 theorem disjoint_sum_le [Fintype V] [PartialOrder V] {ι : Type} [Fintype ι] (S : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (q : V → ℝ) (hq : ∀ v, 0 ≤ q v) :
    (∑ i, ∑ v ∈ S i, q v) ≤ ∑ v, q v := by
  rw [← sum_biUnion (s := univ) (t := S) (by intro i hi j hj hij; exact hd hij)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intro v hv hv'; exact hq v)

 theorem gateWeight_family_le (hF : ForestOrder V) {k : V → ℝ} (hk : TestBound k 1)
    (H : Set V) {ι : Type} [Fintype ι] (S : ι → Finset V)
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    (∑ i, ∑ v ∈ S i, gateWeight H k v) ≤ 1 :=
  (disjoint_sum_le S hd _ (gateWeight_nonneg H k)).trans (gateWeight_sum_le hF hk H)

omit [Fintype V] [PartialOrder V] in
/-- A segment contains at most one coordinate of a gate-supported vector. -/
 theorem sum_gate_supported [Fintype V] [PartialOrder V] {H : Set V} {c : V → ℝ}
    (hc : ∀ v, ¬ Gate H v → c v = 0) {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) : segSum c S = c g := by
  apply sum_eq_single g
  · intro v hv hvg
    apply hc v
    intro hgate
    exact hvg (hS.gate_unique hgate hg hv hgs)
  · exact fun h => (h hgs).elim

noncomputable def correction (H : Set V) (k σ : V → ℝ) (g : V) : ℝ :=
  if Gate H g then σ g * mass k g else 0

 theorem correction_supported (H : Set V) (k σ : V → ℝ) :
    SupportedOn (correction H k σ) Hᶜ := by
  intro v hv
  simp only [Set.mem_compl_iff, not_not] at hv
  exact ite_eq_right (fun hg => hg.1 hv)

 theorem correction_sum {H : Set V} {k σ : V → ℝ} {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) :
    segSum (correction H k σ) S = σ g * mass k g := by
  rw [sum_gate_supported (c := correction H k σ) (fun v hv => ite_eq_right hv) hS hg hgs]
  exact ite_eq_left hg

 theorem correction_segment_sq {H : Set V} {k σ : V → ℝ} (hσ : ∀ v, σ v ^ 2 = 1)
    {S : Finset V} (hS : IsSegment S) :
    segSum (correction H k σ) S ^ 2 = ∑ v ∈ S, gateWeight H k v := by
  by_cases h : ∃ g ∈ S, Gate H g
  · obtain ⟨g, hgs, hg⟩ := h
    rw [correction_sum hS hg hgs, mul_pow, hσ, one_mul]
    symm
    calc
      (∑ v ∈ S, gateWeight H k v) = gateWeight H k g := by
        apply sum_eq_single g
        · intro v hv hvg
          exact ite_eq_right (fun hgate => hvg (hS.gate_unique hgate hg hv hgs))
        · exact fun hn => (hn hgs).elim
      _ = mass k g ^ 2 := ite_eq_left hg
  · have hz : segSum (correction H k σ) S = 0 := by
      apply sum_eq_zero
      intro v hv
      exact ite_eq_right (fun hg => h ⟨v, hv, hg⟩)
    rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    symm
    apply sum_eq_zero
    intro v hv
    exact ite_eq_right (fun hg => h ⟨v, hv, hg⟩)

 theorem correction_testBound (hF : ForestOrder V) {k σ : V → ℝ} (hk : TestBound k 1)
    (hσ : ∀ v, σ v ^ 2 = 1) (H : Set V) : TestBound (correction H k σ) 1 := by
  intro ι inst S hS hd
  simp_rw [correction_segment_sq hσ (hS _)]
  exact gateWeight_family_le hF hk H S hd

 theorem tail_sum_le_mass {H : Set V} (hH : IsLowerSet H) {k : V → ℝ}
    (hk : SupportedOn k Hᶜ) {S : Finset V} (hS : IsSegment S)
    {g : V} (hg : Gate H g) (hgs : g ∈ S) : |segSum k S| ≤ mass k g := by
  obtain ⟨b, hb⟩ := hS.tail_eq_along hH hg hgs
  have he := hk.segSum_filter S
  simp only [Set.mem_compl_iff] at he
  rw [← he, hb]
  exact abs_segSum_along_le k g b

/-- Candidate starts of suffixes whose head sum reaches the gate threshold. -/
noncomputable def largeStarts (f k : V → ℝ) (s : ℝ) (g : V) : Finset V :=
  univ.filter (fun a => a < g ∧ 2 * s * mass k g ≤ |segSum f (before a g)|)

@[simp] theorem mem_largeStarts {f k : V → ℝ} {s : ℝ} {g a : V} :
    a ∈ largeStarts f k s g ↔ a < g ∧ 2 * s * mass k g ≤ |segSum f (before a g)| := by
  simp [largeStarts]

noncomputable def selectedStart (f k : V → ℝ) (s : ℝ) (g : V)
    (h : (largeStarts f k s g).Nonempty) : V :=
  Classical.choose ((largeStarts f k s g).exists_maximal h)

 theorem selectedStart_spec (f k : V → ℝ) (s : ℝ) (g : V)
    (h : (largeStarts f k s g).Nonempty) :
    Maximal (· ∈ largeStarts f k s g) (selectedStart f k s g h) :=
  Classical.choose_spec ((largeStarts f k s g).exists_maximal h)

noncomputable def selectedHead (f k : V → ℝ) (s : ℝ) (g : V) : Finset V :=
  if h : (largeStarts f k s g).Nonempty then before (selectedStart f k s g h) g else ∅

 theorem selectedHead_segment (hF : ForestOrder V) (f k : V → ℝ) (s : ℝ) (g : V) :
    IsSegment (selectedHead f k s g) := by
  unfold selectedHead
  split_ifs
  · exact isSegment_before hF _ _
  · exact isSegment_empty

 theorem selectedHead_subset (hF : ForestOrder V) {f k : V → ℝ} {s : ℝ} {a g : V}
    (ha : a ∈ largeStarts f k s g) : selectedHead f k s g ⊆ before a g := by
  have hne : (largeStarts f k s g).Nonempty := ⟨a, ha⟩
  rw [selectedHead, dite_eq_left hne]
  apply before_mono
  have hb := selectedStart_spec f k s g hne
  exact (hF a (selectedStart f k s g hne) g
    (mem_largeStarts.mp ha).1.le (mem_largeStarts.mp hb.1).1.le).elim id (hb.2 ha)

 theorem selectedHead_large {f k : V → ℝ} {s : ℝ} {a g : V}
    (ha : a ∈ largeStarts f k s g) :
    2 * s * mass k g ≤ |segSum f (selectedHead f k s g)| := by
  have hne : (largeStarts f k s g).Nonempty := ⟨a, ha⟩
  rw [selectedHead, dite_eq_left hne]
  exact (mem_largeStarts.mp (selectedStart_spec f k s g hne).1).2

 theorem sdiff_selectedHead_segment {f k : V → ℝ} {s : ℝ} {a g : V}
    (hS : IsSegment (before a g)) : IsSegment (before a g \ selectedHead f k s g) := by
  unfold selectedHead
  split_ifs
  · exact hS.sdiff_before rfl
  · simpa using hS

end FiniteGeometry

section CrossTermAlgebra

/-- Opposite sign for the selected head sum; at zero either sign is harmless. -/
def oppositeSign (r : ℝ) : ℝ := if r < 0 then 1 else -1

 theorem oppositeSign_sq (r : ℝ) : oppositeSign r ^ 2 = 1 := by
  unfold oppositeSign
  split_ifs <;> norm_num

 theorem abs_oppositeSign (r : ℝ) : |oppositeSign r| = 1 := by
  unfold oppositeSign
  split_ifs <;> norm_num

 theorem oppositeSign_cross {r m d : ℝ} (hd : |d| ≤ m) :
    r * (oppositeSign r * m + d) ≤ 0 := by
  have hd' := abs_le.mp hd
  unfold oppositeSign
  split_ifs with hr
  · exact mul_nonpos_of_nonpos_of_nonneg hr.le (by linarith)
  · exact mul_nonpos_of_nonneg_of_nonpos (le_of_not_gt hr) (by linarith)

 theorem oppositeSign_tail_abs {r m d : ℝ} (hm : 0 ≤ m) (hd : |d| ≤ m) :
    |oppositeSign r * m + d| ≤ 2 * m := by
  calc
    |oppositeSign r * m + d| ≤ |oppositeSign r * m| + |d| := abs_add_le _ _
    _ ≤ m + m := by rw [abs_mul, abs_oppositeSign, abs_of_nonneg hm, one_mul]; linarith
    _ = 2 * m := by ring

 theorem small_cross_bound {a b s m q : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m)
    (ha : |a| ≤ 2 * s * m) (hb : |b| ≤ 2 * m) (hq : m ^ 2 ≤ q) :
    2 * s * a * b ≤ 8 * s ^ 2 * q := by
  have hab : a * b ≤ (2 * s * m) * (2 * m) :=
    (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) (by positivity))
  have h₁ := mul_le_mul_of_nonneg_left hab (show 0 ≤ 2 * s by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hq (show 0 ≤ 8 * s ^ 2 by positivity)
  nlinarith

 theorem cross_sign {a b r : ℝ} (hab : 0 < a * b) (hrb : r * b ≤ 0) : a * r ≤ 0 := by
  rcases lt_or_ge b 0 with hb | hb
  · have ha : a < 0 := (mul_pos_iff.mp hab).resolve_left (fun hh => not_lt_of_ge hb.le hh.2)
      |>.1
    have hr : 0 ≤ r := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hr
  · have hb' : 0 < b := lt_of_le_of_ne hb (by intro h; subst b; simp at hab)
    have ha : 0 < a := (mul_pos_iff.mp hab).resolve_right (fun hh => not_lt_of_ge hb hh.2)
      |>.1
    have hr : r ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hr

/-- A large positive cross term is paid for by splitting off the selected suffix. -/
 theorem large_cross_bound {a b r s m : ℝ} (hs : 0 ≤ s) (hm : 0 ≤ m)
    (hab : 0 < a * b) (hrb : r * b ≤ 0) (hr : 2 * s * m ≤ |r|)
    (hb : |b| ≤ 2 * m) :
    2 * s * a * b ≤ (a - r) ^ 2 + r ^ 2 - a ^ 2 := by
  have har := cross_sign hab hrb
  have h₁ : a * b ≤ |a| * (2 * m) :=
    (le_abs_self _).trans (by
      rw [abs_mul, mul_comm |a| |b|, mul_comm |a| (2 * m)]
      exact mul_le_mul hb le_rfl (abs_nonneg a) (mul_nonneg (by norm_num) hm))
  have h₂ := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 2 * s by positivity)
  have h₃ := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2 * |a| by positivity)
  have he : |a| * |r| = -(a * r) := by rw [← abs_mul, abs_of_nonpos har]
  nlinarith [sq_nonneg r]

end CrossTermAlgebra

end

end ForestSpace

end OAI
