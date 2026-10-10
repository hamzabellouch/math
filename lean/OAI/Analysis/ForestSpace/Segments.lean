import Mathlib

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Every ancestral cone is a chain, the order-theoretic forest condition. -/
def ForestOrder (V : Type) [PartialOrder V] : Prop :=
  ∀ a b c : V, a ≤ c → b ≤ c → a ≤ b ∨ b ≤ a

/-- A finite, order-convex chain. The empty chain is a harmless zero test. -/
def IsSegment {V : Type} [PartialOrder V] (S : Finset V) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a ≤ b ∨ b ≤ a) ∧
  (∀ a ∈ S, ∀ b ∈ S, ∀ c, a ≤ c → c ≤ b → c ∈ S)

/-- The sum of coordinates over a segment. -/
def segSum {V : Type} (u : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, u v

/-- Squared bound on every disjoint family of segment tests. -/
def TestBound {V : Type} [PartialOrder V] (u : V → ℝ) (C : ℝ) : Prop :=
  ∀ (ι : Type) (_ : Fintype ι) (S : ι → Finset V),
    (∀ i, IsSegment (S i)) → Pairwise (fun i j => Disjoint (S i) (S j)) →
    ∑ i, segSum u (S i) ^ 2 ≤ C

section Basic
variable {V : Type} [PartialOrder V]

@[simp] theorem isSegment_empty : IsSegment (∅ : Finset V) := by
  simp [IsSegment]

@[simp] theorem isSegment_singleton (v : V) : IsSegment ({v} : Finset V) := by
  constructor
  · intro a ha b hb
    simp only [mem_singleton] at ha hb
    subst a
    subst b
    exact Or.inl le_rfl
  · intro a ha b hb c hac hcb
    simp only [mem_singleton] at ha hb ⊢
    subst a
    subst b
    exact le_antisymm hcb hac

omit [PartialOrder V] in
@[simp] theorem segSum_empty [PartialOrder V] (u : V → ℝ) : segSum u ∅ = 0 := by simp [segSum]
omit [PartialOrder V] in
@[simp] theorem segSum_zero [PartialOrder V] (S : Finset V) : segSum (0 : V → ℝ) S = 0 := by
  simp [segSum]
omit [PartialOrder V] in
@[simp] theorem segSum_add [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
    segSum (u + v) S = segSum u S + segSum v S := by
  simp [segSum, Finset.sum_add_distrib]
omit [PartialOrder V] in
@[simp] theorem segSum_sub [PartialOrder V] (u v : V → ℝ) (S : Finset V) :
    segSum (u - v) S = segSum u S - segSum v S := by
  simp [segSum, Finset.sum_sub_distrib]
omit [PartialOrder V] in
@[simp] theorem segSum_smul [PartialOrder V] (a : ℝ) (u : V → ℝ) (S : Finset V) :
    segSum (a • u) S = a * segSum u S := by
  simp [segSum, Finset.mul_sum]

 theorem TestBound.mono {u : V → ℝ} {C D : ℝ} (h : TestBound u C) (hCD : C ≤ D) :
    TestBound u D := fun ι inst S hs hd => (h ι inst S hs hd).trans hCD

 theorem TestBound.nonneg {u : V → ℝ} {C : ℝ} (h : TestBound u C) : 0 ≤ C := by
  simpa using h PEmpty inferInstance PEmpty.elim (by simp) (by simp [Pairwise])

 theorem TestBound.single {u : V → ℝ} {C : ℝ} (h : TestBound u C)
    {S : Finset V} (hS : IsSegment S) : segSum u S ^ 2 ≤ C := by
  simpa using h Unit inferInstance (fun _ => S) (fun _ => hS)
    (by simp [Pairwise])

 theorem TestBound.zero : TestBound (0 : V → ℝ) 0 := by
  intro ι inst S hS hd
  simp

 theorem TestBound.smul {u : V → ℝ} {C : ℝ} (h : TestBound u C) (a : ℝ) :
    TestBound (a • u) (a ^ 2 * C) := by
  intro ι inst S hS hd
  have hh := mul_le_mul_of_nonneg_left (h ι inst S hS hd) (sq_nonneg a)
  simpa only [segSum_smul, mul_pow, Finset.mul_sum] using hh

 theorem TestBound.add {u v : V → ℝ} {A B : ℝ}
    (hu : TestBound u (A ^ 2)) (hv : TestBound v (B ^ 2))
    (hA : 0 ≤ A) (hB : 0 ≤ B) : TestBound (u + v) ((A + B) ^ 2) := by
  intro ι inst S hS hd
  have h₁ := hu ι inst S hS hd
  have h₂ := hv ι inst S hS hd
  have hc := Real.sum_mul_le_sqrt_mul_sqrt (univ : Finset ι)
    (fun i => segSum u (S i)) (fun i => segSum v (S i))
  have hs₁ : Real.sqrt (∑ i, segSum u (S i) ^ 2) ≤ A :=
    (Real.sqrt_le_iff).2 ⟨hA, h₁⟩
  have hs₂ : Real.sqrt (∑ i, segSum v (S i) ^ 2) ≤ B :=
    (Real.sqrt_le_iff).2 ⟨hB, h₂⟩
  have hc' : ∑ i, segSum u (S i) * segSum v (S i) ≤ A * B :=
    hc.trans (mul_le_mul hs₁ hs₂ (Real.sqrt_nonneg _) hA)
  have he : (∑ i, segSum (u + v) (S i) ^ 2) =
      (∑ i, segSum u (S i) ^ 2) + 2 * (∑ i, segSum u (S i) * segSum v (S i)) +
      (∑ i, segSum v (S i) ^ 2) := by
    simp only [segSum_add, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  nlinarith

/-- Cutting a segment by an ancestral set produces another segment. -/
 theorem IsSegment.head {S : Finset V} (hS : IsSegment S) (H : Set V)
    (hH : IsLowerSet H) [DecidablePred (· ∈ H)] :
    IsSegment (S.filter (· ∈ H)) := by
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  · intro a ha b hb c hac hcb
    exact mem_filter.mpr ⟨hS.2 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c hac hcb,
      hH hcb (mem_filter.mp hb).2⟩

 theorem IsSegment.tail {S : Finset V} (hS : IsSegment S) (H : Set V)
    (hH : IsLowerSet H) [DecidablePred (· ∈ H)] :
    IsSegment (S.filter (· ∉ H)) := by
  classical
  constructor
  · intro a ha b hb
    exact hS.1 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1
  · intro a ha b hb c hac hcb
    exact mem_filter.mpr ⟨hS.2 a (mem_filter.mp ha).1 b (mem_filter.mp hb).1 c hac hcb,
      fun hc => (mem_filter.mp ha).2 (hH hac hc)⟩

 theorem TestBound.restrict {u : V → ℝ} {C : ℝ} (hu : TestBound u C)
    (H : Set V) (hH : IsLowerSet H) : TestBound (H.indicator u) C := by
  classical
  intro ι inst S hS hd
  have h := hu ι inst (fun i => (S i).filter (· ∈ H))
    (fun i => (hS i).head H hH)
    (fun i j hij => (hd hij).mono (filter_subset _ _) (filter_subset _ _))
  simpa [segSum, Finset.sum_filter, Set.indicator_apply] using h

 theorem TestBound.restrict_compl {u : V → ℝ} {C : ℝ} (hu : TestBound u C)
    (H : Set V) (hH : IsLowerSet H) : TestBound (Hᶜ.indicator u) C := by
  classical
  intro ι inst S hS hd
  have h := hu ι inst (fun i => (S i).filter (· ∉ H))
    (fun i => (hS i).tail H hH)
    (fun i j hij => (hd hij).mono (filter_subset _ _) (filter_subset _ _))
  simpa [segSum, Finset.sum_filter, Set.indicator_apply] using h

end Basic

section Geometry
variable {V : Type} [PartialOrder V]

 theorem IsSegment.endpoints {S : Finset V} (hS : IsSegment S) (hne : S.Nonempty) :
    ∃ a ∈ S, ∃ b ∈ S, ∀ v, v ∈ S ↔ a ≤ v ∧ v ≤ b := by
  obtain ⟨a, ha, hamin⟩ := S.exists_minimal hne
  obtain ⟨b, hb, hbmax⟩ := S.exists_maximal hne
  refine ⟨a, ha, b, hb, ?_⟩
  intro v
  constructor
  · intro hv
    exact ⟨(hS.1 a ha v hv).elim id (hamin hv),
      (hS.1 v hv b hb).elim id (hbmax hv)⟩
  · rintro ⟨hav, hvb⟩
    exact hS.2 a ha b hb v hav hvb

/-- A first vertex outside an ancestral set (including unattached roots). -/
def Gate (H : Set V) (g : V) : Prop := g ∉ H ∧ ∀ v, v < g → v ∈ H

 theorem Gate.eq_of_le {H : Set V} {g h : V} (hg : Gate H g) (hh : Gate H h)
    (hgh : g ≤ h) : g = h := by
  by_contra hne
  exact hg.1 (hh.2 g (lt_of_le_of_ne hgh hne))

 theorem IsSegment.gate_unique {H : Set V} {S : Finset V} (hS : IsSegment S)
    {g h : V} (hg : Gate H g) (hh : Gate H h) (hgs : g ∈ S) (hhs : h ∈ S) : g = h := by
  rcases hS.1 g hgs h hhs with hgh | hhg
  · exact hg.eq_of_le hh hgh
  · exact (hh.eq_of_le hg hhg).symm

 theorem IsSegment.exists_gate (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {S : Finset V} (hS : IsSegment S)
    (hp : ∃ a ∈ S, a ∈ H) (hq : ∃ b ∈ S, b ∉ H) :
    ∃ g ∈ S, Gate H g := by
  classical
  obtain ⟨a, ha, haH⟩ := hp
  let T := S.filter (· ∉ H)
  have hne : T.Nonempty := by
    obtain ⟨b, hb, hbH⟩ := hq
    exact ⟨b, mem_filter.mpr ⟨hb, hbH⟩⟩
  obtain ⟨g, hg, hgmin⟩ := T.exists_minimal hne
  have hgs : g ∈ S := (mem_filter.mp hg).1
  have hgH : g ∉ H := (mem_filter.mp hg).2
  have hag : a ≤ g := (hS.1 a ha g hgs).resolve_right (fun h => hgH (hH h haH))
  refine ⟨g, hgs, hgH, ?_⟩
  intro v hvg
  rcases hF v a g hvg.le hag with hva | hav
  · exact hH hva haH
  · by_contra hvH
    have hvm : v ∈ T := mem_filter.mpr ⟨hS.2 a ha g hgs v hav hvg.le, hvH⟩
    exact (not_le_of_gt hvg) (hgmin hvm hvg.le)

/-- A coordinate vector supported on a specified set. -/
def SupportedOn (u : V → ℝ) (H : Set V) : Prop := ∀ v, v ∉ H → u v = 0

omit [PartialOrder V] in
 theorem SupportedOn.segSum_filter [PartialOrder V] {u : V → ℝ} {H : Set V} (hu : SupportedOn u H)
    (S : Finset V) : segSum u (S.filter (· ∈ H)) = segSum u S := by
  classical
  simp only [segSum, Finset.sum_filter]
  apply sum_congr rfl
  intro v hv
  split_ifs with hh
  · rfl
  · exact (hu v hh).symm

omit [PartialOrder V] in
 theorem SupportedOn.segSum_eq_zero [PartialOrder V] {u : V → ℝ} {H : Set V} (hu : SupportedOn u H)
    {S : Finset V} (hS : ∀ v ∈ S, v ∉ H) : segSum u S = 0 := by
  exact sum_eq_zero fun v hv => hu v (hS v hv)

 theorem cross_zero_of_no_gate (hF : ForestOrder V) {H : Set V} (hH : IsLowerSet H)
    {f v : V → ℝ} (hf : SupportedOn f H) (hv : SupportedOn v Hᶜ)
    {S : Finset V} (hS : IsSegment S) (hg : ¬∃ g ∈ S, Gate H g) :
    segSum f S * segSum v S = 0 := by
  by_cases hp : ∃ a ∈ S, a ∈ H
  · have hq : ∀ b ∈ S, b ∈ H := by
      intro b hb
      by_contra hbH
      exact hg (hS.exists_gate hF hH hp ⟨b, hb, hbH⟩)
    have hz : segSum v S = 0 := hv.segSum_eq_zero (by simpa using hq)
    rw [hz, mul_zero]
  · have hz : segSum f S = 0 := hf.segSum_eq_zero (by simpa using hp)
    rw [hz, zero_mul]

end Geometry

end

end ForestSpace

end OAI
