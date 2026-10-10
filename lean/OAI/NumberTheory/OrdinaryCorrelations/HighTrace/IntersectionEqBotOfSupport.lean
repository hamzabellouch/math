import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.TwoTermBinomial

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.SourceCylinder
variable {ι : Type*} [Fintype ι] {Ω : ι → Type*} [∀ p, Fintype (Ω p)]
local instance : DecidableEq ι := Classical.decEq _
local instance (E : Finset (Cylinder Ω)) : DecidableEq (Intersection E) := Classical.decEq _
local instance (E : Finset (Cylinder Ω)) : DecidableLE (Intersection E) := Classical.decRel _
local instance (E : Finset (Cylinder Ω)) : DecidableLT (Intersection E) := Classical.decRel _
local instance (E : Finset (Cylinder Ω)) : LocallyFiniteOrder (Intersection E) :=
  Fintype.toLocallyFiniteOrder

omit [∀ prime, Fintype (Ω prime)] in
lemma intersection_eq_bot_of_support_empty {E : Finset (Cylinder Ω)} {I : Intersection E}
    (h : I.val.support = ∅) : I = ⊥ :=
  Subtype.ext ((Cylinder.eq_bot_iff I.val).mpr h)

lemma coefficient_support_one {E : Finset (Cylinder Ω)} {I : Intersection E}
    (hcard : I.val.support.card = 1) : coefficient E I = -1 := by
  classical
  have hI : I ≠ ⊥ := by
    intro h; subst I
    have hb : (⊥ : Intersection E).val = ⊥ := rfl
    simp [hb] at hcard
  have hinter : Finset.Ico (⊥ : Intersection E) I = {⊥} := by
    ext J
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨_,hJ⟩
      have hjc := Finset.card_lt_card (Cylinder.support_ssubset hJ)
      exact intersection_eq_bot_of_support_empty (Finset.card_eq_zero.mp (by omega))
    · rintro rfl
      exact ⟨le_rfl, bot_lt_iff_ne_bot.mpr hI⟩
  rw [coefficient, IncidenceAlgebra.mu_eq_neg_sum_Ico_of_ne (Ne.symm hI), hinter]
  simp

lemma coefficient_support_bound (E : Finset (Cylinder Ω)) (I : Intersection E) :
    (coefficient E I).natAbs ≤ max 1 (I.val.support.card ^ (I.val.support.card+1)) := by
  by_cases h0 : I.val.support.card = 0
  · have hI := intersection_eq_bot_of_support_empty (Finset.card_eq_zero.mp h0)
    subst I
    simp [coefficient, show (⊥ : Intersection E).val = ⊥ from rfl]
  by_cases h1 : I.val.support.card = 1
  · rw [coefficient_support_one h1, h1]
    norm_num
  · exact (coefficient_crude E I).trans
      ((factorial_power_bound _ (by omega)).trans (le_max_right _ _))

lemma max_power_mono : Monotone (fun m : ℕ => max 1 (m ^ (m+1))) := by
  intro m n hmn
  apply max_le_max le_rfl
  by_cases hn : n = 0
  · have hm : m = 0 := by omega
    simp [hn,hm]
  · exact (Nat.pow_le_pow_left hmn _).trans (Nat.pow_le_pow_right (by omega) (by omega))

namespace Cylinder

omit [∀ prime, Fintype (Ω prime)]

def on (x : ∀ p, Ω p) (S : Finset ι) : Cylinder Ω :=
  ⟨fun p => if p ∈ S then some (x p) else none⟩

@[simp] lemma on_support (x : ∀ p, Ω p) (S : Finset ι) : (on x S).support = S := by
  ext p
  simp only [mem_support, on]
  by_cases hp : p ∈ S <;> simp [hp]

omit [Fintype ι] in
@[simp] lemma on_holds (x : ∀ p, Ω p) (S : Finset ι) : (on x S).Holds x := by
  intro p a hp
  simp only [on] at hp
  split_ifs at hp with h
  · exact Option.some.inj hp

lemma le_on {c : Cylinder Ω} {x : ∀ p, Ω p} {S : Finset ι}
    (hx : c.Holds x) (hS : c.support ⊆ S) : c ≤ on x S := by
  intro p a hp
  have hmem := hS ((mem_support c p).mpr ⟨a,hp⟩)
  simp [on,hmem,hx p a hp]

lemma on_le {c : Cylinder Ω} {x : ∀ p, Ω p} {S : Finset ι}
    (hx : c.Holds x) (hS : S ⊆ c.support) : on x S ≤ c := by
  intro p a hp
  have hpmem : p ∈ S := by
    by_contra hh
    simp [on,hh] at hp
  obtain ⟨b,hb⟩ := (mem_support c p).mp (hS hpmem)
  have hab : x p = a := by simpa [on,hpmem] using hp
  have hxpb := hx p b hb
  have : a = b := hab.symm.trans hxpb
  simpa [this] using hb

lemma generates_on (A : Finset (Cylinder Ω)) (x : ∀ p, Ω p)
    (hx : ∀e ∈ A, e.Holds x) : Generates A (on x (A.biUnion support)) := by
  classical
  constructor
  · intro e he
    exact le_on (hx e he) (fun p hp => Finset.mem_biUnion.mpr ⟨e,he,hp⟩)
  · intro p hp
    rw [on_support] at hp
    exact Finset.mem_biUnion.mp hp

end Cylinder

def active (E : Finset (Cylinder Ω)) (x : ∀ p, Ω p) : Finset (Cylinder Ω) := by
  classical
  exact E.filter (fun e => e.Holds x)

def atPoint (E : Finset (Cylinder Ω)) (x : ∀ p, Ω p) : Intersection E :=
  ⟨Cylinder.on x ((active E x).biUnion Cylinder.support), active E x,
    by classical exact Finset.filter_subset _ _,
    Cylinder.generates_on _ _ (by classical intro e he; exact (Finset.mem_filter.mp he).2)⟩

omit [∀ prime, Fintype (Ω prime)] in
lemma atPoint_holds (E : Finset (Cylinder Ω)) (x : ∀ p, Ω p) : (atPoint E x).val.Holds x :=
  Cylinder.on_holds _ _

omit [∀ prime, Fintype (Ω prime)] in
lemma holds_iff_le_atPoint (E : Finset (Cylinder Ω)) (I : Intersection E) (x : ∀ p, Ω p) :
    I.val.Holds x ↔ I ≤ atPoint E x := by
  classical
  constructor
  · intro hx
    obtain ⟨A,hAE,hgen⟩ := I.property
    exact Cylinder.generates_le hgen (fun e he =>
      (Cylinder.generates_on (active E x) x
        (by intro f hf; exact (Finset.mem_filter.mp hf).2)).1 e
        (Finset.mem_filter.mpr ⟨hAE he,Cylinder.holds_mono (hgen.1 e he) hx⟩))
  · exact fun h => Cylinder.holds_mono h (atPoint_holds E x)

omit [∀ prime, Fintype (Ω prime)] in
lemma atPoint_bot_iff (E : Finset (Cylinder Ω)) (hproper : ∀e ∈ E, e ≠ ⊥)
    (x : ∀ p, Ω p) : atPoint E x = ⊥ ↔ ∀e ∈ E, ¬e.Holds x := by
  classical
  constructor
  · intro h e he hx
    have hle : e ≤ (atPoint E x).val :=
      (Cylinder.generates_on (active E x) x
        (by intro f hf; exact (Finset.mem_filter.mp hf).2)).1 e
        (Finset.mem_filter.mpr ⟨he,hx⟩)
    rw [h] at hle
    exact hproper e he (le_antisymm hle bot_le)
  · intro h
    apply intersection_eq_bot_of_support_empty
    change (Cylinder.on x ((active E x).biUnion Cylinder.support)).support = ∅
    rw [Cylinder.on_support]
    have hempty : active E x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      exact h e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
    simp [hempty]

attribute [local instance] Classical.propDecidable

lemma full_sum_holds (E : Finset (Cylinder Ω)) (hproper : ∀e ∈ E, e ≠ ⊥)
    (x : ∀ p, Ω p) :
    (∑ I : Intersection E, if I.val.Holds x then coefficient E I else 0) = avoidance E x := by
  classical
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun I : Intersection E => I.val.Holds x) =
      Finset.Icc ⊥ (atPoint E x) := by
    ext I
    simp [holds_iff_le_atPoint]
  rw [hfilter]
  change (∑ I ∈ Finset.Icc ⊥ (atPoint E x), IncidenceAlgebra.mu ℤ ⊥ I) = _
  rw [IncidenceAlgebra.sum_Icc_mu_right]
  simp only [avoidance]
  congr 1
  exact propext (by rw [eq_comm, atPoint_bot_iff E hproper x])

end OrdinaryCorrelations.SourceCylinder

end

end OAI
