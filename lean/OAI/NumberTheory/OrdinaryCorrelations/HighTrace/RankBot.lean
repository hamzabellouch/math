import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.IntersectionEqBotOfSupport

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
attribute [local instance] Classical.propDecidable

lemma rank_bot (E : Finset (Cylinder Ω)) : Cylinder.rank E ⊥ = 0 := by
  classical
  apply Nat.le_zero.mp
  apply Finset.sup_le
  intro A hA
  have hle := (Finset.mem_filter.mp hA).2.1
  have hp := (Finset.mem_filter.mp hA).2.2
  have hempty : A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨p,hpe,_⟩ := hp e he
    have hebot : e = ⊥ := le_antisymm (hle e he) bot_le
    simp [hebot] at hpe
  simp [hempty]

lemma witness_dominating (E : Finset (Cylinder Ω)) (t : ℕ) (x : ∀p, Ω p)
    (I : Intersection E) (hI : I.val.Holds x) (hrI : Cylinder.rank E I.val < t)
    (hhigh : t ≤ Cylinder.rank E (atPoint E x).val) :
    ∃ J ∈ witnesses E t, J.val.Holds x ∧ I ≤ J := by
  classical
  let S := Finset.univ.filter (fun K : Intersection E =>
    I ≤ K ∧ K ≤ atPoint E x ∧ Cylinder.rank E K.val < t)
  have hIS : I ∈ S := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,le_rfl,(holds_iff_le_atPoint E I x).mp hI,hrI⟩
  obtain ⟨K,hKS,hmax⟩ := Finset.exists_max_image S
    (fun K : Intersection E => K.val.support.card) ⟨I,hIS⟩
  obtain ⟨hIK,hKx,hrK⟩ := (Finset.mem_filter.mp hKS).2
  have hext : ∃ e ∈ active E x, ¬e ≤ K.val := by
    by_contra hh
    push Not at hh
    have hJle : (atPoint E x).val ≤ K.val :=
      Cylinder.generates_le (Cylinder.generates_on (active E x) x
        (fun e he => (Finset.mem_filter.mp he).2)) hh
    have hm := Cylinder.rank_mono E hJle
    omega
  obtain ⟨e,he,heK⟩ := hext
  obtain ⟨A,hAE,hcard,hgenA⟩ := Cylinder.minimal_generators E K.val K.property
  let B := insert e A
  have hBE : B ⊆ E := by
    intro f hf
    obtain rfl | hf := Finset.mem_insert.mp hf
    · exact (Finset.mem_filter.mp he).1
    · exact hAE hf
  have hBx : ∀ f ∈ B, f.Holds x := by
    intro f hf
    obtain rfl | hf := Finset.mem_insert.mp hf
    · exact (Finset.mem_filter.mp he).2
    · exact Cylinder.holds_mono ((hgenA.1 f hf).trans hKx) (atPoint_holds E x)
  have hgenB := Cylinder.generates_on B x hBx
  let J : Intersection E := ⟨Cylinder.on x (B.biUnion Cylinder.support),B,hBE,hgenB⟩
  have hJx : J.val.Holds x := Cylinder.on_holds x _
  have hKJ : K ≤ J := Cylinder.generates_le hgenA
    (fun f hf => hgenB.1 f (Finset.mem_insert_of_mem hf))
  have hKJlt : K < J := lt_of_le_of_ne hKJ (by
    intro h
    have heJ := hgenB.1 e (Finset.mem_insert_self e A)
    change e ≤ J.val at heJ
    have hv : K.val = J.val := congrArg Subtype.val h
    rw [← hv] at heJ
    exact heK heJ)
  have hrJ : t ≤ Cylinder.rank E J.val := by
    by_contra hh
    have hJS : J ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hIK.trans hKJ, (holds_iff_le_atPoint E J x).mp hJx, by omega⟩
    have hh := hmax J hJS
    have hlt := Finset.card_lt_card (Cylinder.support_ssubset hKJlt)
    omega
  have hBcard : B.card ≤ t := by
    have hc : B.card ≤ A.card + 1 := Finset.card_insert_le e A
    omega
  exact ⟨J,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hrJ,B,hBE,hBcard,hgenB⟩,
    hJx,hIK.trans hKJ⟩

lemma ideal_card_bound (E : Finset (Cylinder Ω)) (I : Intersection E) :
    (Finset.Icc (⊥ : Intersection E) I).card ≤ 2 ^ I.val.support.card := by
  classical
  calc
    (Finset.Icc (⊥ : Intersection E) I).card ≤ I.val.support.powerset.card := by
      apply Finset.card_le_card_of_injOn (fun J : Intersection E => J.val.support)
      · intro J hJ
        exact Finset.mem_powerset.mpr (Cylinder.support_mono (Finset.mem_Icc.mp hJ).2)
      · intro J hJ K hK hJK
        exact intersection_support_inj E I (Finset.mem_Icc.mp hJ).2
          (Finset.mem_Icc.mp hK).2 hJK
    _ = 2 ^ I.val.support.card := Finset.card_powerset _

lemma witnesses_width (E : Finset (Cylinder Ω)) (t w : ℕ)
    (hwidth : ∀e ∈ E, e.support.card ≤ w) (I : Intersection E) (hI : I ∈ witnesses E t) :
    I.val.support.card ≤ t*w := by
  obtain ⟨A,hAE,hcard,hgen⟩ := (Finset.mem_filter.mp hI).2.2
  exact (Cylinder.generated_width hAE hgen hwidth).trans (Nat.mul_le_mul_right w hcard)

lemma retained_coefficient_bound (E : Finset (Cylinder Ω)) (t w : ℕ)
    (hwidth : ∀e ∈ E, e.support.card ≤ w) (I : Intersection E) (hI : I ∈ retained E t) :
    (coefficient E I).natAbs ≤ max 1 ((t*w) ^ (t*w+1)) := by
  have hr : Cylinder.rank E I.val < t := (Finset.mem_filter.mp hI).2
  have hs : I.val.support.card ≤ t*w :=
    (Cylinder.rank_width I.property hwidth).trans (by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right w hr.le)
  exact (coefficient_support_bound E I).trans (max_power_mono hs)

lemma satisfied_retained_card_bound (E : Finset (Cylinder Ω)) (t w : ℕ)
    (hwidth : ∀e ∈ E, e.support.card ≤ w) (x : ∀p, Ω p)
    (hhigh : t ≤ Cylinder.rank E (atPoint E x).val) :
    ((retained E t).filter (fun I => I.val.Holds x)).card ≤
      witnessCount E t x * 2^(t*w) := by
  classical
  let W := (witnesses E t).filter (fun I => I.val.Holds x)
  calc
    ((retained E t).filter (fun I => I.val.Holds x)).card
        ≤ (W.biUnion (fun J => Finset.Icc (⊥ : Intersection E) J)).card := by
      apply Finset.card_le_card
      intro I hI
      obtain ⟨hIr,hIx⟩ := Finset.mem_filter.mp hI
      have hrI := (Finset.mem_filter.mp hIr).2
      obtain ⟨J,hJ,hJx,hIJ⟩ := witness_dominating E t x I hIx hrI hhigh
      exact Finset.mem_biUnion.mpr
        ⟨J,Finset.mem_filter.mpr ⟨hJ,hJx⟩,Finset.mem_Icc.mpr ⟨bot_le,hIJ⟩⟩
    _ ≤ ∑ J ∈ W, (Finset.Icc (⊥ : Intersection E) J).card := Finset.card_biUnion_le
    _ ≤ ∑ _J ∈ W, 2^(t*w) := by
      apply Finset.sum_le_sum
      intro J hJ
      exact (ideal_card_bound E J).trans (Nat.pow_le_pow_right (by decide)
        (witnesses_width E t w hwidth J (Finset.mem_filter.mp hJ).1))
    _ = witnessCount E t x * 2^(t*w) := by simp [W,witnessCount]

lemma truncation_exact_of_low_rank (E : Finset (Cylinder Ω))
    (hproper : ∀e ∈ E, e ≠ ⊥) (t : ℕ) (x : ∀p, Ω p)
    (hlow : Cylinder.rank E (atPoint E x).val < t) : truncated E t x = avoidance E x := by
  classical
  rw [← full_sum_holds E hproper x]
  unfold truncated
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext I
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, retained]
  constructor
  · intro h; exact h.2
  · intro h
    exact ⟨(Cylinder.rank_mono E ((holds_iff_le_atPoint E I x).mp h)).trans_lt hlow,h⟩

lemma truncation_bound (E : Finset (Cylinder Ω))
    (hproper : ∀e ∈ E, e ≠ ⊥) (t w : ℕ) (ht : 1 ≤ t)
    (hwidth : ∀e ∈ E, e.support.card ≤ w) (x : ∀p, Ω p) :
    (avoidance E x - truncated E t x).natAbs ≤
      2 ^ (t*w) * max 1 ((t*w)^(t*w+1)) * witnessCount E t x := by
  classical
  by_cases hlow : Cylinder.rank E (atPoint E x).val < t
  · rw [truncation_exact_of_low_rank E hproper t x hlow]
    simp
  have hhigh : t ≤ Cylinder.rank E (atPoint E x).val := by omega
  have hno : ¬∀e ∈ E, ¬e.Holds x := by
    intro hh
    have hb := (atPoint_bot_iff E hproper x).mpr hh
    have hval : (atPoint E x).val = ⊥ := congrArg Subtype.val hb
    rw [hval,rank_bot] at hhigh
    omega
  have ha : avoidance E x = 0 := by simp [avoidance,hno]
  rw [ha,zero_sub,Int.natAbs_neg]
  unfold truncated
  calc
    (∑ I ∈ retained E t, if I.val.Holds x then coefficient E I else 0).natAbs
      = (∑ I ∈ (retained E t).filter (fun I => I.val.Holds x), coefficient E I).natAbs := by
        rw [Finset.sum_filter]
    _ ≤ ∑ I ∈ (retained E t).filter (fun I => I.val.Holds x), (coefficient E I).natAbs :=
      Int.natAbs_sum_le _ _
    _ ≤ ∑ _I ∈ (retained E t).filter (fun I => I.val.Holds x), max 1 ((t*w)^(t*w+1)) := by
      apply Finset.sum_le_sum
      intro I hI
      exact retained_coefficient_bound E t w hwidth I (Finset.mem_filter.mp hI).1
    _ = ((retained E t).filter (fun I => I.val.Holds x)).card * max 1 ((t*w)^(t*w+1)) := by simp
    _ ≤ (witnessCount E t x * 2^(t*w)) * max 1 ((t*w)^(t*w+1)) :=
      Nat.mul_le_mul_right _ (satisfied_retained_card_bound E t w hwidth x hhigh)
    _ = 2^(t*w) * max 1 ((t*w)^(t*w+1)) * witnessCount E t x := by ring

end OrdinaryCorrelations.SourceCylinder

end

end OAI
