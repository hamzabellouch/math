import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.DivisorFamily

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification
open OrdinaryCorrelations.SignedTrace
open Finset Classical
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h L : ℕ}

def reverseSegment (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index) (c : Fin k)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩ - s.offset ⟨a+k-c.val,by omega⟩) :
    S.Specification D h L where
  length := k
  length_pos := hk
  length_le := (show k ≤ s.length by omega).trans s.length_le
  offset j := s.offset ⟨a+k-j.val,by omega⟩ - s.offset ⟨a+k,by omega⟩
  offset_zero := by simp
  offsets_distinct := by
    intro i j he
    have hv := congrArg Fin.val (s.offsets_distinct (sub_left_injective he))
    apply Fin.ext
    dsimp only at hv
    omega
  label i := s.label ⟨a+k-(i.val+1),by omega⟩
  label_mem i := s.label_mem _
  sign i := -s.sign ⟨a+k-(i.val+1),by omega⟩
  sign_mem i := by rcases s.sign_mem ⟨a+k-(i.val+1),by omega⟩ with he|he <;> simp [he]
  step i := by
    let r : Fin s.length := ⟨a+k-(i.val+1),by omega⟩
    have hr : r.val+1=a+k-i.val := by dsimp [r]; omega
    have hstep := s.step r
    have he : r.succ = (⟨a+k-i.val,by omega⟩ : Fin (s.length+1)) := Fin.ext hr
    rw [he] at hstep
    simp only [Fin.val_succ,Fin.val_castSucc,sub_sub_sub_cancel_right]
    change s.offset r.castSucc-s.offset ⟨a+k-i.val,by omega⟩ = -s.sign r*(h:ℤ)*s.label r
    linear_combination -hstep
  extra := q
  extra_not_div := hfree
  suffix := c
  extra_div_suffix := by simpa using hd

lemma reverseSegment_oriented (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index) (c : Fin k)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩ - s.offset ⟨a+k-c.val,by omega⟩) :
    s.OrientedSubpath (s.reverseSegment a k hk hak q c hfree hd) (s.offset ⟨a+k,by omega⟩) :=
  ⟨a,hak,Or.inr ⟨rfl,fun _ => rfl⟩⟩

lemma reverseSegment_qualifies (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index) (c : Fin k)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩ - s.offset ⟨a+k-c.val,by omega⟩)
    (x : ℤ) (hx : s.QualifiesAt x)
    (hq : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a+k,by omega⟩) :
    (s.reverseSegment a k hk hak q c hfree hd).QualifiesAt (x+s.offset ⟨a+k,by omega⟩) := by
  refine ⟨hq,?_⟩
  intro i
  change Fin k at i
  let r : Fin s.length := ⟨a+k-(i.val+1),by omega⟩
  have hr : r.val+1=a+k-i.val := by dsimp [r]; omega
  have he : r.succ = (⟨a+k-i.val,by omega⟩ : Fin (s.length+1)) := Fin.ext hr
  have hdvd : (s.label r : ℤ) ∣ x+s.offset r.succ := by
    have hstep : (s.label r : ℤ) ∣ s.offset r.succ-s.offset r.castSucc := by
      rw [s.step r]
      exact dvd_mul_left _ _
    convert (hx.2 r).add hstep using 1
    ring
  rw [he] at hdvd
  change (s.label r:ℤ) ∣ (x+s.offset ⟨a+k,by omega⟩)+
    (s.offset ⟨a+k-i.val,by omega⟩-s.offset ⟨a+k,by omega⟩)
  convert hdvd using 1
  ring

lemma reverseSegment_support (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index) (c : Fin k)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩ - s.offset ⟨a+k-c.val,by omega⟩)
    (hq : (q:ℕ) ∈ s.primeSupport) :
    (s.reverseSegment a k hk hak q c hfree hd).primeSupport ⊆ s.primeSupport := by
  intro p hp
  rcases mem_insert.mp hp with he | he
  · exact he ▸ hq
  · obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp he
    change Fin k at i
    apply mem_insert_of_mem
    exact mem_biUnion.mpr ⟨⟨a+k-(i.val+1),by omega⟩,mem_univ _,hpi⟩

lemma primitive_no_reverseSegment (s : S.Specification D h L) (hs : s.Primitive)
    (a k : ℕ) (hk : 0 < k) (hshort : k < s.length) (hak : a+k ≤ s.length)
    (q : S.Index) (c : Fin k)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩ - s.offset ⟨a+k-c.val,by omega⟩)
    (hq : (q:ℕ) ∈ s.primeSupport) (x : ℤ) (hx : s.QualifiesAt x)
    (hactive : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a+k,by omega⟩) : False := by
  exact hs.2 ⟨s.reverseSegment a k hk hak q c hfree hd,s.offset ⟨a+k,by omega⟩,x,
    hshort,s.reverseSegment_oriented a k hk hak q c hfree hd,
    s.reverseSegment_support a k hk hak q c hfree hd hq,hx,
    s.reverseSegment_qualifies a k hk hak q c hfree hd x hx hactive⟩

theorem primitive_prefix_nondvd (s : S.Specification D h L) (hs : s.Primitive)
    (q : S.Index) (b : Fin s.length) (hqb : (q:ℕ) ∣ s.label b)
    (hfree : ∀ i : Fin s.length, i<b → ¬(q:ℕ) ∣ s.label i)
    (a v : ℕ) (hav : a<v) (hvb : v≤b.val) :
    ¬ ((q:ℕ):ℤ) ∣ s.offset ⟨v,by omega⟩-s.offset ⟨a,by omega⟩ := by
  intro hd
  obtain ⟨x,hx⟩ := hs.1
  let k := b.val - a
  have hk : 0<k := by dsimp [k]; omega
  have ha : a+k=b.val := by dsimp [k]; omega
  have hak : a + k ≤ s.length := by omega
  have hshort : k < s.length := by dsimp [k]; omega
  let c : Fin k := ⟨b.val-v,by dsimp [k]; omega⟩
  have he : a+k-c.val=v := by dsimp [c]; omega
  have hf (i : Fin k) : ¬(q:ℕ) ∣ s.label ⟨a+k-(i.val+1),by omega⟩ := by
    apply hfree
    change a+k-(i.val+1)<b.val
    omega
  have hdiv : ((q:ℕ):ℤ) ∣ s.offset ⟨a,by omega⟩-s.offset ⟨a+k-c.val,by omega⟩ := by
    have hi : (⟨a+k-c.val,by omega⟩ : Fin (s.length+1))=⟨v,by omega⟩ := Fin.ext he
    rw [hi]
    simpa only [neg_sub] using (dvd_neg.mpr hd)
  have hq : (q:ℕ) ∈ s.primeSupport := mem_insert_of_mem (mem_biUnion.mpr
    ⟨b,mem_univ _,Nat.mem_primeFactors.mpr ⟨S.prime_mem q q.property,hqb,by
      have := D.greater_one _ (s.label_mem b); omega⟩⟩)
  have hactive : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a+k,by omega⟩ := by
    have hi : (⟨a+k,by omega⟩ : Fin (s.length+1))=b.castSucc := Fin.ext ha
    rw [hi]
    exact dvd_trans (by exact_mod_cast hqb) (hx.2 b)
  exact s.primitive_no_reverseSegment hs a k hk hshort hak q c hf hdiv hq x hx hactive

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
