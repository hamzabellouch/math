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

def forwardSegment (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+i.val,by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩ - s.offset ⟨a,by omega⟩) :
    S.Specification D h L where
  length := k
  length_pos := hk
  length_le := (show k ≤ s.length by omega).trans s.length_le
  offset j := s.offset ⟨a+j.val,by omega⟩ - s.offset ⟨a,by omega⟩
  offset_zero := by simp
  offsets_distinct := by
    intro i j he
    have hval := congrArg Fin.val (s.offsets_distinct (sub_left_injective he))
    apply Fin.ext
    simpa using hval
  label i := s.label ⟨a+i.val,by omega⟩
  label_mem i := s.label_mem _
  sign i := s.sign ⟨a+i.val,by omega⟩
  sign_mem i := s.sign_mem _
  step i := by
    have hstep := s.step ⟨a+i.val,by omega⟩
    simpa only [Fin.succ_mk,Fin.castSucc_mk,Fin.val_castSucc,Fin.val_succ,sub_sub_sub_cancel_right,Nat.add_assoc] using hstep
  extra := q
  extra_not_div := hfree
  suffix := ⟨0,hk⟩
  extra_div_suffix := by simpa using hd

lemma forwardSegment_oriented (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+i.val,by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩ - s.offset ⟨a,by omega⟩) :
    s.OrientedSubpath (s.forwardSegment a k hk hak q hfree hd) (s.offset ⟨a,by omega⟩) := by
  exact ⟨a,hak,Or.inl ⟨rfl,fun j => rfl⟩⟩

lemma forwardSegment_qualifies (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+i.val,by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩ - s.offset ⟨a,by omega⟩)
    (x : ℤ) (hx : s.QualifiesAt x) (hq : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a,by omega⟩) :
    (s.forwardSegment a k hk hak q hfree hd).QualifiesAt (x+s.offset ⟨a,by omega⟩) := by
  refine ⟨hq,?_⟩
  intro i
  change Fin k at i
  change (s.label ⟨a+i.val,by omega⟩:ℤ) ∣
    (x+s.offset ⟨a,by omega⟩)+(s.offset ⟨a+i.val,by omega⟩-s.offset ⟨a,by omega⟩)
  convert hx.2 ⟨a+i.val,by omega⟩ using 1
  simp only [Fin.castSucc_mk]
  ring

lemma forwardSegment_support (s : S.Specification D h L) (a k : ℕ) (hk : 0 < k)
    (hak : a+k ≤ s.length) (q : S.Index)
    (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+i.val,by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩ - s.offset ⟨a,by omega⟩)
    (hq : (q:ℕ) ∈ s.primeSupport) :
    (s.forwardSegment a k hk hak q hfree hd).primeSupport ⊆ s.primeSupport := by
  intro p hp
  rcases mem_insert.mp hp with he | he
  · exact he ▸ hq
  · obtain ⟨i,hi,hpi⟩ := mem_biUnion.mp he
    change Fin k at i
    apply mem_insert_of_mem
    exact mem_biUnion.mpr ⟨⟨a+i.val,by omega⟩,mem_univ _,hpi⟩

lemma primitive_no_forwardSegment (s : S.Specification D h L) (hs : s.Primitive)
    (a k : ℕ) (hk : 0 < k) (hshort : k < s.length) (hak : a+k ≤ s.length)
    (q : S.Index) (hfree : ∀ i : Fin k, ¬(q:ℕ) ∣ s.label ⟨a+i.val,by omega⟩)
    (hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩ - s.offset ⟨a,by omega⟩)
    (hq : (q:ℕ) ∈ s.primeSupport) (x : ℤ) (hx : s.QualifiesAt x)
    (hactive : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a,by omega⟩) : False := by
  exact hs.2 ⟨s.forwardSegment a k hk hak q hfree hd,s.offset ⟨a,by omega⟩,x,
    hshort,s.forwardSegment_oriented a k hk hak q hfree hd,
    s.forwardSegment_support a k hk hak q hfree hd hq,hx,
    s.forwardSegment_qualifies a k hk hak q hfree hd x hx hactive⟩

lemma qualifies_prime_departure (s : S.Specification D h L) (x : ℤ) (hx : s.QualifiesAt x)
    (i : Fin s.length) (q : ℕ) (hqi : q ∣ s.label i) :
    (q:ℤ) ∣ x+s.offset i.castSucc :=
  dvd_trans (by exact_mod_cast hqi) (hx.2 i)

lemma qualifies_prime_arrival (s : S.Specification D h L) (x : ℤ) (hx : s.QualifiesAt x)
    (i : Fin s.length) (q : ℕ) (hqi : q ∣ s.label i) :
    (q:ℤ) ∣ x+s.offset i.succ := by
  have hd : (q:ℤ) ∣ s.offset i.succ-s.offset i.castSucc := by
    rw [s.step i]
    exact dvd_mul_of_dvd_right (by exact_mod_cast hqi) _
  convert (s.qualifies_prime_departure x hx i q hqi).add hd using 1
  first | rfl | ring

theorem primitive_no_prime_gap (s : S.Specification D h L) (hs : s.Primitive)
    (q : S.Index) (i j : Fin s.length) (hij : i.val+1 < j.val)
    (hqi : (q:ℕ) ∣ s.label i) (hqj : (q:ℕ) ∣ s.label j)
    (hgap : ∀ r : Fin s.length, i < r → r < j → ¬(q:ℕ) ∣ s.label r) : False := by
  obtain ⟨x,hx⟩ := hs.1
  let a := i.val+1
  let k := j.val-a
  have hk : 0 < k := by dsimp [k,a]; omega
  have hak : a+k ≤ s.length := by dsimp [k,a]; omega
  have hshort : k < s.length := by dsimp [k,a]; omega
  have hend : a+k=j.val := by dsimp [k,a]; omega
  have hfree (r : Fin k) : ¬(q:ℕ) ∣ s.label ⟨a+r.val,by omega⟩ := by
    apply hgap
    · change i.val < a+r.val
      dsimp [a]
      omega
    · change a+r.val < j.val
      omega
  have ha : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a,by omega⟩ :=
    s.qualifies_prime_arrival x hx i q hqi
  have hb : ((q:ℕ):ℤ) ∣ x+s.offset ⟨a+k,by omega⟩ := by
    have he : (⟨a+k,by omega⟩ : Fin (s.length+1)) = j.castSucc := Fin.ext hend
    rw [he]
    exact s.qualifies_prime_departure x hx j q hqj
  have hd : ((q:ℕ):ℤ) ∣ s.offset ⟨a+k,by omega⟩-s.offset ⟨a,by omega⟩ := by
    convert hb.sub ha using 1
    first | rfl | ring
  have hq : (q:ℕ) ∈ s.primeSupport := mem_insert_of_mem (mem_biUnion.mpr
    ⟨i,mem_univ _,Nat.mem_primeFactors.mpr ⟨S.prime_mem q q.property,hqi,by
      have := D.greater_one _ (s.label_mem i); omega⟩⟩)
  exact s.primitive_no_forwardSegment hs a k hk hshort hak q hfree hd hq x hx ha

end OrdinaryCorrelations.GraphKernel.PrimeSystem.Specification

end

end OAI
