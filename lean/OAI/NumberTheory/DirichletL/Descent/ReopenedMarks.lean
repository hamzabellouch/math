import OAI.NumberTheory.DirichletL.Descent.ReopenedSource

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_span_primeProduct (S : Finset ι) (v : ι→ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣Ideal.span {primeProduct p S v} ↔ i∈S ∧ 0<v i := by
  simp only [primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  rw [←dvd_iff_emultiplicity_pos,primeIdealProduct_emultiplicity (fun i=>Ideal.span {p i}) hinj]
  by_cases hi : i∈S <;> simp [hi]

omit [DecidableEq σ] in
include hinj in
theorem prime_dvd_reopened_index (S : Finset ι) (v : ι→₀ℕ) (i : ι) :
    (Ideal.span {p i}:Ideal O)∣(Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 ↔
      i∈S∪v.support := by
  have hi : Prime (Ideal.span {p i}:Ideal O) := Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hs := prime_dvd_span_primeProduct p hinj S (fun _=>1) i
  simp only [primeProduct,pow_one,Nat.zero_lt_one,and_true] at hs
  rw [hi.dvd_mul,hi.dvd_pow_iff_dvd (by decide : (3:ℕ)≠0),hs,
    prime_dvd_span_primeProduct p hinj v.support v i,Finset.mem_union]
  have hv : i∈v.support ↔ 0<v i := by rw [Finsupp.mem_support_iff]; omega
  tauto

include hinj in

omit [DecidableEq σ] in
theorem reopened_whole_mark_divisibility (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
    ∏j∈slots,∑i∈lists j,if (Ideal.span {p i}:Ideal O)∣
      (Ideal.span {∏k∈S,p k})*(Ideal.span {primeProduct p v.support v})^3 then a j i else 0 := by
  unfold primeMark primeSlot
  simp_rw [prime_dvd_reopened_index p hinj]

theorem reopened_mark_priority (slots : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (S : Finset ι) (v : ι→₀ℕ) :
    primeMark slots lists a (S∪v.support) =
      ∑J∈slots.powerset,primeMark J lists a v.support *
        primeMark (slots\J) (fun j=>lists j\v.support) a S := by
  rw [Finset.union_comm,primeMark_priority]
  simp only [primeMark_residual_lists]

end
end SevenEighths.InverseMoment

end OAI
