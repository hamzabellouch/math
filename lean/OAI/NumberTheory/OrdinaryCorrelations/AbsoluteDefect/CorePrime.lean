import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.ShiftedMultiplesCard

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff

namespace OrdinaryAnalyticCentering
open Finset OrdinaryCorrelations OrdinaryTwistWidth OrdinaryAnalyticCutoff

lemma core_prime (B:ℝ) {p:ℕ} (hp:p∈core B) : p.Prime := (mem_filter.mp hp).2.1
lemma center_prime (B:ℝ) {p:ℕ} (hp:p∈center B) : p.Prime := (mem_filter.mp hp).2.1
lemma core_center_disjoint (B:ℝ) : Disjoint (core B) (center B) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact (not_lt_of_ge (mem_filter.mp hq).2.2.2) (mem_filter.mp hp).2.2.1
lemma prime_lower (B:ℝ) (hB:1≤B) {p:ℕ} (hp:p∈core B∪center B) : P₀ B<(p:ℝ) := by
  have hpos : 0<(p:ℝ) := by
    rcases mem_union.mp hp with hp|hp
    · exact_mod_cast (core_prime B hp).pos
    · exact_mod_cast (center_prime B hp).pos
  have hl : B^(9999/10000:ℝ)<Real.log p := by
    rcases mem_union.mp hp with hp|hp
    · exact (Real.rpow_le_rpow_of_exponent_le hB (by norm_num : (9999/10000:ℝ)≤999999/1000000)).trans_lt
        (mem_filter.mp hp).2.2.1
    · exact (mem_filter.mp hp).2.2.1
  simpa only [P₀,Real.exp_log hpos] using Real.exp_lt_exp.mpr hl

noncomputable def centralPrimes (B:ℝ) (d:ℕ) : Finset ℕ := (center B).filter (fun p=>p∣d)
noncomputable def corePrimes (B:ℝ) (d:ℕ) : Finset ℕ := (core B).filter (fun p=>p∣d)
noncomputable def retained (d:ℕ) (W:Finset ℕ) : ℕ := ∏p∈d.primeFactors\W,p
noncomputable def removed (W:Finset ℕ) : ℕ := ∏p∈W,p
noncomputable def choices (B:ℝ) (D:Finset ℕ) : Finset (Σ_:ℕ,Finset ℕ) :=
  D.sigma (fun d=>(centralPrimes B d).powerset.erase ∅)

lemma mem_choices {B:ℝ} {D:Finset ℕ} {q:Σ_:ℕ,Finset ℕ} :
    q∈choices B D ↔q.1∈D ∧ q.2≠∅ ∧ q.2⊆centralPrimes B q.1 := by
  simp [choices,mem_sigma,mem_erase,Finset.mem_powerset]

lemma centralPrimes_subset (B:ℝ) {d:ℕ} (hd:d≠0) : centralPrimes B d⊆d.primeFactors := by
  intro p hp
  obtain ⟨hp,hpd⟩:=mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨center_prime B hp,hpd,hd⟩
lemma corePrimes_subset (B:ℝ) {d:ℕ} (hd:d≠0) : corePrimes B d⊆d.primeFactors := by
  intro p hp
  obtain ⟨hp,hpd⟩:=mem_filter.mp hp
  exact Nat.mem_primeFactors.mpr ⟨core_prime B hp,hpd,hd⟩
lemma parts_union (B:ℝ) {d:ℕ} (hd:d≠0) (hS:d.primeFactors⊆core B∪center B) :
    corePrimes B d∪centralPrimes B d=d.primeFactors := by
  apply Subset.antisymm (union_subset (corePrimes_subset B hd) (centralPrimes_subset B hd))
  intro p hp
  have hpd := (Nat.mem_primeFactors.mp hp).2.1
  rcases mem_union.mp (hS hp) with hc|hq
  · exact mem_union_left _ (mem_filter.mpr ⟨hc,hpd⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨hq,hpd⟩)
lemma parts_disjoint (B:ℝ) (d:ℕ) : Disjoint (corePrimes B d) (centralPrimes B d) :=
  (core_center_disjoint B).mono (filter_subset _ _) (filter_subset _ _)
lemma retained_pos (d:ℕ) (W:Finset ℕ) : 0<retained d W := by
  apply prod_pos
  intro p hp
  exact (Nat.mem_primeFactors.mp (mem_sdiff.mp hp).1).1.pos
lemma retained_factors (d:ℕ) (W:Finset ℕ) : (retained d W).primeFactors=d.primeFactors\W := by
  apply Nat.primeFactors_prod
  intro p hp
  exact (Nat.mem_primeFactors.mp (mem_sdiff.mp hp).1).1
lemma removed_factors (W:Finset ℕ) (hW:∀p∈W,p.Prime) : (removed W).primeFactors=W :=
  Nat.primeFactors_prod hW
lemma retained_mul_removed (d:ℕ) (hd:Squarefree d) (W:Finset ℕ) (hW:W⊆d.primeFactors) :
    retained d W*removed W=d := by
  rw [retained,removed,prod_sdiff hW,Nat.prod_primeFactors_of_squarefree hd]
lemma retained_core (B:ℝ) {d:ℕ} (hd:d≠0) (W:Finset ℕ) (hW:W⊆centralPrimes B d) :
    corePrimes B (retained d W)=corePrimes B d := by
  ext p
  by_cases hp:p∈core B
  · have hprime:=core_prime B hp
    have hnW : p∉W := by
      intro hpW
      exact disjoint_left.mp (core_center_disjoint B) hp (mem_filter.mp (hW hpW)).1
    simp only [corePrimes,mem_filter,hp,true_and]
    have he : (p∈(retained d W).primeFactors)↔p∈d.primeFactors∧p∉W := by
      rw [retained_factors,Finset.mem_sdiff]
    constructor
    · intro hpd
      exact (Nat.mem_primeFactors.mp (he.mp (Nat.mem_primeFactors.mpr
        ⟨hprime,hpd,(retained_pos d W).ne'⟩)).1).2.1
    · intro hpd
      exact (Nat.mem_primeFactors.mp (he.mpr ⟨Nat.mem_primeFactors.mpr ⟨hprime,hpd,hd⟩,hnW⟩)).2.1
  · simp [corePrimes,hp]
lemma retained_omitted (B:ℝ) {d:ℕ} (hd:d≠0) (W:Finset ℕ) (hW:W⊆centralPrimes B d) :
    (core B).filter (fun p=>¬p∣retained d W)=(core B).filter (fun p=>¬p∣d) := by
  have he:=retained_core B hd W hW
  ext p
  have hp := congrArg (fun S:Finset ℕ=>p∈S) he
  simp only [corePrimes,mem_filter] at hp ⊢
  tauto
lemma retained_weight (B:ℝ) {d:ℕ} (hd:d≠0) (W:Finset ℕ) (hW:W⊆centralPrimes B d) :
    divisorWeight B (retained d W)=divisorWeight B d := by
  unfold divisorWeight primeCount
  rw [show (core B).filter (fun p=>p∣retained d W)=corePrimes B (retained d W) from rfl,
    retained_core B hd W hW]
  rfl
lemma cut_dilation (phi:ℝ→ℝ) (B:ℝ) {d:ℕ} (hd:d≠0)
    (W:Finset ℕ) (hW:W⊆centralPrimes B d) (v:ℕ) :
    cut phi B d (retained d W*v)=cut phi B (retained d W) v := by
  unfold cut
  rw [←retained_omitted B hd W hW]
  apply cutoff_mul
  · intro p hp;exact core_prime B (mem_filter.mp hp).1
  · intro p hp;exact (mem_filter.mp hp).2

lemma prod_prime_indicator (P:Finset ℕ) (hP:∀p∈P,p.Prime) (n:ℕ) :
    (∏p∈P,if p∣n then (1:ℂ) else 0)=(if (∏p∈P,p)∣n then 1 else 0) := by
  have hd : (∏p∈P,p)∣n ↔∀p∈P,p∣n := by
    constructor
    · intro h p hp;exact (dvd_prod_of_mem (fun p=>p) hp).trans h
    · intro h
      apply prod_dvd_of_isRelPrime _ h
      intro p hp q hq hpq
      exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq)
  rw [prod_ite_zero]
  simp [hd]

lemma centered_product (P:Finset ℕ) (n:ℕ) :
    (∏p∈P,((if p∣n then (1:ℂ) else 0)-(1/4:ℂ)/(p:ℂ)))=
      ∑W∈P.powerset,(-1/4:ℂ)^W.card/(removed W:ℂ)*
        (∏p∈P\W,if p∣n then (1:ℂ) else 0) := by
  rw [prod_sub]
  apply sum_congr rfl
  intro W hW
  simp only [prod_div_distrib,prod_const,Nat.cast_prod,removed]
  rw [show (-1/4:ℂ)=(-1)*(1/4) by ring,mul_pow]
  simp only [div_eq_mul_inv,one_mul]
  ring_nf
  rw [one_div]
  ring

lemma kernel_expansion (phi:ℝ→ℝ) (B:ℝ) {d:ℕ} (hd:Squarefree d)
    (hd0:d≠0) (hS:d.primeFactors⊆core B∪center B) (x y:ℕ) :
    kernel phi B d x y=
      cut phi B d x*cut phi B d y*(divisorWeight B d:ℂ)*
      (∑W∈(centralPrimes B d).powerset,(-1/4:ℂ)^W.card/(removed W:ℂ)*
        (if retained d W∣x then 1 else 0)) := by
  unfold kernel
  change _*(if (∏p∈corePrimes B d,p)∣x then (1:ℂ) else 0)*
    (∏p∈centralPrimes B d,((if p∣x then (1:ℂ) else 0)-(1/4:ℂ)/(p:ℂ)))=_
  rw [centered_product,mul_assoc,mul_sum]
  congr 1
  apply sum_congr rfl
  intro W hW
  have hWsub:=mem_powerset.mp hW
  have he : corePrimes B d∪(centralPrimes B d\W)=d.primeFactors\W := by
    rw [← parts_union B hd0 hS,Finset.union_sdiff_distrib]
    rw [sdiff_eq_left.mpr ((parts_disjoint B d).mono_right hWsub)]
  have hdis : Disjoint (corePrimes B d) (centralPrimes B d\W) :=
    (parts_disjoint B d).mono_right sdiff_subset
  have hpC (p:ℕ) (hp:p∈corePrimes B d) : p.Prime := core_prime B (mem_filter.mp hp).1
  have hpQ (p:ℕ) (hp:p∈centralPrimes B d\W) : p.Prime :=
    center_prime B (mem_filter.mp (mem_sdiff.mp hp).1).1
  have hpR (p:ℕ) (hp:p∈d.primeFactors\W) : p.Prime :=
    ((Nat.mem_primeFactors_of_ne_zero hd.ne_zero).mp (mem_sdiff.mp hp).1).1
  rw [←prod_prime_indicator _ hpC,show retained d W=∏p∈d.primeFactors\W,p from rfl,
    ←prod_prime_indicator _ hpR,←he,prod_union hdis]
  ring
end OrdinaryAnalyticCentering

end

end OAI
