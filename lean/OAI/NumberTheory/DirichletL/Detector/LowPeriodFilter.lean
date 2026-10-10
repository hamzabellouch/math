import OAI.NumberTheory.DirichletL.Detector.LowPeriodSupport

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sum_tuple_filter_zero {ι α : Type*} [Fintype ι] [DecidableEq α]
    (T : ι→Finset α) (good : ι→α→Prop) [∀i,DecidablePred (good i)]
    (c : ι→α→ℂ) (hc : ∀i a,a∈T i→¬good i a→c i a=0) (F : (ι→α)→ℂ) :
    (∑p : ∀i,T i,(∏i,c i (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,(T i).filter (good i),(∏i,c i (p i).val)*F (fun i=>(p i).val) := by
  let forget : (∀i,(T i).filter (good i))→(∀i,T i) := fun p i=>⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩
  have hinj : Function.Injective forget := by
    intro p q h
    funext i
    exact Subtype.ext (congrArg (fun a=> (a i).val) h)
  let H : (∀i,T i)→ℂ := fun p=>(∏i,c i (p i).val)*F (fun i=>(p i).val)
  have hz (p : ∀i,T i) (hp : p∉Finset.univ.image forget) : H p=0 := by
    by_contra hh
    have hn : ∀i,good i (p i).val := by
      intro i
      by_contra hbad
      have hc0 := hc i (p i).val (p i).property hbad
      have hprod : (∏j,c j (p j).val)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hc0
      exact hh (by dsimp [H];rw [hprod,zero_mul])
    let q : ∀i,(T i).filter (good i) := fun i=>⟨(p i).val,Finset.mem_filter.mpr ⟨(p i).property,hn i⟩⟩
    exact hp (Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩)
  have he := Finset.sum_subset (Finset.subset_univ (Finset.univ.image forget))
    (fun p hp hnot=>hz p hnot)
  change (∑p,H p)=_
  rw [←he,Finset.sum_image (fun p _ q _ h=>hinj h)]

def lowPeriodIdeal (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS)*Ideal.span {(72:O)}

def lowPeriodSlotFilter {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset O) : ι→Finset O :=
  fun i=>(T i).filter (fun a=>IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))

lemma lowPeriodSlotFilter_coprime {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset O) (i : ι) (a : O)
    (ha : a∈lowPeriodSlotFilter η S hS T i) :
    IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp ha).2

lemma canonical_prime_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (P : PrimeIdeal) (hP : CanonicalQuadraticSieve.Supported P.val) (hout : P.val∉S) :
    IsCoprime (calibrationForSet S hS).generator (CompletedGauss.primaryGenerator P.val) := by
  apply calibrationForSet_coprime_of_excluded S hS
  intro Q hQ hdiv
  rw [span_primaryGenerator_of_supported P.val hP] at hdiv
  have hpmax := (Ideal.isPrime_of_prime P.property).isMaximal P.property.ne_zero
  have he : P.val=Q := Ideal.IsMaximal.eq_of_le hpmax (hS Q hQ).ne_top (Ideal.dvd_iff_le.mp hdiv)
  exact hout (he.symm ▸ hQ)

lemma canonical_slot_calibration_coprime (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (T : Finset PrimeIdeal)
    (hT : ∀P∈T,CanonicalQuadraticSieve.Supported P.val) (hout : ∀P∈T,P.val∉S)
    (a : O) (ha : a∈canonicalSlotSupport T) : IsCoprime (calibrationForSet S hS).generator a := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact canonical_prime_calibration_coprime S hS P (hT P hP) (hout P hP)

theorem low_slot_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : ι→Finset O)
    (hcop : ∀i a,a∈T i→IsCoprime (calibrationForSet S hS).generator a)
    (W : ι→ℝ→ℂ) (P : ι→ℝ) (t : ℝ) (F : (ι→O)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodSlotFilter η S hS T i,
        (∏i,lowSingleSlotWeight η (W i) (P i) t (p i).val)*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i a=>IsCoprime (Ideal.span {a}) (lowPeriodIdeal η S hS))
    (fun i a=>lowSingleSlotWeight η (W i) (P i) t a) _ F
  intro i a ha hnot
  exact lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (P i) t a (hcop i a ha) hnot

def lowPeriodPrimeList (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) : Finset PrimeIdeal :=
  T.filter (fun P=>IsCoprime P.val (lowPeriodIdeal η S hS))

lemma lowPeriodPrimeList_subset (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal) :
    lowPeriodPrimeList η S hS T⊆T := Finset.filter_subset _ _

lemma lowPeriodPrimeList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (P : PrimeIdeal) (hP : P∈lowPeriodPrimeList η S hS T) :
    IsCoprime P.val (lowPeriodIdeal η S hS) := (Finset.mem_filter.mp hP).2

lemma lowPeriodPrimeList_disjoint {ι : Type*} (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPeriodPrimeList η S hS (T i)) (lowPeriodPrimeList η S hS (T j))) := by
  intro i j hij
  exact (hT hij).mono (lowPeriodPrimeList_subset η S hS _) (lowPeriodPrimeList_subset η S hS _)

theorem low_canonical_polynomial_period_filter {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→PrimeIdeal)→ℂ) :
    (∑p : ∀i,T i,(∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val))=
      ∑p : ∀i,lowPeriodPrimeList η S hS (T i),
        (∏i,lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator (p i).val.val))*F (fun i=>(p i).val) := by
  apply sum_tuple_filter_zero T (fun i P=>IsCoprime P.val (lowPeriodIdeal η S hS))
    (fun i P=>lowSingleSlotWeight η (W i) (Y i) t (CompletedGauss.primaryGenerator P.val)) _ F
  intro i P hP hnot
  apply lowSingleSlotWeight_zero_of_period η S hS hbad (W i) (Y i) t _
    (canonical_prime_calibration_coprime S hS P (hT i P hP) (hout i P hP))
  change ¬IsCoprime (Ideal.span {CompletedGauss.primaryGenerator P.val}) (lowPeriodIdeal η S hS)
  rwa [span_primaryGenerator_of_supported P.val (hT i P hP)]

end SevenEighths.ProbePhysical
end

end OAI
