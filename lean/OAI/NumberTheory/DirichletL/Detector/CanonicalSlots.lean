import OAI.NumberTheory.DirichletL.Detector.TuplePrime

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def canonicalSlotSupport (T : Finset PrimeIdeal) : Finset O :=
  T.image (fun P=>primaryGenerator P.val)

lemma primaryPrime_injective {P Q : PrimeIdeal} (hP : Supported P.val) (hQ : Supported Q.val)
    (h : primaryGenerator P.val=primaryGenerator Q.val) : P=Q := by
  apply Subtype.ext
  have hh := congrArg (fun a : O=>Ideal.span {a}) h
  simpa only [span_primaryGenerator_of_supported _ hP,span_primaryGenerator_of_supported _ hQ] using hh

lemma canonicalSlotSupport_nonzero (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (a : O) (ha : a∈canonicalSlotSupport T) : a≠0 := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp ha
  exact supported_primaryGenerator_ne_zero P.val (hT P hP)

def canonicalSlotEquiv (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val) :
    ↥T ≃ ↥(canonicalSlotSupport T) :=
  Equiv.ofBijective
    (fun P=>⟨primaryGenerator P.val.val,Finset.mem_image.mpr ⟨P.val,P.property,rfl⟩⟩)
    ⟨by
      intro P Q h
      apply Subtype.ext
      exact primaryPrime_injective (hT P.val P.property) (hT Q.val Q.property) (congrArg Subtype.val h),by
      intro a
      obtain ⟨P,hP,he⟩ := Finset.mem_image.mp a.property
      exact ⟨⟨P,hP⟩,Subtype.ext he⟩⟩

@[simp] lemma canonicalSlotEquiv_val (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : (canonicalSlotEquiv T hT P).val=primaryGenerator P.val.val := rfl

lemma canonicalSlotEquiv_span (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : Ideal.span {(canonicalSlotEquiv T hT P).val}=P.val.val :=
  span_primaryGenerator_of_supported _ (hT P.val P.property)

lemma canonicalSlotEquiv_norm (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (P : T) : elementNorm (canonicalSlotEquiv T hT P).val=(Ideal.absNorm P.val.val:ℝ) :=
  primaryTuple_norm P.val (hT P.val P.property)

def canonicalTupleEquiv {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) :
    (∀i,↥(T i)) ≃ (∀i,↥(canonicalSlotSupport (T i))) :=
  Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))

@[simp] lemma canonicalTupleEquiv_val {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (P : ∀i,↥(T i)) (i : Fin K) :
    (canonicalTupleEquiv T hT P i).val=primaryGenerator (P i).val.val := rfl

theorem sum_canonical_element_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),F (fun i=>primaryGenerator (P i).val.val) := by
  exact ((canonicalTupleEquiv T hT).sum_comp (fun p=>F (fun i=>(p i).val))).symm

lemma canonicalSlotSupport_disjoint (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) (hdis : Disjoint T U) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U) := by
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
  obtain ⟨Q,hQ,hQa⟩ := Finset.mem_image.mp hb
  have he : P=Q := primaryPrime_injective (hT P hP) (hU Q hQ) (hPa.trans hQa.symm)
  exact Finset.disjoint_left.mp hdis hP (he.symm ▸ hQ)

lemma idealTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>(P i).val) := by
  intro i j he
  by_contra hij
  apply Finset.disjoint_left.mp (hdis hij) (P i).property
  rw [show (P i).val=(P j).val from he]
  exact (P j).property

lemma canonicalElementTuple_injective_of_disjoint {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j))) (P : ∀i,↥(T i)) :
    Function.Injective (fun i=>primaryGenerator (P i).val.val) := by
  intro i j he
  apply idealTuple_injective_of_disjoint T hdis P
  exact primaryPrime_injective (hT i _ (P i).property) (hT j _ (P j).property) he

theorem sum_canonical_weighted_tuples {K : ℕ} (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(canonicalSlotSupport (T i))),
      (∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*
        F (fun i=>primaryGenerator (P i).val.val) := by
  rw [sum_canonical_element_tuples T hT (fun p=>(∏i,W i (elementNorm (p i)/Y i))*F p)]
  apply Finset.sum_congr rfl
  intro P hP
  simp only [primaryTuple_norm (P _).val (hT _ _ (P _).property)]

def idealSlotOfPrimary (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a})) : Finset PrimeIdeal :=
  A.attach.image (fun a : A => (⟨Ideal.span {a.val}, hp a.val a.property⟩ : PrimeIdeal))

lemma idealSlotOfPrimary_supported (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a})) :
    ∀P∈idealSlotOfPrimary A hp,Supported P.val := by
  intro P hP
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hP
  exact hs a.val a.property

lemma primarySlotNormalization (A : Finset O) (hp : ∀a∈A,Prime (Ideal.span {a}))
    (hs : ∀a∈A,Supported (Ideal.span {a}))
    (hprimary : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1) :
    canonicalSlotSupport (idealSlotOfPrimary A hp)=A := by
  have hg (a : A) : primaryGenerator (Ideal.span {a.val})=a.val := by
    apply primaryGenerator_span a.val
    · intro hz
      have hn := (hs a.val a.property).1
      exact hn (by simp [hz])
    · exact hprimary a.val a.property
  apply Finset.ext
  intro a
  constructor
  · intro ha
    obtain ⟨P,hP,hPa⟩ := Finset.mem_image.mp ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hP
    change primaryGenerator (Ideal.span {b.val})=a at hPa
    rw [hg b] at hPa
    exact hPa ▸ b.property
  · intro ha
    apply Finset.mem_image.mpr
    refine ⟨⟨Ideal.span {a},hp a ha⟩,?_,?_⟩
    · exact Finset.mem_image.mpr ⟨⟨a,ha⟩,by simp,rfl⟩
    · exact hg ⟨a,ha⟩

lemma canonicalSlotSupport_disjoint_iff (T U : Finset PrimeIdeal)
    (hT : ∀P∈T,Supported P.val) (hU : ∀P∈U,Supported P.val) :
    Disjoint (canonicalSlotSupport T) (canonicalSlotSupport U)↔Disjoint T U := by
  constructor
  · intro h
    apply Finset.disjoint_left.mpr
    intro P hP hQ
    exact Finset.disjoint_left.mp h (Finset.mem_image.mpr ⟨P,hP,rfl⟩)
      (Finset.mem_image.mpr ⟨P,hQ,rfl⟩)
  · exact canonicalSlotSupport_disjoint T U hT hU

lemma originalPrimarySlots_disjoint (A B : Finset O)
    (hAp : ∀a∈A,Prime (Ideal.span {a})) (hBp : ∀b∈B,Prime (Ideal.span {b}))
    (hAs : ∀a∈A,Supported (Ideal.span {a})) (hBs : ∀b∈B,Supported (Ideal.span {b}))
    (hAn : ∀a∈A,ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (hBn : ∀b∈B,ConcretePrimeRowBridge.goodLambda^2∣b-1) (h : Disjoint A B) :
    Disjoint (idealSlotOfPrimary A hAp) (idealSlotOfPrimary B hBp) := by
  apply (canonicalSlotSupport_disjoint_iff _ _
    (idealSlotOfPrimary_supported A hAp hAs) (idealSlotOfPrimary_supported B hBp hBs)).mp
  simpa only [primarySlotNormalization A hAp hAs hAn,primarySlotNormalization B hBp hBs hBn] using h

theorem sum_original_primary_weighted_tuples {K : ℕ} (A : Fin K→Finset O)
    (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (F : (Fin K→O)→ℂ) :
    (∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val))=
      ∑P : (∀i,↥(idealSlotOfPrimary (A i) (hp i))),
        (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Y i))*F (fun i=>primaryGenerator (P i).val.val) := by
  have he (i : Fin K) := primarySlotNormalization (A i) (hp i) (hs i) (hn i)
  have hh := sum_canonical_weighted_tuples (fun i=>idealSlotOfPrimary (A i) (hp i))
    (fun i=>idealSlotOfPrimary_supported (A i) (hp i) (hs i)) W Y F
  let G (B : Fin K→Finset O) : ℂ :=
    ∑p : (∀i,↥(B i)),(∏i,W i (elementNorm (p i).val/Y i))*F (fun i=>(p i).val)
  have hfun : (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=A := funext he
  change G (fun i=>canonicalSlotSupport (idealSlotOfPrimary (A i) (hp i)))=_ at hh
  rw [hfun] at hh
  exact hh

end SevenEighths.ProbePhysical
end

end OAI
