import Mathlib

namespace OAI

section
section
namespace ElementaryPositivity.EnergyLaurent
open scoped LaurentSeries
noncomputable section
variable {A B : Type*}

def Admissible (e : A → ℤ) : Prop :=
  (∃K : ℤ,∀a,e a≤K) ∧ ∀E : ℤ,Finite {a // e a=E}

def family (e : A → ℤ) (h : Admissible e) : HahnSeries.SummableFamily ℤ ℚ A where
  toFun a := HahnSeries.single (-e a) 1
  isPWO_iUnion_support' := by
    apply Set.IsWF.isPWO
    apply BddBelow.isWF
    obtain ⟨K,hK⟩:=h.1
    refine ⟨-K,?_⟩
    intro j hj
    simp only [Set.mem_iUnion,HahnSeries.support_single_of_ne (by norm_num : (1:ℚ)≠0),
      Set.mem_singleton_iff] at hj
    obtain ⟨a,rfl⟩:=hj
    exact neg_le_neg (hK a)
  finite_co_support' j := by
    have hs : {a : A | (HahnSeries.single (-e a) (1:ℚ)).coeff j≠0}={a | e a= -j} := by
      ext a
      simp only [HahnSeries.coeff_single,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not,
        Set.mem_ofPred_eq]
      omega
    rw [hs]
    exact Set.finite_coe_iff.mp (h.2 (-j))

def series (e : A → ℤ) (h : Admissible e) : LaurentSeries ℚ := (family e h).hsum

lemma series_coeff (e : A → ℤ) (h : Admissible e) (j : ℤ) :
    (series e h).coeff j=(Nat.card {a // e a= -j}:ℚ) := by
  classical
  let s : Set A:={a | e a= -j}
  have hs : s.Finite:=Set.finite_coe_iff.mp (h.2 (-j))
  rw [series,HahnSeries.SummableFamily.coeff_hsum_eq_sum_of_subset (t:=hs.toFinset)]
  · have hh : ∀a∈hs.toFinset,(family e h a).coeff j=(1:ℚ) := by
      intro a ha
      have ha' : e a= -j:=hs.mem_toFinset.mp ha
      change (HahnSeries.single (-e a) (1:ℚ)).coeff j=1
      simp [ha']
    rw [Finset.sum_congr rfl hh]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
    rw [←s.ncard_eq_toFinset_card hs]
    rfl
  · intro a ha
    change (HahnSeries.single (-e a) (1:ℚ)).coeff j≠0 at ha
    have hja : e a= -j := by
      simp only [HahnSeries.coeff_single,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] at ha
      omega
    exact hs.mem_toFinset.mpr hja

lemma series_eq_of_cards {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f)
    (hc : ∀E,Nat.card {a // e a=E}=Nat.card {b // f b=E}) :
    series e he=series f hf := by
  ext j
  rw [series_coeff,series_coeff,hc]

lemma admissible_prod {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    Admissible (fun p : A×B=>e p.1+f p.2) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    obtain ⟨L,hL⟩:=hf.1
    exact ⟨K+L,fun p=>add_le_add (hK p.1) (hL p.2)⟩
  · intro E
    have hs := ((family e he).mul (family f hf)).finite_co_support (-E)
    have hh : {p : A×B | (((family e he).mul (family f hf)) p).coeff (-E)≠0}=
        {p : A×B | e p.1+f p.2=E} := by
      ext p
      change (HahnSeries.single (-e p.1) (1:ℚ)*HahnSeries.single (-f p.2) 1).coeff (-E)≠0 ↔ _
      rw [HahnSeries.single_mul_single,mul_one,HahnSeries.coeff_single]
      simp only [ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not,Set.mem_ofPred_eq]
      omega
    change {p : A×B | (((family e he).mul (family f hf)) p).coeff (-E)≠0}.Finite at hs
    rw [hh] at hs
    exact hs.to_subtype

lemma series_mul {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    series e he*series f hf=series (fun p : A×B=>e p.1+f p.2) (admissible_prod he hf) := by
  change (family e he).hsum*(family f hf).hsum=_
  rw [←HahnSeries.SummableFamily.hsum_mul]
  congr 1
  apply HahnSeries.SummableFamily.ext
  intro p
  change HahnSeries.single (-e p.1) (1:ℚ)*HahnSeries.single (-f p.2) 1=
    HahnSeries.single (-(e p.1+f p.2)) 1
  rw [HahnSeries.single_mul_single,mul_one,neg_add]

lemma admissible_of_cards {e : A → ℤ} {f : B → ℤ} (he : Admissible e)
    (hf : ∀E,Finite {b // f b=E})
    (hc : ∀E,Nat.card {a // e a=E}=Nat.card {b // f b=E}) : Admissible f := by
  refine ⟨?_,hf⟩
  obtain ⟨K,hK⟩:=he.1
  refine ⟨K,fun b=>?_⟩
  have hp : 0<Nat.card {b' // f b'=f b}:=
    Nat.card_pos_iff.mpr ⟨⟨⟨b,rfl⟩⟩,hf (f b)⟩
  rw [←hc] at hp
  obtain ⟨a,ha⟩:=Nat.card_pos_iff.mp hp |>.1
  rw [←ha]
  exact hK a

lemma admissible_shift {e : A → ℤ} (he : Admissible e) (k : ℤ) :
    Admissible (fun a=>e a+k) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    exact ⟨K+k,fun a=>add_le_add (hK a) le_rfl⟩
  · intro E
    let T:={a : A // e a=E-k}
    let : Finite T:=he.2 (E-k)
    exact Finite.of_injective (fun a : {a : A // e a+k=E}=>
      (⟨a.val,by have h:=a.property; omega⟩:T))
        (fun _ _ h=>Subtype.ext (congrArg (fun t:T=>t.val) h))

lemma series_shift {e : A → ℤ} (he : Admissible e) (k : ℤ) :
    series (fun a=>e a+k) (admissible_shift he k)=
      series e he*HahnSeries.single (-k) (1:ℚ) := by
  ext j
  rw [series_coeff,HahnSeries.coeff_mul_single]
  simp only [mul_one]
  rw [series_coeff]
  congr 1
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun a=>by omega)

lemma series_equiv {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f)
    (q : A ≃ B) (hq : ∀a,f (q a)=e a) : series e he=series f hf := by
  apply series_eq_of_cards
  intro E
  exact Nat.card_congr (q.subtypeEquiv (fun a=>by rw [hq]))

lemma admissible_sum {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    Admissible (Sum.elim e f) := by
  constructor
  · obtain ⟨K,hK⟩:=he.1
    obtain ⟨L,hL⟩:=hf.1
    refine ⟨max K L,?_⟩
    rintro (a|b)
    · exact (hK a).trans (le_max_left _ _)
    · exact (hL b).trans (le_max_right _ _)
  · intro E
    let : Finite {a // e a=E}:=he.2 E
    let : Finite {b // f b=E}:=hf.2 E
    let q : {x // Sum.elim e f x=E} ≃ ({a // e a=E} ⊕ {b // f b=E}) := Equiv.subtypeSum
    exact Finite.of_equiv _ q.symm

lemma series_sum {e : A → ℤ} {f : B → ℤ} (he : Admissible e) (hf : Admissible f) :
    series (Sum.elim e f) (admissible_sum he hf)=series e he+series f hf := by
  ext j
  rw [HahnSeries.coeff_add,series_coeff,series_coeff,series_coeff]
  let : Finite {a // e a= -j}:=he.2 (-j)
  let : Finite {b // f b= -j}:=hf.2 (-j)
  let q : {x // Sum.elim e f x= -j} ≃ ({a // e a= -j} ⊕ {b // f b= -j}) := Equiv.subtypeSum
  rw [Nat.card_congr q,Nat.card_sum,Nat.cast_add]

end
end ElementaryPositivity.EnergyLaurent
end
end

end OAI
