import Mathlib
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.PositionDensities
import OAI.NumberTheory.Jacobsthal.Sieve.MobiusCoprimeExpansion

namespace OAI

namespace Erdos970


namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

noncomputable def crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) : Finset (ZMod (∏ i,m i)) :=
  (Fintype.piFinset E).map (ZMod.prodEquivPi m hcop).symm.toEquiv.toEmbedding

theorem mem_crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (r : ZMod (∏ i,m i)) :
    r ∈ crtResidues m hcop E ↔ ∀ i,(ZMod.prodEquivPi m hcop r) i ∈ E i := by
  constructor
  · intro hr
    obtain ⟨f,hf,hfr⟩ := Finset.mem_map.mp hr
    have he : ZMod.prodEquivPi m hcop r = f := by
      rw [← hfr]
      exact (ZMod.prodEquivPi m hcop).apply_symm_apply f
    rw [he]
    exact Fintype.mem_piFinset.mp hf
  · intro hr
    exact Finset.mem_map.mpr ⟨ZMod.prodEquivPi m hcop r,Fintype.mem_piFinset.mpr hr,
      (ZMod.prodEquivPi m hcop).symm_apply_apply r⟩

theorem crtResidues_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (E : ∀ i,Finset (ZMod (m i))) :
    (crtResidues m hcop E).card = ∏ i,(E i).card := by
  rw [crtResidues,Finset.card_map,Fintype.card_piFinset]

theorem intCast_mem_crtResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (s : ℤ) :
    (s : ZMod (∏ i,m i)) ∈ crtResidues m hcop E ↔ ∀ i,(s : ZMod (m i)) ∈ E i := by
  rw [mem_crtResidues]
  have he (i : ι) : ZMod.prodEquivPi m hcop (s : ZMod (∏ j,m j)) i = (s : ZMod (m i)) := by
    rw [ZMod.prodEquivPi_apply]
    exact map_intCast (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) s
  simp only [he]

end ErdosInverseCRT



namespace Erdos66Dependency.SingleResidueCount

open Finset

noncomputable def residueClass (a b Q r : ℤ) : Finset ℤ :=
  (Ico a b).filter (fun x => Int.ModEq Q x r)

theorem count_exact (a b Q r : ℤ) (hQ : 0 < Q) :
    ((residueClass a b Q r).card : ℤ) =
      max (⌈((b : ℚ) - r) / Q⌉ - ⌈((a : ℚ) - r) / Q⌉) 0 :=
  Int.Ico_filter_modEq_card a b hQ r

lemma count_error_rat (a b Q r : ℤ) (hQ : 0 < Q) (hab : a ≤ b) :
    |((residueClass a b Q r).card : ℚ) - ((b : ℚ) - a) / Q| ≤ 1 := by
  have hQQ : (0:ℚ) < Q := by exact_mod_cast hQ
  have hx : ((a : ℚ) - r) / Q ≤ ((b : ℚ) - r) / Q :=
    div_le_div_of_nonneg_right (by exact_mod_cast sub_le_sub_right hab r) hQQ.le
  have hceil := Int.ceil_mono hx
  have hcount := count_exact a b Q r hQ
  rw [max_eq_left (sub_nonneg.mpr hceil)] at hcount
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) hcount
  push_cast at hcast
  rw [hcast]
  have ha := Int.le_ceil (((a : ℚ) - r) / Q)
  have ha' := Int.ceil_lt_add_one (((a : ℚ) - r) / Q)
  have hb := Int.le_ceil (((b : ℚ) - r) / Q)
  have hb' := Int.ceil_lt_add_one (((b : ℚ) - r) / Q)
  have heq : ((b : ℚ) - a) / Q = ((b : ℚ) - r) / Q - ((a : ℚ) - r) / Q := by ring
  rw [heq,abs_le]
  constructor <;> linarith

theorem count_error_length (a b Q r : ℤ) (hQ : 0 < Q) (hab : a ≤ b) :
    |((residueClass a b Q r).card : ℝ) - ((b : ℝ) - a) / Q| ≤ 1 := by
  have h := count_error_rat a b Q r hQ hab
  have hh := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hh
  exact hh

theorem count_error (a b Q r : ℤ) (hQ : 0 < Q) :
    |((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ) / Q| ≤ 1 := by
  by_cases hab : a ≤ b
  · have hc : ((Ico a b).card : ℤ) = b-a := by
      rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hc
    push_cast at hcast
    rw [hcast]
    exact count_error_length a b Q r hQ hab
  · have he : Ico a b = (∅ : Finset ℤ) := Ico_eq_empty_of_le (le_of_not_ge hab)
    simp [residueClass,he]

end Erdos66Dependency.SingleResidueCount



namespace ErdosVarianceMoments
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem crt_coordinate_val {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (r : ZMod (∏ i,m i)) (i : ι) :
    (ZMod.prodEquivPi m hcop r) i = (r.val : ZMod (m i)) := by
  calc
    (ZMod.prodEquivPi m hcop r) i =
        (ZMod.prodEquivPi m hcop (r.val : ZMod (∏ j,m j))) i := by
      rw [ZMod.natCast_zmod_val]
    _ = (r.val : ZMod (m i)) := by
      rw [ZMod.prodEquivPi_apply]
      exact map_natCast (ZMod.castHom (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) (ZMod (m i))) r.val

theorem literal_residue_choices_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    [NeZero (∏ i,m i)] (E : ∀ i,Finset (ZMod (m i))) :
    (Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i)).card =
      ∏ i,(E i).card := by
  have he : Finset.univ.filter (fun r : ZMod (∏ i,m i) => ∀ i,(r.val : ZMod (m i)) ∈ E i) =
      ErdosInverseCRT.crtResidues m hcop E := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,ErdosInverseCRT.mem_crtResidues,
      crt_coordinate_val]
  rw [he,ErdosInverseCRT.crtResidues_card]

theorem canonical_filter_card (N : ℕ) [NeZero N] (f : ℕ → Prop) [DecidablePred f] :
    (Finset.univ.filter (fun r : ZMod N => f r.val)).card =
      ((Finset.range N).filter f).card := by
  apply Finset.card_bij (fun r _ => r.val)
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr r.val_lt,(Finset.mem_filter.mp hr).2⟩
  · intro r _hr s _hs he
    exact ZMod.val_injective N he
  · intro n hn
    have hlt := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    refine ⟨(n : ZMod N),?_,?_⟩
    · simp only [Finset.mem_filter,Finset.mem_univ,true_and,ZMod.val_natCast,Nat.mod_eq_of_lt hlt]
      exact (Finset.mem_filter.mp hn).2
    · simp only [ZMod.val_natCast,Nat.mod_eq_of_lt hlt]

noncomputable def allowedClasses (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) : Finset (ZMod p) :=
  Finset.univ \ forbiddenClasses S p u c

theorem mem_allowedClasses (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c x : ZMod p) :
    x ∈ allowedClasses S p u c ↔ ∀ j ∈ S,x+(u : ZMod p)*(j : ZMod p) ≠ c := by
  simp only [allowedClasses,Finset.mem_sdiff,Finset.mem_univ,true_and,mem_forbiddenClasses,
    not_exists,not_and]

theorem allowedClasses_card (S : Finset ℕ) (p : ℕ) [NeZero p]
    (u : (ZMod p)ˣ) (c : ZMod p) :
    (allowedClasses S p u c).card = p-(positionResidues S p).card := by
  rw [allowedClasses,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,ZMod.card,
    forbiddenClasses_card]

end ErdosVarianceMoments



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

noncomputable def integerCRTResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (E : ∀ i,Finset (ZMod (m i))) : Finset ℤ :=
  (crtResidues m hcop E).image (fun r => (r.val : ℤ))

theorem integerCRTResidues_card {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    (integerCRTResidues m hcop E).card = ∏ i,(E i).card := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  have hinj : Function.Injective (fun r : ZMod (∏ i,m i) => (r.val : ℤ)) := by
    intro r s he
    exact ZMod.val_injective _ (Int.ofNat_inj.mp he)
  rw [integerCRTResidues,Finset.card_image_of_injective _ hinj,crtResidues_card]

theorem integerCRTResidues_subset {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    integerCRTResidues m hcop E ⊆ Finset.Ico 0 (∏ i,m i : ℕ) := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  intro s hs
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _,by exact_mod_cast ZMod.val_lt r⟩

theorem emod_mem_integerCRTResidues {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) (s : ℤ) :
    s % (∏ i,m i : ℕ) ∈ integerCRTResidues m hcop E ↔ ∀ i,(s : ZMod (m i)) ∈ E i := by
  let : NeZero (∏ i,m i) := ⟨hN.ne'⟩
  rw [← intCast_mem_crtResidues m hcop E s,← ZMod.val_intCast s]
  constructor
  · intro hs
    obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hs
    have heq : r = (s : ZMod (∏ i,m i)) := ZMod.val_injective _ (Int.ofNat_inj.mp he)
    rwa [← heq]
  · intro hs
    exact Finset.mem_image.mpr ⟨(s : ZMod (∏ i,m i)),hs,rfl⟩

theorem product_card_le_moduli {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (E : ∀ i,Finset (ZMod (m i))) (hm : ∀ i,0 < m i) :
    (∏ i,(E i).card) ≤ ∏ i,m i := by
  apply Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _)
  intro i hi
  let : NeZero (m i) := ⟨(hm i).ne'⟩
  simpa only [ZMod.card] using Finset.card_le_univ (E i)

end ErdosInverseCRT



namespace Erdos66Dependency.ResidueLifts

open Finset SingleResidueCount

noncomputable def liftsOn (J : Finset ℤ) (Q : ℤ) (A : Finset ℤ) : Finset ℤ :=
  J.filter (fun x => x % Q ∈ A)

theorem lifts_eq_union (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    liftsOn (Ico a b) Q A = A.biUnion (residueClass a b Q) := by
  classical
  ext x
  simp only [liftsOn,mem_filter,mem_biUnion,residueClass]
  constructor
  · rintro ⟨hx,hA⟩
    exact ⟨x%Q,hA,hx,by unfold Int.ModEq; rw [Int.emod_emod]⟩
  · rintro ⟨r,hr,hx,hmod⟩
    have hrange := mem_Ico.mp (hA hr)
    have he : x%Q=r := by simpa only [Int.ModEq,Int.emod_eq_of_lt hrange.1 hrange.2] using hmod
    exact ⟨hx,he ▸ hr⟩

theorem classes_disjoint (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    (A : Set ℤ).PairwiseDisjoint (residueClass a b Q) := by
  intro r hr s hs hne
  apply Finset.disjoint_left.mpr
  intro x hxr hxs
  have hrange := mem_Ico.mp (hA hr)
  have hsrange := mem_Ico.mp (hA hs)
  have hmodr := (mem_filter.mp hxr).2
  have hmods := (mem_filter.mp hxs).2
  have heqR : x%Q=r := by simpa only [Int.ModEq,Int.emod_eq_of_lt hrange.1 hrange.2] using hmodr
  have heqS : x%Q=s := by simpa only [Int.ModEq,Int.emod_eq_of_lt hsrange.1 hsrange.2] using hmods
  exact hne (heqR.symm.trans heqS)

theorem count_eq_sum (a b Q : ℤ) (A : Finset ℤ) (hA : A ⊆ Ico 0 Q) :
    (liftsOn (Ico a b) Q A).card = ∑ r ∈ A, (residueClass a b Q r).card := by
  rw [lifts_eq_union a b Q A hA,card_biUnion (classes_disjoint a b Q A hA)]

theorem count_error (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q) (hA : A ⊆ Ico 0 Q) :
    |((liftsOn (Ico a b) Q A).card : ℝ) - ((Ico a b).card : ℝ) * A.card / Q| ≤ A.card := by
  rw [count_eq_sum a b Q A hA,Nat.cast_sum]
  have heq : (∑ r ∈ A, ((residueClass a b Q r).card : ℝ)) - ((Ico a b).card : ℝ)*A.card/Q =
      ∑ r ∈ A, (((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ)/Q) := by
    rw [sum_sub_distrib]
    simp only [sum_const,nsmul_eq_mul]
    ring
  rw [heq]
  calc
    _ ≤ ∑ r ∈ A, |((residueClass a b Q r).card : ℝ) - ((Ico a b).card : ℝ)/Q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ A, (1:ℝ) := sum_le_sum (fun r _ => SingleResidueCount.count_error a b Q r hQ)
    _ = (A.card:ℝ) := by simp

lemma card_Ico_real {a b : ℤ} (hab : a ≤ b) : ((Ico a b).card : ℝ) = (b:ℝ)-a := by
  have h : ((Ico a b).card : ℤ) = b-a := by rw [Int.card_Ico,Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
  have hh := congrArg (fun z : ℤ => (z:ℝ)) h
  push_cast at hh
  exact hh

theorem count_error_length (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q)
    (hA : A ⊆ Ico 0 Q) (hab : a ≤ b) :
    |((liftsOn (Ico a b) Q A).card : ℝ) - ((b:ℝ)-a)*A.card/Q| ≤ A.card := by
  simpa only [card_Ico_real hab] using count_error a b Q A hQ hA

theorem count_error_Icc (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q) (hA : A ⊆ Ico 0 Q) :
    |((liftsOn (Icc a b) Q A).card : ℝ) - ((Icc a b).card : ℝ)*A.card/Q| ≤ A.card := by
  have he : Icc a b = Ico a (b+1) := by ext x; simp only [mem_Icc,mem_Ico]; omega
  rw [he]
  exact count_error a (b+1) Q A hQ hA

theorem count_error_Ioc (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q) (hA : A ⊆ Ico 0 Q) :
    |((liftsOn (Ioc a b) Q A).card : ℝ) - ((Ioc a b).card : ℝ)*A.card/Q| ≤ A.card := by
  have he : Ioc a b = Ico (a+1) (b+1) := by ext x; simp only [mem_Ioc,mem_Ico]; omega
  rw [he]
  exact count_error (a+1) (b+1) Q A hQ hA

theorem count_error_Ioo (a b Q : ℤ) (A : Finset ℤ) (hQ : 0 < Q) (hA : A ⊆ Ico 0 Q) :
    |((liftsOn (Ioo a b) Q A).card : ℝ) - ((Ioo a b).card : ℝ)*A.card/Q| ≤ A.card := by
  have he : Ioo a b = Ico (a+1) b := by ext x; simp only [mem_Ioo,mem_Ico]; omega
  rw [he]
  exact count_error (a+1) b Q A hQ hA

end Erdos66Dependency.ResidueLifts



namespace ErdosInverseCRT
open Erdos66Dependency
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable

noncomputable def crtSlopes {ι : Type*} [Fintype ι] (a b : ℤ) (m : ι → ℕ)
    (E : ∀ i,Finset (ZMod (m i))) : Finset ℤ :=
  (Finset.Ico a b).filter (fun s => ∀ i,(s : ZMod (m i)) ∈ E i)

theorem crtSlopes_eq_lifts {ι : Type*} [Fintype ι] (a b : ℤ) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    crtSlopes a b m E = ResidueLifts.liftsOn (Finset.Ico a b) (∏ i,m i : ℕ) (integerCRTResidues m hcop E) := by
  ext s
  simp only [crtSlopes,ResidueLifts.liftsOn,Finset.mem_filter,emod_mem_integerCRTResidues m hcop E hN s]

theorem crt_interval_count_upper {ι : Type*} [Fintype ι] (a b : ℤ) (hab : a ≤ b) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    ((crtSlopes a b m E).card : ℝ) ≤
      ((b : ℝ)-(a : ℝ))*((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,m i : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  have hQ : (0 : ℤ) < (∏ i,m i : ℕ) := by exact_mod_cast hN
  have hh := ResidueLifts.count_error_length a b (∏ i,m i : ℕ) (integerCRTResidues m hcop E)
    hQ (integerCRTResidues_subset m hcop E hN) hab
  rw [← crtSlopes_eq_lifts a b m hcop E hN,integerCRTResidues_card m hcop E hN] at hh
  have hup := (abs_le.mp hh).2
  push_cast at hup ⊢
  linarith

theorem crt_initial_count_upper {ι : Type*} [Fintype ι] (p : ℕ) (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j)))
    (E : ∀ i,Finset (ZMod (m i))) (hN : 0 < ∏ i,m i) :
    ((crtSlopes 0 p m E).card : ℝ) ≤
      (p : ℝ)*((∏ i,(E i).card : ℕ) : ℝ)/(∏ i,m i : ℕ)+((∏ i,(E i).card : ℕ) : ℝ) := by
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero] using
    crt_interval_count_upper 0 p (Int.natCast_nonneg p) m hcop E hN

end ErdosInverseCRT



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

abbrev binaryModuli (d l : ℕ) (i : Bool) : ℕ := match i with
  | false => d
  | true => l

theorem binary_coprime (d l : ℕ) (h : d.Coprime l) :
    Pairwise (fun i j => Nat.Coprime (binaryModuli d l i) (binaryModuli d l j)) := by
  intro i j hij
  cases i <;> cases j
  · exact False.elim (hij rfl)
  · exact h
  · exact h.symm
  · exact False.elim (hij rfl)

noncomputable def binaryClasses (d l : ℕ) (A : Finset (ZMod l)) (i : Bool) :
    Finset (ZMod (binaryModuli d l i)) := match i with
  | false => {0}
  | true => A

theorem binary_modulus_product (d l : ℕ) : (∏ i : Bool,binaryModuli d l i) = d*l := by
  simp [binaryModuli,mul_comm]

noncomputable def divisibleResidues (d l : ℕ) (h : d.Coprime l) (A : Finset (ZMod l)) : Finset ℤ :=
  ErdosInverseCRT.integerCRTResidues (binaryModuli d l) (binary_coprime d l h) (binaryClasses d l A)

theorem divisibleResidues_card (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) : (divisibleResidues d l h A).card = A.card := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  unfold divisibleResidues
  rw [ErdosInverseCRT.integerCRTResidues_card _ _ _ hN]
  simp only [Fintype.prod_bool,binaryClasses,Finset.card_singleton,mul_one]

theorem divisibleResidues_range (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) :
    divisibleResidues d l h A ⊆ Finset.Ico 0 (d*l : ℕ) := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  simpa only [divisibleResidues,binary_modulus_product] using ErdosInverseCRT.integerCRTResidues_subset
    (binaryModuli d l) (binary_coprime d l h) (binaryClasses d l A) hN

theorem mem_divisibleResidues (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) (m : ℤ) :
    m % (d*l : ℕ) ∈ divisibleResidues d l h A ↔ (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A := by
  have hN : 0 < ∏ i : Bool,binaryModuli d l i := by rw [binary_modulus_product]; positivity
  unfold divisibleResidues
  rw [← binary_modulus_product d l,ErdosInverseCRT.emod_mem_integerCRTResidues _ _ _ hN]
  simp only [Bool.forall_bool,binaryClasses,binaryModuli]
  change ((m : ZMod d) ∈ ({0} : Finset (ZMod d)) ∧ (m : ZMod l) ∈ A) ↔ _
  rw [Finset.mem_singleton,ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem divisible_residue_count (d l : ℕ) (hd : 0 < d) (hl : 0 < l)
    (h : d.Coprime l) (A : Finset (ZMod l)) (b c : ℤ) :
    |(((Finset.Ico b c).filter (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A)).card : ℝ) -
      ((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l)| ≤ A.card := by
  have he : (Finset.Ico b c).filter (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A) =
      Erdos66Dependency.ResidueLifts.liftsOn (Finset.Ico b c) (d*l : ℕ) (divisibleResidues d l h A) := by
    ext m
    simp only [Erdos66Dependency.ResidueLifts.liftsOn,Finset.mem_filter,
      mem_divisibleResidues d l hd hl h A]
  rw [he]
  have hh := Erdos66Dependency.ResidueLifts.count_error b c (d*l : ℕ) (divisibleResidues d l h A)
    (by exact_mod_cast Nat.mul_pos hd hl) (divisibleResidues_range d l hd hl h A)
  simpa only [divisibleResidues_card d l hd hl h A,Nat.cast_mul,Int.cast_mul,Int.cast_natCast] using hh

end ErdosCoprimeResidueInterval



namespace ErdosInverseCRT
attribute [local instance] Classical.decEq

def affineEquiv {R : Type*} [CommRing R] (c : Rˣ) (b : R) : R ≃ R where
  toFun s := (c : R)*s+b
  invFun t := (↑(c⁻¹) : R)*(t-b)
  left_inv s := by
    change (↑(c⁻¹) : R)*((c : R)*s+b-b) = s
    have he : (c : R)*s+b-b = (c : R)*s := by ring
    rw [he,Units.inv_mul_cancel_left]
  right_inv t := by
    change (c : R)*((↑(c⁻¹) : R)*(t-b))+b = t
    rw [Units.mul_inv_cancel_left]
    ring

noncomputable def affineResidues {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) : Finset R :=
  E.map (affineEquiv c b).symm.toEmbedding

theorem mem_affineResidues {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) (s : R) :
    s ∈ affineResidues c b E ↔ (c : R)*s+b ∈ E := by
  constructor
  · intro hs
    obtain ⟨t,ht,he⟩ := Finset.mem_map.mp hs
    have hh : (c : R)*s+b = t := by
      rw [← he]
      exact (affineEquiv c b).apply_symm_apply t
    rwa [hh]
  · intro hs
    exact Finset.mem_map.mpr ⟨(c : R)*s+b,hs,(affineEquiv c b).symm_apply_apply s⟩

theorem affineResidues_card {R : Type*} [CommRing R] (c : Rˣ) (b : R) (E : Finset R) :
    (affineResidues c b E).card = E.card := Finset.card_map _

theorem source_edge_class_affine {R : Type*} [CommRing R] (p q : Rˣ) (a b s : R) :
    (a-b-(q : R)*s)*(↑((p*q)⁻¹) : R) =
      (↑(-(p⁻¹)) : R)*s+(a-b)*(↑((p*q)⁻¹) : R) := by
  have hc : (q : R)*(↑((p*q)⁻¹) : R) = (↑(p⁻¹) : R) := by
    change (↑(q*(p*q)⁻¹) : R) = (↑(p⁻¹) : R)
    congr 1
    simp [mul_inv_rev]
  calc
    _ = (a-b)*(↑((p*q)⁻¹) : R)-s*((q : R)*(↑((p*q)⁻¹) : R)) := by ring
    _ = _ := by rw [hc];simp only [Units.val_neg];ring

end ErdosInverseCRT



namespace ErdosCoprimeResidueInterval
open scoped ArithmeticFunction.Moebius
attribute [local instance] Classical.propDecidable

noncomputable def coprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℤ) : Finset ℤ :=
  (Finset.Ico b c).filter (fun m => H.Coprime m.natAbs ∧ (m : ZMod l) ∈ A)

theorem coprime_residue_count (H l : ℕ) (hH : 0 < H) (hl : 0 < l)
    (hcop : H.Coprime l) (A : Finset (ZMod l)) (b c : ℤ) :
    |((coprimeResidues H l A b c).card : ℝ) - ((Finset.Ico b c).card : ℝ)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤
        (H.divisors.card : ℝ)*(A.card : ℝ) := by
  classical
  let f (d : ℕ) := (((Finset.Ico b c).filter
    (fun m : ℤ => (d : ℤ) ∣ m ∧ (m : ZMod l) ∈ A)).card : ℝ)
  have hcount : ((coprimeResidues H l A b c).card : ℝ) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*f d := by
    convert coprime_count_expansion H hH (Finset.Ico b c) (fun m : ℤ => (m : ZMod l) ∈ A) using 1
    · apply congrArg (fun S : Finset ℤ => (S.card : ℝ))
      ext m
      simp only [coprimeResidues,Finset.mem_filter]
    · apply Finset.sum_congr rfl
      intro d _
      congr 1
      apply congrArg (fun S : Finset ℤ => (S.card : ℝ))
      ext m
      simp only [Finset.mem_filter]
  have he : ((coprimeResidues H l A b c).card : ℝ) - ((Finset.Ico b c).card : ℝ)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) =
      ∑ d ∈ H.divisors, (μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l)) := by
    rw [hcount]
    rw [← moebius_density H hH]
    simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    dsimp only [f]
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ H.divisors, |(μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ H.divisors, (A.card : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hdl : d.Coprime l := Nat.Coprime.of_dvd_left (Nat.dvd_of_mem_divisors hd) hcop
      have herr := divisible_residue_count d l hd0 hl hdl A b c
      change |(μ d : ℝ)*(f d-((Finset.Ico b c).card : ℝ)*(A.card : ℝ)/((d : ℝ)*l))| ≤ (A.card : ℝ)
      rw [abs_mul]
      exact (mul_le_mul (moebius_abs_le_one d) herr (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
    _ = _ := by simp

theorem coprime_residue_count_length (H l : ℕ) (hH : 0 < H) (hl : 0 < l)
    (hcop : H.Coprime l) (A : Finset (ZMod l)) (b c : ℤ) (hbc : b ≤ c) :
    |((coprimeResidues H l A b c).card : ℝ) - ((c : ℝ)-b)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤
        (H.divisors.card : ℝ)*(A.card : ℝ) := by
  simpa only [Erdos66Dependency.ResidueLifts.card_Ico_real hbc] using
    coprime_residue_count H l hH hl hcop A b c

end ErdosCoprimeResidueInterval



namespace ErdosCoprimeResidueInterval
attribute [local instance] Classical.propDecidable

noncomputable def realCoprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℝ) : Finset ℤ :=
  coprimeResidues H l A ⌈b⌉ ⌈c⌉

theorem mem_realCoprimeResidues (H l : ℕ) (A : Finset (ZMod l)) (b c : ℝ) (m : ℤ) :
    m ∈ realCoprimeResidues H l A b c ↔
      b ≤ (m : ℝ) ∧ (m : ℝ) < c ∧ H.Coprime m.natAbs ∧ (m : ZMod l) ∈ A := by
  simp only [realCoprimeResidues,coprimeResidues,Finset.mem_filter,Finset.mem_Ico,
    Int.ceil_le,Int.lt_ceil,and_assoc]

theorem ceiling_interval_error (b c : ℝ) (hbc : b ≤ c) :
    |((Finset.Ico ⌈b⌉ ⌈c⌉).card : ℝ)-(c-b)| ≤ 1 := by
  rw [Erdos66Dependency.ResidueLifts.card_Ico_real (Int.ceil_mono hbc),abs_le]
  constructor <;> linarith [Int.le_ceil b,Int.ceil_lt_add_one b,Int.le_ceil c,Int.ceil_lt_add_one c]

theorem coprime_density_bounds (H l : ℕ) (hH : 0 < H) (hl : 0 < l) (A : Finset (ZMod l)) :
    0 ≤ ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) ∧
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ)) ≤ (A.card : ℝ) := by
  have hV : (H.totient : ℝ)/(H : ℝ) ≤ 1 :=
    (div_le_one (show (0 : ℝ) < H by exact_mod_cast hH)).mpr (by exact_mod_cast Nat.totient_le H)
  have hAl : (A.card : ℝ)/(l : ℝ) ≤ A.card :=
    div_le_self (Nat.cast_nonneg _) (by exact_mod_cast hl)
  refine ⟨by positivity,?_⟩
  exact (mul_le_mul_of_nonneg_right hV (by positivity)).trans (by simpa only [one_mul] using hAl)

theorem real_coprime_residue_count (H l : ℕ) (hH : 0 < H) (hl : 0 < l)
    (hcop : H.Coprime l) (A : Finset (ZMod l)) (b c : ℝ) (hbc : b ≤ c) :
    |((realCoprimeResidues H l A b c).card : ℝ) - (c-b)*
      ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤
        2*(H.divisors.card : ℝ)*(A.card : ℝ) := by
  let rho := ((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))
  let L := ((Finset.Ico ⌈b⌉ ⌈c⌉).card : ℝ)
  have hr := coprime_density_bounds H l hH hl A
  have hbase := coprime_residue_count H l hH hl hcop A ⌈b⌉ ⌈c⌉
  have hround := ceiling_interval_error b c hbc
  have hpert : |(L-(c-b))*rho| ≤ A.card := by
    rw [abs_mul,abs_of_nonneg hr.1]
    exact (mul_le_mul_of_nonneg_right hround hr.1).trans (by simpa only [one_mul] using hr.2)
  have ht : (1 : ℝ) ≤ H.divisors.card := by
    exact_mod_cast Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr hH.ne'⟩)
  have htA := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg A.card)
  have he : ((realCoprimeResidues H l A b c).card : ℝ)-(c-b)*rho =
      (((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*rho)+(L-(c-b))*rho := by
    dsimp [realCoprimeResidues]
    ring
  change |((realCoprimeResidues H l A b c).card : ℝ)-(c-b)*((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤ _
  rw [mul_assoc,he]
  have hh := abs_add_le (((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*rho) ((L-(c-b))*rho)
  change |((coprimeResidues H l A ⌈b⌉ ⌈c⌉).card : ℝ)-L*((H.totient : ℝ)/(H : ℝ))*((A.card : ℝ)/(l : ℝ))| ≤ _ at hbase
  rw [mul_assoc] at hbase
  nlinarith [hh,hpert,hbase,htA]

end ErdosCoprimeResidueInterval


end Erdos970

end OAI
