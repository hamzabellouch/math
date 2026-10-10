import Mathlib

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.SparseGrowth
variable {A B : Type*} [Group A] [Group B] [DecidableEq A] [DecidableEq B]

def HasDegree (S : Finset A) (d : ℕ) : Prop :=
  ∃ C : ℕ, ∀ R : ℕ, ∃ n ≥ R, (S ^ n).card ≤ C * n ^ d

lemma cyclic_inter_lower_bound (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    n + 1 ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
  have hinj : Injective (fun i : ℕ => a^i) := fun _ _ h =>
    (pow_inj_iff_of_orderOf_eq_zero ha0).mp h
  calc
    n+1 = ((Finset.range (n+1)).image (fun i => a^i)).card := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range]
    _ ≤ ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      apply Finset.card_le_card
      intro x hx
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
      have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      refine Finset.mem_filter.mpr ⟨?_,H.pow_mem ha i⟩
      apply Finset.pow_subset_pow_right h1 (Nat.mul_le_mul_left L hi')
      simpa only [pow_mul] using Finset.pow_mem_pow (n := i) haL

lemma quotient_linear_packing (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (n : ℕ) :
    ((S.image (QuotientGroup.mk' H)) ^ n).card * (n+1) ≤
      (S ^ ((L+1)*n)).card := by
  calc
    _ ≤ ((S^n).image (QuotientGroup.mk' H)).card *
        ((S ^ (L*n)).filter (fun x => x ∈ H)).card := by
      rw [Finset.image_pow]
      exact Nat.mul_le_mul_left _ (cyclic_inter_lower_bound S h1 H a ha ha0 L haL n)
    _ ≤ (S ^ (n + L*n)).card := Finset.card_pow_quotient_mul_pow_inter_subgroup_le
    _ = (S ^ ((L+1)*n)).card := by congr 2; ring

theorem quotient_degree_descent (S : Finset A) (h1 : (1 : A) ∈ S)
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a = 0)
    (L : ℕ) (haL : a ∈ S ^ L) (d : ℕ) (hg : HasDegree S (d+1)) :
    HasDegree (S.image (QuotientGroup.mk' H)) d := by
  obtain ⟨C,hC⟩ := hg
  refine ⟨C * (2*(L+1))^(d+1),?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hL : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n, Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hL).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hL
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  have hb : ((S.image (QuotientGroup.mk' H))^n).card * n ≤
      (C*(2*(L+1))^(d+1)*n^d)*n := by
    calc
      _ ≤ ((S.image (QuotientGroup.mk' H))^n).card * (n+1) :=
        Nat.mul_le_mul_left _ (Nat.le_succ n)
      _ ≤ (S ^ ((L+1)*n)).card := quotient_linear_packing S h1 H a ha ha0 L haL n
      _ ≤ (S ^ r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 hnr)
      _ ≤ C*r^(d+1) := hbound
      _ ≤ C*((2*(L+1))*n)^(d+1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn (d+1))
      _ = (C*(2*(L+1))^(d+1)*n^d)*n := by rw [mul_pow,pow_succ n]; ac_rfl
  exact Nat.le_of_mul_le_mul_right hb (by omega : 0<n)

theorem finite_of_degree_zero (S : Finset A) (h1 : (1 : A) ∈ S)
    (hgen : Subgroup.closure (S : Set A) = ⊤) (hg : HasDegree S 0) : Finite A := by
  rcases finite_or_infinite A with hA | hA
  · exact hA
  let _ := hA
  obtain ⟨C,hC⟩ := hg
  obtain ⟨n,hn,hbound⟩ := hC C
  have hinf : (Subgroup.closure (S : Set A) : Set A).Infinite := by
    simpa only [hgen, Subgroup.coe_top] using (Set.infinite_univ : (Set.univ : Set A).Infinite)
  have hlow := Finset.add_one_le_card_pow h1 hinf n
  simp only [pow_zero,mul_one] at hbound
  omega

omit [DecidableEq A] [DecidableEq B] in

theorem virtuallyNilpotent_of_central_kernel (f : A →* B)
    (hc : f.ker ≤ Subgroup.center A) (hB : Group.IsVirtuallyNilpotent B) :
    Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hB
  let _ := hN
  let _ := hNi
  let P := N.comap f
  let _ : P.FiniteIndex := by
    constructor
    rw [N.index_comap]
    exact (inferInstance : (N.subgroupOf f.range).FiniteIndex).index_ne_zero
  let j : P →* N :=
    { toFun := fun a => ⟨f a.val,a.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f a.val b.val) }
  have hker : j.ker ≤ Subgroup.center P := by
    intro a ha
    have haf : (a : A) ∈ f.ker := congrArg Subtype.val ha
    rw [Subgroup.mem_center_iff]
    intro b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hc haf)) b.val)
  exact ⟨P,Subgroup.isNilpotent_of_ker_le_center j hker,inferInstance⟩

omit [DecidableEq A] in

theorem virtuallyNilpotent_of_finiteIndex (H : Subgroup A) [H.FiniteIndex]
    (hH : Group.IsVirtuallyNilpotent H) : Group.IsVirtuallyNilpotent A := by
  obtain ⟨N,hN,hNi⟩ := hH
  let _ := hN
  refine ⟨N.map H.subtype,Group.nilpotent_of_surjective
    (H.subtype.subgroupMap N) (H.subtype.subgroupMap_surjective N),?_⟩
  constructor
  rw [Subgroup.index_map_subtype]
  exact mul_ne_zero hNi.index_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero

lemma exists_mem_pow (S : Finset A) (hsym : S⁻¹=S)
    {a : A} (ha : a ∈ Subgroup.closure (S : Set A)) : ∃ n : ℕ, a ∈ S^n := by
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact ⟨1,by simpa using hx⟩
  | one => exact ⟨0,by simp⟩
  | mul x y hx hy ix iy =>
    obtain ⟨m,hm⟩ := ix
    obtain ⟨n,hn⟩ := iy
    refine ⟨m+n,?_⟩
    rw [pow_add]
    exact Finset.mul_mem_mul hm hn
  | inv x hx ih =>
    obtain ⟨n,hn⟩ := ih
    refine ⟨n,?_⟩
    have hh : x⁻¹ ∈ (S^n)⁻¹ := Finset.inv_mem_inv hn
    simpa only [← inv_pow,hsym] using hh

lemma finite_subset_word_ball (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (T : Finset A) :
    ∃ L : ℕ, T ⊆ S^L := by
  have hword : ∀ a : A, ∃ n : ℕ, a ∈ S^n := fun a =>
    exists_mem_pow S hsym (by rw [hgen]; trivial)
  choose l hl using hword
  refine ⟨T.sup l,fun a ha => ?_⟩
  exact Finset.pow_subset_pow_right h1 (Finset.le_sup ha) (hl a)

theorem degree_of_injective (S : Finset A) (h1 : (1 : A) ∈ S) (hsym : S⁻¹=S)
    (hgen : Subgroup.closure (S : Set A)=⊤) (f : B →* A) (hf : Injective f)
    (T : Finset B) (d : ℕ) (hg : HasDegree S d) : HasDegree T d := by
  obtain ⟨L,hL⟩ := finite_subset_word_ball S h1 hsym hgen (T.image f)
  obtain ⟨C,hC⟩ := hg
  refine ⟨C*(2*(L+1))^d,?_⟩
  intro R
  obtain ⟨r,hr,hbound⟩ := hC ((L+1)*max R 1)
  let n := r/(L+1)
  have hLpos : 0 < L+1 := by omega
  have hnr : (L+1)*n ≤ r := by
    simpa only [n,Nat.mul_comm] using Nat.div_mul_le_self r (L+1)
  have hn : max R 1 ≤ n := (Nat.le_div_iff_mul_le hLpos).mpr (by simpa [Nat.mul_comm] using hr)
  have hn1 : 1 ≤ n := (le_max_right R 1).trans hn
  have hrn : r ≤ (2*(L+1))*n := by
    have hlt := Nat.lt_mul_div_succ r hLpos
    change r < (L+1)*(n+1) at hlt
    have hh : (L+1)*(n+1) ≤ (2*(L+1))*n := by nlinarith
    exact hlt.le.trans hh
  refine ⟨n,(le_max_left R 1).trans hn,?_⟩
  calc
    (T^n).card = ((T^n).image f).card := (Finset.card_image_of_injective _ hf).symm
    _ = ((T.image f)^n).card := by rw [Finset.image_pow]
    _ ≤ ((S^L)^n).card := Finset.card_le_card (Finset.pow_subset_pow_left hL)
    _ = (S^(L*n)).card := by rw [pow_mul]
    _ ≤ (S^r).card := Finset.card_le_card (Finset.pow_subset_pow_right h1 (by nlinarith))
    _ ≤ C*r^d := hbound
    _ ≤ C*((2*(L+1))*n)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hrn d)
    _ = C*(2*(L+1))^d*n^d := by rw [mul_pow,mul_assoc]

def HasPolynomialDegree (A : Type*) [Group A] (d : ℕ) : Prop :=
  ∃ S : Set A, S.Finite ∧ (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure S=⊤ ∧
    ∃ C : ℕ, ∀ R : ℕ, ∃ n≥R, (S^n).ncard ≤ C*n^d

lemma hasPolynomialDegree_iff (d : ℕ) : HasPolynomialDegree A d ↔
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧
      Subgroup.closure (S : Set A)=⊤ ∧ HasDegree S d := by
  constructor
  · rintro ⟨S,hSf,h1,hsym,hgen,C,hC⟩
    refine ⟨hSf.toFinset,by simpa using h1,?_,by simpa using hgen,C,?_⟩
    · apply Finset.coe_injective
      simpa only [Finset.coe_inv,Set.Finite.coe_toFinset] using hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      refine ⟨n,hn,?_⟩
      have hb' : ((hSf.toFinset : Set A)^n).ncard ≤ C*n^d := by
        simpa only [Set.Finite.coe_toFinset] using hb
      simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb'
  · rintro ⟨S,h1,hsym,hgen,C,hC⟩
    refine ⟨S,S.finite_toSet,h1,?_,hgen,C,?_⟩
    · simpa only [Finset.coe_inv] using congrArg (fun T : Finset A => (T : Set A)) hsym
    · intro R
      obtain ⟨n,hn,hb⟩ := hC R
      exact ⟨n,hn,by simpa only [← Finset.coe_pow,Set.ncard_coe_finset] using hb⟩

omit [DecidableEq A] in
lemma HasPolynomialDegree.fg {d : ℕ} (h : HasPolynomialDegree A d) : Group.FG A := by
  obtain ⟨S,hS,_,_,hgen,_⟩ := h
  exact Group.fg_iff.mpr ⟨S,hgen,hS⟩

lemma exists_symmetric_generators [Group.FG A] :
    ∃ S : Finset A, (1 : A)∈S ∧ S⁻¹=S ∧ Subgroup.closure (S : Set A)=⊤ := by
  obtain ⟨F,hF⟩ := Group.FG.out (G := A)
  let S := insert 1 (F ∪ F⁻¹)
  refine ⟨S,by simp [S],?_,?_⟩
  · ext a
    simp only [S,Finset.mem_inv',Finset.mem_insert,Finset.mem_union,inv_eq_one,inv_inv]
    tauto
  · apply top_unique
    rw [← hF]
    apply Subgroup.closure_mono
    intro a ha
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ ha)

theorem HasPolynomialDegree.of_injective {d : ℕ} (h : HasPolynomialDegree A d)
    (f : B →* A) (hf : Injective f) [Group.FG B] : HasPolynomialDegree B d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff d).mp h
  obtain ⟨T,hT1,hTs,hTgen⟩ := exists_symmetric_generators (A := B)
  exact (hasPolynomialDegree_iff d).mpr ⟨T,hT1,hTs,hTgen,
    degree_of_injective S h1 hs hgen f hf T d hg⟩

theorem HasPolynomialDegree.finiteIndex_subgroup {d : ℕ} (h : HasPolynomialDegree A d)
    (H : Subgroup A) [H.FiniteIndex] : HasPolynomialDegree H d := by
  let _ := h.fg
  exact h.of_injective H.subtype H.subtype_injective

theorem HasPolynomialDegree.finite (h : HasPolynomialDegree A 0) : Finite A := by
  obtain ⟨S,h1,_,hgen,hg⟩ := (hasPolynomialDegree_iff 0).mp h
  exact finite_of_degree_zero S h1 hgen hg

theorem HasPolynomialDegree.quotient_descent {d : ℕ} (h : HasPolynomialDegree A (d+1))
    (H : Subgroup A) [H.Normal] (a : A) (ha : a ∈ H) (ha0 : orderOf a=0) :
    HasPolynomialDegree (A ⧸ H) d := by
  obtain ⟨S,h1,hs,hgen,hg⟩ := (hasPolynomialDegree_iff (d+1)).mp h
  obtain ⟨L,haL⟩ := exists_mem_pow S hs (a := a) (by rw [hgen]; trivial)
  apply (hasPolynomialDegree_iff d).mpr
  refine ⟨S.image (QuotientGroup.mk' H),?_,?_,?_,
    quotient_degree_descent S h1 H a ha ha0 L haL d hg⟩
  · exact Finset.mem_image.mpr ⟨1,h1,map_one _⟩
  · rw [← Finset.image_inv,hs]
  · rw [Finset.coe_image,← MonoidHom.map_closure,hgen]
    exact Subgroup.map_top_of_surjective _ QuotientGroup.mk_surjective

omit [DecidableEq A] in
lemma virtuallyNilpotent_of_finite [Finite A] : Group.IsVirtuallyNilpotent A :=
  ⟨⊥,inferInstance,inferInstance⟩

universe u

def BadDegree (d : ℕ) : Prop :=
  ∃ A : Type u, ∃ _ : Group A,
    HasPolynomialDegree A d ∧ ¬Group.IsVirtuallyNilpotent A

theorem minimal_counterexample_center_torsion {d : ℕ} (hbad : BadDegree.{u} d) :
    ∃ e ≤ d, ∃ A : Type u, ∃ _ : Group A,
      HasPolynomialDegree A e ∧ ¬Group.IsVirtuallyNilpotent A ∧
      Infinite A ∧ 0 < e ∧
      ∀ H : Subgroup A, H.FiniteIndex →
        ∀ a : H, a ∈ Subgroup.center H → IsOfFinOrder a := by
  have hex : ∃ e : ℕ, BadDegree.{u} e := ⟨d,hbad⟩
  let e := Nat.find hex
  have he : BadDegree.{u} e := Nat.find_spec hex
  have hmin (k : ℕ) (hk : k < e) : ¬BadDegree.{u} k := Nat.find_min hex hk
  obtain ⟨A,inst,hgrowth,hnot⟩ := he
  let _ := inst
  have hinf : Infinite A := by
    rcases finite_or_infinite A with hfin | hinf
    · let _ := hfin
      exact False.elim (hnot virtuallyNilpotent_of_finite)
    · exact hinf
  have hepos : 0 < e := by
    by_contra hn
    have hez : e=0 := by omega
    rw [hez] at hgrowth
    let _ := hgrowth.finite
    exact hnot virtuallyNilpotent_of_finite
  refine ⟨e,Nat.find_min' hex hbad,A,inst,hgrowth,hnot,hinf,hepos,?_⟩
  intro H hHi a ha
  let _ := hHi
  by_contra horder
  have ha0 : orderOf a=0 := orderOf_eq_zero_iff.mpr horder
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hepos)
  have hHgrowth : HasPolynomialDegree H (k+1) := by
    simpa only [hk,Nat.succ_eq_add_one] using hgrowth.finiteIndex_subgroup H
  have hQgrowth := hHgrowth.quotient_descent (Subgroup.center H) a ha ha0
  have hQnil : Group.IsVirtuallyNilpotent (H ⧸ Subgroup.center H) := by
    by_contra hn
    exact hmin k (by omega) ⟨H ⧸ Subgroup.center H,inferInstance,hQgrowth,hn⟩
  have hHnil : Group.IsVirtuallyNilpotent H :=
    virtuallyNilpotent_of_central_kernel (QuotientGroup.mk' (Subgroup.center H))
      (by rw [QuotientGroup.ker_mk']) hQnil
  exact hnot (virtuallyNilpotent_of_finiteIndex H hHnil)

end CriticalPercolation.SparseGrowth
end
end

end OAI
