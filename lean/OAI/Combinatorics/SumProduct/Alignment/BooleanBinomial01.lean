import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeFaces01
import OAI.Combinatorics.SumProduct.Alignment.LeibmanSquare01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology
end
end
 

 
section
open scoped commutatorElement Pointwise

 

namespace HorizontalCubeCharacter
open CubeFaces
variable {G A ι : Type*} [Group G] [CommGroup A] [DecidableEq ι]

 
def faceLift (H : Filtration G) (I D : Finset ι) (k : ℕ)
    (hDI : D ⊆ I) (hDk : D.card ≤ k) : H.level k →* cube H I 0 where
  toFun x := ⟨face D (x:G),face_mem_cube H hDI (by
    simpa using H.antitone hDk x.property)⟩
  map_one' := by apply Subtype.ext; exact (face D).map_one
  map_mul' x y := by apply Subtype.ext; exact (face D).map_mul (x:G) (y:G)

@[simp] lemma faceLift_coe (H : Filtration G) (I D : Finset ι) (k : ℕ)
    (hDI : D ⊆ I) (hDk : D.card ≤ k) (x : H.level k) :
    ((faceLift H I D k hDI hDk x : cube H I 0) : Finset ι → G) = face D (x:G) := rfl

 
lemma eq_one_of_faces (H : Filtration G) (I : Finset ι)
    (χ : cube H I 0 →* A)
    (hχ : ∀ D (hDI : D ⊆ I), χ.comp (faceLift H I D D.card hDI le_rfl) = 1) : χ = 1 := by
  let K : Subgroup (Finset ι → G) := χ.ker.map (cube H I 0).subtype
  have hle : cube H I 0 ≤ K := by
    refine iSup_le fun D => iSup_le fun hDI => ?_
    rintro f ⟨g,hg,rfl⟩
    have hg' : g ∈ H.level D.card := by simpa using hg
    refine ⟨faceLift H I D D.card hDI le_rfl ⟨g,hg'⟩,?_,rfl⟩
    change χ (faceLift H I D D.card hDI le_rfl ⟨g,hg'⟩) = 1
    exact DFunLike.congr_fun (hχ D hDI) ⟨g,hg'⟩
  ext x
  rcases hle x.property with ⟨y,hy,he⟩
  have he' : y = x := Subtype.ext he
  simpa [he'] using hy

 
lemma split_face (D : Finset ι) (i k : ℕ) (hD : D.card ≤ i+k) :
    ∃ E F : Finset ι, E ⊆ D ∧ F ⊆ D ∧ E.card ≤ i ∧ F.card ≤ k ∧ E ∪ F = D := by
  obtain ⟨E,hED,hE⟩ := Finset.exists_subset_card_eq (s := D) (Nat.min_le_right i D.card)
  refine ⟨E,D\E,hED,Finset.sdiff_subset,?_,?_,?_⟩
  · rw [hE]; exact Nat.min_le_left _ _
  · rw [Finset.card_sdiff_of_subset hED,hE]
    omega
  · exact Finset.union_sdiff_of_subset hED

 
structure MaximalFace (H : Filtration G) (I : Finset ι)
    (χ : cube H I 0 →* A) where
  level : ℕ
  positive : 0 < level
  face : Finset ι
  subset : face ⊆ I
  card_le : face.card ≤ level
  nontrivial : χ.comp (faceLift H I face level subset card_le) ≠ 1
  maximal : ∀ k, level < k → ∀ D (hDI : D ⊆ I) (hDk : D.card ≤ k),
    χ.comp (faceLift H I D k hDI hDk) = 1

noncomputable section

 

theorem exists_maximalFace (H : Filtration G) (I : Finset ι)
    (h01 : H.level 0 = H.level 1) (s : ℕ) (hs : H.level (s+1) = ⊥)
    (χ : cube H I 0 →* A) (hne : χ ≠ 1) : Nonempty (MaximalFace H I χ) := by
  classical
  have hgen : ∃ D, ∃ hDI : D ⊆ I,
      χ.comp (faceLift H I D D.card hDI le_rfl) ≠ 1 := by
    by_contra! hn
    exact hne (eq_one_of_faces H I χ hn)
  obtain ⟨D,hDI,hD⟩ := hgen
  have hex : ∃ k, 0 < k ∧ ∃ D, ∃ hDI : D ⊆ I, ∃ hDk : D.card ≤ k,
      χ.comp (faceLift H I D k hDI hDk) ≠ 1 := by
    by_cases hc : D.card = 0
    · refine ⟨1,by omega,D,hDI,by omega,?_⟩
      intro hh
      apply hD
      ext x
      have hx : (x:G) ∈ H.level 1 := by rw [← h01,← hc]; exact x.property
      have he := DFunLike.congr_fun hh ⟨(x:G),hx⟩
      exact he
    · exact ⟨D.card,by omega,D,hDI,le_rfl,hD⟩
  let P (k : ℕ) : Prop := 0 < k ∧ ∃ D, ∃ hDI : D ⊆ I, ∃ hDk : D.card ≤ k,
      χ.comp (faceLift H I D k hDI hDk) ≠ 1
  have hbound : ∀ k, P k → k ≤ s := by
    rintro k ⟨hk,D,hDI,hDk,hχ⟩
    by_contra! hsk
    apply hχ
    ext x
    have hx : (x:G) ∈ H.level (s+1) := H.antitone hsk x.property
    rw [hs,Subgroup.mem_bot] at hx
    have hx' : x = 1 := Subtype.ext hx
    simp [hx']
  let S := (Finset.range (s+1)).filter P
  have hS : S.Nonempty := by
    obtain ⟨k,hk⟩ := hex
    exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbound k hk; omega),hk⟩⟩
  obtain ⟨j,hj,hmax⟩ := S.exists_max_image id hS
  have hjP : P j := (Finset.mem_filter.mp hj).2
  rcases hjP with ⟨hj,D,hDI,hDj,hn⟩
  refine ⟨⟨j,hj,D,hDI,hDj,hn,?_⟩⟩
  intro k hjk E hEI hEk
  by_contra hke
  have hp : P k := ⟨by omega,E,hEI,hEk,hke⟩
  have hh := hmax k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have := hbound k hp; omega),hp⟩)
  change k ≤ j at hh
  omega

 

structure LevelCharacter (H : Filtration G) (j : ℕ) where
  value : H.level j →* A
  kills_next : ∀ x (hx : x ∈ H.level (j+1)),
    value ⟨x,H.antitone (Nat.le_succ j) hx⟩ = 1
  kills_brackets : ∀ i k : ℕ, 0 < i → 0 < k → ∀ hik : i+k=j,
    ∀ x (hx : x ∈ H.level i) y (hy : y ∈ H.level k),
      value ⟨⁅x,y⁆,by
        rw [← hik]
        exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩ = 1

 
def MaximalFace.character {H : Filtration G} {I : Finset ι}
    {χ : cube H I 0 →* A} (M : MaximalFace H I χ) :
    LevelCharacter (A := A) H M.level where
  value := χ.comp (faceLift H I M.face M.level M.subset M.card_le)
  kills_next x hx := by
    have h := DFunLike.congr_fun
      (M.maximal (M.level+1) (Nat.lt_succ_self _) M.face M.subset
        (M.card_le.trans (Nat.le_succ _))) ⟨x,hx⟩
    exact h
  kills_brackets i k hi hk hik x hx y hy := by
    obtain ⟨E,F,hED,hFD,hEi,hFk,hEF⟩ := split_face M.face i k (by rw [hik]; exact M.card_le)
    let u := faceLift H I E i (hED.trans M.subset) hEi ⟨x,hx⟩
    let v := faceLift H I F k (hFD.trans M.subset) hFk ⟨y,hy⟩
    have hcomm : ⁅u,v⁆ = faceLift H I M.face M.level M.subset M.card_le
        ⟨⁅x,y⁆,by rw [← hik]; exact H.commutator_le i k (Subgroup.commutator_mem_commutator hx hy)⟩ := by
      apply Subtype.ext
      change ⁅CubeFaces.face E x,CubeFaces.face F y⁆ = CubeFaces.face M.face ⁅x,y⁆
      rw [face_commutator,hEF]
    change χ _ = 1
    rw [← hcomm,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)

lemma MaximalFace.character_nontrivial {H : Filtration G} {I : Finset ι}
    {χ : cube H I 0 →* A} (M : MaximalFace H I χ) : M.character.value ≠ 1 :=
  M.nontrivial

end
end HorizontalCubeCharacter
end
 

 
section

 

namespace BooleanBinomial
open scoped BigOperators
noncomputable section
open MvPolynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 
abbrev Exponent (ι : Type*) := Option ι →₀ ℕ

def degree (e : Exponent ι) : ℕ := e.sum (fun _ n => n)

def incrementSupport (e : Exponent ι) : Finset ι :=
  Finset.univ.filter (fun i => e (some i) ≠ 0)

omit [DecidableEq ι] in
@[simp] lemma mem_incrementSupport (e : Exponent ι) (i : ι) :
    i ∈ incrementSupport e ↔ e (some i) ≠ 0 := by simp [incrementSupport]

def part (D : Finset ι) (p : MvPolynomial (Option ι) ℝ) :
    MvPolynomial (Option ι) ℝ :=
  AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter (fun e => incrementSupport e = D))

@[simp] lemma coeff_part (D : Finset ι) (p : MvPolynomial (Option ι) ℝ)
    (e : Exponent ι) :
    (part D p).coeff e = if incrementSupport e = D then p.coeff e else 0 := rfl

lemma part_support (D : Finset ι) (p : MvPolynomial (Option ι) ℝ)
    {e : Exponent ι} (he : e ∈ (part D p).support) : incrementSupport e = D := by
  have hh : (part D p).coeff e ≠ 0 := MvPolynomial.mem_support_iff.mp he
  by_contra hn
  simp [coeff_part,hn] at hh

lemma sum_parts (p : MvPolynomial (Option ι) ℝ) :
    ∑ D : Finset ι, part D p = p := by
  ext e
  simp

 
def composeSum {σ : Type*} [Fintype σ] (p : Polynomial ℝ) : MvPolynomial σ ℝ :=
  p.eval₂ C (∑ i, X i)

lemma coeff_composeSum {σ : Type*} [Fintype σ] (p : Polynomial ℝ) (e : σ →₀ ℕ) :
    (composeSum p).coeff e = p.coeff (e.sum (fun _ n => n)) * e.multinomial := by
  classical
  simp only [composeSum,Polynomial.eval₂_eq_sum,Polynomial.sum,
    coeff_sum,coeff_C_mul,coeff_sum_X_pow_of_fintype,Nat.cast_ite,Nat.cast_zero]
  by_cases he : e.sum (fun _ n => n) ∈ p.support
  · rw [Finset.sum_eq_single_of_mem _ he]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
  · have hp : p.coeff (e.sum (fun _ n => n)) = 0 := Polynomial.notMem_support_iff.mp he
    rw [hp,zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    have hne : e.sum (fun _ n => n) ≠ b := by rintro rfl; exact he hb
    simp [hne]

 
def binomial (j : ℕ) : Polynomial ℝ :=
  Polynomial.C (j.factorial : ℝ)⁻¹ * descPochhammer ℝ j

lemma binomial_eval (j : ℕ) (x : ℝ) : (binomial j).eval x = Ring.choose x j := by
  rw [Ring.choose_eq_smul,smul_eq_mul,← Polynomial.aeval_eq_smeval,
    Polynomial.aeval_def,← Polynomial.eval_map,descPochhammer_map]
  simp [binomial]

lemma binomial_coeff_top (j : ℕ) : (binomial j).coeff j = (j.factorial : ℝ)⁻¹ := by
  rw [binomial,Polynomial.coeff_C_mul]
  have hh := (monic_descPochhammer ℝ j).coeff_natDegree
  rw [descPochhammer_natDegree] at hh
  rw [hh,mul_one]

lemma binomial_coeff_above (j n : ℕ) (hn : j < n) : (binomial j).coeff n = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  exact (Polynomial.natDegree_C_mul_le _ _).trans_lt (by simpa using hn)

 
def cubeBinomial (j : ℕ) : MvPolynomial (Option ι) ℝ := composeSum (binomial j)

def faceBinomial (j : ℕ) (D : Finset ι) : MvPolynomial (Option ι) ℝ :=
  part D (cubeBinomial j)

lemma faceBinomial_coeff (j : ℕ) (D : Finset ι) (e : Exponent ι) :
    (faceBinomial j D).coeff e =
      if incrementSupport e = D then (binomial j).coeff (degree e) * e.multinomial else 0 := by
  simp only [faceBinomial,coeff_part,cubeBinomial,coeff_composeSum,degree]

lemma faceBinomial_support (j : ℕ) (D : Finset ι) {e : Exponent ι}
    (he : e ∈ (faceBinomial j D).support) :
    incrementSupport e = D ∧ degree e ≤ j := by
  have hs : incrementSupport e = D := part_support D _ he
  refine ⟨hs,?_⟩
  by_contra! hd
  have hh := MvPolynomial.mem_support_iff.mp he
  rw [faceBinomial_coeff,ite_eq_left hs,binomial_coeff_above _ _ hd,zero_mul] at hh
  exact hh rfl

 
def isolatedExponent (j : ℕ) (D : Finset ι) : Exponent ι :=
  Finsupp.equivFunOnFinite.symm (fun i => match i with
    | none => j-D.card
    | some i => if i ∈ D then 1 else 0)

@[simp] lemma isolatedExponent_none (j : ℕ) (D : Finset ι) :
    isolatedExponent j D none = j-D.card := by simp [isolatedExponent]

@[simp] lemma isolatedExponent_some (j : ℕ) (D : Finset ι) (i : ι) :
    isolatedExponent j D (some i) = if i ∈ D then 1 else 0 := by
  simp [isolatedExponent]

@[simp] lemma isolatedExponent_support (j : ℕ) (D : Finset ι) :
    incrementSupport (isolatedExponent j D) = D := by
  ext i
  simp

omit [DecidableEq ι] in
lemma degree_eq_sum (e : Exponent ι) : degree e = e none + ∑ i, e (some i) := by
  rw [degree,Finsupp.sum_of_support_subset e (Finset.subset_univ _) _ (by simp),
    Fintype.sum_option]

lemma isolatedExponent_degree (j : ℕ) (D : Finset ι) (hD : D.card ≤ j) :
    degree (isolatedExponent j D) = j := by
  rw [degree_eq_sum]
  simp only [isolatedExponent_none,isolatedExponent_some]
  simp [Nat.sub_add_cancel hD]

lemma isolatedExponent_multinomial (j : ℕ) (D : Finset ι) (hD : D.card ≤ j) :
    (j-D.card).factorial * (isolatedExponent j D).multinomial = j.factorial := by
  have hh := Nat.multinomial_spec Finset.univ (isolatedExponent j D)
  rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at hh
  have hs : (∑ i,isolatedExponent j D i) = j := by
    rw [Fintype.sum_option]
    simpa only [← degree_eq_sum] using isolatedExponent_degree j D hD
  rw [hs,Fintype.prod_option] at hh
  simpa only [isolatedExponent_none,isolatedExponent_some,apply_ite Nat.factorial,
    Nat.factorial_one,Nat.factorial_zero,ite_self,Finset.prod_const_one,mul_one] using hh

 

theorem isolated_coefficient (j : ℕ) (D : Finset ι) (hD : D.card ≤ j) :
    (faceBinomial j D).coeff (isolatedExponent j D) =
      ((j-D.card).factorial : ℝ)⁻¹ := by
  rw [faceBinomial_coeff,isolatedExponent_support,ite_eq_left rfl,
    isolatedExponent_degree j D hD,binomial_coeff_top]
  have hh : ((j-D.card).factorial : ℝ) * (isolatedExponent j D).multinomial = j.factorial :=
    by exact_mod_cast isolatedExponent_multinomial j D hD
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero j)
  have hd : ((j-D.card).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp
  nlinarith

lemma coefficient_other_face (ℓ j : ℕ) (D E : Finset ι) (hDE : D ≠ E) :
    (faceBinomial ℓ E).coeff (isolatedExponent j D) = 0 := by
  rw [faceBinomial_coeff,isolatedExponent_support,ite_eq_right hDE]

lemma coefficient_lower_order (ℓ j : ℕ) (D E : Finset ι)
    (hD : D.card ≤ j) (hℓ : ℓ < j) :
    (faceBinomial ℓ E).coeff (isolatedExponent j D) = 0 := by
  rw [faceBinomial_coeff,isolatedExponent_degree j D hD,binomial_coeff_above _ _ hℓ]
  simp

 

theorem horizontal_coefficient (j : ℕ) (D : Finset ι) (hD : D.card ≤ j)
    (w : ℕ → Finset ι → ℝ) :
    (∑ ℓ ∈ Finset.range (j+1), ∑ E : Finset ι, C (w ℓ E) * faceBinomial ℓ E).coeff
      (isolatedExponent j D) =
        w j D / (j-D.card).factorial := by
  simp only [coeff_sum,coeff_C_mul]
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (Nat.lt_succ_self _))]
  · rw [Finset.sum_eq_single D]
    · rw [isolated_coefficient j D hD,div_eq_mul_inv]
    · intro E _ hE
      rw [coefficient_other_face j j D E (Ne.symm hE),mul_zero]
    · simp
  · intro ℓ hℓ hne
    have hlt : ℓ < j := lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hℓ)) hne
    apply Finset.sum_eq_zero
    intro E _
    rw [coefficient_lower_order ℓ j D E hD hlt,mul_zero]

def mask (b : Option ι → ℝ) (v : Finset ι) : Option ι → ℝ
  | none => b none
  | some i => if i ∈ v then b (some i) else 0

lemma masked_monomial (b : Option ι → ℝ) (v : Finset ι) (e : Exponent ι) :
    e.prod (fun i n => mask b v i ^ n) =
      if incrementSupport e ⊆ v then e.prod (fun i n => b i ^ n) else 0 := by
  classical
  by_cases h : incrementSupport e ⊆ v
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro i hi
    cases i with
    | none => rfl
    | some i =>
      have hv := h ((mem_incrementSupport e i).mpr (Finsupp.mem_support_iff.mp hi))
      simp [mask,hv]
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hv⟩ := Finset.not_subset.mp h
    apply Finset.prod_eq_zero (show some i ∈ e.support from
      Finsupp.mem_support_iff.mpr ((mem_incrementSupport e i).mp hi))
    simp [mask,hv,zero_pow ((mem_incrementSupport e i).mp hi)]

lemma part_mask_eval (b : Option ι → ℝ) (v D : Finset ι)
    (p : MvPolynomial (Option ι) ℝ) :
    eval (mask b v) (part D p) = if D ⊆ v then eval b (part D p) else 0 := by
  by_cases h : D ⊆ v
  · rw [ite_eq_left h,eval_eq,eval_eq]
    apply Finset.sum_congr rfl
    intro e he
    change _ * e.prod (fun i n => mask b v i ^ n) =
      _ * e.prod (fun i n => b i ^ n)
    rw [masked_monomial,part_support D p he,ite_eq_left h]
  · rw [ite_eq_right h,eval_eq]
    apply Finset.sum_eq_zero
    intro e he
    change _ * e.prod (fun i n => mask b v i ^ n) = 0
    rw [masked_monomial,part_support D p he,ite_eq_right h,mul_zero]

lemma eval_composeSum {σ : Type*} [Fintype σ] (p : Polynomial ℝ) (b : σ → ℝ) :
    eval b (composeSum p) = p.eval (∑ i,b i) := by
  simp [composeSum,Polynomial.eval₂_eq_sum,Polynomial.eval_eq_sum,Polynomial.sum]

omit [DecidableEq ι] in
lemma cubeBinomial_eval (j : ℕ) (b : Option ι → ℝ) :
    eval b (cubeBinomial j) = Ring.choose (b none + ∑ i,b (some i)) j := by
  rw [cubeBinomial,eval_composeSum,binomial_eval,Fintype.sum_option]

 
theorem binomial_expansion (j : ℕ) (b : Option ι → ℝ) (v : Finset ι) :
    Ring.choose (b none + ∑ i ∈ v,b (some i)) j =
      ∑ D : Finset ι, if D ⊆ v then eval b (faceBinomial j D) else 0 := by
  have hb : b none + ∑ i ∈ v,b (some i) =
      mask b v none + ∑ i,mask b v (some i) := by simp [mask]
  rw [hb,← cubeBinomial_eval]
  calc
    _ = eval (mask b v) (∑ D : Finset ι,part D (cubeBinomial j)) :=
      congrArg (eval (mask b v)) (sum_parts (cubeBinomial j)).symm
    _ = ∑ D : Finset ι, if D ⊆ v then eval b (faceBinomial j D) else 0 := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro D _
      exact part_mask_eval b v D _

omit [Fintype ι] in
lemma boolean_product (D v : Finset ι) :
    (∏ i ∈ D, if i ∈ v then (1:ℝ) else 0) = if D ⊆ v then 1 else 0 := by
  by_cases h : D ⊆ v
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i hi
    exact ite_eq_left (h hi)
  · rw [ite_eq_right h]
    obtain ⟨i,hi,hv⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (ite_eq_right hv)

 
theorem boolean_binomial_expansion (j : ℕ) (b : Option ι → ℝ) (v : Finset ι) :
    Ring.choose (b none + ∑ i ∈ v,b (some i)) j =
      ∑ D : Finset ι, (∏ i ∈ D,if i ∈ v then (1:ℝ) else 0) *
        eval b (faceBinomial j D) := by
  rw [binomial_expansion]
  apply Finset.sum_congr rfl
  intro D _
  rw [boolean_product]
  split_ifs <;> simp

omit [DecidableEq ι] in
lemma incrementSupport_card_le (e : Exponent ι) : (incrementSupport e).card ≤ degree e := by
  rw [degree_eq_sum]
  calc
    _ = ∑ _i ∈ incrementSupport e, 1 := by simp
    _ ≤ ∑ i ∈ incrementSupport e,e (some i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.one_le_iff_ne_zero.mpr ((mem_incrementSupport e i).mp hi)
    _ ≤ ∑ i,e (some i) := Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
    _ ≤ e none + ∑ i,e (some i) := Nat.le_add_left _ _

 
theorem faceBinomial_vanish (j : ℕ) (D : Finset ι) (hD : j < D.card) :
    faceBinomial j D = 0 := by
  ext e
  rw [AddMonoidAlgebra.coeff_zero]
  by_contra h
  have he : e ∈ (faceBinomial j D).support := MvPolynomial.mem_support_iff.mpr h
  obtain ⟨hs,hd⟩ := faceBinomial_support j D he
  have hc := incrementSupport_card_le e
  rw [hs] at hc
  omega

end
end BooleanBinomial

end
end
end
end

end OAI
