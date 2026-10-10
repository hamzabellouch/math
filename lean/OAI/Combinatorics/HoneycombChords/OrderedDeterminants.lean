import OAI.Combinatorics.HoneycombChords.ParameterJets

namespace OAI

/-! Ordered determinant inequalities and positivity of the mixed interpolation family.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace Honeycomb370
open Matrix Finset

lemma det_two_update_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c d : ι → ℝ) :
    (((1 : Matrix ι ι ℝ).updateCol i c).updateCol j d).det = c i*d j-d i*c j := by
  let U : Matrix ι (Fin 2) ℝ := fun k a ↦
    if a = 0 then c k - if k = i then 1 else 0
    else d k - if k = j then 1 else 0
  let V : Matrix (Fin 2) ι ℝ := fun a k ↦
    if a = 0 then if k = i then 1 else 0 else if k = j then 1 else 0
  have he : ((1 : Matrix ι ι ℝ).updateCol i c).updateCol j d = 1+U*V := by
    ext k l
    rw [Matrix.add_apply,Matrix.mul_apply]
    by_cases hli : l = i
    · subst l
      simp [U,V,hij,Matrix.one_apply,eq_comm]
    · by_cases hlj : l = j
      · subst l
        simp [U,V,Fin.sum_univ_two,hij,Matrix.one_apply,eq_comm]
      · simp [U,V,hli,hlj,Ne.symm hli,Ne.symm hlj,Matrix.one_apply,eq_comm]
  rw [he,det_one_add_mul_comm,Matrix.det_fin_two]
  simp only [Matrix.add_apply,Matrix.mul_apply,Matrix.one_apply_eq,Matrix.one_apply_ne (Fin.zero_ne_one),
    Matrix.one_apply_ne (Fin.zero_ne_one.symm),zero_add]

  simp [U,V,hij,hij.symm]

lemma det_two_update_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) (hij : i ≠ j) (c d : ι → ℝ) :
    ((A.updateCol i (A *ᵥ c)).updateCol j (A *ᵥ d)).det =
      (c i*d j-d i*c j)*A.det := by
  have he : (A.updateCol i (A *ᵥ c)).updateCol j (A *ᵥ d) =
      A*(((1 : Matrix ι ι ℝ).updateCol i c).updateCol j d) := by
    rw [Matrix.mul_updateCol,Matrix.mul_updateCol,Matrix.mul_one]
  rw [he,det_mul,det_two_update_one i j hij]
  ring

lemma det_update_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i : ι) (c : ι → ℝ) :
    (A.updateCol i (A *ᵥ c)).det = c i*A.det := by
  change (A.updateCol i (fun k ↦ ∑ j, A k j*c j)).det = _
  simpa only [smul_eq_mul, mul_comm] using
    Matrix.det_updateCol_sum A i c


theorem determinant_column_diamond {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) (i j : ι) (hij : i ≠ j)
    (u v : ι → ℝ) :
    (A.updateCol i u).det*(A.updateCol j v).det -
        A.det*((A.updateCol i u).updateCol j v).det =
      (A.updateCol i v).det*(A.updateCol j u).det := by
  let c := A⁻¹ *ᵥ u
  let d := A⁻¹ *ᵥ v
  have hu : A *ᵥ c = u := by
    dsimp [c]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  have hv : A *ᵥ d = v := by
    dsimp [d]
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hA),
      Matrix.one_mulVec]
  rw [←hu,←hv,det_two_update_mulVec A i j hij,det_update_mulVec,
    det_update_mulVec,det_update_mulVec,det_update_mulVec]
  ring
end Honeycomb370

end


section


namespace Honeycomb370
open Finset

private def mix {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  if i.val < k then x i else y i

private lemma mix_strictMono {n : ℕ} {x y : Fin n → ℝ}
    (hx : StrictMono x) (hy : StrictMono y) (hxy : x ≤ y) (k : ℕ) :
    StrictMono (mix x y k) := by
  intro i j hij
  by_cases hi : i.val < k
  · by_cases hj : j.val < k
    · simpa [mix,hi,hj] using hx hij
    · simpa [mix,hi,hj] using (hx hij).trans_le (hxy j)
  · have hj : ¬j.val < k := fun hj ↦ hi (lt_trans hij hj)
    simpa [mix,hi,hj] using hy hij

private lemma mix_le {n : ℕ} {x y : Fin n → ℝ} (hxy : x ≤ y) (k : ℕ) :
    x ≤ mix x y k ∧ mix x y k ≤ y := by
  constructor <;> intro i <;> dsimp [mix] <;> split_ifs
  · exact le_rfl
  · exact hxy i
  · exact hxy i
  · exact le_rfl

private lemma mix_zero {n : ℕ} (x y : Fin n → ℝ) : mix x y 0 = y := by
  ext i
  simp [mix]

private lemma mix_end {n : ℕ} (x y : Fin n → ℝ) : mix x y n = x := by
  ext i
  simp [mix, i.isLt]

private lemma mix_step {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) (hk : k < n) :
    mix x y k = Function.update (mix x y (k+1)) ⟨k,hk⟩ (y ⟨k,hk⟩) := by
  ext i
  by_cases hi : i = ⟨k,hk⟩
  · subst i
    simp [mix]
  · have hine : i.val ≠ k := by simpa [Fin.ext_iff] using hi
    have hh : i.val < k+1 ↔ i.val < k := by omega
    simp [Function.update_of_ne hi, mix, hh]

/-- Coordinatewise monotonicity on the ordered positive chamber. -/
theorem monotone_ordered_of_coordinate {n : ℕ} (a : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hlocal : ∀ x i r, (∀ k,a<x k) → StrictMono x → x i≤r →
      StrictMono (Function.update x i r) → f x≤f (Function.update x i r))
    {x y : Fin n → ℝ} (hxy : x≤y) (hxpos : ∀ k,a<x k)
    (hx : StrictMono x) (hy : StrictMono y) : f x≤f y := by
  have step (k : ℕ) (hk : k<n) : f (mix x y (k+1))≤f (mix x y k) := by
    rw [mix_step x y k hk]
    apply hlocal
    · intro j
      exact (hxpos j).trans_le ((mix_le hxy _).1 j)
    · exact mix_strictMono hx hy hxy _
    · simpa [mix] using hxy ⟨k,hk⟩
    · rw [←mix_step x y k hk]
      exact mix_strictMono hx hy hxy _
  have hh (k : ℕ) (hk : k≤n) : f (mix x y k)≤f (mix x y 0) := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (step k (by omega)).trans (ih (by omega))
  simpa only [mix_end,mix_zero] using hh n le_rfl

/-- Increasing a single coordinate has a larger increment at a larger ordered
base, provided all four ordered tuples are admissible. -/
theorem increasing_increment_ordered {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hlocal : ∀ (x : Fin n → ℝ) (i j : Fin n) (r s : ℝ), i ≠ j →
      x i ≤ r → x j ≤ s → (∀ k, 0 < x k) → StrictMono x →
      StrictMono (Function.update x i r) → StrictMono (Function.update x j s) →
      StrictMono (Function.update (Function.update x i r) j s) →
      f (Function.update x i r) + f (Function.update x j s) ≤
        f x + f (Function.update (Function.update x i r) j s))
    {x y : Fin n → ℝ} (i : Fin n) (r : ℝ)
    (hxy : x ≤ y) (hi : x i = y i) (hr : y i ≤ r)
    (hxpos : ∀ k, 0 < x k) (hx : StrictMono x) (hy : StrictMono y)
    (hxr : StrictMono (Function.update x i r))
    (hyr : StrictMono (Function.update y i r)) :
    f (Function.update x i r) - f x ≤ f (Function.update y i r) - f y := by
  have hup : Function.update x i r ≤ Function.update y i r := by
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simpa [Function.update_of_ne hji] using hxy j
  have hmixup (k : ℕ) : Function.update (mix x y k) i r =
      mix (Function.update x i r) (Function.update y i r) k := by
    ext j
    by_cases hji : j = i
    · subst j; simp [mix]
    · simp [Function.update_of_ne hji, mix]
  have hadd (k : ℕ) (hk : k < n) :
      f (Function.update (mix x y (k+1)) i r) - f (mix x y (k+1)) ≤
      f (Function.update (mix x y k) i r) - f (mix x y k) := by
    let j : Fin n := ⟨k,hk⟩
    by_cases hij : i = j
    · subst i
      have he : mix x y k = mix x y (k+1) := by
        rw [mix_step x y k hk]
        apply Function.update_eq_self_iff.mpr
        dsimp [mix,j]
        simpa using hi.symm
      rw [he]
    · have hb : mix x y (k+1) j = x j := by simp [mix,j]
      have hbi : mix x y (k+1) i ≤ r := ((mix_le hxy _).2 i).trans hr
      have hl := hlocal (mix x y (k+1)) i j r (y j) hij hbi
        (by rw [hb]; exact hxy j) (fun l ↦ (hxpos l).trans_le ((mix_le hxy _).1 l))
        (mix_strictMono hx hy hxy _)
        (by rw [hmixup]; exact mix_strictMono hxr hyr hup _)
        (by rw [←mix_step x y k hk]; exact mix_strictMono hx hy hxy _)
        (by rw [Function.update_comm hij,←mix_step x y k hk,hmixup]
            exact mix_strictMono hxr hyr hup _)
      rw [Function.update_comm hij,←mix_step x y k hk] at hl
      linarith
  have hh (k : ℕ) (hk : k ≤ n) :
      f (Function.update (mix x y k) i r) - f (mix x y k) ≤
      f (Function.update (mix x y 0) i r) - f (mix x y 0) := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hadd k (by omega)).trans (ih (by omega))
  simpa only [mix_zero,mix_end] using hh n le_rfl

/-- The exact global lattice inequality needed in the four-functions theorem.
All inputs here are local two-coordinate inequalities, not association. -/
theorem supermodular_ordered_of_local {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hlocal : ∀ (x : Fin n → ℝ) (i j : Fin n) (r s : ℝ), i ≠ j →
      x i ≤ r → x j ≤ s → (∀ k, 0 < x k) → StrictMono x →
      StrictMono (Function.update x i r) → StrictMono (Function.update x j s) →
      StrictMono (Function.update (Function.update x i r) j s) →
      f (Function.update x i r) + f (Function.update x j s) ≤
        f x + f (Function.update (Function.update x i r) j s))
    {x y : Fin n → ℝ} (hxpos : ∀ k, 0 < x k) (hypos : ∀ k, 0 < y k)
    (hx : StrictMono x) (hy : StrictMono y) :
    f x + f y ≤ f (x ⊓ y) + f (x ⊔ y) := by
  let a := x ⊓ y
  let b := x ⊔ y
  have ha : StrictMono a := by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (hx hij))
      ((min_le_right _ _).trans_lt (hy hij))
  have hb : StrictMono b := by
    intro i j hij
    exact max_lt ((hx hij).trans_le (le_max_left _ _))
      ((hy hij).trans_le (le_max_right _ _))
  have hax : a ≤ x := inf_le_left
  have hyb : y ≤ b := le_sup_right
  have halve (k : ℕ) : mix a x k ≤ mix y b k := by
    intro i
    dsimp [mix]
    split_ifs
    · exact inf_le_right (a := x) (b := y) i
    · exact le_sup_left (a := x) (b := y) i
  have step (k : ℕ) (hk : k < n) :
      f (mix y b (k+1)) - f (mix a x (k+1)) ≤
      f (mix y b k) - f (mix a x k) := by
    let i : Fin n := ⟨k,hk⟩
    by_cases hi : x i ≤ y i
    · have haxi : a i = x i := min_eq_left hi
      have hbyi : b i = y i := max_eq_right hi
      have h1 : mix a x k = mix a x (k+1) := by
        rw [mix_step a x k hk]
        apply Function.update_eq_self_iff.mpr
        simpa [mix,i] using haxi.symm
      have h2 : mix y b k = mix y b (k+1) := by
        rw [mix_step y b k hk]
        apply Function.update_eq_self_iff.mpr
        simpa [mix,i] using hbyi
      rw [h1,h2]
    · have hi' : y i ≤ x i := le_of_not_ge hi
      have hai : a i = y i := min_eq_right hi'
      have hbi : b i = x i := max_eq_left hi'
      have hu : mix a x (k+1) i = y i := by simpa [mix,i] using hai
      have hv : mix y b (k+1) i = y i := by simp [mix,i]
      have hinc := increasing_increment_ordered f hlocal i (x i)
        (halve (k+1)) (hu.trans hv.symm) (by rw [hv]; exact hi')
        (fun j ↦ (lt_min (hxpos j) (hypos j)).trans_le ((mix_le hax _).1 j))
        (mix_strictMono ha hx hax _) (mix_strictMono hy hb hyb _)
        (by rw [←mix_step a x k hk]; exact mix_strictMono ha hx hax _)
        (by rw [←hbi,←mix_step y b k hk]; exact mix_strictMono hy hb hyb _)
      rw [←mix_step a x k hk,←hbi,←mix_step y b k hk] at hinc
      linarith
  have hh (k : ℕ) (hk : k ≤ n) :
      f (mix y b k) - f (mix a x k) ≤ f (mix y b 0) - f (mix a x 0) := by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (step k (by omega)).trans (ih (by omega))
  have he := hh n le_rfl
  simp only [mix_zero,mix_end] at he
  dsimp [a,b] at he
  linarith
end Honeycomb370

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def familyCombination {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i,a i*F i x
def PositiveFlag (F : ℕ → ℝ → ℝ) (m : ℕ) : Prop :=
  ∀ k,k ≤ m → PositiveEvaluation (fun i : Fin k=>F i)
noncomputable def familyTestCoeffs {n : ℕ} (F : ℕ → ℝ → ℝ) (v : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun i=>(-1)^i.val*(Matrix.of (fun k j : Fin n=>F (i.succAbove k) (v j))).det
lemma familyTest_eq_det {n : ℕ} (F : ℕ → ℝ → ℝ) (v : Fin n → ℝ) (x : ℝ) :
    familyCombination F (familyTestCoeffs F v) x=(evaluationMatrix (fun i : Fin (n+1)=>F i) (Fin.cons x v)).det := by
  rw [Matrix.det_succ_column_zero]
  unfold familyCombination familyTestCoeffs
  apply sum_congr rfl
  intro i _
  simp only [evaluationMatrix,Fin.cons_zero,Matrix.submatrix,Fin.cons_succ]
  ring
lemma monomial_positiveEvaluation (n : ℕ) : PositiveEvaluation (fun i : Fin n=>fun x : ℝ=>x^i.val) := by
  intro x hx _
  have he : evaluationMatrix (fun i : Fin n=>fun y : ℝ=>y^i.val) x=(Matrix.vandermonde x).transpose := by ext;rfl
  rw [he,Matrix.det_transpose,Matrix.det_vandermonde]
  exact prod_pos (fun i _=>prod_pos (fun j hj=>sub_pos.mpr (hx (mem_Ioi.mp hj))))
lemma familyTest_sign_product {n : ℕ} (F : ℕ → ℝ → ℝ) (v : Fin n → ℝ) {x : ℝ}
    (hF : PositiveEvaluation (fun i : Fin (n+1)=>F i))
    (hv : StrictMono v) (hv0 : ∀ i,0 < v i) (hx0 : 0 < x) (hx : ∀ i,x ≠ v i) :
    0 < familyCombination F (familyTestCoeffs F v) x*(∏ i,(v i-x)) := by
  have hix : Function.Injective (Fin.cons x v) := by
    intro i j he
    refine Fin.cases (Fin.cases (fun _=>rfl) (fun j h=>False.elim (hx j h)) j)
      (fun i=>Fin.cases (fun h=>False.elim (hx i h.symm)) (fun j h=>congrArg Fin.succ (hv.injective h)) j) i he
  have hp:=evaluation_det_product_pos (fun i : Fin (n+1)=>F i) (fun i : Fin (n+1)=>fun y : ℝ=>y^i.val)
    hF (monomial_positiveEvaluation _) (Fin.cons x v) hix (Fin.cases hx0 hv0)
  have he : evaluationMatrix (fun i : Fin (n+1)=>fun y : ℝ=>y^i.val) (Fin.cons x v)=
      (Matrix.vandermonde (Fin.cons x v)).transpose := by ext;rfl
  rw [he,Matrix.det_transpose,vandermonde_cons_det,←familyTest_eq_det] at hp
  have hc : 0 < (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde]
    exact prod_pos (fun i _=>prod_pos (fun j hj=>sub_pos.mpr (hv (mem_Ioi.mp hj))))
  rw [←mul_assoc] at hp
  exact pos_of_mul_pos_left hp hc.le
lemma familyCombination_smul {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ) (e x : ℝ) :
    familyCombination F (fun i=>e*a i) x=e*familyCombination F a x := by
  simp only [familyCombination,mul_sum]
  apply sum_congr rfl
  intro i _
  ring
lemma familyCombination_continuous {n : ℕ} (F : ℕ → ℝ → ℝ) (a : Fin n → ℝ)
    (hF : ∀ i : Fin n,Continuous (F i)) : Continuous (familyCombination F a) := by
  exact continuous_finsetSum _ (fun i _=>(hF i).const_mul (a i))

theorem positive_flag_sign_matching {m : ℕ} (F : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hF : PositiveFlag F m) (hf : Continuous f) (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x)
    (hz : ∀ x,0 < x → (f x=0 ↔ x ∈ s)) (hc : s.card < m) :
    ∃ k : ℕ,k+1 ≤ m ∧ ∃ a : Fin (k+1) → ℝ,
      (∀ x,0 < x → 0 ≤ f x*familyCombination F a x) ∧
      (∀ x,0 < x → f x ≠ 0 → 0 < f x*familyCombination F a x) := by
  classical
  obtain ⟨t,ht,e,he,hpos⟩ := finite_zero_sign_polynomial f hf s 0 hs hz
  let o := t.orderIsoOfFin rfl
  let v : Fin t.card → ℝ := fun i=>(o i).val
  have hv : StrictMono v := o.strictMono
  have hvpos i : 0 < v i := hs _ (ht (o i).property)
  have hdim : t.card+1 ≤ m := Nat.add_one_le_iff.mpr ((card_le_card ht).trans_lt hc)
  let A : Fin (t.card+1) → ℝ := fun i=>(e*(-1)^t.card)*familyTestCoeffs F v i
  have hstrict : ∀ x,0 < x → f x ≠ 0 → 0 < f x*familyCombination F A x := by
    intro x hx hfx
    have hxs : x∉s := fun h=>hfx ((hz x hx).mpr h)
    have hxv i : x ≠ v i := fun h=>hxs (h.symm ▸ ht (o i).property)
    have hp:=hpos x hx hxs
    have hj:=familyTest_sign_product F v (hF _ hdim) hv hvpos hx hxv
    have hprod : (∏ i : Fin t.card,(x-v i))=∏ z ∈ t,(x-z) := by
      calc
        _ = ∏ z : t,(x-z.val) := Equiv.prod_comp o.toEquiv (fun z : t=>x-z.val)
        _ = _ := Finset.prod_attach _ _
    have hneg : (∏ i : Fin t.card,(v i-x))=(-1:ℝ)^t.card*(∏ z ∈ t,(x-z)) := by
      simp_rw [show ∀ i : Fin t.card,v i-x=(-1:ℝ)*(x-v i) from fun i=>by ring]
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,hprod]
    rw [hneg] at hj
    have hpp:=mul_pos hp hj
    have heq : (f x*(e*∏ z ∈ t,(x-z)))*(familyCombination F (familyTestCoeffs F v) x*
        ((-1:ℝ)^t.card*∏ z ∈ t,(x-z)))=
        (f x*familyCombination F A x)*(∏ z ∈ t,(x-z))^2 := by
      dsimp [A]
      rw [familyCombination_smul]
      ring
    rw [heq] at hpp
    exact pos_of_mul_pos_left hpp (sq_nonneg _)
  refine ⟨t.card,hdim,A,?_,hstrict⟩
  intro x hx
  by_cases hfx : f x=0
  · simp [hfx]
  · exact (hstrict x hx hfx).le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Honeycomb370

lemma vandermonde_local_logsupermodular {n : ℕ} (x : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (r s : ℝ) (hr : x i ≤ r) (hs : x j ≤ s)
    (hu : StrictMono (Function.update x i r))
    (hv : StrictMono (Function.update x j s)) :
    (Matrix.vandermonde (Function.update x i r)).det *
        (Matrix.vandermonde (Function.update x j s)).det ≤
      (Matrix.vandermonde x).det *
        (Matrix.vandermonde (Function.update (Function.update x i r) j s)).det := by
  simp only [Matrix.det_vandermonde,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro a _
    apply prod_nonneg
    intro b hb
    exact mul_nonneg (sub_nonneg.mpr (hu (mem_Ioi.mp hb)).le)
      (sub_nonneg.mpr (hv (mem_Ioi.mp hb)).le)
  · intro a _
    apply Finset.prod_le_prod₀
    · intro b hb
      exact mul_nonneg (sub_nonneg.mpr (hu (mem_Ioi.mp hb)).le)
        (sub_nonneg.mpr (hv (mem_Ioi.mp hb)).le)
    · intro b hb
      have hab : a ≠ b := ne_of_lt (mem_Ioi.mp hb)
      simp only [Function.update_apply]
      split_ifs <;> simp_all only [ne_eq, not_true_eq_false, not_false_eq_true] <;> nlinarith [mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hs)]

private lemma eval_update {n : ℕ} (F : Fin n → ℝ → ℝ) (x : Fin n → ℝ)
    (i : Fin n) (r : ℝ) :
    evaluationMatrix F (Function.update x i r) = (evaluationMatrix F x).updateCol i (fun a ↦ F a r) := by
  ext a b
  by_cases h : b = i <;> simp [evaluationMatrix,h]

private lemma eval_det_zero_of_noninjective {n : ℕ} (F : Fin n → ℝ → ℝ) (x : Fin n → ℝ)
    (hx : ¬Function.Injective x) : (evaluationMatrix F x).det = 0 := by
  obtain ⟨i,j,hx,hij⟩ := Function.not_injective_iff.mp hx
  apply Matrix.det_zero_of_column_eq hij
  intro a
  simp only [evaluationMatrix,hx]


theorem positiveEvaluation_local_logsupermodular {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : PositiveEvaluation F) (x : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) (r s : ℝ) (hr : x i ≤ r) (hs : x j ≤ s)
    (hx0 : ∀ k, 0 < x k) (hx : StrictMono x)
    (hu : StrictMono (Function.update x i r))
    (hv : StrictMono (Function.update x j s)) :
    (evaluationMatrix F (Function.update x i r)).det *
        (evaluationMatrix F (Function.update x j s)).det ≤
      (evaluationMatrix F x).det *
        (evaluationMatrix F (Function.update (Function.update x i r) j s)).det := by
  let P : Fin n → ℝ → ℝ := fun a t ↦ t^a.val
  have hP : PositiveEvaluation P := monomial_positiveEvaluation n
  have hd := determinant_column_diamond (evaluationMatrix F x) (hF x hx hx0).ne'
    i j hij (fun a ↦ F a r) (fun a ↦ F a s)
  have hpd := determinant_column_diamond (evaluationMatrix P x) (hP x hx hx0).ne'
    i j hij (fun a ↦ P a r) (fun a ↦ P a s)
  simp only [←eval_update] at hd hpd
  have hvd := vandermonde_local_logsupermodular x i j hij r s hr hs hu hv
  have he (z : Fin n → ℝ) : (evaluationMatrix P z).det = (Matrix.vandermonde z).det := by
    change (Matrix.vandermonde z).transpose.det = _
    exact Matrix.det_transpose _
  simp only [he] at hpd
  have hprodV : (Matrix.vandermonde (Function.update x i s)).det *
      (Matrix.vandermonde (Function.update x j r)).det ≤ 0 := by linarith
  have hcross : (evaluationMatrix F (Function.update x i s)).det *
      (evaluationMatrix F (Function.update x j r)).det ≤ 0 := by
    by_cases h1 : Function.Injective (Function.update x i s)
    · by_cases h2 : Function.Injective (Function.update x j r)
      · have hp1 := evaluation_det_product_pos F P hF hP (Function.update x i s) h1 (by
          intro k
          by_cases hk : k = i
          · subst k; simpa using (hx0 j).trans_le hs
          · simpa [Function.update_of_ne hk] using hx0 k)
        have hp2 := evaluation_det_product_pos F P hF hP (Function.update x j r) h2 (by
          intro k
          by_cases hk : k = j
          · subst k; simpa using (hx0 i).trans_le hr
          · simpa [Function.update_of_ne hk] using hx0 k)
        rw [he] at hp1 hp2
        have hh := mul_pos hp1 hp2
        have hrel :
            ((evaluationMatrix F (Function.update x i s)).det *
              (evaluationMatrix F (Function.update x j r)).det) *
            ((Matrix.vandermonde (Function.update x i s)).det *
              (Matrix.vandermonde (Function.update x j r)).det) > 0 := by nlinarith [hh]
        exact le_of_lt (neg_of_mul_pos_left hrel hprodV)
      · rw [eval_det_zero_of_noninjective F _ h2,mul_zero]
    · rw [eval_det_zero_of_noninjective F _ h1,zero_mul]
  linarith

/-- Ordered-node MTP2 for a genuine (not necessarily polynomial) positive
Chebyshev evaluation determinant. -/
theorem positiveEvaluation_logsupermodular {n : ℕ} (F : Fin n → ℝ → ℝ)
    (hF : PositiveEvaluation F) {x y : Fin n → ℝ}
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i)
    (hx : StrictMono x) (hy : StrictMono y) :
    (evaluationMatrix F x).det * (evaluationMatrix F y).det ≤
      (evaluationMatrix F (x ⊓ y)).det * (evaluationMatrix F (x ⊔ y)).det := by
  have ha : StrictMono (x ⊓ y) := by
    intro i j hij
    exact lt_min ((min_le_left _ _).trans_lt (hx hij))
      ((min_le_right _ _).trans_lt (hy hij))
  have hb : StrictMono (x ⊔ y) := by
    intro i j hij
    exact max_lt ((hx hij).trans_le (le_max_left _ _))
      ((hy hij).trans_le (le_max_right _ _))
  have hlocal (z : Fin n → ℝ) (i j : Fin n) (r s : ℝ)
      (hij : i ≠ j) (hr : z i ≤ r) (hs : z j ≤ s)
      (hz0 : ∀ k,0<z k) (hz : StrictMono z)
      (hu : StrictMono (Function.update z i r))
      (hv : StrictMono (Function.update z j s))
      (hw : StrictMono (Function.update (Function.update z i r) j s)) :
      Real.log (evaluationMatrix F (Function.update z i r)).det +
          Real.log (evaluationMatrix F (Function.update z j s)).det ≤
        Real.log (evaluationMatrix F z).det +
          Real.log (evaluationMatrix F (Function.update (Function.update z i r) j s)).det := by
    have hup : ∀ k,0<Function.update z i r k := by
      intro k
      by_cases hk : k=i
      · subst k; simpa using (hz0 i).trans_le hr
      · simpa [hk] using hz0 k
    have hvp : ∀ k,0<Function.update z j s k := by
      intro k
      by_cases hk : k=j
      · subst k; simpa using (hz0 j).trans_le hs
      · simpa [hk] using hz0 k
    have hwp : ∀ k,0<Function.update (Function.update z i r) j s k := by
      intro k
      by_cases hk : k=j
      · subst k; simpa using (hz0 j).trans_le hs
      · simpa [hk] using hup k
    have h1:=hF _ hu hup
    have h2:=hF _ hv hvp
    have h3:=hF _ hz hz0
    have h4:=hF _ hw hwp
    rw [←Real.log_mul h1.ne' h2.ne',←Real.log_mul h3.ne' h4.ne']
    exact Real.log_le_log (mul_pos h1 h2)
      (positiveEvaluation_local_logsupermodular F hF z i j hij r s hr hs hz0 hz hu hv)
  have hh:=supermodular_ordered_of_local (fun z ↦ Real.log (evaluationMatrix F z).det)
    hlocal hx0 hy0 hx hy
  have h1:=hF _ hx hx0
  have h2:=hF _ hy hy0
  have h3:=hF _ ha (fun i ↦ lt_min (hx0 i) (hy0 i))
  have h4:=hF _ hb (fun i ↦ (hx0 i).trans_le (le_max_left _ _))
  rw [←Real.log_mul h1.ne' h2.ne',←Real.log_mul h3.ne' h4.ne'] at hh
  exact (Real.log_le_log_iff (mul_pos h1 h2) (mul_pos h3 h4)).mp hh

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory

noncomputable def centralIndex (N : ℕ) : Fin (2*N+1) := ⟨N, by omega⟩
noncomputable def fixedFamily (N : ℕ) : Fin (2*N+1) → ℝ → ℝ :=
  fun i => cosineKernelJet (nodalOrder (interiorKnotLabels N (angle/2)) i) 0
    (interiorKnotLabels N (angle/2) i)
noncomputable def realG (x : ℝ) : ℝ := ∫ t in (0:ℝ)..angle, cosineKernelJet 0 0 (t^2) x
noncomputable def mixedFamily (N : ℕ) : Fin (2*N+1) → ℝ → ℝ :=
  Function.update (fixedFamily N) (centralIndex N) realG

lemma realG_complex (x : ℝ) : (realG x : ℂ) = g x := by
  simp only [realG,g,C_eq_beta_square,intervalIntegral.integral_ofReal]

lemma fixedFamily_central (N : ℕ) (x : ℝ) :
    fixedFamily N (centralIndex N) x=cosineKernelJet 0 0 ((angle/2)^2) x := by
  rw [fixedFamily,interiorKnot_nodalOrder N _ (by linarith [strip_angle_pos] : 0<angle/2) (by linarith [strip_angle_pos])]
  simp [centralIndex,interiorKnotLabels]

lemma fixedFamily_eq_interior_away (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle)
    {i : Fin (2*N+1)} (hi : i ≠ centralIndex N) :
    fixedFamily N i = cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0
      (interiorKnotLabels N t i) := by
  have hi' : (i:ℕ) ≠ N := by simpa [centralIndex,Fin.ext_iff] using hi
  rw [fixedFamily,interiorKnot_nodalOrder N _ (by linarith [strip_angle_pos] : 0<angle/2) (by linarith [strip_angle_pos]),
    interiorKnot_nodalOrder N _ ht htL]
  simp only [interiorKnotLabels,hi',ite_false]

lemma fixedFamily_update_interior (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    Function.update (fixedFamily N) (centralIndex N) (cosineKernelJet 0 0 (t^2)) =
      fun i : Fin (2*N+1) => cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0
        (interiorKnotLabels N t i) := by
  funext i
  by_cases hi : i=centralIndex N
  · subst i
    rw [Function.update_self,interiorKnot_nodalOrder N _ ht htL]
    simp [centralIndex,interiorKnotLabels]
  · rw [Function.update_of_ne hi]
    exact fixedFamily_eq_interior_away N ht htL hi

noncomputable def rowDetLinear {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun v := (A.updateRow i v).det
  map_add' u v := Matrix.det_updateRow_add A i u v
  map_smul' s v := by simpa using Matrix.det_updateRow_smul A i s v

lemma rowDet_integral {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n)
    (v : ℝ → Fin n → ℝ) {a b : ℝ} (hv : Continuous v) :
    (A.updateRow i (fun j => ∫ t in a..b, v t j)).det =
      ∫ t in a..b, (A.updateRow i (v t)).det := by
  let L := (rowDetLinear A i).toContinuousLinearMap
  have he : (∫ t in a..b, v t) = fun j=>∫ t in a..b, v t j := by
    funext j
    exact ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).intervalIntegral_comp_comm
      (hv.intervalIntegrable (μ:=volume) a b)).symm
  have h := L.intervalIntegral_comp_comm (hv.intervalIntegrable (μ:=volume) a b)
  rw [he] at h
  exact h.symm

lemma evaluationMatrix_update {n : ℕ} (F : Fin n → ℝ → ℝ) (x : Fin n → ℝ)
    (i : Fin n) (H : ℝ → ℝ) :
    evaluationMatrix (Function.update F i H) x =
      (evaluationMatrix F x).updateRow i (fun j=>H (x j)) := by
  ext k j
  rw [Matrix.updateRow_apply]
  change (Function.update F i H k) (x j) = _
  by_cases hk : k=i
  · subst k
    rw [Function.update_self,ite_eq_left rfl]
  · rw [Function.update_of_ne hk,ite_eq_right hk]
    rfl

lemma fixedFamily_positiveEvaluation (N : ℕ) : PositiveEvaluation (fixedFamily N) := by
  apply jet_positiveEvaluation
  · exact (interiorKnot_monotone N (by linarith [strip_angle_pos] : 0<angle/2) (by linarith [strip_angle_pos])).comp (fun _ _ h => h)
  · intro i
    exact interiorKnot_nonneg N i (angle/2)

lemma mixedFamily_positiveEvaluation (N : ℕ) : PositiveEvaluation (mixedFamily N) := by
  intro x hx hx0
  let A := evaluationMatrix (fixedFamily N) x
  let v : ℝ → Fin (2*N+1) → ℝ := fun t j=>cosineKernelJet 0 0 (t^2) (x j)
  have hv : Continuous v := by
    apply continuous_pi
    intro j
    exact (cosineKernelJet_contDiff_left 0 0 (x j) 0).continuous.comp (by fun_prop)
  have hd : Continuous (fun t => (A.updateRow (centralIndex N) (v t)).det) :=
    ((rowDetLinear A (centralIndex N)).toContinuousLinearMap.continuous).comp hv
  have hpos {t : ℝ} (ht : 0<t) (htL : t<angle) :
      0 < (A.updateRow (centralIndex N) (v t)).det := by
    change 0 < ((evaluationMatrix (fixedFamily N) x).updateRow (centralIndex N)
      (fun j=>cosineKernelJet 0 0 (t^2) (x j))).det
    rw [← evaluationMatrix_update,fixedFamily_update_interior N ht htL]
    exact jet_positiveEvaluation (interiorKnotLabels N t)
      ((interiorKnot_monotone N ht htL).comp (fun _ _ h => h))
      (fun i=>interiorKnot_nonneg N i t) x hx hx0
  have hnonneg : Set.Icc (0:ℝ) angle ⊆ {t | 0 ≤ (A.updateRow (centralIndex N) (v t)).det} := by
    rw [← closure_Ioo strip_angle_pos.ne]
    apply closure_minimal
    · intro t ht
      exact (hpos ht.1 ht.2).le
    · exact isClosed_le continuous_const hd
  change 0<(evaluationMatrix (Function.update (fixedFamily N) (centralIndex N) realG) x).det
  rw [evaluationMatrix_update]
  change 0<(A.updateRow (centralIndex N) (fun j=>∫ t in (0:ℝ)..angle,v t j)).det
  rw [rowDet_integral A (centralIndex N) v hv]
  apply intervalIntegral.integral_pos strip_angle_pos hd.continuousOn
  · intro t ht
    exact hnonneg ⟨ht.1.le,ht.2⟩
  · exact ⟨angle/2,⟨by linarith [strip_angle_pos],by linarith [strip_angle_pos]⟩,
      hpos (by linarith [strip_angle_pos]) (by linarith [strip_angle_pos])⟩

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Topology

lemma realG_sq {p : ℝ} (hp : 0<p) : realG (p^2) = Real.sinh (angle*p)/p := by
  apply Complex.ofReal_injective
  rw [realG_complex,g_sq hp]

lemma realG_sq_nonneg {p : ℝ} (hp : 0<p) : 0 ≤ realG (p^2) := by
  rw [realG_sq hp]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr (mul_nonneg strip_angle_pos.le hp.le)) hp.le

lemma realG_sq_le {p : ℝ} (hp : 0 ≤ p) :
    realG (p^2) ≤ angle*cosineKernelJet 0 0 (angle^2) (p^2) := by
  have he (t : ℝ) : cosineKernelJet 0 0 (t^2) (p^2)=Real.cosh (t*p) := by
    apply Complex.ofReal_injective
    rw [← C_eq_beta_square,C_sq _ hp]
  simp_rw [realG,he]
  have h := intervalIntegral.integral_mono_on (μ:=volume) strip_angle_pos.le
    ((show Continuous (fun t : ℝ=>Real.cosh (t*p)) by fun_prop).intervalIntegrable 0 angle)
    (continuous_const.intervalIntegrable 0 angle) (fun t (ht : t ∈ Set.Icc (0:ℝ) angle) =>
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_nonneg (mul_nonneg ht.1 hp),abs_of_nonneg (mul_nonneg strip_angle_pos.le hp)]
        exact mul_le_mul_of_nonneg_right ht.2 hp))
  simpa [mul_comm] using h

lemma jet_realG_pair_integrable {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ (3*angle/2)^2) (r : ℕ) :
    IntegrableOn (fun p => cosineKernelJet r 0 b (p^2)*realG (p^2)*stripDensity p) (Set.Ioi 0) := by
  have hbase := (strip_jet_pair_integrable hb0 (sq_nonneg angle) hb le_rfl r 0).const_mul angle
  have hf : Continuous (fun p : ℝ=>cosineKernelJet r 0 b (p^2)) :=
    (cosineKernelJet_contDiff_right r 0 b 0).continuous.comp (by fun_prop)
  have hg : AEStronglyMeasurable (fun p : ℝ=>realG (p^2)) (volume.restrict (Set.Ioi 0)) := by
    apply (show Measurable (fun p : ℝ=>Real.sinh (angle*p)/p) by fun_prop).aestronglyMeasurable.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact (realG_sq hp).symm
  apply hbase.mono'
  · exact (hf.aestronglyMeasurable.mul hg).mul
      (show Measurable stripDensity by unfold stripDensity;fun_prop).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hf0 := cosineKernelJet_nonneg hb0 (sq_nonneg p) r 0
    have hg0 := realG_sq_nonneg hp
    have hw0 := (stripDensity_pos hp).le
    rw [Real.norm_of_nonneg (by positivity)]
    calc
      _ ≤ cosineKernelJet r 0 b (p^2)*(angle*cosineKernelJet 0 0 (angle^2) (p^2))*stripDensity p :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (realG_sq_le hp.le) hf0) hw0
      _ = _ := by ring

lemma fixedFamily_pair_integrable (N : ℕ) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>fixedFamily N i (p^2)*fixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
  have ht : 0<angle/2 := by linarith [strip_angle_pos]
  have htL : angle/2<angle := by linarith [strip_angle_pos]
  apply strip_jet_pair_integrable (interiorKnot_nonneg N i _) (interiorKnot_nonneg N j _)
  · exact (interiorKnot_le N i ht htL).trans (by nlinarith [sq_nonneg angle])
  · exact interiorKnot_le N j ht htL

lemma fixed_mixed_pair_integrable (N : ℕ) (i j : Fin (2*N+1)) :
    IntegrableOn (fun p=>fixedFamily N i (p^2)*mixedFamily N j (p^2)*stripDensity p) (Set.Ioi 0) := by
  by_cases hj : j=centralIndex N
  · subst j
    simp only [mixedFamily,Function.update_self]
    apply jet_realG_pair_integrable (interiorKnot_nonneg N i _)
    exact (interiorKnot_le N i (by linarith [strip_angle_pos] : 0<angle/2)
      (by linarith [strip_angle_pos])).trans (by nlinarith [sq_nonneg angle])
  · simp only [mixedFamily,Function.update_of_ne hj]
    exact fixedFamily_pair_integrable N i j

/-- The nonsymmetric pairing matrix in the precise F0 and G spaces is
invertible. This follows from its positive determinant, not from symmetry. -/
theorem fixed_mixed_Gram_det_pos (N : ℕ) :
    0 < (familyGram stripDensity (fixedFamily N) (mixedFamily N)).det :=
  familyGram_det_pos _ _ _ (fixedFamily_positiveEvaluation N) (mixedFamily_positiveEvaluation N)
    (fun _ hp=>stripDensity_pos hp) (fixed_mixed_pair_integrable N)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
