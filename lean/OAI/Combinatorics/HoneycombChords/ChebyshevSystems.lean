import OAI.Combinatorics.HoneycombChords.StripGram

namespace OAI

/-! Chebyshev spaces, sign changes, orthogonality, and nested jet flags.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
/-- Literal complete labels of M: N jets at 0, N at L^2. -/
noncomputable def twoKnotLabels (N : ℕ) (k : ℕ) : ℝ := if k<N then 0 else angle^2
/-- Literal complete labels of M + R C_t, with the C_t row inserted in order. -/
noncomputable def interiorKnotLabels (N : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  if k<N then 0 else if k=N then t^2 else angle^2

def FirstObliqueCharacteristicComparison : Prop :=
  ∀ (N : ℕ),0<N → ∀ t : ℝ,0<t → t<angle → ∀ y z : ℝ,0<y → y<z →
    let M := twoKnotLabels N
    let F := interiorKnotLabels N (angle/2)
    let G := interiorKnotLabels N t
    let S := (jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(y^2))).det/
      (jetPencil (n:=2*N) (poleAdjustedDensity z) M M (-(z^2))).det
    let Q := (jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(y^2))).det/
      (jetPencil (n:=2*N+1) (poleAdjustedDensity z) F G (-(z^2))).det
    (y^2/z^2)*S ≤ Q ∧ Q ≤ S
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
noncomputable def jetCombination {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (x : ℝ) : ℝ :=
  ∑ i,a i*cosineKernelJet (nodalOrder b i) 0 (b i) x
lemma jetCombination_contDiff {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (k : ℕ) :
    ContDiff ℝ k (jetCombination b a) := by
  apply ContDiff.sum
  intro i _
  exact contDiff_const.mul (cosineKernelJet_contDiff_right _ _ _ k)
lemma jetCombination_iteratedDeriv {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (jetCombination b a) x=(k.factorial:ℝ)*
      ∑ i,a i*cosineKernelJet (nodalOrder b i) k (b i) x := by
  unfold jetCombination
  rw [iteratedDeriv_fun_sum (fun i _=>(contDiff_const.mul (cosineKernelJet_contDiff_right _ _ _ k)).contDiffAt)]
  simp_rw [iteratedDeriv_const_mul_field,cosineKernelJet_iteratedDeriv_right]
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  ring
/-- The literal complete beta-jet family is Chebyshev counting multiplicities. -/
theorem jetCombination_confluent_unique {n : ℕ} (b x : ℕ → ℝ) (a : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : Monotone (fun i : Fin n=>x i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i : Fin n,0 ≤ x i)
    (hz : ∀ j : Fin n,iteratedDeriv (nodalOrder x j) (jetCombination b a) (x j)=0) : a=0 := by
  let A : Matrix (Fin n) (Fin n) ℝ := fun i j=>cosineKernelJet (nodalOrder b i) (nodalOrder x j) (b i) (x j)
  have hu : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (cosineKernelJet_det_pos b x hb hx hb0 hx0).ne')
  apply (Matrix.vecMul_injective_iff_isUnit.mpr hu)
  ext j
  dsimp only
  rw [Matrix.zero_vecMul]
  change (∑ i,a i*A i j)=0
  have h:=hz j
  rw [jetCombination_iteratedDeriv] at h
  exact (mul_eq_zero.mp h).resolve_left (by positivity)
lemma jetCombination_unique {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (x : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i)
    (hx : Function.Injective x) (hx0 : ∀ i,0 ≤ x i)
    (hz : ∀ i,jetCombination b a (x i)=0) : a=0 := by
  have hd : (jetEvaluation b x).det ≠ 0 := by
    have h:=jetEvaluation_det_product_pos b b x hb hb hb0 hb0 hx hx0
    exact fun he=>by rw [he,zero_mul] at h;exact lt_irrefl _ h
  apply (Matrix.vecMul_injective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)))
  ext j
  dsimp only
  rw [Matrix.zero_vecMul]
  exact hz j
lemma jetCombination_zeros_card_lt {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i) (ha : a ≠ 0)
    (s : Finset ℝ) (hs : ∀ x∈s,0 ≤ x ∧ jetCombination b a x=0) : s.card<n := by
  classical
  by_contra hc
  obtain ⟨t,ht,htc⟩ := Finset.exists_subset_card_eq (le_of_not_gt hc)
  let o := t.equivFinOfCardEq htc
  let x : Fin n → ℝ := fun i=>(o.symm i).val
  apply ha
  apply jetCombination_unique b a x hb hb0
  · intro i j he
    exact o.symm.injective (Subtype.ext he)
  · intro i
    exact (hs _ (ht (o.symm i).property)).1
  · intro i
    exact (hs _ (ht (o.symm i).property)).2
lemma jetCombination_finite_zeros {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hb0 : ∀ i : Fin n,0 ≤ b i) (ha : a ≠ 0) :
    {x : ℝ | 0 ≤ x ∧ jetCombination b a x=0}.Finite := by
  by_contra hf
  obtain ⟨s,hs,hcard⟩ := Set.Infinite.exists_subset_card_eq hf n
  have h:=jetCombination_zeros_card_lt b a hb hb0 ha s (fun x hx=>hs hx)
  omega
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Set
lemma continuous_nonzero_sign {f : ℝ → ℝ} {s : Set ℝ} (hc : IsPreconnected s)
    (hf : ContinuousOn f s) (hz : ∀ x∈s,f x ≠ 0) {u v : ℝ} (hu : u∈s) (hv : v∈s) :
    0 < f u*f v := by
  have hu0:=hz u hu
  have hv0:=hz v hv
  rcases lt_or_gt_of_ne hu0 with hn|hp
  · have hn' : f v<0 := by
      by_contra h
      obtain ⟨x,hx,hfx⟩ := hc.intermediate_value hu hv hf (show 0∈Icc (f u) (f v) from ⟨hn.le,le_of_not_gt h⟩)
      exact hz x hx hfx
    exact mul_pos_of_neg_of_neg hn hn'
  · have hp' : 0<f v := by
      by_contra h
      obtain ⟨x,hx,hfx⟩ := hc.intermediate_value hv hu hf (show 0∈Icc (f v) (f u) from ⟨le_of_not_gt h,hp.le⟩)
      exact hz x hx hfx
    exact mul_pos hp hp'
/-- For a continuous function with finitely many zeros on a ray, its sign is
matched by a polynomial using a subset of these zeros, not by an assumed
oscillation hypothesis. This is the sign test needed by oblique jet pencils. -/
theorem finite_zero_sign_polynomial (f : ℝ → ℝ) (hf : Continuous f) (s : Finset ℝ) :
    ∀ a : ℝ,(∀ x∈s,a<x) → (∀ x,a<x → (f x=0 ↔ x∈s)) →
      ∃ t : Finset ℝ,t⊆s ∧ ∃ e : ℝ,e≠0 ∧
        ∀ x,a<x → x∉s → 0<f x*(e*∏ z∈t,(x-z)) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro a hs hz
    by_cases hempty : s=∅
    · subst s
      refine ⟨∅,Finset.Subset.rfl,f (a+1),?_,?_⟩
      · intro h
        have hmem := (hz (a+1) (by linarith)).mp h
        simp at hmem
      · intro x hx _
        simpa using continuous_nonzero_sign isPreconnected_Ioi hf.continuousOn
          (fun y hy h=>by simpa using (hz y hy).mp h) hx (show a<a+1 by linarith)
    · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
      let r:=s.min' hne
      have hr : r∈s := s.min'_mem hne
      have hra : a<r:=hs r hr
      have hmin (y) (hy : y∈s) : r≤y := s.min'_le y hy
      obtain ⟨t,ht,e,he,hpos⟩ := ih (s.erase r) (Finset.erase_ssubset hr) r
        (by
          intro y hy
          exact lt_of_le_of_ne (hmin y (mem_of_mem_erase hy)) (ne_of_mem_erase hy).symm)
        (by
          intro y hy
          rw [hz y (hra.trans hy),mem_erase]
          exact ⟨fun h=>⟨ne_of_gt hy,h⟩,fun h=>h.2⟩)
      let P : ℝ → ℝ := fun x=>e*∏ z∈t,(x-z)
      have hP : Continuous P := by dsimp [P];fun_prop
      have hp0 (x) (hx : x<r) : P x≠0 := by
        apply mul_ne_zero he
        apply prod_ne_zero_iff.mpr
        intro z hz'
        have hzmin:=hmin z (mem_of_mem_erase (ht hz'))
        exact sub_ne_zero.mpr (ne_of_lt (hx.trans_le hzmin))
      have hf0 (x) (hx : x∈Ioo a r) : f x≠0 := by
        intro h
        have hh:=hmin x ((hz x hx.1).mp h)
        exact not_lt_of_ge hh hx.2
      let u := (a+r)/2
      have hu : u∈Ioo a r := by dsimp [u];constructor <;>linarith
      have hprod : f u*P u≠0 := mul_ne_zero (hf0 u hu) (hp0 u hu.2)
      have hsame {x : ℝ} (hx : x∈Ioo a r) : 0<(f x*P x)*(f u*P u) :=
        continuous_nonzero_sign isPreconnected_Ioo (hf.mul hP).continuousOn
          (fun y hy=>mul_ne_zero (hf0 y hy) (hp0 y hy.2)) hx hu
      rcases lt_or_gt_of_ne hprod with hn|hp
      · refine ⟨insert r t,?_,e,he,?_⟩
        · exact insert_subset hr (fun x hx=>mem_of_mem_erase (ht hx))
        · intro x hx hxs
          have hxr : x≠r := fun hh=>hxs (hh.symm ▸ hr)
          have hrt : r∉t := fun hh=>(ne_of_mem_erase (ht hh)) rfl
          rw [prod_insert hrt]
          change 0<f x*(e*((x-r)*∏ z∈t,(x-z)))
          have hid : f x*(e*((x-r)*∏ z∈t,(x-z)))=(f x*P x)*(x-r) := by dsimp [P];ring
          rw [hid]
          rcases lt_or_gt_of_ne hxr with hlt|hgt
          · have hh:=hsame ⟨hx,hlt⟩
            exact mul_pos_of_neg_of_neg (neg_of_mul_pos_left hh hn.le) (sub_neg.mpr hlt)
          · exact mul_pos (hpos x hgt (fun hh=>hxs (mem_of_mem_erase hh))) (sub_pos.mpr hgt)
      · refine ⟨t,fun x hx=>mem_of_mem_erase (ht hx),e,he,?_⟩
        intro x hx hxs
        have hxr : x≠r := fun hh=>hxs (hh.symm ▸ hr)
        rcases lt_or_gt_of_ne hxr with hlt|hgt
        · exact pos_of_mul_pos_left (hsame ⟨hx,hlt⟩) hp.le
        · exact hpos x hgt (fun hh=>hxs (mem_of_mem_erase hh))
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma vandermonde_cons_det {n : ℕ} (x : ℝ) (v : Fin n → ℝ) :
    (Matrix.vandermonde (Fin.cons x v)).det=(∏ i,(v i-x))*(Matrix.vandermonde v).det := by
  have eqn {m : ℕ} (w : Fin m → ℝ) : (Matrix.vandermonde w).det=
      ∏ i,∏ j,if i<j then w j-w i else 1 := by
    rw [Matrix.det_vandermonde]
    apply prod_congr rfl
    intro i _
    rw [←prod_filter]
    congr 1
    ext j
    simp
  rw [eqn,Fin.prod_univ_succ]
  simp_rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ,lt_self_iff_false,ite_false,one_mul,
    Fin.succ_pos,ite_true,Fin.not_lt_zero,Fin.succ_lt_succ_iff]
  rw [eqn]
lemma jetEvaluation_zero_labels {n : ℕ} (x : Fin n → ℝ) :
    (jetEvaluation (fun _=>0) x).det=
      (∏ i : Fin n,((2*i.val).factorial:ℝ)⁻¹)*(Matrix.vandermonde x).det := by
  have hno (k : ℕ) : nodalOrder (fun _ : ℕ=>(0:ℝ)) k=k := by simp [nodalOrder]
  have he : jetEvaluation (fun _=>0) x=fun i j : Fin n=>
      ((2*i.val).factorial:ℝ)⁻¹*(Matrix.vandermonde x)ᵀ i j := by
    ext i j
    simp [jetEvaluation,hno,cosineKernelJet_at_zero,div_eq_mul_inv,mul_comm]
  rw [he]
  change (Matrix.of (fun i j : Fin n=>((2*i.val).factorial:ℝ)⁻¹*(Matrix.vandermonde x)ᵀ i j)).det=_
  rw [Matrix.det_mul_column,Matrix.det_transpose]
/-- Cofactor coefficients of the literal complete-jet interpolant test. -/
noncomputable def jetTestCoeffs {n : ℕ} (b : ℕ → ℝ) (v : Fin n → ℝ) : Fin (n+1) → ℝ :=
  fun i=>(-1)^i.val*(Matrix.of (fun k j : Fin n=>cosineKernelJet (nodalOrder b (i.succAbove k)) 0
    (b (i.succAbove k)) (v j))).det
lemma jetTest_eq_det {n : ℕ} (b : ℕ → ℝ) (v : Fin n → ℝ) (x : ℝ) :
    jetCombination b (jetTestCoeffs b v) x=(jetEvaluation b (Fin.cons x v)).det := by
  rw [Matrix.det_succ_column_zero]
  unfold jetCombination jetTestCoeffs
  apply sum_congr rfl
  intro i _
  simp only [jetEvaluation,Fin.cons_zero,Matrix.submatrix,Fin.cons_succ]
  ring
lemma jetTest_sign_product {n : ℕ} (b : ℕ → ℝ) (v : Fin n → ℝ) {x : ℝ}
    (hb : Monotone (fun i : Fin (n+1)=>b i)) (hb0 : ∀ i : Fin (n+1),0 ≤ b i)
    (hv : StrictMono v) (hv0 : ∀ i,0 ≤ v i) (hx0 : 0≤x) (hx : ∀ i,x≠v i) :
    0 < jetCombination b (jetTestCoeffs b v) x*(∏ i,(v i-x)) := by
  have hix : Function.Injective (Fin.cons x v) := by
    intro i j he
    refine Fin.cases (Fin.cases (fun _=>rfl) (fun j h=>False.elim (hx j h)) j)
      (fun i=>Fin.cases (fun h=>False.elim (hx i h.symm)) (fun j h=>congrArg Fin.succ (hv.injective h)) j) i he
  have hp:=jetEvaluation_det_product_pos b (fun _=>0) (Fin.cons x v) hb
    (fun _ _ _=>le_refl _) hb0 (fun _=>le_refl _) hix (Fin.cases hx0 hv0)
  rw [jetEvaluation_zero_labels,vandermonde_cons_det,←jetTest_eq_det] at hp
  have hc : 0<(∏ i : Fin (n+1),((2*i.val).factorial:ℝ)⁻¹)*(Matrix.vandermonde v).det := by
    apply mul_pos (prod_pos (fun _ _=>by positivity))
    rw [Matrix.det_vandermonde]
    exact prod_pos (fun i _=>prod_pos (fun j hj=>sub_pos.mpr (hv (mem_Ioi.mp hj))))
  have heq : jetCombination b (jetTestCoeffs b v) x*
      ((∏ i : Fin (n+1),((2*i.val).factorial:ℝ)⁻¹)*((∏ i,(v i-x))*(Matrix.vandermonde v).det))=
      (jetCombination b (jetTestCoeffs b v) x*(∏ i,(v i-x)))*
      ((∏ i : Fin (n+1),((2*i.val).factorial:ℝ)⁻¹)*(Matrix.vandermonde v).det) := by ring
  rw [heq] at hp
  exact pos_of_mul_pos_left hp hc.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset
lemma jetCombination_smul {n : ℕ} (b : ℕ → ℝ) (a : Fin n → ℝ) (e x : ℝ) :
    jetCombination b (fun i=>e*a i) x=e*jetCombination b a x := by
  simp only [jetCombination,mul_sum]
  apply sum_congr rfl
  intro i _
  ring

theorem jet_flag_sign_matching {m : ℕ} (b : ℕ → ℝ) (f : ℝ → ℝ)
    (hb : Monotone (fun i : Fin m=>b i)) (hb0 : ∀ i : Fin m,0 ≤ b i)
    (hf : Continuous f) (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x)
    (hz : ∀ x,0 < x → (f x = 0 ↔ x ∈ s)) (hc : s.card < m) :
    ∃ k : ℕ,k + 1 ≤ m ∧ ∃ a : Fin (k+1) → ℝ,
      (∀ x,0 < x → 0 ≤ f x*jetCombination b a x) ∧
      (∀ x,0 < x → f x≠0 → 0 < f x*jetCombination b a x) := by
  classical
  obtain ⟨t,ht,e,he,hpos⟩ := finite_zero_sign_polynomial f hf s 0 hs hz
  let o := t.orderIsoOfFin rfl
  let v : Fin t.card → ℝ := fun i=>(o i).val
  have hv : StrictMono v := o.strictMono
  have hvpos i : 0<v i := hs _ (ht (o i).property)
  have hdim : t.card + 1 ≤ m := (Nat.add_one_le_iff.mpr ((card_le_card ht).trans_lt hc))
  have hb' : Monotone (fun i : Fin (t.card+1)=>b i) :=
    fun i j hij=>hb (show (i.castLE hdim : Fin m) ≤ j.castLE hdim from hij)
  have hb0' (i : Fin (t.card+1)) : 0 ≤ b i := hb0 (i.castLE hdim)
  let A : Fin (t.card+1) → ℝ := fun i=>(e*(-1)^t.card)*jetTestCoeffs b v i
  have hstrict : ∀ x,0 < x → f x≠0 → 0 < f x*jetCombination b A x := by
    intro x hx hfx
    have hxs : x∉s := fun h=>(hfx ((hz x hx).mpr h))
    have hxv i : x≠v i := fun h=>hxs (h.symm ▸ ht (o i).property)
    have hp:=hpos x hx hxs
    have hj:=jetTest_sign_product b v hb' hb0' hv (fun i=>(hvpos i).le) hx.le hxv
    have hprod : (∏ i : Fin t.card,(x-v i))=∏ z∈t,(x-z) := by
      calc
        _ = ∏ z : t,(x-z.val) := Equiv.prod_comp o.toEquiv (fun z : t=>x-z.val)
        _ = _ := Finset.prod_attach _ _
    have hneg : (∏ i : Fin t.card,(v i-x))=(-1:ℝ)^t.card*(∏ z∈t,(x-z)) := by
      simp_rw [show ∀ i : Fin t.card,v i-x=(-1:ℝ)*(x-v i) from fun i=>by ring]
      rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,hprod]
    rw [hneg] at hj
    have hpp:=mul_pos hp hj
    have heq : (f x*(e*∏ z∈t,(x-z)))*(jetCombination b (jetTestCoeffs b v) x*
        ((-1:ℝ)^t.card*∏ z∈t,(x-z)))=
        (f x*jetCombination b A x)*(∏ z∈t,(x-z))^2 := by
      dsimp [A]
      rw [jetCombination_smul]
      ring
    rw [heq] at hpp
    exact pos_of_mul_pos_left hpp (sq_nonneg _)
  refine ⟨t.card,hdim,A,?_,hstrict⟩
  intro x hx
  by_cases hfx : f x = 0
  · simp [hfx]
  · exact (hstrict x hx hfx).le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter
/-- Orthogonality forces at least m distinct zeros (indeed m sign changes) for
continuous functions against a complete m-dimensional jet flag. The measure
and the squared p-coordinate are those used by the actual strip pairing. -/
theorem jet_flag_integral_nonzero {m : ℕ} (b : ℕ → ℝ) (f w : ℝ → ℝ)
    (hb : Monotone (fun i : Fin m=>b i)) (hb0 : ∀ i : Fin m,0 ≤ b i)
    (hf : Continuous f) (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ i : Fin m,IntegrableOn (fun p=>f (p^2)*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p) (Set.Ioi 0))
    (s : Finset ℝ) (hs : ∀ x ∈ s,0 < x) (hz : ∀ x,0 < x → (f x = 0 ↔ x ∈ s)) (hc : s.card < m) :
    ∃ i : Fin m,(∫ p in Set.Ioi (0:ℝ),f (p^2)*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p)≠0 := by
  classical
  by_contra hall
  push Not at hall
  obtain ⟨k,hk,a,hnonneg,hpos⟩ := jet_flag_sign_matching b f hb hb0 hf s hs hz hc
  let F : Fin (k+1) → ℝ → ℝ := fun i p=>a i*(f (p^2)*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p)
  let H : ℝ → ℝ := fun p=>f (p^2)*jetCombination b a (p^2)
  let g : ℝ → ℝ := fun p=>H p*w p
  have heq : g=fun p=>∑ i,F i p := by
    funext p
    dsimp [g,H,F,jetCombination]
    rw [mul_sum,sum_mul]
    apply sum_congr rfl
    intro i _
    ring
  have hiF (i : Fin (k+1)) : IntegrableOn (F i) (Set.Ioi 0) := (hi (i.castLE hk)).const_mul (a i)
  have hig : IntegrableOn g (Set.Ioi 0) := by rw [heq];exact integrable_finsetSum _ (fun i _=>hiF i)
  have hzero : (∫ p in Set.Ioi (0:ℝ),g p)=0 := by
    rw [heq,integral_finsetSum _ (fun i _=>hiF i)]
    apply sum_eq_zero
    intro i _
    rw [show (F i)=fun p=>a i*(f (p^2)*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p) from rfl,
      integral_const_mul]
    have hz := hall (i.castLE hk)
    change (∫ p in Set.Ioi (0:ℝ),f (p^2)*cosineKernelJet (nodalOrder b i) 0 (b i) (p^2)*w p)=0 at hz
    rw [hz,mul_zero]
  have hgnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    exact mul_nonneg (hnonneg (p^2) (sq_pos_of_pos hp)) (hw p hp).le
  have hH : Continuous H := by
    exact (hf.comp (continuous_id.pow 2)).mul ((jetCombination_contDiff b a 0).continuous.comp (continuous_id.pow 2))
  let U : Set ℝ := Set.Ioi 0 ∩ {p | 0<H p}
  have hopen : IsOpen U := isOpen_Ioi.inter (isOpen_lt continuous_const hH)
  obtain ⟨R,hR⟩ := (insert 0 s).finite_toSet.bddAbove
  let x := R+1
  have hR0 : 0≤R := hR (by simp)
  have hx : 0 < x := by dsimp [x];linarith
  have hxs : x∉s := by
    intro h
    have hh : x≤R := hR (mem_insert_of_mem h)
    dsimp [x] at hh
    linarith
  have hune : U.Nonempty := by
    refine ⟨Real.sqrt x,Real.sqrt_pos.mpr hx,?_⟩
    dsimp [H]
    rw [Real.sq_sqrt hx.le]
    exact hpos x hx (fun h=>hxs ((hz x hx).mp h))
  have hup : 0<(volume.restrict (Set.Ioi (0:ℝ))) U := by
    rw [Measure.restrict_apply hopen.measurableSet,Set.inter_eq_left.mpr Set.inter_subset_left]
    exact hopen.measure_pos volume hune
  have hus : U⊆Function.support g := by
    intro p hp
    exact (mul_pos hp.2 (hw p hp.1)).ne'
  have hgpos : 0<∫ p in Set.Ioi (0:ℝ),g p :=
    (integral_pos_iff_support_of_nonneg_ae hgnonneg hig).mpr (hup.trans_le (measure_mono hus))
  exact hgpos.ne' hzero
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset MeasureTheory

theorem jet_linear_nonorthogonality {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    (w : ℝ → ℝ) (t : ℝ) (hnm : n < m)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin m=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i) (ha : a≠0)
    (hw : ∀ p,0<p → 0<w p)
    (hi : ∀ j : Fin m,IntegrableOn (fun p=>(p^2-t)*jetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p) (Set.Ioi 0)) :
    ∃ j : Fin m,(∫ p in Set.Ioi (0:ℝ),(p^2-t)*jetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*w p)≠0 := by
  classical
  let Z := (jetCombination_finite_zeros b a hb hb0 ha).toFinset
  have hZ : ∀ x,x∈Z ↔ 0 ≤ x ∧ jetCombination b a x=0 := by
    intro x
    exact Set.Finite.mem_toFinset _
  have hZcard : Z.card<n := jetCombination_zeros_card_lt b a hb hb0 ha Z (fun x hx=>(hZ x).mp hx)
  let s := (insert t Z).filter (fun x=>0<x)
  have hs : ∀ x∈s,0<x := fun x hx=>(mem_filter.mp hx).2
  have hz : ∀ x,0<x → ((x-t)*jetCombination b a x=0 ↔ x∈s) := by
    intro x hx
    simp only [s,mem_filter,mem_insert,hZ,mul_eq_zero,sub_eq_zero]
    constructor
    · intro hh
      exact ⟨hh.imp_right (fun h=>⟨hx.le,h⟩),hx⟩
    · rintro ⟨h|h,_⟩
      · exact Or.inl h
      · exact Or.inr h.2
  have hsc : s.card < m := by
    have h : s.card ≤ Z.card+1 := (card_filter_le _ _).trans (card_insert_le _ _)
    omega
  exact jet_flag_integral_nonzero c (fun x=>(x-t)*jetCombination b a x) w hc hc0
    ((continuous_id.sub continuous_const).mul (jetCombination_contDiff b a 0).continuous)
    hw hi s hs hz hsc

lemma pole_jetCombination_linear_pair_integrable {n m : ℕ} (b c : ℕ → ℝ)
    (a : Fin n → ℝ) {z : ℝ} (hz : 0<z) (t : ℝ)
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin m,c i ≤ angle^2)
    (j : Fin m) :
    IntegrableOn (fun p=>(p^2-t)*jetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*poleAdjustedDensity z p) (Set.Ioi 0) := by
  have hi (i : Fin n) := (pole_jet_pair_pencil_integrable (hb0 i) (hc0 j) (hb1 i) (hc1 j) hz
    (nodalOrder b i) (nodalOrder c j) t).const_mul (a i)
  apply (integrable_finsetSum _ (fun i _=>hi i)).congr
  filter_upwards with p
  dsimp [jetCombination]
  rw [mul_sum,sum_mul,sum_mul]
  apply sum_congr rfl
  intro i _
  ring
theorem pole_jet_linear_nonorthogonality {n m : ℕ} (b c : ℕ → ℝ) (a : Fin n → ℝ)
    {z : ℝ} (hz : 0<z) (t : ℝ) (hnm : n < m)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin m=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin m,0 ≤ c i) (ha : a≠0)
    (hb1 : ∀ i : Fin n,b i ≤ (3*angle/2)^2) (hc1 : ∀ i : Fin m,c i ≤ angle^2) :
    ∃ j : Fin m,(∫ p in Set.Ioi (0:ℝ),(p^2-t)*jetCombination b a (p^2)*
      cosineKernelJet (nodalOrder c j) 0 (c j) (p^2)*poleAdjustedDensity z p)≠0 :=
  jet_linear_nonorthogonality b c a _ t hnm hb hc hb0 hc0 ha (fun _ hp=>poleAdjustedDensity_pos hz hp)
    (pole_jetCombination_linear_pair_integrable b c a hz t hb0 hc0 hb1 hc1)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset
lemma strip_angle_pos : 0<angle := by unfold angle;positivity
lemma twoKnot_monotone (N : ℕ) : Monotone (twoKnotLabels N) := by
  intro i j hij
  unfold twoKnotLabels
  split_ifs <;> first | positivity | omega | exact le_rfl
lemma twoKnot_nonneg (N k : ℕ) : 0 ≤ twoKnotLabels N k := by
  unfold twoKnotLabels
  split_ifs <;> positivity
lemma twoKnot_le (N k : ℕ) : twoKnotLabels N k ≤ angle^2 := by
  unfold twoKnotLabels
  split_ifs <;> first | positivity | exact le_rfl
lemma interiorKnot_monotone (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    Monotone (interiorKnotLabels N t) := by
  have ht2 : t^2 ≤ angle^2 := by nlinarith [strip_angle_pos]
  intro i j hij
  unfold interiorKnotLabels
  split_ifs <;> first | assumption | positivity | omega | exact le_rfl
lemma interiorKnot_nonneg (N k : ℕ) (t : ℝ) : 0 ≤ interiorKnotLabels N t k := by
  unfold interiorKnotLabels
  split_ifs <;> positivity
lemma interiorKnot_le (N k : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    interiorKnotLabels N t k ≤ angle^2 := by
  have ht2 : t^2 ≤ angle^2 := by nlinarith [strip_angle_pos]
  unfold interiorKnotLabels
  split_ifs <;> first | assumption | positivity | exact le_rfl
lemma twoKnot_nodalOrder (N k : ℕ) :
    nodalOrder (twoKnotLabels N) k=if k<N then k else k-N := by
  classical
  have hL : angle^2≠0 := (sq_pos_of_pos strip_angle_pos).ne'
  unfold nodalOrder
  by_cases hk : k<N
  · rw [ite_eq_left hk]
    have h : (range k).filter (fun j=>twoKnotLabels N j=twoKnotLabels N k)=range k := by
      apply filter_eq_self.mpr
      intro j hj
      have hjN : j<N := (mem_range.mp hj).trans hk
      simp [twoKnotLabels,hk,hjN]
    rw [h,card_range]
  · rw [ite_eq_right hk]
    have h : (range k).filter (fun j=>twoKnotLabels N j=twoKnotLabels N k)=Ico N k := by
      ext j
      simp only [mem_filter,mem_range,mem_Ico]
      by_cases hj : j<N
      · simp [twoKnotLabels,hj,hk,hL.symm,show ¬N≤j by omega]
      · simp [twoKnotLabels,hj,hk,show N≤j by omega]
    rw [h,Nat.card_Ico]
lemma interiorKnot_nodalOrder (N k : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    nodalOrder (interiorKnotLabels N t) k=if k<N then k else if k=N then 0 else k-(N+1) := by
  classical
  have hL : angle^2≠0 := (sq_pos_of_pos strip_angle_pos).ne'
  have ht0 : t^2≠0 := (sq_pos_of_pos ht).ne'
  have ht2 : t^2≠angle^2 := by nlinarith [strip_angle_pos]
  unfold nodalOrder
  by_cases hk : k<N
  · rw [ite_eq_left hk]
    have h : (range k).filter (fun j=>interiorKnotLabels N t j=interiorKnotLabels N t k)=range k := by
      apply filter_eq_self.mpr
      intro j hj
      have hjN : j<N := (mem_range.mp hj).trans hk
      simp [interiorKnotLabels,hk,hjN]
    rw [h,card_range]
  · rw [ite_eq_right hk]
    by_cases he : k=N
    · rw [ite_eq_left he,card_eq_zero]
      apply filter_eq_empty_iff.mpr
      intro j hj
      have hjN : j<N := he ▸ mem_range.mp hj
      simp [interiorKnotLabels,he,hjN,ht0.symm]
    · rw [ite_eq_right he]
      have h : (range k).filter (fun j=>interiorKnotLabels N t j=interiorKnotLabels N t k)=Ico (N+1) k := by
        ext j
        simp only [mem_filter,mem_range,mem_Ico]
        by_cases hj : j<N
        · simp [interiorKnotLabels,hj,hk,he,hL.symm,show ¬N+1≤j by omega]
        · by_cases hje : j=N
          · simp [interiorKnotLabels,hk,he,hje,ht2]
          · simp [interiorKnotLabels,hj,hk,he,hje,show N+1≤j by omega]
      rw [h,Nat.card_Ico]
/-- Insertion map for the common M rows into the (sorted) interior-knot flag. -/
def insertKnotIndex (N : ℕ) (i : Fin (2*N)) : Fin (2*N+1) :=
  ⟨if i.val<N then i.val else i.val+1,by split_ifs <;> omega⟩
lemma insertKnot_row (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) (i : Fin (2*N)) (x : ℝ) :
    cosineKernelJet (nodalOrder (interiorKnotLabels N t) (insertKnotIndex N i)) 0
      (interiorKnotLabels N t (insertKnotIndex N i)) x=
    cosineKernelJet (nodalOrder (twoKnotLabels N) i) 0 (twoKnotLabels N i) x := by
  rw [interiorKnot_nodalOrder N _ ht htL,twoKnot_nodalOrder]
  by_cases hi : i.val<N
  · simp [insertKnotIndex,hi,interiorKnotLabels,twoKnotLabels]
  · have hneq : i.val+1≠N := by omega
    have hlt : ¬i.val+1<N := by omega
    simp [insertKnotIndex,hi,interiorKnotLabels,twoKnotLabels,hneq,hlt]
lemma insertKnotIndex_injective (N : ℕ) : Function.Injective (insertKnotIndex N) := by
  intro i j h
  have := congrArg Fin.val h
  dsimp [insertKnotIndex] at this
  apply Fin.ext
  split_ifs at this <;> omega
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Equiv
/-- Move the inserted t² label to the last index, leaving M in its original
order. This is only a simultaneous change of basis of the actual pencil. -/
def knotPermutation (N : ℕ) : Equiv.Perm (Fin (2*N+1)) :=
  (finSuccEquiv' (Fin.last (2*N))).trans (finSuccEquiv' ⟨N,by omega⟩).symm
lemma knotPermutation_castSucc (N : ℕ) (i : Fin (2*N)) :
    knotPermutation N i.castSucc=insertKnotIndex N i := by
  simp only [knotPermutation,Equiv.trans_apply,finSuccEquiv'_last_apply_castSucc,finSuccEquiv'_symm_some]
  by_cases hi : i.val<N
  · rw [Fin.succAbove_of_castSucc_lt _ _ (show i.castSucc<(⟨N,by omega⟩ : Fin (2*N+1)) from hi)]
    apply Fin.ext
    simp [insertKnotIndex,hi]
  · rw [Fin.succAbove_of_le_castSucc _ _ (show (⟨N,by omega⟩ : Fin (2*N+1)) ≤ i.castSucc from le_of_not_gt hi)]
    apply Fin.ext
    simp [insertKnotIndex,hi]
lemma knotPermutation_last (N : ℕ) : knotPermutation N (Fin.last (2*N))=⟨N,by omega⟩ := by
  simp [knotPermutation]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
