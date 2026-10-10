import Mathlib

namespace OAI

/-! Positive confluent power and hyperbolic kernel determinants and Andreief integration.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix
open Set (Icc)
lemma signVariations_lt_support (P : Polynomial ℝ) (hP : P ≠ 0) :
    P.signVariations < P.support.card := by
  generalize hn : P.support.card = n
  induction n using Nat.strong_induction_on generalizing P with
  | h n ih =>
    have hc := Polynomial.card_support_eraseLead_add_one hP
    rw [Polynomial.signVariations_eq_eraseLead_add_ite hP]
    by_cases he : P.eraseLead = 0
    · have hs : SignType.sign P.leadingCoeff ≠ 0 := by
        simpa using hP
      simp only [he, signVariations_zero, leadingCoeff_zero, sign_zero, neg_zero,
        ite_eq_right hs, add_zero]
      have : 0 < P.support.card := Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hP)
      omega
    · have hh := ih P.eraseLead.support.card (by omega) P.eraseLead he rfl
      split_ifs <;> omega

lemma positive_roots_lt_support (P : Polynomial ℝ) (hP : P ≠ 0) :
    P.roots.countP (0 < ·) < P.support.card :=
  (P.roots_countP_pos_le_signVariations).trans_lt (signVariations_lt_support P hP)

lemma sparse_polynomial_eq_zero {n : ℕ} (e : Fin n → ℕ) (c : Fin n → ℝ)
    (x : Fin n → ℝ) (hx : Function.Injective x) (hpos : ∀ j,0 < x j)
    (hz : ∀ j,∑ i : Fin n,c i*(x j)^e i=0) :
    (∑ i : Fin n,Polynomial.monomial (e i) (c i)) = 0 := by
  classical
  let P : Polynomial ℝ := ∑ i : Fin n,Polynomial.monomial (e i) (c i)
  by_contra hP
  have hs : P.support ⊆ univ.image e := by
    intro k hk
    by_contra hn
    have he : ∀ i : Fin n,k ≠ e i := by
      intro i hi
      exact hn (mem_image.mpr ⟨i,mem_univ _,hi.symm⟩)
    have : P.coeff k = 0 := by
      simp [P, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,fun i=>(he i).symm]
    exact (Polynomial.mem_support_iff.mp hk) this
  have hcard : P.support.card ≤ n := (card_le_card hs).trans (by simpa using card_image_le (s:=univ) (f:=e))
  have hroots : univ.image x ⊆ (P.roots.filter (0 < ·)).toFinset := by
    rintro r hr
    rcases mem_image.mp hr with ⟨j,_,rfl⟩
    simp only [Multiset.mem_toFinset,Multiset.mem_filter]
    refine ⟨?_,hpos j⟩
    apply (Polynomial.mem_roots hP).mpr
    change P.eval (x j)=0
    simpa [P,Polynomial.eval_finsetSum] using hz j
  have hRootCard : n ≤ P.roots.countP (0 < ·) := by
    rw [Multiset.countP_eq_card_filter]
    calc
      n=(univ.image x).card := by simp [card_image_of_injective _ hx]
      _ ≤ (P.roots.filter (0 < ·)).toFinset.card := card_le_card hroots
      _ ≤ _ := Multiset.toFinset_card_le _
  have hlt := positive_roots_lt_support P hP
  omega

lemma power_det_ne_zero {n : ℕ} (e : Fin n → ℕ) (x : Fin n → ℝ)
    (he : Function.Injective e) (hx : Function.Injective x) (hpos : ∀ j,0 < x j) :
    Matrix.det (fun i j=>x j^e i) ≠ 0 := by
  classical
  apply isUnit_iff_ne_zero.mp
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : ∀ j,∑ k : Fin n,c k*x j^e k=0 := by
    intro j
    simpa [Matrix.row] using congrFun hc j
  have hp := sparse_polynomial_eq_zero e c x hx hpos hz
  have hcoeff := congrArg (fun P : Polynomial ℝ=>P.coeff (e i)) hp
  simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,he.eq_iff,eq_comm] using hcoeff

lemma power_det_pos_geometric {n : ℕ} (e : Fin n → ℕ) (he : StrictMono e) :
    0 < Matrix.det (fun i j : Fin n=>(2:ℝ)^(j.val*e i)) := by
  have hm : (fun i j : Fin n=>(2:ℝ)^(j.val*e i))=Matrix.vandermonde (fun i=>(2:ℝ)^e i) := by
    ext i j
    change (2:ℝ)^(j.val*e i)=((2:ℝ)^e i)^j.val
    rw [←pow_mul,mul_comm]
  rw [hm,Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  apply sub_pos.mpr
  exact pow_lt_pow_right₀ (by norm_num) (he (Finset.mem_Ioi.mp hj))

lemma power_det_pos {n : ℕ} (e : Fin n → ℕ) (x : Fin n → ℝ)
    (he : StrictMono e) (hx : StrictMono x) (hpos : ∀ j,0 < x j) :
    0 < Matrix.det (fun i j=>x j^e i) := by
  let z : ℝ → Fin n → ℝ := fun t j=>(1-t)*x j+t*2^j.val
  let f : ℝ → ℝ := fun t=>Matrix.det (fun i j=>z t j^e i)
  have hc : Continuous f := by
    apply Continuous.matrix_det
    fun_prop
  have h0 : f 0=Matrix.det (fun i j=>x j^e i) := by simp [f,z]
  have h1 : 0 < f 1 := by
    simpa [f,z,←pow_mul] using power_det_pos_geometric e he
  have hne : ∀ t∈Icc (0:ℝ) 1,f t≠0 := by
    intro t ht
    apply power_det_ne_zero e (z t) he.injective
    · apply StrictMono.injective
      intro i j hij
      have hp : (2:ℝ)^i.val < 2^j.val := pow_lt_pow_right₀ (by norm_num) hij
      have hxp := hx hij
      dsimp [z]
      rcases ht.1.eq_or_lt with rfl|htt
      · simpa using hxp
      · nlinarith [mul_pos htt (sub_pos.mpr hp),mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hxp.le)]
    · intro j
      dsimp [z]
      have hp : 0 < (2:ℝ)^j.val := by positivity
      rcases ht.1.eq_or_lt with rfl|htt
      · simpa using hpos j
      · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) (hpos j).le) (mul_pos htt hp)
  by_contra hh
  have hf0 : f 0 ≤ 0 := by rw [h0];exact le_of_not_gt hh
  obtain ⟨t,ht,heq⟩:=intermediate_value_Icc (show (0:ℝ) ≤ 1 by norm_num) hc.continuousOn ⟨hf0,h1.le⟩
  exact hne t ht heq
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix
noncomputable def newtonBasis (b : ℕ → ℝ) (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ range n,(X-Polynomial.C (b j))
noncomputable def newtonQuot (b : ℕ → ℝ) (P : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => P
  | n+1 => newtonQuot b P n /ₘ (X-Polynomial.C (b n))
noncomputable def newtonCoeff (b : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) : ℝ :=
  (newtonQuot b P n).eval (b n)
noncomputable def nodalOrder (b : ℕ → ℝ) (n : ℕ) : ℕ :=
  ((range n).filter (fun j=>b j=b n)).card
noncomputable def polynomialJet (P : Polynomial ℝ) (a : ℝ) (k : ℕ) : ℝ :=
  (taylor a P).coeff k
lemma newtonBasis_succ (b : ℕ → ℝ) (n : ℕ) :
    newtonBasis b (n+1)=newtonBasis b n*(X-Polynomial.C (b n)) := by
  simp [newtonBasis,prod_range_succ]
lemma newton_decomposition (b : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) :
    P=(∑ j ∈ range n,Polynomial.C (newtonCoeff b P j)*newtonBasis b j)+newtonBasis b n*newtonQuot b P n := by
  induction n with
  | zero => simp [newtonBasis,newtonQuot]
  | succ n ih =>
    have h := (newtonQuot b P n).modByMonic_add_div (X-Polynomial.C (b n))
    rw [modByMonic_X_sub_C_eq_C_eval] at h
    calc
      P=(∑ j ∈ range n,Polynomial.C (newtonCoeff b P j)*newtonBasis b j)+newtonBasis b n*newtonQuot b P n := ih
      _=(∑ j ∈ range n,Polynomial.C (newtonCoeff b P j)*newtonBasis b j)+newtonBasis b n*(Polynomial.C ((newtonQuot b P n).eval (b n))+(X-Polynomial.C (b n))*(newtonQuot b P n/ₘ(X-Polynomial.C (b n)))) := by rw [h]
      _=_ := by rw [sum_range_succ,newtonBasis_succ,newtonQuot,newtonCoeff];ring
lemma newtonQuot_natDegree_le (b : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (newtonQuot b P n).natDegree ≤ P.natDegree := by
  induction n with
  | zero => rfl
  | succ n ih => exact (natDegree_le_natDegree (degree_divByMonic_le _ _)).trans ih
lemma coeff_divByMonic_linear_fixed (P : Polynomial ℝ) (a : ℝ) (k D : ℕ)
    (hD : P.natDegree ≤ D) :
    (P/ₘ(X-Polynomial.C a)).coeff k=∑ j ∈ Icc (k+1) D,a^(j-(k+1))*P.coeff j := by
  rw [coeff_divByMonic_X_sub_C]
  apply sum_subset
  · intro j hj
    exact mem_Icc.mpr ⟨(mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans hD⟩
  · intro j hj hn
    rw [coeff_eq_zero_of_natDegree_lt,mul_zero]
    exact lt_of_not_ge (fun hh=>hn (mem_Icc.mpr ⟨(mem_Icc.mp hj).1,hh⟩))
lemma continuous_newtonQuot_coeff (P : Polynomial ℝ) (n k : ℕ) :
    Continuous (fun b : ℕ → ℝ=>(newtonQuot b P n).coeff k) := by
  induction n generalizing k with
  | zero =>
    change Continuous (fun _ : ℕ → ℝ => P.coeff k)
    exact continuous_const
  | succ n ih =>
    have he : (fun b : ℕ → ℝ=>(newtonQuot b P (n+1)).coeff k)=
        fun b=>∑ j ∈ Icc (k+1) P.natDegree,b n^(j-(k+1))*(newtonQuot b P n).coeff j := by
      funext b
      exact coeff_divByMonic_linear_fixed _ _ _ _ (newtonQuot_natDegree_le b P n)
    rw [he]
    exact continuous_finsetSum _ (fun j _=>(continuous_apply n).pow _ |>.mul (ih j))
lemma continuous_newtonCoeff (P : Polynomial ℝ) (n : ℕ) :
    Continuous (fun b=>newtonCoeff b P n) := by
  have he : (fun b=>newtonCoeff b P n)=fun b=>∑ j ∈ range (P.natDegree+1),
      (newtonQuot b P n).coeff j*b n^j := by
    funext b
    dsimp [newtonCoeff]
    rw [Polynomial.eval_eq_sum_range]
    apply sum_subset
    · exact range_mono (Nat.add_le_add_right (newtonQuot_natDegree_le b P n) 1)
    · intro j _ hj
      rw [coeff_eq_zero_of_natDegree_lt,zero_mul]
      exact Nat.lt_of_succ_le ((not_lt).mp (by simpa using hj))
  rw [he]
  exact continuous_finsetSum _ (fun j _=>(continuous_newtonQuot_coeff P n j).mul ((continuous_apply n).pow j))

lemma taylor_nodal_product (b : ℕ → ℝ) (s : Finset ℕ) (a : ℝ) :
    taylor a (∏ j∈s,(X-Polynomial.C (b j)))=
      X^((s.filter (fun j=>b j=a)).card)*∏ j∈s.filter (fun j=>b j≠a),(X+Polynomial.C (a-b j)) := by
  classical
  change (taylorAlgHom a) (∏ j∈s,(X-Polynomial.C (b j)))=_
  rw [map_prod]
  change (∏ j∈s,taylor a (X-Polynomial.C (b j)))=_
  have he : (fun j=>taylor a (X-Polynomial.C (b j)))=fun j=>X+Polynomial.C (a-b j) := by
    funext j
    simp [taylor_X,taylor_C,sub_eq_add_neg,add_assoc]
  rw [he,←Finset.prod_filter_mul_prod_filter_not (s:=s) (p:=fun j=>b j=a)]
  congr 1
  calc
    ∏ j∈s.filter (fun j=>b j=a),(X+Polynomial.C (a-b j))=∏ _j∈s.filter (fun j=>b j=a),(X:Polynomial ℝ) := by
      apply prod_congr rfl
      intro j hj
      simp [(mem_filter.mp hj).2]
    _ = _ := by simp
lemma polynomialJet_nodal_product_self (b : ℕ → ℝ) (s : Finset ℕ) (a : ℝ) :
    polynomialJet (∏ j∈s,(X-Polynomial.C (b j))) a ((s.filter (fun j=>b j=a)).card)=
      ∏ j∈s.filter (fun j=>b j≠a),(a-b j) := by
  rw [polynomialJet,taylor_nodal_product]
  rw [coeff_X_pow_mul']
  simp only [Nat.le_refl,ite_true,Nat.sub_self]
  rw [coeff_zero_eq_eval_zero,Polynomial.eval_prod]
  simp
lemma polynomialJet_mul_nodal_product_zero (b : ℕ → ℝ) (s : Finset ℕ) (a : ℝ)
    (k : ℕ) (Q : Polynomial ℝ) (hk : k < (s.filter (fun j=>b j=a)).card) :
    polynomialJet ((∏ j∈s,(X-Polynomial.C (b j)))*Q) a k=0 := by
  rw [polynomialJet,taylor_mul,taylor_nodal_product,mul_assoc,coeff_X_pow_mul']
  simp [not_le.mpr hk]
lemma nodalOrder_lt_count {b : ℕ → ℝ} {k n : ℕ} (hkn : k < n) :
    nodalOrder b k < ((range n).filter (fun j=>b j=b k)).card := by
  classical
  have hs : insert k ((range k).filter (fun j=>b j=b k)) ⊆ (range n).filter (fun j=>b j=b k) := by
    intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · simp [hkn]
    · exact mem_filter.mpr ⟨mem_range.mpr ((mem_range.mp (mem_filter.mp hj).1).trans hkn),(mem_filter.mp hj).2⟩
  have hcard := card_le_card hs
  have hk : k ∉ (range k).filter (fun j=>b j=b k) := by simp
  rw [card_insert_of_notMem hk] at hcard
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hcard
lemma polynomialJet_newtonBasis_gt {b : ℕ → ℝ} {k n : ℕ} (hkn : k < n) :
    polynomialJet (newtonBasis b n) (b k) (nodalOrder b k)=0 := by
  simpa [newtonBasis] using polynomialJet_mul_nodal_product_zero b (range n) (b k) (nodalOrder b k) 1 (nodalOrder_lt_count hkn)
lemma polynomialJet_newtonBasis_diagonal (b : ℕ → ℝ) (k : ℕ) :
    polynomialJet (newtonBasis b k) (b k) (nodalOrder b k)=
      ∏ j∈(range k).filter (fun j=>b j≠b k),(b k-b j) :=
  polynomialJet_nodal_product_self b (range k) (b k)
lemma polynomialJet_decomposition {n : ℕ} (b : ℕ → ℝ) (P : Polynomial ℝ) (k : Fin n) :
    polynomialJet P (b k) (nodalOrder b k)=∑ j : Fin n,newtonCoeff b P j*polynomialJet (newtonBasis b j) (b k) (nodalOrder b k) := by
  have h := congrArg (fun Q=>polynomialJet Q (b k) (nodalOrder b k)) (newton_decomposition b P n)
  have hz:=polynomialJet_mul_nodal_product_zero b (range n) (b k) (nodalOrder b k) (newtonQuot b P n) (nodalOrder_lt_count k.isLt)
  have hsum : polynomialJet (∑ j∈range n,Polynomial.C (newtonCoeff b P j)*newtonBasis b j) (b k) (nodalOrder b k)=
      ∑ j∈range n,newtonCoeff b P j*polynomialJet (newtonBasis b j) (b k) (nodalOrder b k) := by
    simp [polynomialJet,map_sum,taylor_mul,Polynomial.coeff_C_mul]
  have h2 : polynomialJet P (b k) (nodalOrder b k)=
      polynomialJet (∑ j∈range n,Polynomial.C (newtonCoeff b P j)*newtonBasis b j) (b k) (nodalOrder b k)+
      polynomialJet (newtonBasis b n*newtonQuot b P n) (b k) (nodalOrder b k) := by
    simpa only [polynomialJet,map_add,coeff_add] using h
  rw [hsum,show polynomialJet (newtonBasis b n*newtonQuot b P n) (b k) (nodalOrder b k)=0 from hz,add_zero] at h2
  rw [Fin.sum_univ_eq_sum_range (fun j=>newtonCoeff b P j*polynomialJet (newtonBasis b j) (b k) (nodalOrder b k)) n]
  exact h2
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix Filter Topology
noncomputable def newtonJetMatrix (n : ℕ) (b : ℕ → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>polynomialJet (newtonBasis b i) (b j) (nodalOrder b j)
lemma newtonJetMatrix_det (n : ℕ) (b : ℕ → ℝ) :
    (newtonJetMatrix n b).det=∏ k : Fin n,∏ j∈(range k.val).filter (fun j=>b j≠b k),(b k-b j) := by
  rw [Matrix.det_of_isUpperTriangular]
  · apply prod_congr rfl
    intro k _
    exact polynomialJet_newtonBasis_diagonal b k
  · intro i j hij
    exact polynomialJet_newtonBasis_gt hij
lemma newtonJetMatrix_det_pos {n : ℕ} (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) : 0 < (newtonJetMatrix n b).det := by
  rw [newtonJetMatrix_det]
  apply prod_pos
  intro k _
  apply prod_pos
  intro j hj
  have hjk : j < k.val := mem_range.mp (mem_filter.mp hj).1
  have hbj := hb (show (⟨j,hjk.trans k.isLt⟩:Fin n) ≤ k from Nat.le_of_lt hjk)
  exact sub_pos.mpr (lt_of_le_of_ne hbj (mem_filter.mp hj).2)
lemma jet_det_factorization {n : ℕ} (b : ℕ → ℝ) (P : Fin n → Polynomial ℝ) :
    Matrix.det (fun i j=>polynomialJet (P i) (b j) (nodalOrder b j))=
      Matrix.det (fun i j : Fin n=>newtonCoeff b (P i) j)*(newtonJetMatrix n b).det := by
  have hm : (Matrix.of fun i j : Fin n=>polynomialJet (P i) (b j) (nodalOrder b j))=
      (Matrix.of fun i j : Fin n=>newtonCoeff b (P i) j)*newtonJetMatrix n b := by
    ext i j
    exact polynomialJet_decomposition b (P i) j
  exact (congrArg Matrix.det hm).trans (Matrix.det_mul _ _)
lemma nodalOrder_eq_zero_strict {n : ℕ} {b : ℕ → ℝ} (hb : StrictMono (fun i : Fin n=>b i)) (k : Fin n) :
    nodalOrder b k=0 := by
  classical
  unfold nodalOrder
  rw [card_eq_zero,filter_eq_empty_iff]
  intro j hj
  have hlt := hb (show (⟨j,(mem_range.mp hj).trans k.isLt⟩:Fin n) < k from mem_range.mp hj)
  exact hlt.ne
lemma polynomialJet_zero (P : Polynomial ℝ) (a : ℝ) : polynomialJet P a 0=P.eval a := by
  simp [polynomialJet,coeff_zero_eq_eval_zero,Polynomial.taylor_eval]
lemma newton_power_det_pos {n : ℕ} (b : ℕ → ℝ) (e : Fin n → ℕ)
    (hb : StrictMono (fun i : Fin n=>b i)) (hpos : ∀ i : Fin n,0 < b i) (he : StrictMono e) :
    0 < Matrix.det (fun i j : Fin n=>newtonCoeff b (X^e i) j) := by
  have h := power_det_pos e (fun i : Fin n=>b i) he hb hpos
  have hf := jet_det_factorization b (fun i=>X^e i)
  have hj : (fun i j : Fin n=>polynomialJet ((X:Polynomial ℝ)^e i) (b j) (nodalOrder b j))=
      fun i j : Fin n=>b j^e i := by
    ext i j
    rw [nodalOrder_eq_zero_strict hb,polynomialJet_zero]
    simp
  rw [←hj,hf] at h
  exact (mul_pos_iff_of_pos_right (newtonJetMatrix_det_pos b hb.monotone)).mp h
lemma newton_power_det_nonneg {n : ℕ} (b : ℕ → ℝ) (e : Fin n → ℕ)
    (hb : Monotone (fun i : Fin n=>b i)) (hpos : ∀ i : Fin n,0 ≤ b i) (he : StrictMono e) :
    0 ≤ Matrix.det (fun i j : Fin n=>newtonCoeff b (X^e i) j) := by
  let B : ℝ → ℕ → ℝ := fun t j=>b j+t*(j+1)
  let f : ℝ → ℝ := fun t=>Matrix.det (fun i j : Fin n=>newtonCoeff (B t) (X^e i) j)
  have hc : Continuous f := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (continuous_newtonCoeff (X^e i) j).comp (by dsimp [B];fun_prop)
  have hp : ∀ᶠ t in 𝓝[>] (0:ℝ),0 ≤ f t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply (newton_power_det_pos (B t) e _ _ he).le
    · intro i j hij
      have hb' := hb hij.le
      have hc' : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
      dsimp [B]
      nlinarith [mul_pos ht (sub_pos.mpr hc')]
    · intro i
      dsimp [B]
      exact add_pos_of_nonneg_of_pos (hpos i) (mul_pos ht (by positivity))
  have hh : 0 ≤ f 0 := ge_of_tendsto (hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)) hp
  simpa [f,B] using hh
lemma power_jet_det_nonneg {n : ℕ} (b : ℕ → ℝ) (e : Fin n → ℕ)
    (hb : Monotone (fun i : Fin n=>b i)) (hpos : ∀ i : Fin n,0 ≤ b i) (he : StrictMono e) :
    0 ≤ Matrix.det (fun i j : Fin n=>polynomialJet (X^e i) (b j) (nodalOrder b j)) := by
  rw [jet_det_factorization]
  exact mul_nonneg (newton_power_det_nonneg b e hb hpos he) (newtonJetMatrix_det_pos b hb).le

lemma newtonQuot_natDegree (b : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (newtonQuot b P n).natDegree=P.natDegree-n := by
  induction n with
  | zero => simp [newtonQuot]
  | succ n ih => simp [newtonQuot,natDegree_divByMonic _ (monic_X_sub_C _),ih,Nat.sub_sub]
lemma newtonQuot_leadingCoeff {b : ℕ → ℝ} {P : Polynomial ℝ} {n : ℕ} (hn : n ≤ P.natDegree) :
    (newtonQuot b P n).leadingCoeff=P.leadingCoeff := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [newtonQuot,leadingCoeff_divByMonic_X_sub_C,ih (by omega)]
    intro hz
    have hdeg : (newtonQuot b P n).natDegree=0 := natDegree_eq_of_degree_eq_some hz
    rw [newtonQuot_natDegree] at hdeg
    omega
lemma newtonQuot_eq_zero_of_lt {b : ℕ → ℝ} {P : Polynomial ℝ} {n : ℕ} (hn : P.natDegree < n) :
    newtonQuot b P n=0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [newtonQuot]
    apply (divByMonic_eq_zero_iff (monic_X_sub_C _)).mpr
    rw [degree_X_sub_C]
    have hh : (newtonQuot b P n).natDegree=0 := by rw [newtonQuot_natDegree];omega
    exact (natDegree_eq_zero_iff_degree_le_zero.mp hh).trans_lt (by norm_num)
lemma newtonCoeff_X_pow_diagonal (b : ℕ → ℝ) (n : ℕ) : newtonCoeff b (X^n) n=1 := by
  have hd : (newtonQuot b (X^n) n).natDegree=0 := by rw [newtonQuot_natDegree,natDegree_X_pow];omega
  have hl : (newtonQuot b (X^n) n).leadingCoeff=1 := by
    rw [newtonQuot_leadingCoeff (by simp),leadingCoeff_X_pow]
  have he : newtonQuot b (X^n) n=1 := by
    rw [eq_C_of_natDegree_eq_zero hd]
    have hc := hl
    rw [leadingCoeff,hd] at hc
    rw [hc,Polynomial.C_1]
  simp [newtonCoeff,he]
lemma newtonCoeff_X_pow_above {b : ℕ → ℝ} {i j : ℕ} (hij : i < j) :
    newtonCoeff b (X^i) j=0 := by
  rw [newtonCoeff,newtonQuot_eq_zero_of_lt (by simpa using hij)]
  simp
lemma newton_consecutive_det (n : ℕ) (b : ℕ → ℝ) :
    Matrix.det (fun i j : Fin n=>newtonCoeff b (X^i.val) j)=1 := by
  have ht : (Matrix.of fun i j : Fin n=>newtonCoeff b (X^i.val) j).IsLowerTriangular := by
    intro i j hij
    exact newtonCoeff_X_pow_above hij
  exact (Matrix.det_of_isLowerTriangular _ ht).trans (by simp [newtonCoeff_X_pow_diagonal])
lemma consecutive_jet_det_pos {n : ℕ} (b : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) :
    0 < Matrix.det (fun i j : Fin n=>polynomialJet (X^i.val) (b j) (nodalOrder b j)) := by
  rw [jet_det_factorization,newton_consecutive_det,one_mul]
  exact newtonJetMatrix_det_pos b hb
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
lemma det_rectangular_expansion {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    (A*B).det=∑ f : n → m, (A.submatrix id f).det*∏ i,B (f i) i := by
  classical
  simp only [Matrix.det_apply',Matrix.mul_apply,Finset.prod_univ_sum,
    Finset.mul_sum,Fintype.piFinset_univ,Matrix.submatrix_apply,id_eq]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro f _
  rw [Finset.sum_mul]
  apply sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib,mul_assoc]
lemma det_rectangular_binet {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
    (A : Matrix n m ℝ) (B : Matrix m n ℝ) :
    ∑ f : n → m,(A.submatrix id f).det*(B.submatrix f id).det=
      Fintype.card (Equiv.Perm n)*(A*B).det := by
  classical
  simp_rw [Matrix.det_apply' (B.submatrix _ _),Finset.mul_sum]
  rw [Finset.sum_comm]
  have he (σ : Equiv.Perm n) :
      (∑ f : n → m,(A.submatrix id f).det*
        ((Equiv.Perm.sign σ:ℤ)*∏ i,(B.submatrix f id) (σ i) i))=(A*B).det := by
    rw [det_rectangular_expansion]
    let e : (n → m) ≃ (n → m) := Equiv.arrowCongr σ.symm (Equiv.refl m)
    apply Fintype.sum_equiv e
    intro f
    have hm : A.submatrix id (e f)=(A.submatrix id f).submatrix id σ := by
      ext i j
      rfl
    rw [hm,Matrix.det_permute']
    have hp : (∏ i,(B.submatrix f id) (σ i) i)=∏ i,B ((e f) i) i := by
      rfl
    rw [hp]
    ring
  simp_rw [he]
  simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Equiv
lemma sorted_injective_exponents {n : ℕ} {e : Fin n → ℕ} (he : Function.Injective e) :
    ∃ (d : Fin n → ℕ) (σ : Equiv.Perm (Fin n)),StrictMono d ∧ e=d∘σ := by
  classical
  let s := univ.image e
  have hc : s.card=n := by simp [s,card_image_of_injective _ he]
  let o := s.orderIsoOfFin hc
  let q : Fin n ≃ s := Equiv.ofBijective (fun i=>⟨e i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact he (congrArg Subtype.val h)
    · intro a
      obtain ⟨i,_,hi⟩ := mem_image.mp a.property
      exact ⟨i,Subtype.ext hi⟩)
  refine ⟨fun i=>(o i).val,q.trans o.symm,?_,?_⟩
  · exact o.strictMono
  · ext i
    exact (congrArg Subtype.val (o.apply_symm_apply (q i))).symm
lemma power_jet_det_pair_nonneg {n : ℕ} (b x : ℕ → ℝ) (e : Fin n → ℕ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : Monotone (fun i : Fin n=>x i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i : Fin n,0 ≤ x i) :
    0 ≤ Matrix.det (fun i j : Fin n=>polynomialJet (X^e i) (b j) (nodalOrder b j))*
      Matrix.det (fun i j : Fin n=>polynomialJet (X^e i) (x j) (nodalOrder x j)) := by
  classical
  by_cases he : Function.Injective e
  · obtain ⟨d,σ,hd,he⟩ := sorted_injective_exponents he
    rw [he]
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j=>polynomialJet (X^d i) (b j) (nodalOrder b j)
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j=>polynomialJet (X^d i) (x j) (nodalOrder x j)
    change 0 ≤ (A.submatrix σ id).det*(B.submatrix σ id).det
    rw [Matrix.det_permute,Matrix.det_permute]
    have hA := power_jet_det_nonneg b d hb hb0 hd
    have hB := power_jet_det_nonneg x d hx hx0 hd
    have hp := mul_nonneg (sq_nonneg (((Equiv.Perm.sign σ:ℤ):ℝ))) (mul_nonneg hA hB)
    dsimp [A,B] at *
    nlinarith only [hp]
  · obtain ⟨i,j,heq,hij⟩ := Function.not_injective_iff.mp he
    have hz : (Matrix.of fun i j : Fin n=>polynomialJet (X^e i) (b j) (nodalOrder b j)).det=0 := by
      apply Matrix.det_zero_of_row_eq hij
      change (fun j : Fin n=>polynomialJet (X^e i) (b j) (nodalOrder b j))=
        (fun k : Fin n=>polynomialJet (X^e j) (b k) (nodalOrder b k))
      rw [heq]
    change 0 ≤ (Matrix.of fun i j : Fin n=>polynomialJet (X^e i) (b j) (nodalOrder b j)).det*_
    rw [hz,zero_mul]
noncomputable def kernelPartial (m : ℕ) (b x : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ k∈range m,polynomialJet (X^k) (b i) (nodalOrder b i)*
    polynomialJet (X^k) (x j) (nodalOrder x j)/(2*k).factorial
lemma kernelPartial_det_lower {n m : ℕ} (hnm : n ≤ m) (b x : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : Monotone (fun i : Fin n=>x i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i : Fin n,0 ≤ x i) :
    (∏ i : Fin n,((2*i.val).factorial:ℝ)⁻¹)*
      Matrix.det (fun i j : Fin n=>polynomialJet (X^i.val) (b j) (nodalOrder b j))*
      Matrix.det (fun i j : Fin n=>polynomialJet (X^i.val) (x j) (nodalOrder x j)) ≤
      Fintype.card (Equiv.Perm (Fin n))*Matrix.det (fun i j : Fin n=>kernelPartial m b x i j) := by
  classical
  let A : Matrix (Fin n) (Fin m) ℝ := fun i k=>
    ((2*k.val).factorial:ℝ)⁻¹*polynomialJet (X^k.val) (b i) (nodalOrder b i)
  let B : Matrix (Fin m) (Fin n) ℝ := fun k j=>polynomialJet (X^k.val) (x j) (nodalOrder x j)
  have hm : (A*B)=Matrix.of (fun i j : Fin n=>kernelPartial m b x i j) := by
    ext i j
    rw [Matrix.mul_apply]
    dsimp [A,B,kernelPartial]
    rw [Fin.sum_univ_eq_sum_range (fun k=>((2*k).factorial:ℝ)⁻¹*polynomialJet (X^k) (b i) (nodalOrder b i)*polynomialJet (X^k) (x j) (nodalOrder x j)) m]
    apply sum_congr rfl
    intro k _
    ring
  have hdet (f : Fin n → Fin m) :
      (A.submatrix id f).det=(∏ i : Fin n,((2*(f i).val).factorial:ℝ)⁻¹)*
        Matrix.det (fun i j : Fin n=>polynomialJet (X^(f i).val) (b j) (nodalOrder b j)) := by
    rw [←Matrix.det_transpose]
    change Matrix.det (Matrix.of fun i j : Fin n=>((2*(f i).val).factorial:ℝ)⁻¹*
      polynomialJet (X^(f i).val) (b j) (nodalOrder b j))=_
    exact Matrix.det_mul_column _ _
  have hn (f : Fin n → Fin m) : 0 ≤ (A.submatrix id f).det*(B.submatrix f id).det := by
    rw [hdet,mul_assoc]
    exact mul_nonneg (prod_nonneg (fun i _=>by positivity))
      (power_jet_det_pair_nonneg b x (fun i=>(f i).val) hb hx hb0 hx0)
  have hl := single_le_sum (fun f _=>hn f) (mem_univ (fun i : Fin n=>i.castLE hnm))
  rw [det_rectangular_binet,hm] at hl
  rw [hdet] at hl
  exact hl
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Filter Topology
lemma polynomialJet_X_pow (k r : ℕ) (a : ℝ) : polynomialJet (X^k) a r=(k.choose r:ℝ)*a^(k-r) := by
  rw [polynomialJet,taylor_coeff,←monomial_one_right_eq_X_pow,hasseDeriv_monomial]
  simp
lemma polynomialJet_hasDerivAt (P : Polynomial ℝ) (r : ℕ) (a : ℝ) :
    HasDerivAt (fun y=>polynomialJet P y r) ((r+1:ℝ)*polynomialJet P a (r+1)) a := by
  have he : (hasseDeriv r P).derivative=(r+1) • hasseDeriv (r+1) P := by
    have h := DFunLike.congr_fun (hasseDeriv_comp (R:=ℝ) 1 r) P
    simpa [Nat.add_comm,add_mul] using h
  have h := (hasseDeriv r P).hasDerivAt a
  rw [he] at h
  simpa [polynomialJet,taylor_coeff,eval_smul,nsmul_eq_mul] using h
lemma polynomialJet_X_pow_bound (k r : ℕ) {a R : ℝ} (hR : 1 ≤ R) (ha : |a| ≤ R) :
    |polynomialJet (X^k) a r| ≤ (2*R)^k := by
  rw [polynomialJet_X_pow,abs_mul,abs_of_nonneg (Nat.cast_nonneg _),abs_pow,mul_pow]
  apply mul_le_mul
  · exact_mod_cast Nat.choose_le_two_pow k r
  · exact (pow_le_pow_left₀ (abs_nonneg _) ha _).trans (pow_le_pow_right₀ hR (Nat.sub_le _ _))
  · positivity
  · positivity
lemma summable_evenFactorial {T : ℝ} (hT : 0 ≤ T) : Summable (fun k : ℕ=>T^k/(2*k).factorial) := by
  convert (Real.hasSum_cosh (Real.sqrt T)).summable using 1
  funext k
  rw [pow_mul,Real.sq_sqrt hT]
noncomputable def kernelJetTerm (r s : ℕ) (b x : ℝ) (k : ℕ) : ℝ :=
  polynomialJet (X^k) b r*polynomialJet (X^k) x s/(2*k).factorial
noncomputable def cosineKernelJet (r s : ℕ) (b x : ℝ) : ℝ := ∑' k,kernelJetTerm r s b x k
lemma kernelJetTerm_bound (r s k : ℕ) {b x R S : ℝ}
    (hR : 1 ≤ R) (hS : 1 ≤ S) (hb : |b| ≤ R) (hx : |x| ≤ S) :
    ‖kernelJetTerm r s b x k‖ ≤ (4*R*S)^k/(2*k).factorial := by
  rw [kernelJetTerm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ ((2*k).factorial:ℝ) from Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    |polynomialJet (X^k) b r| * |polynomialJet (X^k) x s| ≤ (2*R)^k*(2*S)^k :=
      mul_le_mul (polynomialJet_X_pow_bound k r hR hb) (polynomialJet_X_pow_bound k s hS hx) (abs_nonneg _) (by positivity)
    _=(4*R*S)^k := by rw [←mul_pow];ring_nf
lemma kernelJetTerm_summable (r s : ℕ) (b x : ℝ) : Summable (kernelJetTerm r s b x) := by
  exact (summable_evenFactorial (show 0 ≤ 4*(|b|+1)*(|x|+1) by positivity)).of_norm_bounded
    (fun k=>kernelJetTerm_bound r s k (by linarith [abs_nonneg b]) (by linarith [abs_nonneg x]) (by linarith) (by linarith))
lemma cosineKernelJet_hasDerivAt_left (r s : ℕ) (b x : ℝ) :
    HasDerivAt (fun y=>cosineKernelJet r s y x) ((r+1:ℝ)*cosineKernelJet (r+1) s b x) b := by
  let R := |b|+2
  let S := |x|+1
  have hR : 1 ≤ R := by dsimp [R];linarith [abs_nonneg b]
  have hS : 1 ≤ S := by dsimp [S];linarith [abs_nonneg x]
  have hg (k : ℕ) (y : ℝ) : HasDerivAt (fun z=>kernelJetTerm r s z x k)
      ((r+1:ℝ)*kernelJetTerm (r+1) s y x k) y := by
    convert ((polynomialJet_hasDerivAt (X^k) r y).mul_const (polynomialJet (X^k) x s)).div_const ((2*k).factorial:ℝ) using 1 <;> first | rfl | (unfold kernelJetTerm; ring)
  have hu : Summable (fun k : ℕ=>(r+1:ℝ)*((4*R*S)^k/(2*k).factorial)) :=
    (summable_evenFactorial (by positivity : 0 ≤ 4*R*S)).mul_left _
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo (convex_Ioo (-R) R).isPreconnected
    (fun k y _=>hg k y) (y₀:=b) (y:=b) (t:=Set.Ioo (-R) R)
  have hb : b ∈ Set.Ioo (-R) R := by dsimp [R];constructor <;> linarith [le_abs_self b,neg_abs_le b]
  have hh := h (fun k y hy=>by
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (r+1:ℝ))]
    exact mul_le_mul_of_nonneg_left
      (kernelJetTerm_bound (r+1) s k hR hS ((abs_lt.mpr hy).le) (by dsimp [S];linarith)) (by positivity))
    hb (kernelJetTerm_summable r s b x) hb
  simpa only [cosineKernelJet,tsum_mul_left] using hh
lemma cosineKernelJet_symm (r s : ℕ) (b x : ℝ) : cosineKernelJet r s b x=cosineKernelJet s r x b := by
  unfold cosineKernelJet
  apply tsum_congr
  intro k
  unfold kernelJetTerm
  rw [mul_comm]
lemma cosineKernelJet_hasDerivAt_right (r s : ℕ) (b x : ℝ) :
    HasDerivAt (fun y=>cosineKernelJet r s b y) ((s+1:ℝ)*cosineKernelJet r (s+1) b x) x := by
  simpa only [cosineKernelJet_symm r s,cosineKernelJet_symm r (s+1)] using cosineKernelJet_hasDerivAt_left s r x b
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Filter Topology
lemma cosineKernelJet_iteratedDeriv_left (r s : ℕ) (b x : ℝ) :
    iteratedDeriv r (fun y=>cosineKernelJet 0 s y x) b=(r.factorial:ℝ)*cosineKernelJet r s b x := by
  induction r generalizing b with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv r (fun y=>cosineKernelJet 0 s y x)=
      (fun y=>(r.factorial:ℝ)*cosineKernelJet r s y x) from funext (fun y=>ih y)]
    rw [((cosineKernelJet_hasDerivAt_left r s b x).const_mul (r.factorial:ℝ)).deriv]
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    ring
lemma cosineKernelJet_iteratedDeriv_right (r s : ℕ) (b x : ℝ) :
    iteratedDeriv s (fun y=>cosineKernelJet r 0 b y) x=(s.factorial:ℝ)*cosineKernelJet r s b x := by
  simpa only [cosineKernelJet_symm r 0,cosineKernelJet_symm r s] using cosineKernelJet_iteratedDeriv_left s r x b
lemma cosineKernelJet_mixed (r s : ℕ) (b x : ℝ) :
    iteratedDeriv s (fun y=>iteratedDeriv r (fun z=>cosineKernelJet 0 0 z y) b) x=
      (r.factorial:ℝ)*(s.factorial:ℝ)*cosineKernelJet r s b x := by
  simp_rw [cosineKernelJet_iteratedDeriv_left]
  rw [iteratedDeriv_const_mul_field,cosineKernelJet_iteratedDeriv_right]
  ring
lemma cosineKernelJet_zero_zero_cosh {b x : ℝ} (hb : 0 ≤ b) (hx : 0 ≤ x) :
    cosineKernelJet 0 0 b x=Real.cosh (Real.sqrt b*Real.sqrt x) := by
  apply HasSum.tsum_eq
  convert Real.hasSum_cosh (Real.sqrt b*Real.sqrt x) using 1
  ext k
  dsimp [kernelJetTerm]
  rw [polynomialJet_X_pow,polynomialJet_X_pow]
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  rw [mul_pow,pow_mul,pow_mul,Real.sq_sqrt hb,Real.sq_sqrt hx]
lemma kernelPartial_tendsto (b x : ℕ → ℝ) (i j : ℕ) :
    Tendsto (fun m=>kernelPartial m b x i j) atTop
      (𝓝 (cosineKernelJet (nodalOrder b i) (nodalOrder x j) (b i) (x j))) :=
  (kernelJetTerm_summable _ _ _ _).hasSum.tendsto_sum_nat
lemma cosineKernelJet_det_pos {n : ℕ} (b x : ℕ → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : Monotone (fun i : Fin n=>x i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i : Fin n,0 ≤ x i) :
    0 < Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) (nodalOrder x j) (b i) (x j)) := by
  let c := (∏ i : Fin n,((2*i.val).factorial:ℝ)⁻¹)*
      Matrix.det (fun i j : Fin n=>polynomialJet (X^i.val) (b j) (nodalOrder b j))*
      Matrix.det (fun i j : Fin n=>polynomialJet (X^i.val) (x j) (nodalOrder x j))
  have hc : 0 < c := by
    apply mul_pos
    · exact mul_pos (prod_pos (fun i _=>by positivity)) (consecutive_jet_det_pos b hb)
    · exact consecutive_jet_det_pos x hx
  have hd : Continuous (Matrix.det : Matrix (Fin n) (Fin n) ℝ → ℝ) := continuous_id.matrix_det
  have ht := hd.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun i : Fin n=>tendsto_pi_nhds.mpr (fun j : Fin n=>kernelPartial_tendsto b x i j)))
  have hl : c ≤ Fintype.card (Equiv.Perm (Fin n))*Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) (nodalOrder x j) (b i) (x j)) := by
    apply ge_of_tendsto (ht.const_mul (Fintype.card (Equiv.Perm (Fin n)):ℝ))
    filter_upwards [eventually_ge_atTop n] with m hm
    exact kernelPartial_det_lower hm b x hb hx hb0 hx0
  have hp : 0 < (Fintype.card (Equiv.Perm (Fin n)):ℝ) := by positivity
  exact pos_of_mul_pos_right (hc.trans_le hl) hp.le
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory Matrix Finset Equiv
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace α]
variable (μ : Measure α) [SigmaFinite μ] (F G : ι → α → ℝ)
noncomputable def evaluationMatrix (x : ι → α) : Matrix ι ι ℝ := fun i j=>F i (x j)
noncomputable def gramMatrix : Matrix ι ι ℝ := fun i j=>∫ x,F i x*G j x ∂μ
omit [MeasurableSpace α] in
lemma det_evaluation_product_expansion (x : ι → α) :
    (evaluationMatrix F x).det*(evaluationMatrix G x).det=
      ∑ σ : Perm ι,∑ τ : Perm ι,((Perm.sign σ:ℤ):ℝ)*((Perm.sign τ:ℤ):ℝ)*
        ∏ i,F (σ i) (x i)*G (τ i) (x i) := by
  simp only [Matrix.det_apply',evaluationMatrix,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  apply sum_congr rfl
  intro τ _
  rw [prod_mul_distrib]
  ring
lemma integrable_det_evaluation_product (h : ∀ i j,Integrable (fun x=>F i x*G j x) μ) :
    Integrable (fun x : ι → α=>(evaluationMatrix F x).det*(evaluationMatrix G x).det)
      (Measure.pi (fun _ : ι=>μ)) := by
  simp_rw [det_evaluation_product_expansion]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  exact (Integrable.fintype_prod (fun i=>h (σ i) (τ i))).const_mul _
lemma andreief (h : ∀ i j,Integrable (fun x=>F i x*G j x) μ) :
    (∫ x : ι → α,(evaluationMatrix F x).det*(evaluationMatrix G x).det ∂Measure.pi (fun _ : ι=>μ))=
      Fintype.card (Perm ι)*(gramMatrix μ F G).det := by
  classical
  have hi (σ τ : Perm ι) : Integrable (fun x : ι → α=>
      ((Perm.sign σ:ℤ):ℝ)*((Perm.sign τ:ℤ):ℝ)*(∏ i,F (σ i) (x i)*G (τ i) (x i)))
      (Measure.pi (fun _ : ι=>μ)) :=
    (Integrable.fintype_prod (fun i=>h (σ i) (τ i))).const_mul _
  simp_rw [det_evaluation_product_expansion]
  rw [integral_finsetSum univ (fun σ _=>integrable_finsetSum _ (fun τ _=>hi σ τ))]
  simp only [integral_finsetSum univ (fun τ _=>hi _ τ),integral_const_mul]
  rw [sum_comm]
  have he (τ : Perm ι) :
      (∑ σ : Perm ι,((Perm.sign σ:ℤ):ℝ)*((Perm.sign τ:ℤ):ℝ)*
        ∏ i,∫ x,F (σ i) x*G (τ i) x ∂μ)=(gramMatrix μ F G).det := by
    calc
      _=((Perm.sign τ:ℤ):ℝ)*(gramMatrix μ F G |>.submatrix id τ).det := by
        rw [Matrix.det_apply',mul_sum]
        apply sum_congr rfl
        intro σ _
        simp only [Matrix.submatrix_apply,gramMatrix,id_eq]
        ring
      _=_ := by
        rw [Matrix.det_permute',←mul_assoc,←Int.cast_mul,←Units.val_mul,Int.units_mul_self]
        simp
  have ip (σ τ : Perm ι) :
      (∫ x : ι → α,∏ i,F (σ i) (x i)*G (τ i) (x i) ∂Measure.pi (fun _ : ι=>μ))=
        ∏ i,∫ x,F (σ i) x*G (τ i) x ∂μ :=
    integral_fintype_prod_eq_prod (fun i x=>F (σ i) x*G (τ i) x)
  simp_rw [ip]
  simp_rw [he]
  simp
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Matrix Finset Equiv
lemma sorted_injective_real {n : ℕ} {e : Fin n → ℝ} (he : Function.Injective e) :
    ∃ (d : Fin n → ℝ) (σ : Equiv.Perm (Fin n)),StrictMono d ∧ e=d∘σ := by
  classical
  let s := univ.image e
  have hc : s.card=n := by simp [s,card_image_of_injective _ he]
  let o := s.orderIsoOfFin hc
  let q : Fin n ≃ s := Equiv.ofBijective (fun i=>⟨e i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h
      exact he (congrArg Subtype.val h)
    · intro a
      obtain ⟨i,_,hi⟩ := mem_image.mp a.property
      exact ⟨i,Subtype.ext hi⟩)
  refine ⟨fun i=>(o i).val,q.trans o.symm,?_,?_⟩
  · exact o.strictMono
  · ext i
    exact (congrArg Subtype.val (o.apply_symm_apply (q i))).symm
noncomputable def jetEvaluation {n : ℕ} (b : ℕ → ℝ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j=>cosineKernelJet (nodalOrder b i) 0 (b i) (x j)
lemma jetEvaluation_det_pos {n : ℕ} (b : ℕ → ℝ) (x : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hx : StrictMono x)
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hx0 : ∀ i,0 ≤ x i) :
    0 < (jetEvaluation b x).det := by
  classical
  let y : ℕ → ℝ := fun k=> if hk : k<n then x ⟨k,hk⟩ else 0
  have hy (i : Fin n) : y i=x i := by simp [y]
  have ho (i : Fin n) : nodalOrder y i=0 := by
    rw [nodalOrder,card_eq_zero]
    apply filter_eq_empty_iff.mpr
    intro k hk he
    have hki : k < i.val := mem_range.mp hk
    have hkn : k<n := lt_trans hki i.isLt
    have hkval : y k=x ⟨k,hkn⟩ := by simp [y,hkn]
    rw [hy,hkval] at he
    exact (hx (show (⟨k,hkn⟩:Fin n) < i from hki)).ne he
  have h:=cosineKernelJet_det_pos b y hb (fun i j hij=>by simpa only [hy] using hx.monotone hij) hb0
    (fun i=>by simpa only [hy] using hx0 i)
  change 0 < Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i) (x j))
  simpa only [ho,hy] using h
lemma jetEvaluation_det_product_pos {n : ℕ} (b c : ℕ → ℝ) (x : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i)
    (hx : Function.Injective x) (hx0 : ∀ i,0 ≤ x i) :
    0 < (jetEvaluation b x).det*(jetEvaluation c x).det := by
  obtain ⟨d,σ,hd,he⟩ := sorted_injective_real hx
  have hd0 (i) : 0 ≤ d i := by
    have h:=hx0 (σ.symm i)
    simpa only [he,Function.comp_apply,σ.apply_symm_apply] using h
  have hA := jetEvaluation_det_pos b d hb hd hb0 hd0
  have hB := jetEvaluation_det_pos c d hc hd hc0 hd0
  have hhe (a : ℕ → ℝ) : jetEvaluation a x=(jetEvaluation a d).submatrix id σ := by
    ext i j
    simp [jetEvaluation,he]
  rw [hhe b,hhe c,Matrix.det_permute',Matrix.det_permute']
  have hs : (((Perm.sign σ:ℤ):ℝ))*(((Perm.sign σ:ℤ):ℝ))=1 := by
    rw [←Int.cast_mul,←Units.val_mul,Int.units_mul_self];norm_num
  nlinarith only [mul_pos hA hB,hs]
lemma jetEvaluation_det_product_nonneg {n : ℕ} (b c : ℕ → ℝ) (x : Fin n → ℝ)
    (hb : Monotone (fun i : Fin n=>b i)) (hc : Monotone (fun i : Fin n=>c i))
    (hb0 : ∀ i : Fin n,0 ≤ b i) (hc0 : ∀ i : Fin n,0 ≤ c i) (hx0 : ∀ i,0 ≤ x i) :
    0 ≤ (jetEvaluation b x).det*(jetEvaluation c x).det := by
  by_cases hx : Function.Injective x
  · exact (jetEvaluation_det_product_pos b c x hb hc hb0 hc0 hx hx0).le
  · obtain ⟨i,j,he,hij⟩ := Function.not_injective_iff.mp hx
    have hz : (jetEvaluation b x).det=0 := by
      apply Matrix.det_zero_of_column_eq hij
      intro k
      simp only [jetEvaluation,he]
    rw [hz,zero_mul]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
