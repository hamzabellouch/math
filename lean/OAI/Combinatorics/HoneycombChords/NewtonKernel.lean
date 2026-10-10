import OAI.Combinatorics.HoneycombChords.BetaKernel

namespace OAI

/-! Total positivity and convergence of Newton interpolation kernels.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv

def TotallyNonnegative {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ (n : ℕ) (r c : Fin n → Fin d),StrictMono r → StrictMono c →
    0≤(A.submatrix r c).det

lemma lowerBidiagonal_totallyNonnegative {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (ha : ∀ i j,0≤A i j)
    (hz : ∀ i j,A i j≠0 → i.val=j.val ∨ i.val=j.val+1) : TotallyNonnegative A := by
  classical
  intro n r c hr hc
  rw [Matrix.det_apply']
  apply sum_nonneg
  intro σ hσ
  by_cases hp : (∏ i : Fin n,A (r (σ i)) (c i))=0
  · simp only [Matrix.submatrix_apply,hp,mul_zero,le_refl]
  · have he : ∀ i,A (r (σ i)) (c i)≠0 := fun i=> (prod_ne_zero_iff.mp hp) i (mem_univ i)
    have hm : StrictMono σ := by
      intro i j hij
      by_contra hn
      have hji : σ j<σ i := lt_of_le_of_ne (le_of_not_gt hn) (by intro h;exact (ne_of_lt hij) (σ.injective h).symm)
      have hR := hr hji
      have hC := hc hij
      have hi := hz _ _ (he i)
      have hj := hz _ _ (he j)
      change (r (σ j)).val<(r (σ i)).val at hR
      change (c i).val<(c j).val at hC
      omega
    have hid : σ=1 := by apply Equiv.ext;intro i;exact congrFun hm.eq_id i
    subst σ
    simpa using (prod_nonneg (s:=univ) (fun i _=>ha (r i) (c i)))

lemma totallyNonnegative_one (d : ℕ) : TotallyNonnegative (1 : Matrix (Fin d) (Fin d) ℝ) := by
  apply lowerBidiagonal_totallyNonnegative
  · intro i j;simp only [Matrix.one_apply];split_ifs <;> norm_num
  · intro i j hij
    by_cases h:i=j
    · exact Or.inl (congrArg Fin.val h)
    · exfalso;exact hij (by simp [h])

lemma sorted_injective_fin {n d : ℕ} {f : Fin n → Fin d} (hf : Function.Injective f) :
    ∃ (g : Fin n → Fin d) (σ : Perm (Fin n)),StrictMono g ∧ f=g∘σ := by
  classical
  let s:=univ.image f
  have hs : s.card=n := by simp [s,card_image_of_injective _ hf]
  let o:=s.orderIsoOfFin hs
  let q : Fin n ≃ s := Equiv.ofBijective (fun i=>⟨f i,mem_image.mpr ⟨i,mem_univ _,rfl⟩⟩) (by
    constructor
    · intro i j h;exact hf (congrArg Subtype.val h)
    · intro a;obtain ⟨i,_,hi⟩:=mem_image.mp a.property;exact ⟨i,Subtype.ext hi⟩)
  refine ⟨fun i=>(o i).val,q.trans o.symm,o.strictMono,?_⟩
  funext i
  exact (congrArg Subtype.val (o.apply_symm_apply (q i))).symm

lemma TotallyNonnegative.mul {d : ℕ} {A B : Matrix (Fin d) (Fin d) ℝ}
    (hA : TotallyNonnegative A) (hB : TotallyNonnegative B) : TotallyNonnegative (A*B) := by
  classical
  intro n r c hr hc
  have he : (A*B).submatrix r c=A.submatrix r id * B.submatrix id c := by
    ext i j;simp [Matrix.mul_apply]
  rw [he]
  have hs : 0≤ ∑ f : Fin n → Fin d,
      ((A.submatrix r id).submatrix id f).det*((B.submatrix id c).submatrix f id).det := by
    apply sum_nonneg
    intro f hf
    change 0≤(A.submatrix r f).det*(B.submatrix f c).det
    by_cases hi : Function.Injective f
    · obtain ⟨g,σ,hg,rfl⟩:=sorted_injective_fin hi
      have hx : A.submatrix r (g∘σ)=(A.submatrix r g).submatrix id σ := rfl
      have hy : B.submatrix (g∘σ) c=(B.submatrix g c).submatrix σ id := rfl
      rw [hx,hy,Matrix.det_permute',Matrix.det_permute]
      have hp:=mul_nonneg (sq_nonneg (((Perm.sign σ:ℤ):ℝ))) (mul_nonneg (hA n r g hr hg) (hB n g c hg hc))
      nlinarith only [hp]
    · obtain ⟨i,j,hij,hne⟩:=Function.not_injective_iff.mp hi
      have hz : (A.submatrix r f).det=0 := by
        apply Matrix.det_zero_of_column_eq hne
        intro k
        simp only [Matrix.submatrix_apply,hij]
      rw [hz,zero_mul]
  rw [det_rectangular_binet] at hs
  exact (mul_nonneg_iff_of_pos_left (by positivity : (0:ℝ)<Fintype.card (Perm (Fin n)))).mp hs

lemma TotallyNonnegative.adjacent_row {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : TotallyNonnegative A) {i j : Fin d} (hij : i.val=j.val+1) {a : ℝ} (ha : 0≤a) :
    TotallyNonnegative (A.updateRow i (A i+a • A j)) := by
  classical
  let L : Matrix (Fin d) (Fin d) ℝ := (1 : Matrix (Fin d) (Fin d) ℝ).updateRow i
    ((1 : Matrix (Fin d) (Fin d) ℝ) i+a • (1 : Matrix (Fin d) (Fin d) ℝ) j)
  have hL : TotallyNonnegative L := by
    apply lowerBidiagonal_totallyNonnegative
    · intro u v
      simp only [L,Matrix.updateRow_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Matrix.one_apply]
      split_ifs <;> positivity
    · intro u v huv
      by_cases hui:u=i
      · subst u
        by_cases hvi:v=i
        · exact Or.inl (congrArg Fin.val hvi.symm)
        · by_cases hvj:v=j
          · exact Or.inr (by simpa [hvj] using hij)
          · exfalso;exact huv (by simp [L,Matrix.updateRow_apply,Ne.symm hvi,Ne.symm hvj])
      · have huv' : u=v := by
          by_contra h
          exact huv (by simp [L,Matrix.updateRow_apply,hui,h])
        exact Or.inl (congrArg Fin.val huv')
  have he : L*A=A.updateRow i (A i+a • A j) := by
    ext u v
    by_cases hu:u=i
    · subst u
      simp [Matrix.mul_apply,L,Matrix.updateRow_apply,add_mul,Finset.sum_add_distrib,Matrix.one_apply]
    · simp [Matrix.mul_apply,L,Matrix.updateRow_apply,hu,Matrix.one_apply]
  rw [←he]
  exact hL.mul hA

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section


namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv

lemma TotallyNonnegative.prefix_recursive {d : ℕ}
    {A B : Matrix (Fin (d+1)) (Fin (d+1)) ℝ} (hA : TotallyNonnegative A)
    {a : ℝ} (ha : 0≤a) (hzero : B 0=A 0)
    (hstep : ∀ k : Fin d,B k.succ=A k.succ+a • B k.castSucc) : TotallyNonnegative B := by
  classical
  let P (k : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ := fun i j=>if i.val≤k then B i j else A i j
  have hp0 : P 0=A := by
    ext i j
    by_cases hi:i=0
    · subst i;simp [P,hzero]
    · have hv : ¬i.val≤0 := by intro h;apply hi;apply Fin.ext;simpa using h
      simp [P,hv]
  have hp : ∀ k,k≤d → TotallyNonnegative (P k) := by
    intro k
    induction k with
    | zero => intro _;rw [hp0];exact hA
    | succ k ih =>
      intro hk
      let j : Fin (d+1):=⟨k,by omega⟩
      let i : Fin (d+1):=⟨k+1,by omega⟩
      have he : P (k+1)=(P k).updateRow i (P k i+a • P k j) := by
        ext u v
        by_cases hu:u=i
        · subst u
          have hs := congrFun (hstep ⟨k,by omega⟩) v
          simpa [P,Matrix.updateRow,i,j] using hs
        · have hc : (u.val≤k+1) ↔ u.val≤k := by
            have hn : u.val≠k+1 := by intro h;apply hu;exact Fin.ext h
            omega
          simp [P,Matrix.updateRow,hu,hc]
      rw [he]
      exact (ih (by omega)).adjacent_row (i:=i) (j:=j) (by rfl) ha
  have he : P d=B := by ext i j;simp [P,show i.val≤d by omega]
  rw [←he]
  exact hp d le_rfl

noncomputable def liftNewton {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  Fin.cases (fun j=>if j=0 then 1 else 0) (fun i=>Fin.cases 0 (A i))

@[simp] lemma liftNewton_zero_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) : liftNewton A 0 0=1 := rfl
@[simp] lemma liftNewton_zero_succ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) : liftNewton A 0 j.succ=0 := by simp [liftNewton]
@[simp] lemma liftNewton_succ_zero {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : liftNewton A i.succ 0=0 := rfl
@[simp] lemma liftNewton_succ_succ {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (i j : Fin d) : liftNewton A i.succ j.succ=A i j := rfl

lemma TotallyNonnegative.lift_newton {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : TotallyNonnegative A) : TotallyNonnegative (liftNewton A) := by
  classical
  intro n r c hr hc
  cases n with
  | zero => simp
  | succ n =>
    by_cases hr0:r 0=0
    · by_cases hc0:c 0=0
      · let r' : Fin n → Fin d:=fun i=>(r i.succ).pred (by
          have h:=hr (Fin.succ_pos i);rw [hr0] at h;exact ne_of_gt h)
        let c' : Fin n → Fin d:=fun i=>(c i.succ).pred (by
          have h:=hc (Fin.succ_pos i);rw [hc0] at h;exact ne_of_gt h)
        have hr' : StrictMono r' := by intro i j hij;simpa [r',Fin.pred_lt_pred_iff] using hr (Fin.succ_lt_succ_iff.mpr hij)
        have hc' : StrictMono c' := by intro i j hij;simpa [c',Fin.pred_lt_pred_iff] using hc (Fin.succ_lt_succ_iff.mpr hij)
        have he : (liftNewton A).submatrix r c=liftNewton (A.submatrix r' c') := by
          ext i j
          refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j
          · simp [Matrix.submatrix_apply,hr0,hc0]
          · rw [Matrix.submatrix_apply,hr0,←Fin.succ_pred (c j.succ) (by
              have h:=hc (Fin.succ_pos j);rw [hc0] at h;exact ne_of_gt h)]
            simp only [liftNewton_zero_succ]
          · rw [Matrix.submatrix_apply,hc0,←Fin.succ_pred (r i.succ) (by
              have h:=hr (Fin.succ_pos i);rw [hr0] at h;exact ne_of_gt h)]
            simp only [liftNewton_succ_zero]
          · change liftNewton A (r i.succ) (c j.succ)=A (r' i) (c' j)
            rw [←Fin.succ_pred (r i.succ) (by have h:=hr (Fin.succ_pos i);rw [hr0] at h;exact ne_of_gt h),
              ←Fin.succ_pred (c j.succ) (by have h:=hc (Fin.succ_pos j);rw [hc0] at h;exact ne_of_gt h)]
            rfl
        have hd (Q : Matrix (Fin n) (Fin n) ℝ) : (liftNewton Q).det=Q.det := by
          rw [Matrix.det_succ_row_zero,Fin.sum_univ_succ]
          simp only [liftNewton_zero_zero,Fin.succAbove_zero,
            liftNewton_zero_succ,mul_zero,zero_mul,sum_const_zero,add_zero]
          simp only [Fin.val_zero,pow_zero,one_mul,mul_one]
          rfl
        rw [he,hd]
        exact hA n r' c' hr' hc'
      · have hz : ((liftNewton A).submatrix r c).det=0 := by
          apply Matrix.det_eq_zero_of_row_eq_zero 0
          intro j
          have hj : c j≠0 := by
            intro h
            have hle:=hc.monotone (Fin.zero_le j)
            rw [h] at hle
            exact hc0 (le_antisymm hle (Fin.zero_le _))
          simp [Matrix.submatrix_apply,hr0,liftNewton,hj]
        rw [hz]
    · by_cases hc0:c 0=0
      · have hz : ((liftNewton A).submatrix r c).det=0 := by
          apply Matrix.det_eq_zero_of_column_eq_zero 0
          intro i
          have hi : r i≠0 := by
            intro h
            have hle:=hr.monotone (Fin.zero_le i)
            rw [h] at hle
            exact hr0 (le_antisymm hle (Fin.zero_le _))
          rw [Matrix.submatrix_apply,hc0,←Fin.succ_pred (r i) hi]
          simp only [liftNewton_succ_zero]
        rw [hz]
      · let r' : Fin (n+1) → Fin d:=fun i=>(r i).pred (by
          intro h;exact hr0 (le_antisymm (h ▸ hr.monotone (Fin.zero_le i)) (Fin.zero_le _)))
        let c' : Fin (n+1) → Fin d:=fun i=>(c i).pred (by
          intro h;exact hc0 (le_antisymm (h ▸ hc.monotone (Fin.zero_le i)) (Fin.zero_le _)))
        have hr' : StrictMono r' := by intro i j hij;simpa [r',Fin.pred_lt_pred_iff] using hr hij
        have hc' : StrictMono c' := by intro i j hij;simpa [c',Fin.pred_lt_pred_iff] using hc hij
        have he : (liftNewton A).submatrix r c=A.submatrix r' c' := by
          ext i j
          change liftNewton A (r i) (c j)=A (r' i) (c' j)
          have hrp : (r' i).succ=r i := Fin.succ_pred _ _
          have hcp : (c' j).succ=c j := Fin.succ_pred _ _
          rw [←hrp,←hcp]
          rfl
        rw [he]
        exact hA (n+1) r' c' hr' hc'

noncomputable def powerNewton (v : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0,k => if k=0 then 1 else 0
  | n+1,0 => v 0*powerNewton v n 0
  | n+1,k+1 => v 0*powerNewton v n (k+1)+powerNewton (fun i=>v (i+1)) n k

lemma powerNewton_zero (v : ℕ → ℝ) (n : ℕ) : powerNewton v n 0=(v 0)^n := by
  induction n with
  | zero => simp [powerNewton]
  | succ n ih => rw [powerNewton,ih,pow_succ'];
lemma powerNewton_eq_zero (v : ℕ → ℝ) {n k : ℕ} (h:n<k) : powerNewton v n k=0 := by
  induction n generalizing v k with
  | zero => simp [powerNewton,show k≠0 by omega]
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => rw [powerNewton,ih v (by omega),ih (fun i=>v (i+1)) (by omega),mul_zero,add_zero]

lemma powerNewton_totallyNonnegative (d : ℕ) (v : ℕ → ℝ) (hv : ∀ i,0≤v i) :
    TotallyNonnegative (fun i j : Fin d=>powerNewton v i.val j.val) := by
  induction d generalizing v with
  | zero =>
    intro n r c hr hc
    have hn:n=0 := by by_contra h;exact Fin.elim0 (r ⟨0,by omega⟩)
    subst n
    simp
  | succ d ih =>
    apply TotallyNonnegative.prefix_recursive
      ((ih (fun i=>v (i+1)) (fun i=>hv (i+1))).lift_newton) (hv 0)
    · funext j
      refine Fin.cases ?_ (fun j=>?_) j <;> simp [powerNewton,liftNewton]
    · intro k
      funext j
      refine Fin.cases ?_ (fun j=>?_) j
      · simp [powerNewton,liftNewton]
      · simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,liftNewton,Fin.cases_succ,Fin.val_succ,Fin.val_castSucc,powerNewton]
        ring

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix

lemma powerNewton_det_nonneg {n : ℕ} (v : ℕ → ℝ) (hv : ∀ i,0≤v i)
    (e c : Fin n → ℕ) (he : StrictMono e) (hc : StrictMono c) :
    0≤Matrix.det (fun i j=>powerNewton v (e i) (c j)) := by
  classical
  let D:=1+univ.sup e+univ.sup c
  let r : Fin n → Fin D:=fun i=>⟨e i,by
    have h: e i≤univ.sup e:=le_sup (mem_univ i)
    dsimp [D];omega⟩
  let s : Fin n → Fin D:=fun i=>⟨c i,by
    have h:c i≤univ.sup c:=le_sup (mem_univ i)
    dsimp [D];omega⟩
  exact powerNewton_totallyNonnegative D v hv n r s he hc

lemma newtonBasis_head (v : ℕ → ℝ) (k : ℕ) :
    newtonBasis v (k+1)=(X-Polynomial.C (v 0))*newtonBasis (fun i=>v (i+1)) k := by
  simp only [newtonBasis,Finset.prod_range_succ']
  ring

lemma powerNewton_expansion (v : ℕ → ℝ) (n : ℕ) :
    (X:Polynomial ℝ)^n=∑ k ∈ range (n+1),Polynomial.C (powerNewton v n k)*newtonBasis v k := by
  induction n generalizing v with
  | zero => simp [powerNewton,newtonBasis]
  | succ n ih =>
    have hs : (∑ k ∈ range (n+2),Polynomial.C (powerNewton v (n+1) k)*newtonBasis v k)=
        Polynomial.C (v 0)*(∑ k ∈ range (n+2),Polynomial.C (powerNewton v n k)*newtonBasis v k)+
        (X-Polynomial.C (v 0))*(∑ k ∈ range (n+1),Polynomial.C (powerNewton (fun i=>v (i+1)) n k)*newtonBasis (fun i=>v (i+1)) k) := by
      rw [sum_range_succ' _ (n+1),sum_range_succ' _ (n+1)]
      simp only [powerNewton,C_mul,show newtonBasis v 0=1 by simp [newtonBasis],mul_one]
      rw [mul_add,add_assoc,add_comm]
      rw [Finset.mul_sum,Finset.mul_sum,add_left_comm]
      congr 1
      rw [←Finset.sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [newtonBasis_head,C_add,C_mul]
      ring
    have hl : (∑ k ∈ range (n+2),Polynomial.C (powerNewton v n k)*newtonBasis v k)=
        ∑ k ∈ range (n+1),Polynomial.C (powerNewton v n k)*newtonBasis v k := by
      rw [sum_range_succ,powerNewton_eq_zero v (by omega),C_0,zero_mul,add_zero]
    rw [hs,hl,←ih v,←ih (fun i=>v (i+1))]
    ring

lemma powerNewton_expansion_truncated (v : ℕ → ℝ) (n D : ℕ) (h:n<D) :
    (X:Polynomial ℝ)^n =∑ k ∈ range D,Polynomial.C (powerNewton v n k)*newtonBasis v k := by
  rw [powerNewton_expansion v n]
  apply sum_subset (range_mono h)
  intro k hk hn
  have hnk:n<k := by simpa using hn
  rw [powerNewton_eq_zero v hnk,C_0,zero_mul]

lemma newtonBasis_eval_zero {v : ℕ → ℝ} {j k : ℕ} (h:j<k) :
    (newtonBasis v k).eval (v j)=0 := by
  rw [newtonBasis,Polynomial.eval_prod]
  apply prod_eq_zero (mem_range.mpr h)
  simp

/-- Evaluation factors through the first m Newton coefficients, even for a
sparse power whose degree is much larger than m. -/
lemma powerNewton_evaluation {m : ℕ} (v : ℕ → ℝ) (n : ℕ) (j : Fin m) :
    v j^n=∑ k : Fin m,powerNewton v n k*(newtonBasis v k).eval (v j) := by
  let D:=n+m+1
  have hp:=congrArg (fun P : Polynomial ℝ=>P.eval (v j)) (powerNewton_expansion_truncated v n D (by dsimp [D];omega))
  simp only [Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C] at hp
  rw [show (∑ k : Fin m,powerNewton v n k*(newtonBasis v k).eval (v j)) =
    ∑ k ∈ range m,powerNewton v n k*(newtonBasis v k).eval (v j) from
      Fin.sum_univ_eq_sum_range (fun k : ℕ=>powerNewton v n k*(newtonBasis v k).eval (v j)) m]
  rw [hp]
  symm
  apply sum_subset (range_mono (by dsimp [D];omega))
  intro k hk hn
  have hmk:m≤k := by simpa using hn
  rw [newtonBasis_eval_zero (lt_of_lt_of_le j.isLt hmk),mul_zero]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Filter Topology

lemma powerNewton_bound (k n : ℕ) {b : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R) : |powerNewton b k n| ≤ (2*R)^k := by
  induction k generalizing b n with
  | zero => simp only [powerNewton,pow_zero];split_ifs <;> norm_num
  | succ k ih =>
    cases n with
    | zero =>
      rw [powerNewton,abs_mul,pow_succ']
      exact (mul_le_mul (hb 0) (ih _ hb) (abs_nonneg _) (by linarith)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
    | succ n =>
      rw [powerNewton,pow_succ']
      calc
        |b 0*powerNewton b k (n+1)+powerNewton (fun i=>b (i+1)) k n| ≤
            |b 0| *|powerNewton b k (n+1)|+|powerNewton (fun i=>b (i+1)) k n| := by
          simpa only [abs_mul] using abs_add_le (b 0*powerNewton b k (n+1)) _
        _ ≤ R*(2*R)^k+(2*R)^k := add_le_add
          (mul_le_mul (hb 0) (ih _ hb) (abs_nonneg _) (by linarith))
          (ih _ (fun i => hb (i+1)))
        _ ≤ 2*R*(2*R)^k := by nlinarith [pow_nonneg (show 0 ≤ 2*R by linarith) k]

lemma continuous_powerNewton (k n : ℕ) : Continuous (fun b : ℕ → ℝ => powerNewton b k n) := by
  induction k generalizing n with
  | zero => simp only [powerNewton];split_ifs <;> exact continuous_const
  | succ k ih =>
    cases n with
    | zero => exact (continuous_apply 0).mul (ih 0)
    | succ n =>
      exact ((continuous_apply 0).mul (ih (n+1))).add
        ((ih n).comp (continuous_pi (fun i => continuous_apply (i+1))))

lemma powerNewton_jet_evaluation {m : ℕ} (b : ℕ → ℝ) (k : ℕ) (j : Fin m) :
    polynomialJet (X^k) (b j) (nodalOrder b j)=
      ∑ r : Fin m,powerNewton b k r*polynomialJet (newtonBasis b r) (b j) (nodalOrder b j) := by
  let D:=k+m+1
  have hp:=congrArg (fun P : Polynomial ℝ => polynomialJet P (b j) (nodalOrder b j))
    (powerNewton_expansion_truncated b k D (by dsimp [D];omega))
  have hsum : polynomialJet (∑ r∈range D,Polynomial.C (powerNewton b k r)*newtonBasis b r) (b j) (nodalOrder b j)=
      ∑ r∈range D,powerNewton b k r*polynomialJet (newtonBasis b r) (b j) (nodalOrder b j) := by
    simp [polynomialJet,map_sum,taylor_mul,Polynomial.coeff_C_mul]
  rw [hsum] at hp
  rw [Fin.sum_univ_eq_sum_range (fun r => powerNewton b k r*polynomialJet (newtonBasis b r) (b j) (nodalOrder b j)) m,hp]
  symm
  apply sum_subset (range_mono (by dsimp [D];omega))
  intro r hr hnr
  have hmr : m ≤ r := by simpa using hnr
  rw [polynomialJet_newtonBasis_gt (lt_of_lt_of_le j.isLt hmr),mul_zero]

noncomputable def newtonKernelTerm (b : ℕ → ℝ) (x : ℝ) (e r k : ℕ) : ℝ :=
  powerNewton b k r*polynomialJet (X^k) x e/(2*k).factorial
noncomputable def newtonKernel (b : ℕ → ℝ) (x : ℝ) (e r : ℕ) : ℝ :=
  ∑' k,newtonKernelTerm b x e r k

lemma newtonKernelTerm_bound {b : ℕ → ℝ} {x R S : ℝ} (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hb : ∀ i,|b i| ≤ R) (hx : |x| ≤ S) (e r k : ℕ) :
    ‖newtonKernelTerm b x e r k‖ ≤ (4*R*S)^k/(2*k).factorial := by
  rw [newtonKernelTerm,Real.norm_eq_abs,abs_div,abs_mul,abs_of_nonneg (show (0:ℝ) ≤ ((2*k).factorial:ℝ) from Nat.cast_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    |powerNewton b k r| *|polynomialJet (X^k) x e| ≤ (2*R)^k*(2*S)^k :=
      mul_le_mul (powerNewton_bound k r hR hb) (polynomialJet_X_pow_bound k e hS hx)
        (abs_nonneg _) (by positivity)
    _=(4*R*S)^k := by rw [←mul_pow];ring_nf

lemma newtonKernelTerm_summable {b : ℕ → ℝ} {R : ℝ} (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R)
    (x : ℝ) (e r : ℕ) : Summable (newtonKernelTerm b x e r) := by
  apply (summable_evenFactorial (show 0 ≤ 4*R*(|x|+1) by positivity)).of_norm_bounded
  intro k
  exact newtonKernelTerm_bound hR (by linarith [abs_nonneg x]) hb (by linarith) e r k

lemma cosineKernelJet_newton {m : ℕ} {b : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R) (x : ℝ) (e : ℕ) (j : Fin m) :
    cosineKernelJet (nodalOrder b j) e (b j) x=
      ∑ r : Fin m,newtonKernel b x e r*newtonJetMatrix m b r j := by
  simp only [newtonKernel,←tsum_mul_right]
  rw [←Summable.tsum_finsetSum]
  · apply tsum_congr
    intro k
    simp only [kernelJetTerm,newtonKernelTerm,newtonJetMatrix]
    rw [powerNewton_jet_evaluation b k j]
    rw [Finset.sum_mul,Finset.sum_div]
    apply sum_congr rfl
    intro r hr
    ring
  · intro r hr
    exact (newtonKernelTerm_summable hR hb x e r).mul_right _

lemma continuousOn_newtonKernel {α : Type*} [TopologicalSpace α]
    {s : Set α} {b : α → ℕ → ℝ} {R : ℝ} (hR : 1 ≤ R)
    (hb : ContinuousOn b s) (hbound : ∀ z ∈ s,∀ i,|b z i| ≤ R)
    (x : ℝ) (e r : ℕ) : ContinuousOn (fun z => newtonKernel (b z) x e r) s := by
  apply continuousOn_tsum
  · intro k
    exact (((continuous_powerNewton k r).comp_continuousOn hb).mul continuousOn_const).div_const _
  · exact summable_evenFactorial (show 0 ≤ 4*R*(|x|+1) by positivity)
  · intro k z hz
    exact newtonKernelTerm_bound hR (by linarith [abs_nonneg x]) (hbound z hz) (by linarith) e r k

lemma cosineKernelJet_det_newton {m : ℕ} {b : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R) (x : ℝ) (e : Fin m → ℕ) :
    Matrix.det (fun i j : Fin m => cosineKernelJet (nodalOrder b j) (e i) (b j) x)=
      Matrix.det (fun i j : Fin m => newtonKernel b x (e i) j)*(newtonJetMatrix m b).det := by
  have hm : (Matrix.of (fun i j : Fin m => cosineKernelJet (nodalOrder b j) (e i) (b j) x))=
      (Matrix.of (fun i j : Fin m => newtonKernel b x (e i) j))*newtonJetMatrix m b := by
    ext i j
    exact cosineKernelJet_newton hR hb x (e i) j
  exact (congrArg Matrix.det hm).trans (Matrix.det_mul _ _)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset

lemma powerNewton_nonneg {b : ℕ → ℝ} (hb : ∀ i,0 ≤ b i) (k r : ℕ) : 0 ≤ powerNewton b k r := by
  induction k generalizing b r with
  | zero => simp only [powerNewton]; split_ifs <;> norm_num
  | succ k ih =>
    cases r with
    | zero => exact mul_nonneg (hb 0) (ih hb 0)
    | succ r => exact add_nonneg (mul_nonneg (hb 0) (ih hb _)) (ih (fun i ↦ hb (i+1)) r)

lemma powerNewton_mono {b c : ℕ → ℝ} (hb : ∀ i,0 ≤ b i) (hbc : ∀ i,b i ≤ c i)
    (k r : ℕ) : powerNewton b k r ≤ powerNewton c k r := by
  induction k generalizing b c r with
  | zero => rfl
  | succ k ih =>
    cases r with
    | zero => exact mul_le_mul (hbc 0) (ih hb hbc 0) (powerNewton_nonneg hb _ _) ((hb 0).trans (hbc 0))
    | succ r =>
      exact add_le_add
        (mul_le_mul (hbc 0) (ih hb hbc _) (powerNewton_nonneg hb _ _) ((hb 0).trans (hbc 0)))
        (ih (fun i ↦ hb (i+1)) (fun i ↦ hbc (i+1)) r)

lemma nodalOrder_const (a : ℝ) (k : ℕ) : nodalOrder (fun _ ↦ a) k=k := by
  simp [nodalOrder]

lemma polynomialJet_newtonBasis_const (a : ℝ) (r k : ℕ) :
    polynomialJet (newtonBasis (fun _ ↦ a) r) a k = if r=k then 1 else 0 := by
  have he : newtonBasis (fun _ ↦ a) r=(X-Polynomial.C a)^r := by simp [newtonBasis]
  rw [he,polynomialJet]
  simp [taylor_pow,map_sub,taylor_X,taylor_C,eq_comm]

lemma powerNewton_const (a : ℝ) (k r : ℕ) :
    powerNewton (fun _ ↦ a) k r=polynomialJet (X^k) a r := by
  have h:=powerNewton_jet_evaluation (m:=r+1) (fun _ ↦ a) k (Fin.last r)
  simp only [nodalOrder_const,Fin.val_last,polynomialJet_newtonBasis_const] at h
  have he (i : Fin (r+1)) : (i:ℕ)=r ↔ i=Fin.last r := ⟨fun h ↦ Fin.ext h,fun h ↦ congrArg Fin.val h⟩
  simpa only [mul_ite,mul_one,mul_zero,he,sum_ite_eq',mem_univ,ite_true,Fin.val_last] using h.symm

lemma newtonKernel_const (a x : ℝ) (r : ℕ) :
    newtonKernel (fun _ ↦ a) x 0 r=cosineKernelJet r 0 a x := by
  unfold newtonKernel cosineKernelJet
  apply tsum_congr
  intro k
  simp only [newtonKernelTerm,kernelJetTerm,powerNewton_const]

lemma newtonKernel_nonneg {b : ℕ → ℝ} (hb : ∀ i,0 ≤ b i) {x : ℝ} (hx : 0 ≤ x) (r : ℕ) :
    0 ≤ newtonKernel b x 0 r := by
  apply tsum_nonneg
  intro k
  unfold newtonKernelTerm
  apply div_nonneg (mul_nonneg (powerNewton_nonneg hb _ _) _) (Nat.cast_nonneg _)
  simp only [polynomialJet_X_pow,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  positivity

lemma newtonKernel_le_jet {b : ℕ → ℝ} {a x : ℝ} (hb : ∀ i,0 ≤ b i) (hba : ∀ i,b i ≤ a)
    (hx : 0 ≤ x) (r : ℕ) : newtonKernel b x 0 r ≤ cosineKernelJet r 0 a x := by
  have ha : 0 ≤ a := (hb 0).trans (hba 0)
  have hs:=newtonKernelTerm_summable (b:=b) (R:=a+1) (by linarith)
      (fun i ↦ by rw [abs_of_nonneg (hb i)]; linarith [hba i]) x 0 r
  have ht:=newtonKernelTerm_summable (b:=fun _ ↦ a) (R:=a+1) (by linarith)
      (fun _ ↦ by rw [abs_of_nonneg ha]; linarith) x 0 r
  rw [←newtonKernel_const]
  apply hs.tsum_le_tsum _ ht
  intro k
  unfold newtonKernelTerm
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply mul_le_mul_of_nonneg_right (powerNewton_mono hb hba k r)
  simp only [polynomialJet_X_pow,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero]
  exact pow_nonneg hx k

lemma newtonKernel_exp_bound {b : ℕ → ℝ} {a δ : ℝ} (hb : ∀ i,0 ≤ b i)
    (hba : ∀ i,b i ≤ a) (hd : 0<δ) (r : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    |newtonKernel b (p^2) 0 r| ≤ δ^(-(r:ℤ))*Real.exp (Real.sqrt (a+δ)*p) := by
  rw [abs_of_nonneg (newtonKernel_nonneg hb (sq_nonneg p) r)]
  exact (newtonKernel_le_jet hb hba (sq_nonneg p) r).trans
    ((le_abs_self _).trans (cosineKernelJet_exp_bound ((hb 0).trans (hba 0)) hd r hp))

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset Matrix Filter Topology

lemma newtonJetMatrix_det_ne_zero (n : ℕ) (b : ℕ → ℝ) : (newtonJetMatrix n b).det≠0 := by
  rw [newtonJetMatrix_det]
  apply prod_ne_zero_iff.mpr
  intro k _
  apply prod_ne_zero_iff.mpr
  intro j hj
  exact sub_ne_zero.mpr (mem_filter.mp hj).2.symm

lemma newtonKernel_as_combination {n : ℕ} {b : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R) (x : ℝ) (r : Fin n) :
    newtonKernel b x 0 r = ∑ j : Fin n,cosineKernelJet (nodalOrder b j) 0 (b j) x *
      (newtonJetMatrix n b)⁻¹ j r := by
  have h : (fun j : Fin n ↦ cosineKernelJet (nodalOrder b j) 0 (b j) x)=
      (fun r : Fin n ↦ newtonKernel b x 0 r) ᵥ* newtonJetMatrix n b := by
    funext j
    exact cosineKernelJet_newton hR hb x 0 j
  have he:=congrArg (fun v : Fin n → ℝ ↦ (v ᵥ* (newtonJetMatrix n b)⁻¹) r) h
  rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (newtonJetMatrix_det_ne_zero n b)),Matrix.vecMul_one] at he
  exact he.symm

lemma continuous_newtonKernel {b : ℕ → ℝ} {R : ℝ} (hR : 1 ≤ R) (hb : ∀ i,|b i| ≤ R) (r : ℕ) :
    Continuous (fun x ↦ newtonKernel b x 0 r) := by
  have he : (fun x ↦ newtonKernel b x 0 r)=
      fun x ↦ ∑ j : Fin (r+1),cosineKernelJet (nodalOrder b j) 0 (b j) x *
        (newtonJetMatrix (r+1) b)⁻¹ j (Fin.last r) := by
    funext x
    exact newtonKernel_as_combination hR hb x (Fin.last r)
  rw [he]
  exact continuous_finsetSum _ (fun i _ ↦ ((cosineKernelJet_contDiff_right _ _ _ 0).continuous).mul continuous_const)

lemma tendsto_newtonKernel_of_bounded {b : ℕ → ℕ → ℝ} {a : ℕ → ℝ} {R : ℝ}
    (hR : 1 ≤ R) (hb : ∀ k i,|b k i|≤R) (ha : ∀ i,|a i|≤R)
    (ht : Tendsto b atTop (𝓝 a)) (x : ℝ) (r : ℕ) :
    Tendsto (fun k ↦ newtonKernel (b k) x 0 r) atTop (𝓝 (newtonKernel a x 0 r)) := by
  let S : Set (ℕ → ℝ):={v | ∀ i,|v i|≤R}
  have hc : ContinuousOn (fun v ↦ newtonKernel v x 0 r) S :=
    continuousOn_newtonKernel hR continuousOn_id (fun v hv ↦ hv) x 0 r
  exact (hc a ha).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨ht,Filter.Eventually.of_forall hb⟩)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
