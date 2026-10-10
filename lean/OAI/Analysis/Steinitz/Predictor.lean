import OAI.Analysis.Steinitz.FilterMoments

namespace OAI

/-! Predictor-column energy and exact feedback cancellation. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def rawRow (R : Matrix ι κ ℝ) (b : ι → ℝ) : κ → ℝ :=
  fun j => eta b*(b ⬝ᵥ (fun i => R i j))
noncomputable def predictorRows (R : Matrix ι κ ℝ) : List (Step ι κ) → List (κ → ℝ)
  | [] => []
  | p::ps => rawRow R p.b :: predictorRows (p.apply R) ps

omit [Fintype κ] [DecidableEq ι] in
lemma predictorRows_length (R : Matrix ι κ ℝ) (L : List (Step ι κ)) :
    (predictorRows R L).length=L.length := by
  induction L generalizing R with
  | nil => rfl
  | cons p ps ih => simp only [predictorRows,List.length_cons,ih]

omit [Fintype κ] [DecidableEq ι] in
lemma predictorRows_get (R : Matrix ι κ ℝ) (L : List (Step ι κ)) (k : ℕ) (hk : k<L.length) :
    (predictorRows R L)[k]'(by rw [predictorRows_length]; exact hk) =
      rawRow (run R (L.take k)) (L[k].b) := by
  induction L generalizing R k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simpa only [predictorRows,List.getElem_cons_succ,List.take_succ_cons,run] using
        ih (p.apply R) k (by simpa using hk)

omit [DecidableEq κ] in
lemma vectorMass_vecMul {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (b : ι → ℝ) :
    vectorMass (b ᵥ* R)=vectorMass b := by
  have hh := congrArg (fun A : Matrix ι ι ℝ => b ⬝ᵥ(A*ᵥb)) hR
  rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.mulVec_transpose,Matrix.one_mulVec] at hh
  simpa only [vectorMass,dotProduct,← pow_two] using hh

omit [DecidableEq κ] in
lemma rawRow_mass {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (b : ι → ℝ) :
    vectorMass (rawRow R b) ≤ vectorMass b := by
  have he : vectorMass (rawRow R b)=eta b^2*vectorMass (b ᵥ* R) := by
    unfold vectorMass rawRow
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_pow]
    rfl
  rw [he,vectorMass_vecMul hR]
  have hh : eta b^2≤1 := by nlinarith [eta_pos b,eta_le_one b]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hh (vectorMass_nonneg b)

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma rawRow_zero_col (R : Matrix ι κ ℝ) (b : ι → ℝ) {j : κ} (h : ∀ i,R i j=0) :
    rawRow R b j=0 := by simp [rawRow,h,dotProduct]

omit [Fintype κ] in
lemma rawRow_loss {p : Step ι κ} (hs : p.C=symmetricContraction p.b) (hb : vectorMass p.b≤1)
    (R : Matrix ι κ ℝ) (hR : ∀ i,R i p.j=0) (j : κ) :
    rawRow R p.b j^2+vectorMass (fun i => p.apply R i j) ≤
      vectorMass (fun i => R i j)+(if p.j=j then vectorMass p.b else 0) := by
  have heta : eta p.b^2≤1 := by nlinarith [eta_pos p.b,eta_le_one p.b]
  by_cases hj : p.j=j
  · subst j
    have he : (fun i => p.apply R i p.j)=p.b := by
      ext i
      simp [Step.apply,Matrix.mul_apply,insert,hR]
    rw [he,rawRow_zero_col R p.b hR]
    simp [vectorMass,hR]
  · have he : (fun i => p.apply R i j)=symmetricContraction p.b*ᵥ(fun i => R i j) := by
      ext i
      simp [Step.apply,Matrix.mul_apply,insert,Ne.symm hj,hs,Matrix.mulVec,dotProduct]
    rw [he,ite_eq_right hj]
    have hh := contraction_loss hb (fun i => R i j)
    have hm := mul_le_mul_of_nonneg_right heta (sq_nonneg (p.b ⬝ᵥ fun i => R i j))
    simp only [rawRow,mul_pow]
    nlinarith

omit [Fintype κ] in
lemma predictor_column_budget {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hs : ∀ p∈L,p.C=symmetricContraction p.b) (hb : ∀ p∈L,vectorMass p.b≤1)
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) (j : κ) :
    ((predictorRows R L).map (fun m => m j^2)).sum + vectorMass (fun i => run R L i j) ≤
      vectorMass (fun i => R i j)+(L.map (fun p => if p.j=j then vectorMass p.b else 0)).sum := by
  induction L generalizing R with
  | nil => simp [predictorRows,run]
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r∈ps,p.j≠r.j := by
      intro r hr he
      exact hd'.1 (List.mem_map.mpr ⟨r,hr,he.symm⟩)
    have hh := ih (fun r hr => hs r (List.mem_cons_of_mem p hr))
      (fun r hr => hb r (List.mem_cons_of_mem p hr)) (Step.fresh_tail hf htail) hd'.2
    have hstep := rawRow_loss (hs p (List.mem_cons_self ..)) (hb p (List.mem_cons_self ..)) R (hf p (List.mem_cons_self ..)) j
    simp only [predictorRows,List.map_cons,List.sum_cons,run]
    linarith

omit [Fintype κ] [DecidableEq ι] in
lemma insertion_budget {L : List (Step ι κ)} (hd : (L.map Step.j).Nodup) {B : ℝ} (hB : 0≤B)
    (hb : ∀ p∈L,vectorMass p.b≤B) (j : κ) :
    (L.map (fun p => if p.j=j then vectorMass p.b else 0)).sum ≤ B := by
  induction L with
  | nil => simpa using hB
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    by_cases hj : p.j=j
    · have ht : ∀ r∈ps,r.j≠j := by
        intro r hr he
        exact hd'.1 (List.mem_map.mpr ⟨r,hr,he.trans hj.symm⟩)
      have hz : (ps.map (fun p => if p.j=j then vectorMass p.b else 0)).sum=0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hx
        simp [ht r hr]
      simpa only [List.map_cons,List.sum_cons,ite_eq_left hj,hz,add_zero] using hb p (List.mem_cons_self ..)
    · simpa only [List.map_cons,List.sum_cons,ite_eq_right hj,zero_add] using
        ih hd'.2 (fun r hr => hb r (List.mem_cons_of_mem p hr))

omit [Fintype κ] in
lemma predictor_column_bound {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hs : ∀ p∈L,p.C=symmetricContraction p.b) (hb : ∀ p∈L,vectorMass p.b≤1)
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) {B : ℝ} (hB : 0≤B)
    (hbB : ∀ p∈L,vectorMass p.b≤B) (j : κ) (hR : ∀ i,R i j=0) :
    ((predictorRows R L).map (fun m => m j^2)).sum ≤ B := by
  have hh := predictor_column_budget hs hb hf hd j
  have ht := insertion_budget hd hB hbB j
  have hz : vectorMass (fun i => R i j)=0 := by simp [vectorMass,hR]
  rw [hz,zero_add] at hh
  linarith [vectorMass_nonneg (fun i => run R L i j)]

lemma predictor_row_bound {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) {L : List (Step ι κ)}
    (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (k : ℕ) (hk : k<L.length) :
    vectorMass ((predictorRows R L)[k]'(by rw [predictorRows_length]; exact hk)) ≤ vectorMass (L[k].b) := by
  rw [predictorRows_get R L k hk]
  apply rawRow_mass
  exact run_coisometry hR (good_prefix hp (List.take_prefix k L)) (fresh_prefix hf (List.take_prefix k L))
    (nodup_prefix hd (List.take_prefix k L))

omit [Fintype κ] [DecidableEq ι] in
lemma predictor_future_zero {R : Matrix ι κ ℝ} {L : List (Step ι κ)}
    (hf : Fresh R L) (hd : (L.map Step.j).Nodup) (k l : ℕ) (hkl : k≤l) (hl : l<L.length) :
    ((predictorRows R L)[k]'(by rw [predictorRows_length]; omega)) (L[l].j)=0 := by
  rw [predictorRows_get R L k (hkl.trans_lt hl)]
  apply rawRow_zero_col
  have ht : Fresh (run R (L.take k)) (L.drop k) := run_fresh_append
    (by simpa only [List.take_append_drop] using hf) (by simpa only [List.take_append_drop] using hd)
  apply ht
  have he : (L.drop k)[l-k]'(by simp only [List.length_drop]; omega)=L[l] := by
    simp only [List.getElem_drop,Nat.add_sub_of_le hkl]
  rw [← he]
  exact List.getElem_mem _

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

noncomputable def rowMap (m : κ → ℝ) : EuclideanSpace ℝ κ →L[ℝ] ℝ := innerSL ℝ (WithLp.toLp 2 m)
omit [DecidableEq κ] in
lemma rowMap_apply (m : κ → ℝ) (x : EuclideanSpace ℝ κ) : rowMap m x=m ⬝ᵥ x := by
  change inner ℝ (WithLp.toLp 2 m) x=m ⬝ᵥ x
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  exact dotProduct_comm _ _
lemma rowMap_single (m : κ → ℝ) (j : κ) : rowMap m (EuclideanSpace.single j 1)=m j := by
  rw [rowMap_apply]
  simp [dotProduct,PiLp.single_apply]
lemma rowMatrix_norm (m : κ → ℝ) (x : EuclideanSpace ℝ κ) :
    ‖matrixMap (fun _ : Unit => m) x‖=|rowMap m x| := by
  have he : matrixMap (fun _ : Unit => m) x=EuclideanSpace.single () (rowMap m x) := by
    ext u
    cases u
    simp only [PiLp.single_apply,ite_true,rowMap_apply]
    rfl
  rw [he,PiLp.norm_single,Real.norm_eq_abs]

omit [DecidableEq ι] [DecidableEq κ] in
lemma rawRow_eval (R : Matrix ι κ ℝ) (b : ι → ℝ) (x : EuclideanSpace ℝ κ) :
    rowMap (rawRow R b) x=eta b*(b ⬝ᵥ (R*ᵥx)) := by
  rw [rowMap_apply,Matrix.dotProduct_mulVec]
  simp only [dotProduct,rawRow,Matrix.vecMul,← Finset.mul_sum,mul_assoc]

noncomputable def noiseRow {ν : Type*} (m : ι⊕ν → ℝ) : ι⊕ν → ℝ :=
  Sum.elim (fun _ => 0) (fun j => m (Sum.inr j))

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma noiseRow_mass {ν : Type*} [Fintype ν] (m : ι⊕ν → ℝ) :
    vectorMass (noiseRow m)≤vectorMass m := by
  simp only [vectorMass,Fintype.sum_sum_type,noiseRow,Sum.elim_inl,Sum.elim_inr,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero,zero_add]
  linarith [Finset.sum_nonneg (fun i (_ : i∈(Finset.univ : Finset ι)) => sq_nonneg (m (Sum.inl i)))]

omit [Fintype κ] [DecidableEq κ] [DecidableEq ι] in
lemma noiseRow_eval {ν : Type*} [Fintype ν] [DecidableEq ν] (m : ι⊕ν → ℝ)
    (x : EuclideanSpace ℝ (ι⊕ν)) (hx : ∀ i,x (Sum.inl i)=0) : rowMap (noiseRow m) x=rowMap m x := by
  simp [rowMap_apply,dotProduct,Fintype.sum_sum_type,noiseRow,hx]

omit [DecidableEq ι] [Fintype ι] in
lemma insert_mulVec_eq (b : ι → ℝ) (j : κ) (x : κ → ℝ) : insert b j*ᵥx=(x j) • b := by
  ext i
  simp [insert,Matrix.mulVec,dotProduct,mul_comm]

lemma step_cancel {p : Step ι κ} (hs : p.C=symmetricContraction p.b) (R : Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) (ε : ℝ) (hx : x p.j=rowMap (rawRow R p.b) x+ε) :
    matrixMap (p.apply R) x=matrixMap R x+ε • WithLp.toLp 2 p.b := by
  apply WithLp.ofLp_injective
  change (p.C*R+insert p.b p.j)*ᵥ x=R*ᵥ x+ε • p.b
  rw [Matrix.add_mulVec,← Matrix.mulVec_mulVec,hs,contraction_apply,insert_mulVec_eq,hx,rawRow_eval]
  ext i
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

lemma run_prefix_cancel {n : ℕ} (p : Fin n → Step ι κ) (R : Matrix ι κ ℝ)
    (x : EuclideanSpace ℝ κ) (ε : Fin n → ℝ)
    (hs : ∀ i,(p i).C=symmetricContraction (p i).b)
    (hx : ∀ i,x (p i).j=rowMap (rawRow (run R ((List.ofFn p).take i.val)) (p i).b) x+ε i)
    (k : ℕ) :
    matrixMap (run R ((List.ofFn p).take k)) x = matrixMap R x+
      ((List.ofFn (fun i => ε i • WithLp.toLp 2 (p i).b)).take k).sum := by
  induction n generalizing R k with
  | zero => simp [List.ofFn_zero,run]
  | succ n ih =>
    cases k with
    | zero => simp [run]
    | succ k =>
      have ht : ∀ i : Fin n,x (p i.succ).j=
          rowMap (rawRow (run ((p 0).apply R) ((List.ofFn (fun i : Fin n => p i.succ)).take i.val)) (p i.succ).b) x+ε i.succ := by
        intro i
        simpa only [List.ofFn_succ,Fin.val_succ,List.take_succ_cons,run] using hx i.succ
      have hrec := ih (fun i => p i.succ) ((p 0).apply R) (fun i => ε i.succ) (fun i => hs i.succ) ht k
      simp only [List.ofFn_succ,List.take_succ_cons,run,List.sum_cons]
      rw [hrec,step_cancel (hs 0) R x (ε 0) (by simpa only [Fin.val_zero,List.take_zero,run] using hx 0)]
      abel

end EuclideanSteinitz.Filter

end

end OAI
