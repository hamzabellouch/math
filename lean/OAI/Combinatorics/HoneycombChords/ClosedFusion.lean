import OAI.Combinatorics.HoneycombChords.StripProjection

namespace OAI

/-! Closed spectral fusion and its physical specialization.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet ClosedFourRow RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma Q_at_L : Q L=(Real.cos L : ℂ) := by
  unfold Q
  rw [show Real.pi/4+L=3*L by unfold L;ring,
    show b+L=4*L by unfold b L;ring]
  change ((Real.sin (3*CriticalHoneycombTransfer.L):ℂ)*
    (Real.sin (4*CriticalHoneycombTransfer.L):ℂ))=_
  rw [CriticalHoneycombTransfer.sin_three_L,CriticalHoneycombTransfer.sin_four_L]
  simp only [Complex.ofReal_one,mul_one]
  rfl
lemma Q_at_L_ne_zero : Q L≠0 := by
  rw [Q_at_L,Complex.ofReal_ne_zero]
  exact ne_of_gt CriticalHoneycombTransfer.cos_L_pos
lemma physicalR_binding : spectralR L=fun p q=>
    Planar.sourceR (kappa:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) (kappa^2:ℂ) 0 p q := by
  rw [spectralR_normalized L Q_at_L_ne_zero]
  have hw : Transfer.a L=kappa ∧ Transfer.h L=kappa^2 ∧ Transfer.v L=kappa^2 ∧
      Transfer.c L=kappa^2 ∧ Transfer.d L=0 := CriticalHoneycombTransfer.physical_weights
  have hp : Transfer.phase=Planar.phase := rfl
  funext p q
  rcases p with ⟨a,b⟩;rcases q with ⟨c,d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [normalizedR,Planar.sourceR,hw.1,hw.2.1,hw.2.2.1,hw.2.2.2.1,hw.2.2.2.2,hp]
noncomputable def reverseSites (n : ℕ) : Space n≃Space n where
  toFun x i:=x i.rev
  invFun x i:=x i.rev
  left_inv x:=by funext i;simp
  right_inv x:=by funext i;simp
lemma reverseSites_apply (n : ℕ) (x : Space n) (i : Fin n) :
    reverseSites n x i=x i.rev := rfl
lemma row_eq_product (n : ℕ) (A : Fin n→Local) (s t : Space n) :
    row n A s t=(List.ofFn (fun i=>block (A i) (s i) (t i))).prod := by
  induction n with
  | zero => simp [row]
  | succ n ih => rw [row,List.ofFn_succ,List.prod_cons,ih];rfl
lemma row_eq_matrixPath (n : ℕ) (A : Fin n→Local) (s t : Space n) (a b : Spin) :
    row n A s t a b=matrixPath (fun i=>block (A i) (s i) (t i)) a b := by
  rw [matrixPath_eq_prod,row_eq_product]
lemma cons_reverseSites (n : ℕ) (a : Spin) (v : Space n) (i : Fin (n+1)) :
    Fin.cons (α:=fun _=>Spin) a (reverseSites n v) i=Fin.snoc (α:=fun _=>Spin) v a i.rev := by
  exact (Fin.snoc_rev a v i).symm
lemma physical_row_kernel (n : ℕ) (w e : Space n) (a b : Spin) :
    row n (fun _=>spectralR L) (reverseSites n w) (reverseSites n e) a b=
      columnKernel n b a w e := by
  rw [row_eq_matrixPath]
  unfold matrixPath
  rw [←(reverseSites n).sum_comp]
  unfold columnKernel
  apply Finset.sum_congr rfl
  intro v hv
  simp only [cons_reverseSites,Fin.rev_last,reverseSites_apply]
  split_ifs with h
  · unfold columnProduct
    rw [←Equiv.prod_comp (Fin.revPerm (n:=n))]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Fin.revPerm_apply,Fin.rev_rev,Fin.rev_castSucc,block,physicalR_binding]
  · rfl
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.BoundaryJet
noncomputable def reflected (a : Jet) : Jet :=
  form (star (base a)) (star (right a)) (star (left a)) (star (both a))
@[simp] lemma reflected_base (a : Jet) : base (reflected a)=star (base a) := base_form _ _ _ _
@[simp] lemma reflected_left (a : Jet) : left (reflected a)=star (right a) := left_form _ _ _ _
@[simp] lemma reflected_right (a : Jet) : right (reflected a)=star (left a) := right_form _ _ _ _
@[simp] lemma reflected_both (a : Jet) : both (reflected a)=star (both a) := both_form _ _ _ _
lemma reflected_involutive : Function.Involutive reflected := by
  intro a
  apply jet_ext <;> simp
noncomputable def reflectJet : Jet ≃+* Jet where
  toFun:=reflected
  invFun:=reflected
  left_inv:=reflected_involutive
  right_inv:=reflected_involutive
  map_add' a b:=by apply jet_ext <;> simp
  map_mul' a b:=by apply jet_ext <;> simp ; ring
lemma reflectJet_apply (a : Jet) : reflectJet a=reflected a := rfl
@[simp] lemma reflectJet_C (z : ℂ) : reflectJet (C z)=C (star z) := by
  rw [reflectJet_apply]
  apply jet_ext <;> simp only [reflected_base,reflected_left,
    reflected_right,reflected_both,base_C,left_C,right_C,both_C,star_zero]
@[simp] lemma reflectJet_eL : reflectJet eL=eR := by
  rw [reflectJet_apply]
  apply jet_ext <;>
    simp only [reflected_base,reflected_left,reflected_right,reflected_both] <;>
    norm_num [base,left,right,both,eL,eR]
@[simp] lemma reflectJet_eR : reflectJet eR=eL := by
  rw [reflectJet_apply]
  apply jet_ext <;>
    simp only [reflected_base,reflected_left,reflected_right,reflected_both] <;>
    norm_num [base,left,right,both,eL,eR]
end CriticalHoneycomb.BoundaryJet

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma bulk_spin_star_0 (u : ℝ) (b c d : Spin) :
    bulkNumerator u ((0:Spin).rev,b.rev) (c.rev,d.rev)=
      star (bulkNumerator u (0,b) (c,d)) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bulkNumerator,Fin.rev,coeffA,coeffH,coeffV,coeffC,coeffD,S,
      Fusion.sine_star,Fusion.phase_star]
lemma bulk_spin_star_1 (u : ℝ) (b c d : Spin) :
    bulkNumerator u ((1:Spin).rev,b.rev) (c.rev,d.rev)=
      star (bulkNumerator u (1,b) (c,d)) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bulkNumerator,Fin.rev,coeffA,coeffH,coeffV,Q,S,
      Fusion.sine_star,Fusion.phase_star]
  all_goals try ring
lemma bulk_spin_star_2 (u : ℝ) (b c d : Spin) :
    bulkNumerator u ((2:Spin).rev,b.rev) (c.rev,d.rev)=
      star (bulkNumerator u (2,b) (c,d)) := by
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [bulkNumerator,Fin.rev,coeffA,coeffH,coeffV,coeffC,coeffD,S,
      Fusion.sine_star,Fusion.phase_star]
  all_goals try ring
lemma spectralR_spin_star (u : ℝ) (a b c d : Spin) :
    spectralR u (a.rev,b.rev) (c.rev,d.rev)=star (spectralR u (a,b) (c,d)) := by
  have hQ : star ((Q u)⁻¹)=(Q u)⁻¹ := by simp [Q,Fusion.sine_star]
  simp only [spectralR,Matrix.smul_apply,smul_eq_mul,star_mul,hQ]
  have h : bulkNumerator u (a.rev,b.rev) (c.rev,d.rev)=
      star (bulkNumerator u (a,b) (c,d)) := by
    fin_cases a
    · exact bulk_spin_star_0 u b c d
    · exact bulk_spin_star_1 u b c d
    · exact bulk_spin_star_2 u b c d
  rw [h,mul_comm]
noncomputable def flipSites (n : ℕ) : Space n≃Space n :=
  Equiv.piCongrRight (fun _=>Fusion.spinFlip)
@[simp] lemma flipSites_apply (n : ℕ) (w : Space n) (i : Fin n) :
    flipSites n w i=(w i).rev := rfl
lemma row_spin_star (n : ℕ) (u : ℝ) (w e : Space n) (a b : Spin) :
    row n (fun _=>spectralR u) (flipSites n w) (flipSites n e) a.rev b.rev=
      star (row n (fun _=>spectralR u) w e a b) := by
  induction n generalizing a b with
  | zero => simp [row,Matrix.one_apply]
  | succ n ih =>
    simp only [row,Matrix.mul_apply]
    rw [star_sum]
    rw [←Equiv.sum_comp Fusion.spinFlip]
    apply Finset.sum_congr rfl
    intro z hz
    change spectralR u (a.rev,(w 0).rev) (z.rev,(e 0).rev)*
      row n (fun _=>spectralR u) (flipSites n (fun i=>w i.succ))
        (flipSites n (fun i=>e i.succ)) z.rev b.rev=_
    rw [spectralR_spin_star,ih]
    simp only [star_mul,mul_comm,block]
    rfl
noncomputable def reflectedSites (n : ℕ) : Space n≃Space n :=
  (flipSites n).trans (reverseSites n)
lemma physical_reflected_row (n : ℕ) (w e : Space n) (a b : Spin) :
    row n (fun _=>spectralR L) (reflectedSites n w) (reflectedSites n e) a.rev b.rev=
      star (columnKernel n b a w e) := by
  have h : ∀ x : Space n, reflectedSites n x=flipSites n (reverseSites n x) := by
    intro x; rfl
  rw [h,h,row_spin_star,physical_row_kernel]
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet RasterGrid
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def homogeneous (n : ℕ) : Fin n→ℝ := fun _=>-L/2
lemma b_sub_gamma : b-gamma=gamma := by unfold b gamma;ring
lemma gamma_homogeneous (n : ℕ) (i : Fin n) : gamma+homogeneous n i=L := by
  unfold gamma homogeneous L;ring
lemma sine_twice_gamma_ne_zero : sine (2*gamma)≠0 := by
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi <;> unfold gamma <;> linarith [Real.pi_pos]
lemma homogeneous_nonsingular (n : ℕ) : Nonsingular n (homogeneous n) gamma := by
  rw [Nonsingular,b_sub_gamma]
  refine ⟨?_,?_,fun i=>?_⟩
  · convert sine_twice_gamma_ne_zero using 1 ; congr 1 ; ring
  · convert sine_twice_gamma_ne_zero using 1 ; congr 1 ; ring
  · rw [gamma_homogeneous]
    exact ⟨Q_at_L_ne_zero,Q_at_L_ne_zero⟩
noncomputable def positiveK (e : Jet) (a b : Spin) : Jet :=
  physicalMarkedK e (spinEquiv.symm a) (spinEquiv.symm b)
lemma positiveK_binding (e : Jet) (a b : Spin) :
    K e gamma (a.rev,b.rev)=positiveK e a b := by
  have h : sine (gamma+gamma)=sine (2*gamma) := by congr 1;ring
  have hp : Reflection.phase≠0 := point_ne_zero _
  have hz : sine 0=0 := by simp [sine]
  fin_cases a <;> fin_cases b <;>
    simp [K,K0,K1,boundary0,boundary1,positiveK,spinEquiv,
      physicalMarkedK,Fin.rev,spinValue,h,sine_twice_gamma_ne_zero,hz,hp]
lemma reflect_positiveK (e : Jet) (a b : Spin) :
    reflectJet (positiveK e a b)=positiveK (reflectJet e) a b := by
  fin_cases a <;> fin_cases b <;>
    simp [positiveK,spinEquiv,physicalMarkedK]
lemma markedDoubleMatrix_fin (n : ℕ) (w e : Space n) :
    markedDoubleMatrix n w e=
      ∑ s₁ : Spin,∑ s₂ : Spin,∑ z₁ : Spin,∑ z₂ : Spin,
        positiveK eL s₁ s₂*positiveK eR z₁ z₂*
        C ((columnKernel n s₁ z₁*columnKernel n s₂ z₂) w e) := by
  simp only [markedDoubleMatrix,fixedDoubleMatrix_eq]
  simp only [←Equiv.sum_comp spinEquiv]
  simp only [positiveK,Equiv.symm_apply_apply]
lemma markedDoubleMatrix_pair (n : ℕ) (w e : Space n) :
    markedDoubleMatrix n w e=∑ p : Pair,∑ q : Pair,
      positiveK eL p.1 p.2*positiveK eR q.1 q.2*
        C ((columnKernel n p.1 q.1*columnKernel n p.2 q.2) w e) := by
  rw [markedDoubleMatrix_fin]
  simp only [Fintype.sum_prod_type]
lemma physical_bulkRows (n : ℕ) (w e : Space n) (a b c d : Spin) :
    bulkRows n (homogeneous n) gamma (reflectedSites n w) (reflectedSites n e)
      (a.rev,b.rev) (c.rev,d.rev)=
      star ((columnKernel n c a*columnKernel n d b) w e) := by
  have hs : exactSites n (homogeneous n) gamma=fun _=>spectralR L := by
    funext i
    simp only [exactSites,gamma_homogeneous]
  simp only [bulkRows,b_sub_gamma,hs,forward,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,Matrix.of_apply,Matrix.mul_apply,star_sum]
  rw [←Equiv.sum_comp (reflectedSites n)]
  apply Finset.sum_congr rfl
  intro v hv
  rw [physical_reflected_row,physical_reflected_row]
  simp only [star_mul,mul_comm]
noncomputable def physicalFamily (n : ℕ) (u : ℝ) : Matrix (Space n) (Space n) Jet :=
  ((T n (homogeneous n) u).submatrix (reflectedSites n) (reflectedSites n)).map reflectJet
lemma physicalFamily_at_gamma (n : ℕ) : physicalFamily n gamma=markedDoubleMatrix n := by
  funext w e
  change reflectJet (T n (homogeneous n) gamma (reflectedSites n w) (reflectedSites n e))=_
  rw [markedDoubleMatrix_pair]
  conv_rhs => rw [Finset.sum_comm]
  simp only [T,b_sub_gamma,RingEquiv.map_sum,RingEquiv.map_mul,reflectJet_C]
  rw [←Equiv.sum_comp (Equiv.prodCongr Fusion.spinFlip Fusion.spinFlip)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [←Equiv.sum_comp (Equiv.prodCongr Fusion.spinFlip Fusion.spinFlip)]
  apply Finset.sum_congr rfl
  intro q hq
  rcases p with ⟨a,b⟩
  rcases q with ⟨c,d⟩
  simp only [Equiv.prodCongr_apply,Prod.map_apply,Fusion.spinFlip_apply,positiveK_binding,
    reflect_positiveK,reflectJet_eL,reflectJet_eR,physical_bulkRows,star_star]
  ring
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.FusionContraction
open scoped Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {k n m a b : Type*} [CommSemiring k]
variable [Fintype n] [Fintype m] [Fintype a] [Fintype b]
variable [DecidableEq n] [DecidableEq m] [DecidableEq a] [DecidableEq b]
noncomputable def contract (L R : Matrix n m k) (P : Matrix n n k) (Q : Matrix m m k) : k :=
  Matrix.trace (Lᵀ*P*R*Qᵀ)
omit [Fintype m] [Fintype a] [DecidableEq n] [DecidableEq m] [DecidableEq a] [DecidableEq b] in
lemma output_transpose (W : Matrix n a k) (Z : Matrix b m k)
    (L : Matrix n m k) (l : Matrix a b k) (h : Wᵀ*L=l*Z) :
    Lᵀ*W=Zᵀ*lᵀ := by
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using congrArg Matrix.transpose h
omit [DecidableEq m] [DecidableEq b] in
lemma quotient_transpose (Z : Matrix b m k) (Q : Matrix m m k) (G : Matrix b b k)
    (h : Z*Q=G*Z) : Qᵀ*Zᵀ=Zᵀ*Gᵀ := by
  simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose h

omit [DecidableEq n] [DecidableEq m] [DecidableEq b] in
theorem range_compression
    (W : Matrix n a k) (J : Matrix a n k) (Z : Matrix b m k)
    (P : Matrix n n k) (Q : Matrix m m k) (F : Matrix a a k) (G : Matrix b b k)
    (L R : Matrix n m k) (l r : Matrix a b k)
    (hJ : J*W=1) (hP : W*J*P=P) (hF : P*W=W*F) (hG : Z*Q=G*Z)
    (hL : Wᵀ*L=l*Z) (hR : R*Zᵀ=W*r) :
    contract L R P Q=contract l r F G := by
  have hLT := output_transpose W Z L l hL
  have hGT := quotient_transpose Z Q G hG
  unfold contract
  calc
    _ = Matrix.trace (Lᵀ*(W*J*P)*R*Qᵀ) := by rw [hP]
    _ = Matrix.trace (Zᵀ*(lᵀ*J*P*R*Qᵀ)) := by
      simp only [←Matrix.mul_assoc,hLT]
    _ = Matrix.trace ((lᵀ*J*P*R*Qᵀ)*Zᵀ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (lᵀ*J*P*(R*Zᵀ)*Gᵀ) := by
      simp only [Matrix.mul_assoc,hGT]
    _ = Matrix.trace (lᵀ*J*(P*W)*r*Gᵀ) := by
      rw [hR]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (lᵀ*(J*W)*F*r*Gᵀ) := by
      rw [hF]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ,Matrix.mul_one]

omit [DecidableEq n] [DecidableEq m] [DecidableEq a] in
theorem quotient_compression
    (W : Matrix n a k) (Z : Matrix b m k) (V : Matrix m b k)
    (P : Matrix n n k) (Q : Matrix m m k) (F : Matrix a a k) (G : Matrix b b k)
    (L R : Matrix n m k) (l r : Matrix a b k)
    (hV : Z*V=1) (hQ : Q*V*Z=Q) (hF : P*W=W*F) (hG : Z*Q=G*Z)
    (hL : Wᵀ*L=l*Z) (hR : R*Zᵀ=W*r) :
    contract L R P Q=contract l r F G := by
  have hLT := output_transpose W Z L l hL
  have hGT := quotient_transpose Z Q G hG
  have hQ' : Qᵀ=Zᵀ*Vᵀ*Qᵀ := by
    simpa only [Matrix.transpose_mul,Matrix.mul_assoc] using
      (congrArg Matrix.transpose hQ).symm
  have hV' : Vᵀ*Zᵀ=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_one] using congrArg Matrix.transpose hV
  unfold contract
  calc
    _ = Matrix.trace (Lᵀ*P*R*(Zᵀ*Vᵀ*Qᵀ)) := by
      conv_lhs => rw [hQ']
    _ = Matrix.trace (Lᵀ*P*(R*Zᵀ)*Vᵀ*Qᵀ) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Lᵀ*W)*(F*r*Vᵀ*Qᵀ)) := by
      rw [hR]
      calc
        _ = Matrix.trace (Lᵀ*(P*W)*r*Vᵀ*Qᵀ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hF]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Zᵀ*(lᵀ*F*r*Vᵀ*Qᵀ)) := by
      rw [hLT]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((lᵀ*F*r*Vᵀ*Qᵀ)*Zᵀ) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((lᵀ*F*r)*(Vᵀ*Zᵀ)*Gᵀ) := by
      simp only [Matrix.mul_assoc,hGT]
    _ = _ := by rw [hV',Matrix.mul_one]
end CriticalHoneycomb.Transfer.FusionContraction

end

section

namespace CriticalHoneycomb.Transfer.ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {α ι k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]
def rotateAux : Aux α ≃ Aux α where
  toFun p := (p.2.1,p.2.2.1,p.1,p.2.2.2)
  invFun p := (p.2.2.1,p.1,p.2.1,p.2.2.2)
  left_inv p := by rcases p with ⟨a,b,c,d⟩;rfl
  right_inv p := by rcases p with ⟨a,b,c,d⟩;rfl
def rotateSite : AuxSite α ι ≃ AuxSite α ι :=
  Equiv.prodCongr rotateAux (Equiv.refl ι)
omit [Fintype α] [Fintype ι] [DecidableEq ι] in
lemma rotate_rowA (M : Row α ι k) :
    (rowA M).submatrix rotateSite rotateSite=rowB M := by
  funext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [Matrix.submatrix,rowA,rowB,rotateSite,rotateAux,Matrix.one_apply,mul_ite]
  all_goals split_ifs <;> simp_all
omit [Fintype α] [Fintype ι] [DecidableEq ι] in
lemma rotate_rowB (M : Row α ι k) :
    (rowB M).submatrix rotateSite rotateSite=rowC M := by
  funext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [Matrix.submatrix,rowB,rowC,rotateSite,rotateAux,Matrix.one_apply,mul_ite]
  all_goals split_ifs <;> simp_all
omit [Fintype α] [Fintype ι] [DecidableEq ι] in
lemma rotate_rowC (M : Row α ι k) :
    (rowC M).submatrix rotateSite rotateSite=rowA M := by
  funext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [Matrix.submatrix,rowC,rowA,rotateSite,rotateAux,Matrix.one_apply,mul_ite]
omit [Fintype α] [Fintype ι] [DecidableEq ι] in
lemma rotate_rowD (M : Row α ι k) :
    (rowD M).submatrix rotateSite rotateSite=rowD M := by
  funext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [Matrix.submatrix,rowD,rotateSite,rotateAux,Matrix.one_apply,mul_ite]
  all_goals split_ifs <;> simp_all
omit [DecidableEq α] in
lemma close4_rotate (l r : Aux α→k) (X : Total α ι k) :
    close4 l r X=close4 (l ∘ rotateAux) (r ∘ rotateAux)
      (X.submatrix rotateSite rotateSite) := by
  have hl : (leftWall (l ∘ rotateAux) : Matrix ι (AuxSite α ι) k)=
      (leftWall l).submatrix id rotateSite := rfl
  have hr : (rightWall (r ∘ rotateAux) : Matrix (AuxSite α ι) ι k)=
      (rightWall r).submatrix rotateSite id := rfl
  simp only [close4,hl,hr,Matrix.submatrix_mul_equiv,Matrix.submatrix_id_id]
omit [DecidableEq ι] in
lemma pairAB_backward (M N : Row α ι k) : rowB N*rowA M=pairAB (backwardPair M N) := by
  funext ⟨⟨a,b,c,d⟩,s⟩ ⟨⟨a',b',c',d'⟩,t⟩
  simp [rowA,rowB,pairAB,backwardPair,Matrix.mul_apply,Fintype.sum_prod_type,
    Matrix.kronecker,Matrix.kroneckerMap,Matrix.one_apply,mul_ite,ite_mul,
    Matrix.sum_apply,Matrix.of_apply,mul_comm]
  all_goals split_ifs <;> simp_all
lemma auxBC_mul (F G : Matrix (α×α) (α×α) k) : auxBC (F*G)=auxBC F*auxBC G := by
  funext ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩
  simp [auxBC,Matrix.mul_apply,Fintype.sum_prod_type,Matrix.one_apply,mul_ite,ite_mul]
omit [Fintype α] in
lemma auxBC_one : auxBC (1 : Matrix (α×α) (α×α) k)=1 := by
  funext ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩
  simp only [auxBC,Matrix.one_apply,Prod.mk.injEq]
  all_goals split_ifs <;> simp_all
lemma middle_close (A B C D : Row α ι k) (F G : Matrix (α×α) (α×α) k)
    (hGF : G*F=1)
    (h : ∀ s t,F*forwardPair C A s t=backwardPair C A s t*F)
    (l₁ l₂ r₁ r₂ : α×α→k) :
    closePair (forwardPair B C) l₁ r₁*closePair (forwardPair A D) l₂ r₂=
      close4 ((tensorBoundary l₁ l₂ ᵥ* auxBC G) ∘ rotateAux)
        ((auxBC F *ᵥ tensorBoundary r₁ r₂) ∘ rotateAux)
        (pairAB (backwardPair A B)*pairCD (forwardPair C D)) := by
  let X := rowA B*rowB C*rowC A*rowD D
  let Y := rowA B*rowC A*rowB C*rowD D
  have hx : closePair (forwardPair B C) l₁ r₁*closePair (forwardPair A D) l₂ r₂=
      close4 (tensorBoundary l₁ l₂) (tensorBoundary r₁ r₂) X := by
    rw [←close4_pair_product,←pairAB_forward,←pairCD_forward]
    simp only [X,Matrix.mul_assoc]
  have he : (auxLift (auxBC F) : Total α ι k)*X=Y*auxLift (auxBC F) := by
    exact middle_exchange _ _ _ _ _ (exBC_rowA F B) (exBC_rowD F D)
      (exchangeBC F C A h)
  have hi : (auxLift (auxBC G) : Total α ι k)*auxLift (auxBC F)=1 := by
    rw [←auxLift_mul,←auxBC_mul,hGF,auxBC_one]
    simp [auxLift]
  have hxy : X=auxLift (auxBC G)*Y*auxLift (auxBC F) := by
    calc
      _= (auxLift (auxBC G)*auxLift (auxBC F))*X := by rw [hi,Matrix.one_mul]
      _= _ := by rw [Matrix.mul_assoc,he,←Matrix.mul_assoc]
  rw [hx,hxy]
  have hc : close4 (tensorBoundary l₁ l₂) (tensorBoundary r₁ r₂)
      (auxLift (auxBC G)*Y*auxLift (auxBC F))=
      close4 (tensorBoundary l₁ l₂ ᵥ* auxBC G) (auxBC F *ᵥ tensorBoundary r₁ r₂) Y := by
    simp only [close4,←leftWall_auxLift,←auxLift_rightWall,Matrix.mul_assoc]
  rw [hc,close4_rotate]
  congr 1
  simp only [Y,←Matrix.submatrix_mul_equiv _ _ _ rotateSite _,
    rotate_rowA,rotate_rowB,rotate_rowC,rotate_rowD]
  rw [←pairAB_backward,←pairCD_forward]
  simp only [Matrix.mul_assoc]
end CriticalHoneycomb.Transfer.ClosedFourRow

end

section

namespace CriticalHoneycomb.Transfer
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace FusionContraction
variable {k n m : Type*} [CommSemiring k] [Fintype n] [Fintype m]
lemma contract_eq_sum (L R : Matrix n m k) (P : Matrix n n k) (Q : Matrix m m k) :
    contract L R P Q = ∑ a,∑ b,∑ c,∑ d,L a b*P a c*R c d*Q b d := by
  simp only [contract,Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,
    Finset.sum_mul]
  conv_lhs =>
    enter [2,b,2,d]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,b]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro a ha
  apply Finset.sum_congr rfl;intro b hb
  rw [Finset.sum_comm]
end FusionContraction
namespace ClosedFourRow
variable {α ι k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α]
  [Fintype ι] [DecidableEq ι]
noncomputable def matrixBoundary (D : Matrix (α×α) (α×α) k) : Aux α→k :=
  fun p => D (p.1,p.2.1) (p.2.2.1,p.2.2.2)
lemma close4_fusion_contract (L R : Matrix (α×α) (α×α) k)
    (P Q : ι→ι→Matrix (α×α) (α×α) k) (s t : ι) :
    close4 (matrixBoundary L) (matrixBoundary R) (pairAB P*pairCD Q) s t=
      ∑ v,FusionContraction.contract L R (P s v) (Q v t) := by
  rw [close4_apply]
  simp only [sum_aux,matrixBoundary,pairAB_mul_CD,Finset.mul_sum,Finset.sum_mul,
    FusionContraction.contract_eq_sum]
  conv_lhs =>
    enter [2,a,2,b,2,c]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a,2,b]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  repeat first | apply Finset.sum_congr rfl; intro _ _ | ring
omit [DecidableEq α] [DecidableEq ι] in
lemma closePair_fusion_contract (L R : Matrix α α k) (M N : Row α ι k) (s t : ι) :
    closePair (forwardPair M N) (fun p=>L p.1 p.2) (fun p=>R p.1 p.2) s t=
      ∑ v,FusionContraction.contract L R (M s v) (N v t) := by
  simp only [closePair,forwardPair,Matrix.sum_apply,Matrix.kronecker,Matrix.kroneckerMap,
    Fintype.sum_prod_type,Matrix.of_apply,Finset.mul_sum,Finset.sum_mul,
    FusionContraction.contract_eq_sum]
  conv_lhs =>
    enter [2,a,2,b,2,c]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a,2,b]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2,a]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  repeat first | apply Finset.sum_congr rfl; intro _ _ | ring
end ClosedFourRow
end CriticalHoneycomb.Transfer

end

section

namespace CriticalHoneycomb.Transfer.Reflection
open Fusion
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma source_swap_transpose (u : ℝ) (a b c d : Fin 3) :
    spectralR u (a,b) (c,d)=spectralR u (d,c) (b,a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> rfl

noncomputable def fusionVector (u : ℝ) (A B : Matrix Spin3 Spin3 ℂ) :
    Matrix Pair Pair ℂ := fun p q => crossedBC (spectralR (b-u)) A B p.2 q.1 p.1 q.2
noncomputable def fusionUnbend (G : Matrix Pair Pair ℂ) : Matrix Pair Pair ℂ := fun p q =>
  phase^(-spinValue q.1-spinValue q.2)*G p (q.2.rev,q.1.rev)
lemma fusion_unbend (u : ℝ) (A B : Matrix Spin3 Spin3 ℂ) :
    fusionUnbend (fusionVector u A B)=slot2 A*spectralR u*slot1 B := by
  ext ⟨a,b⟩ ⟨c,d⟩
  have hh := congrFun (congrFun (unbend_BC u A B) (b,a)) (d,c)
  simp only [unbend] at hh
  change phase^(-spinValue c-spinValue d)*crossedBC (spectralR (Reflection.b-u)) A B b d.rev a c.rev=_
  rw [show -spinValue c-spinValue d = -spinValue d-spinValue c by ring,hh]
  rw [sandwich12,sandwich21,Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i hi
  apply Finset.sum_congr rfl; intro j hj
  rw [Matrix.transpose_apply,source_swap_transpose u d i j a]
noncomputable def bendPair : Matrix Pair Pair ℂ := fun p q =>
  if p=(q.2.rev,q.1.rev) then phase^(-spinValue q.1-spinValue q.2) else 0
noncomputable def bendSpin : Matrix Spin3 Spin3 ℂ := fun p q =>
  if p=q.rev then phase^(spinValue q.rev) else 0
lemma mul_bendPair (M : Matrix Pair Pair ℂ) (p q : Pair) :
    (M*bendPair) p q=M p (q.2.rev,q.1.rev)*phase^(-spinValue q.1-spinValue q.2) := by
  simp [Matrix.mul_apply,bendPair,mul_ite]
lemma mul_bendSpin {a : Type*} (M : Matrix a Spin3 ℂ) (i : a) (j : Spin3) :
    (M*bendSpin) i j=M i j.rev*phase^(spinValue j.rev) := by
  simp [Matrix.mul_apply,bendSpin,mul_ite]
lemma fusion_bend (u : ℝ) (A B : Matrix Spin3 Spin3 ℂ) :
    fusionVector u A B=(slot2 A*spectralR u*slot1 B)*bendPair := by
  rw [←fusion_unbend]
  ext p q
  rw [mul_bendPair]
  simp only [fusionUnbend,Fin.rev_rev,spinValue_rev,neg_neg]
  have hp : phase≠0 := point_ne_zero _
  rw [mul_right_comm,←zpow_add₀ hp]
  simp [show spinValue q.2+spinValue q.1+(-spinValue q.1-spinValue q.2)=0 by ring]
lemma bendPair_Wbar : bendPair*sourceWbar=sourceWbar*bendSpin := by
  ext ⟨a,b⟩ j
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fintype.sum_prod_type,Fin.sum_univ_three,bendPair,bendSpin,
      sourceWbar,spinValue,Fin.rev,div_eq_mul_inv] <;> ring
lemma Wbar_transpose_bendPair : sourceWbarᵀ*bendPair=bendSpin*sourceWbarᵀ := by
  ext j ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_three,bendPair,bendSpin,
      sourceWbar,spinValue,Fin.rev,div_eq_mul_inv] <;> ring
lemma boundary_bend (A : Matrix Spin3 Spin3 ℂ) (i j : Spin3) :
    (A*bendSpin) i j=boundaryVector A (i,j) := by
  rw [mul_bendSpin]
  exact mul_comm _ _

lemma fusion_right_close (u : ℝ) (A B D : Matrix Spin3 Spin3 ℂ)
    (h : slot2 A*spectralR u*slot1 B*sourceWbar=sourceW*D) :
    fusionVector u A B*sourceWbar=sourceW*(D*bendSpin) := by
  rw [fusion_bend,Matrix.mul_assoc, bendPair_Wbar,←Matrix.mul_assoc,h,Matrix.mul_assoc]

lemma fusion_left_close (u : ℝ) (A B D : Matrix Spin3 Spin3 ℂ)
    (h : sourceWᵀ*slot2 A*spectralR u*slot1 B=D*sourceWbarᵀ) :
    sourceWᵀ*fusionVector u A B=(D*bendSpin)*sourceWbarᵀ := by
  rw [fusion_bend]
  calc
    _=(sourceWᵀ*slot2 A*spectralR u*slot1 B)*bendPair := by simp only [Matrix.mul_assoc]
    _=D*sourceWbarᵀ*bendPair := by rw [h]
    _=_ := by rw [Matrix.mul_assoc,Wbar_transpose_bendPair,←Matrix.mul_assoc]

lemma fusion_right_close_add (u : ℝ) (A B A' B' D : Matrix Spin3 Spin3 ℂ)
    (h : slot2 A*spectralR u*slot1 B*sourceWbar+
      slot2 A'*spectralR u*slot1 B'*sourceWbar=sourceW*D) :
    (fusionVector u A B+fusionVector u A' B')*sourceWbar=sourceW*(D*bendSpin) := by
  simp only [fusion_bend,Matrix.add_mul,Matrix.mul_assoc,bendPair_Wbar]
  simp only [←Matrix.mul_assoc]
  rw [←Matrix.add_mul,h,Matrix.mul_assoc]
lemma fusion_left_close_add (u : ℝ) (A B A' B' D : Matrix Spin3 Spin3 ℂ)
    (h : sourceWᵀ*slot2 A*spectralR u*slot1 B+
      sourceWᵀ*slot2 A'*spectralR u*slot1 B'=D*sourceWbarᵀ) :
    sourceWᵀ*(fusionVector u A B+fusionVector u A' B')=(D*bendSpin)*sourceWbarᵀ := by
  simp only [fusion_bend,Matrix.mul_add,←Matrix.mul_assoc]
  rw [←Matrix.add_mul,h,Matrix.mul_assoc,Wbar_transpose_bendPair,←Matrix.mul_assoc]
lemma source_fusion_right_constant (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    fusionVector (2*t) (boundary0 (t-L)) (boundary0 (t+L))*sourceWbar=
      sourceW*(boundary0 t*bendSpin) :=
  fusion_right_close _ _ _ _ (boundary_fusion_constant t hQ ht hm hp)
lemma source_fusion_right_linear (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    (fusionVector (2*t) (boundary1 (t-L)) (boundary0 (t+L))+
      fusionVector (2*t) (boundary0 (t-L)) (boundary1 (t+L)))*sourceWbar=
      sourceW*(boundary1 t*bendSpin) :=
  fusion_right_close_add _ _ _ _ _ _ (boundary_fusion_linear t hQ ht hm hp)
lemma source_fusion_left_constant (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    sourceWᵀ*fusionVector (2*t) (boundary0 (t+L)) (boundary0 (t-L))=
      (boundary0 t*bendSpin)*sourceWbarᵀ :=
  fusion_left_close _ _ _ _ (boundary_fusion_dual_constant t hQ ht hm hp)
lemma source_fusion_left_linear (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    sourceWᵀ*(fusionVector (2*t) (boundary0 (t+L)) (boundary1 (t-L))+
      fusionVector (2*t) (boundary1 (t+L)) (boundary0 (t-L)))=
      (boundary1 t*bendSpin)*sourceWbarᵀ :=
  fusion_left_close_add _ _ _ _ _ _ (boundary_fusion_dual_linear t hQ ht hm hp)
end CriticalHoneycomb.Transfer.Reflection

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection Reflection.Fusion BoundaryJet
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
noncomputable def wallMatrix (e : Jet) (u : ℝ) : Matrix Spin3 Spin3 Jet :=
  fun i j => K e u (i,j)
noncomputable def markedFusionVector (e : Jet) (x u v : ℝ) : Matrix Pair Pair Jet :=
  fun p q => ∑ i,∑ j, C (spectralR (b-x) (q.1,p.1) (i,j))*
    K e u (p.2,i)*K e v (j,q.2)
lemma wallMatrix_affine (e : Jet) (u : ℝ) :
    wallMatrix e u=(boundary0 u*bendSpin).map C+e • (boundary1 u*bendSpin).map C := by
  funext i j
  simp only [wallMatrix,K,Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,
    boundary_bend,K0,K1,boundaryVector,smul_eq_mul]
lemma markedFusionVector_affine (e : Jet) (he : e*e=0) (x u v : ℝ) :
    markedFusionVector e x u v=(fusionVector x (boundary0 u) (boundary0 v)).map C+
      e • (fusionVector x (boundary1 u) (boundary0 v)+
        fusionVector x (boundary0 u) (boundary1 v)).map C := by
  funext p q
  simp only [markedFusionVector,Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,
    fusionVector,crossedBC,K,K0,K1,boundaryVector,smul_eq_mul,map_add,map_sum,map_mul,
    Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  calc
    _ = C (spectralR (b-x) (q.1,p.1) (i,j))*
      C (Reflection.phase^(spinValue i.rev)*boundary0 u p.2 i.rev)*
      C (Reflection.phase^(spinValue q.2.rev)*boundary0 v j q.2.rev)+
      e*(C (spectralR (b-x) (q.1,p.1) (i,j))*
        C (Reflection.phase^(spinValue i.rev)*boundary1 u p.2 i.rev)*
        C (Reflection.phase^(spinValue q.2.rev)*boundary0 v j q.2.rev))+ 
      e*(C (spectralR (b-x) (q.1,p.1) (i,j))*
        C (Reflection.phase^(spinValue i.rev)*boundary0 u p.2 i.rev)*
        C (Reflection.phase^(spinValue q.2.rev)*boundary1 v j q.2.rev))+
      (e*e)*(C (spectralR (b-x) (q.1,p.1) (i,j))*
        C (Reflection.phase^(spinValue i.rev)*boundary1 u p.2 i.rev)*
        C (Reflection.phase^(spinValue q.2.rev)*boundary1 v j q.2.rev)) := by simp only [map_mul];ring
    _ = _ := by rw [he,zero_mul,add_zero];simp only [map_mul];ring
local instance : IsScalarTower Jet Jet Jet where
  smul_assoc a b c := mul_assoc a b c
local instance : SMulCommClass Jet Jet Jet := ⟨fun a b c => by
  change a*(b*c)=b*(a*c)
  ring⟩
lemma affine_right {a n m d : Type*} [Fintype a] [Fintype n] [Fintype m] [Fintype d]
    (W : Matrix n a ℂ) (Z : Matrix m d ℂ) (G0 G1 : Matrix n m ℂ)
    (D0 D1 : Matrix a d ℂ) (e : Jet)
    (h0 : G0*Z=W*D0) (h1 : G1*Z=W*D1) :
    (G0.map C+e • G1.map C)*Z.map C=W.map C*(D0.map C+e • D1.map C) := by
  rw [Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul e (G1.map C) (Z.map C),
    Matrix.mul_smul (W.map C) e (D1.map C)]
  simp only [←Matrix.map_mul, h0, h1]
lemma affine_left {a n m d : Type*} [Fintype a] [Fintype n] [Fintype m] [Fintype d]
    (W : Matrix a n ℂ) (Z : Matrix d m ℂ) (G0 G1 : Matrix n m ℂ)
    (D0 D1 : Matrix a d ℂ) (e : Jet)
    (h0 : W*G0=D0*Z) (h1 : W*G1=D1*Z) :
    W.map C*(G0.map C+e • G1.map C)=(D0.map C+e • D1.map C)*Z.map C := by
  rw [Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul (W.map C) e (G1.map C),
    Matrix.smul_mul e (D1.map C) (Z.map C)]
  simp only [←Matrix.map_mul, h0, h1]
lemma marked_fusion_right (e : Jet) (he : e*e=0) (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    markedFusionVector e (2*t) (t-L) (t+L)*sourceWbar.map C=
      sourceW.map C*wallMatrix e t := by
  rw [markedFusionVector_affine e he,wallMatrix_affine]
  exact affine_right _ _ _ _ _ _ e (source_fusion_right_constant t hQ ht hm hp)
    (source_fusion_right_linear t hQ ht hm hp)
lemma marked_fusion_left (e : Jet) (he : e*e=0) (t : ℝ) (hQ : Q (2*t)≠0)
    (ht : sine (gamma+t)≠0) (hm : sine (gamma+(t-L))≠0) (hp : sine (gamma+(t+L))≠0) :
    sourceWᵀ.map C*markedFusionVector e (2*t) (t+L) (t-L)=
      wallMatrix e t*sourceWbarᵀ.map C := by
  rw [markedFusionVector_affine e he,wallMatrix_affine]
  have hh:=affine_left _ _ _ _ _ _ e (source_fusion_left_constant t hQ ht hm hp)
    (source_fusion_left_linear t hQ ht hm hp)
  simpa only [add_comm] using hh
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
namespace ClosedFourRow
variable {α k : Type*} [CommSemiring k] [Fintype α] [DecidableEq α]
lemma right_middle_boundary (F : Matrix (α×α) (α×α) k) (r₁ r₂ : α×α→k) :
    (auxBC F *ᵥ tensorBoundary r₁ r₂) ∘ rotateAux=
      matrixBoundary (fun p q=>∑ i,∑ j,F (q.1,p.1) (i,j)*r₁ (p.2,i)*r₂ (j,q.2)) := by
  funext ⟨a,b,c,d⟩
  simp [rotateAux,auxBC,tensorBoundary,matrixBoundary,
    Matrix.mulVec, dotProduct,Fintype.sum_prod_type,Matrix.one_apply,mul_ite,ite_mul]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  ring
lemma left_middle_boundary (G : Matrix (α×α) (α×α) k) (l₁ l₂ : α×α→k) :
    (tensorBoundary l₁ l₂ ᵥ* auxBC Gᵀ) ∘ rotateAux=
      matrixBoundary (fun p q=>∑ i,∑ j,G (q.1,p.1) (i,j)*l₁ (p.2,i)*l₂ (j,q.2)) := by
  funext ⟨a,b,c,d⟩
  simp [rotateAux,auxBC,tensorBoundary,matrixBoundary,
    Matrix.vecMul, dotProduct,Fintype.sum_prod_type,Matrix.one_apply,mul_ite,Matrix.transpose_apply]
  apply Finset.sum_congr rfl;intro i hi
  apply Finset.sum_congr rfl;intro j hj
  ring
end ClosedFourRow
namespace SpectralFamily
open Reflection BoundaryJet ClosedFourRow
lemma marked_middle_right (e : Jet) (t : ℝ) :
    (auxBC ((spectralR (b-2*t)).map C) *ᵥ tensorBoundary (K e (t-L)) (K e (t+L))) ∘
      rotateAux=matrixBoundary (markedFusionVector e (2*t) (t-L) (t+L)) := by
  rw [right_middle_boundary]
  rfl
lemma marked_middle_left (e : Jet) (t : ℝ) :
    (tensorBoundary (K e ((b-t)+L)) (K e ((b-t)-L)) ᵥ*
      auxBC ((spectralR (-(b-2*t)))ᵀ.map C)) ∘ rotateAux=
      matrixBoundary (markedFusionVector e (2*(b-t)) ((b-t)+L) ((b-t)-L)) := by
  have hr : b-2*(b-t)=-(b-2*t) := by ring
  change (tensorBoundary _ _ ᵥ* auxBC (((spectralR (-(b-2*t))).map C)ᵀ)) ∘ _=_
  rw [left_middle_boundary]
  unfold markedFusionVector
  rw [hr]
  rfl
end SpectralFamily
end CriticalHoneycomb.Transfer

end

section

namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix BigOperators
noncomputable def sourceJ : Matrix (Fin 3) Pair ℂ := fun j p =>
  if p=(j,1) then if j=1 then 1 else twoCos else 0
lemma sourceJ_W : sourceJ*sourceW=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,sourceJ,sourceW,kappa_normalization]
lemma sourceJ_Wbar : sourceJ*sourceWbar=1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,sourceJ,sourceWbar,kappa_normalization]
lemma sourceWbar_J : sourceWbarᵀ*sourceJᵀ=1 := by
  simpa only [Matrix.transpose_mul,Matrix.transpose_one] using
    congrArg Matrix.transpose sourceJ_Wbar
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer
lemma cos_angle_pos : 0 < Real.cos angle := by
  rw [angle,Real.cos_pi_div_eight]
  positivity
lemma sine2_sq : sine2^2=(1:ℝ)/2 := by
  have hh:=Real.sin_sq_add_cos_sq (2*angle)
  rw [cos_two_angle] at hh
  change sine2^2+sine2^2=1 at hh
  linarith
lemma denominator_two_angle : denominator (2*angle)=Real.cos angle := by
  unfold denominator
  rw [show 2*angle+2*angle=Real.pi/2 by unfold angle;ring,
    show bigAngle+2*angle=Real.pi-bigAngle by unfold bigAngle angle;ring,
    Real.sin_pi_div_two,Real.sin_pi_sub,sin_bigAngle,one_mul]
lemma special_two_angle :
    a (2*angle)=(1/(2*Real.cos angle))^2 ∧
    h (2*angle)=1/(2*Real.cos angle) ∧
    v (2*angle)=(1/(2*Real.cos angle))^2 ∧
    c (2*angle)=0 ∧
    d (2*angle)=(1/(2*Real.cos angle))^2 := by
  have hc : Real.cos angle≠0 := ne_of_gt cos_angle_pos
  have hb : bigAngle-2*angle=angle := by unfold bigAngle;ring
  have hd : 2*angle-angle=angle := by ring
  have he : sine2=2*Real.sin angle*Real.cos angle := Real.sin_two_mul angle
  have hs : 8*(Real.sin angle)^2*(Real.cos angle)^2=1 := by
    have hsq:=sine2_sq
    rw [he] at hsq
    nlinarith
  have ha : sine2*Real.sin angle/Real.cos angle=(1/(2*Real.cos angle))^2 := by
    rw [he]
    field_simp
    nlinarith
  have hh : sine2*sine2/Real.cos angle=1/(2*Real.cos angle) := by
    field_simp
    nlinarith [sine2_sq]
  simp only [a,h,v,c,d,denominator_two_angle,hb,hd,sub_self,Real.sin_zero,mul_zero,
    zero_div,show Real.sin (2*angle)=sine2 from rfl]
  exact ⟨ha,hh,by simpa only [mul_comm] using ha,True.intro,ha⟩
lemma denominator_zero : denominator 0=sine2*Real.cos angle := by
  simp only [denominator,add_zero,sin_bigAngle];rfl
lemma sine2_pos : 0<sine2 := by
  unfold sine2
  rw [show 2*angle=Real.pi/4 by unfold angle;ring,Real.sin_pi_div_four]
  positivity
lemma special_zero : a 0=1 ∧ h 0=0 ∧ v 0=0 ∧ c 0=1 ∧ d 0=0 := by
  have hn : sine2*Real.cos angle≠0 := mul_ne_zero (ne_of_gt sine2_pos) (ne_of_gt cos_angle_pos)
  simp only [a,h,v,c,d,denominator_zero,sub_zero,Real.sin_zero,mul_zero,zero_div,
    sin_bigAngle,show Real.sin (2*angle)=sine2 from rfl]
  simp [hn,mul_comm,]
lemma denominator_bigAngle : denominator bigAngle=Real.cos angle*sine2 := by
  unfold denominator
  rw [show 2*angle+bigAngle=Real.pi-bigAngle by unfold bigAngle angle;ring,
    show bigAngle+bigAngle=Real.pi-2*angle by unfold bigAngle angle;ring,
    Real.sin_pi_sub,Real.sin_pi_sub,sin_bigAngle]
  rfl
lemma special_bigAngle : a bigAngle=0 ∧ h bigAngle=1 ∧ v bigAngle=0 ∧
    c bigAngle=0 ∧ d bigAngle=1 := by
  have hn : Real.cos angle*sine2≠0 := mul_ne_zero (ne_of_gt cos_angle_pos) (ne_of_gt sine2_pos)
  have hd : bigAngle-angle=2*angle := by unfold bigAngle;ring
  simp only [a,h,v,c,d,denominator_bigAngle,sub_self,Real.sin_zero,zero_mul,zero_div,
    sin_bigAngle,hd,show Real.sin (2*angle)=sine2 from rfl]
  simp [mul_comm,ne_of_gt sine2_pos,ne_of_gt cos_angle_pos]
end CriticalHoneycomb.Transfer

end

section
namespace CriticalHoneycomb.Transfer.Reflection.Fusion
open scoped Matrix
noncomputable def swapR : Matrix Pair Pair ℂ := fun p q=>
  if p.1=q.2 then if p.2=q.1 then 1 else 0 else 0
noncomputable def sourceOmega : Pair→ℂ := fun p=>
  match p.1.val,p.2.val with
  | 0,2 => phase⁻¹
  | 1,1 => 1
  | 2,0 => phase
  | _,_ => 0
noncomputable def sourceOmegaBar : Pair→ℂ := fun p=>
  match p.1.val,p.2.val with
  | 0,2 => phase
  | 1,1 => 1
  | 2,0 => phase⁻¹
  | _,_ => 0
lemma sourceKappa_real : ((1/(2*Real.cos Transfer.angle):ℝ):ℂ)=sourceKappa := by
  simp [sourceKappa,twoCos,Transfer.angle,L,one_div]
lemma Q_ne_of_denominator_ne {u : ℝ} (h : Transfer.denominator u≠0) : Q u≠0 := by
  rw [←denominator_binding]
  exact_mod_cast h
lemma Q_zero_ne : Q 0≠0 := by
  apply Q_ne_of_denominator_ne
  rw [Transfer.denominator_zero]
  exact mul_ne_zero (ne_of_gt Transfer.sine2_pos) (ne_of_gt Transfer.cos_angle_pos)
lemma Q_two_L_ne : Q (2*L)≠0 := by
  apply Q_ne_of_denominator_ne
  change Transfer.denominator (2*Transfer.angle)≠0
  rw [Transfer.denominator_two_angle]
  exact ne_of_gt Transfer.cos_angle_pos
lemma Q_b_ne : Q b≠0 := by
  apply Q_ne_of_denominator_ne
  rw [←bigAngle_binding,Transfer.denominator_bigAngle]
  exact mul_ne_zero (ne_of_gt Transfer.cos_angle_pos) (ne_of_gt Transfer.sine2_pos)
private lemma spectralValueSpecialZero00 (c d : Fin 3) :
    normalizedR 0 (0,0) (c,d)=swapR (0,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,hc,swapR]
private lemma spectralValueSpecialZero01 (c d : Fin 3) :
    normalizedR 0 (0,1) (c,d)=swapR (0,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,ha,hv,swapR]
private lemma spectralValueSpecialZero02 (c d : Fin 3) :
    normalizedR 0 (0,2) (c,d)=swapR (0,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,hh,hc,hd,swapR]
private lemma spectralValueSpecialZero10 (c d : Fin 3) :
    normalizedR 0 (1,0) (c,d)=swapR (1,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,ha,hv,swapR]
private lemma spectralValueSpecialZero11 (c d : Fin 3) :
    normalizedR 0 (1,1) (c,d)=swapR (1,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,hh,swapR]
private lemma spectralValueSpecialZero12 (c d : Fin 3) :
    normalizedR 0 (1,2) (c,d)=swapR (1,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,ha,hv,swapR]
private lemma spectralValueSpecialZero20 (c d : Fin 3) :
    normalizedR 0 (2,0) (c,d)=swapR (2,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,hh,hc,hd,swapR]
private lemma spectralValueSpecialZero21 (c d : Fin 3) :
    normalizedR 0 (2,1) (c,d)=swapR (2,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,ha,hv,swapR]
private lemma spectralValueSpecialZero22 (c d : Fin 3) :
    normalizedR 0 (2,2) (c,d)=swapR (2,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_zero
  fin_cases c <;> fin_cases d <;> simp [normalizedR,hc,swapR]

theorem source_R_zero : spectralR 0=swapR := by
  rw [spectralR_normalized 0 Q_zero_ne]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact spectralValueSpecialZero00 c d
  · exact spectralValueSpecialZero01 c d
  · exact spectralValueSpecialZero02 c d
  · exact spectralValueSpecialZero10 c d
  · exact spectralValueSpecialZero11 c d
  · exact spectralValueSpecialZero12 c d
  · exact spectralValueSpecialZero20 c d
  · exact spectralValueSpecialZero21 c d
  · exact spectralValueSpecialZero22 c d
private lemma spectralValueSpecialTwo00 (c d : Fin 3) :
    normalizedR (2*L) (0,0) (c,d)=(sourceW*sourceWbarᵀ) (0,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,div_eq_mul_inv]  
private lemma spectralValueSpecialTwo01 (c d : Fin 3) :
    normalizedR (2*L) (0,1) (c,d)=(sourceW*sourceWbarᵀ) (0,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo02 (c d : Fin 3) :
    normalizedR (2*L) (0,2) (c,d)=(sourceW*sourceWbarᵀ) (0,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    phase_binding,div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo10 (c d : Fin 3) :
    normalizedR (2*L) (1,0) (c,d)=(sourceW*sourceWbarᵀ) (1,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo11 (c d : Fin 3) :
    normalizedR (2*L) (1,1) (c,d)=(sourceW*sourceWbarᵀ) (1,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    phase_binding,div_eq_mul_inv]  
private lemma spectralValueSpecialTwo12 (c d : Fin 3) :
    normalizedR (2*L) (1,2) (c,d)=(sourceW*sourceWbarᵀ) (1,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo20 (c d : Fin 3) :
    normalizedR (2*L) (2,0) (c,d)=(sourceW*sourceWbarᵀ) (2,0) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    phase_binding,div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo21 (c d : Fin 3) :
    normalizedR (2*L) (2,1) (c,d)=(sourceW*sourceWbarᵀ) (2,1) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,Fin.sum_univ_three,
    div_eq_mul_inv] <;> field_simp [hs] 
private lemma spectralValueSpecialTwo22 (c d : Fin 3) :
    normalizedR (2*L) (2,2) (c,d)=(sourceW*sourceWbarᵀ) (2,2) (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_two_angle
  have hs : phase≠0 := point_ne_zero _
  change normalizedR (2*Transfer.angle) _ _=_
  fin_cases c <;> fin_cases d <;>
    simp only [normalizedR,ha,hh,hv,hc,hd,Complex.ofReal_pow,sourceKappa_real]
  all_goals simp [sourceW,sourceWbar,Matrix.mul_apply,div_eq_mul_inv]  

theorem source_R_two : spectralR (2*L)=sourceW*sourceWbarᵀ := by
  rw [spectralR_normalized (2*L) Q_two_L_ne]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact spectralValueSpecialTwo00 c d
  · exact spectralValueSpecialTwo01 c d
  · exact spectralValueSpecialTwo02 c d
  · exact spectralValueSpecialTwo10 c d
  · exact spectralValueSpecialTwo11 c d
  · exact spectralValueSpecialTwo12 c d
  · exact spectralValueSpecialTwo20 c d
  · exact spectralValueSpecialTwo21 c d
  · exact spectralValueSpecialTwo22 c d
private lemma spectralValueSpecialB00 (c d : Fin 3) :
    normalizedR Reflection.b (0,0) (c,d)=sourceOmega (0,0)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,hc,sourceOmega,sourceOmegaBar,] 
private lemma spectralValueSpecialB01 (c d : Fin 3) :
    normalizedR Reflection.b (0,1) (c,d)=sourceOmega (0,1)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,ha,hv,sourceOmega,sourceOmegaBar,] 
private lemma spectralValueSpecialB02 (c d : Fin 3) :
    normalizedR Reflection.b (0,2) (c,d)=sourceOmega (0,2)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,hh,hc,hd,phase_binding,sourceOmega,sourceOmegaBar,hs,div_eq_mul_inv] ; ring
private lemma spectralValueSpecialB10 (c d : Fin 3) :
    normalizedR Reflection.b (1,0) (c,d)=sourceOmega (1,0)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,ha,hv,sourceOmega,sourceOmegaBar,] 
private lemma spectralValueSpecialB11 (c d : Fin 3) :
    normalizedR Reflection.b (1,1) (c,d)=sourceOmega (1,1)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,hh,phase_binding,sourceOmega,sourceOmegaBar,div_eq_mul_inv] 
private lemma spectralValueSpecialB12 (c d : Fin 3) :
    normalizedR Reflection.b (1,2) (c,d)=sourceOmega (1,2)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,ha,hv,sourceOmega,sourceOmegaBar,] 
private lemma spectralValueSpecialB20 (c d : Fin 3) :
    normalizedR Reflection.b (2,0) (c,d)=sourceOmega (2,0)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,hh,hc,hd,phase_binding,sourceOmega,sourceOmegaBar,hs] ; ring
private lemma spectralValueSpecialB21 (c d : Fin 3) :
    normalizedR Reflection.b (2,1) (c,d)=sourceOmega (2,1)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,ha,hv,sourceOmega,sourceOmegaBar,] 
private lemma spectralValueSpecialB22 (c d : Fin 3) :
    normalizedR Reflection.b (2,2) (c,d)=sourceOmega (2,2)*sourceOmegaBar (c,d) := by
  obtain ⟨ha,hh,hv,hc,hd⟩:=Transfer.special_bigAngle
  rw [bigAngle_binding] at ha hh hv hc hd
  have hs : phase≠0 := point_ne_zero _
  fin_cases c <;> fin_cases d <;>
    simp [normalizedR,hc,sourceOmega,sourceOmegaBar,] 

theorem source_R_b : spectralR b=fun p q=>sourceOmega p*sourceOmegaBar q := by
  rw [spectralR_normalized b Q_b_ne]
  ext ⟨a,b⟩ ⟨c,d⟩
  fin_cases a <;> fin_cases b
  · exact spectralValueSpecialB00 c d
  · exact spectralValueSpecialB01 c d
  · exact spectralValueSpecialB02 c d
  · exact spectralValueSpecialB10 c d
  · exact spectralValueSpecialB11 c d
  · exact spectralValueSpecialB12 c d
  · exact spectralValueSpecialB20 c d
  · exact spectralValueSpecialB21 c d
  · exact spectralValueSpecialB22 c d
end CriticalHoneycomb.Transfer.Reflection.Fusion

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix

lemma localBackward_with_swap (A : Local) (s t a b d e : Spin) :
    localBackward A (fun p q=>if p.1=q.2 then if p.2=q.1 then 1 else 0 else 0)
      s t (a,b) (d,e)=if e=s then A (a,b) (d,t) else 0 := by
  by_cases he : e=s
  · subst e
    simp [localBackward,block,Matrix.kronecker,Matrix.kroneckerMap,Matrix.sum_apply,Matrix.of_apply,mul_ite]
  · simp [localBackward,block,Matrix.kronecker,Matrix.kroneckerMap,Matrix.sum_apply,Matrix.of_apply,mul_ite,he,Ne.symm he]
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open scoped Matrix BigOperators

theorem row_range_factor (n : ℕ) (W : Matrix (Spin×Spin) Spin ℂ)
    (A B C : Fin n→Local)
    (hf : ∀ i s t,localBackward (A i) (B i) s t*W=W*block (C i) s t)
    (i : Fin n)
    (hi : ∀ s t,∃ F : Matrix Spin (Spin×Spin) ℂ,localBackward (A i) (B i) s t=W*F)
    (s t : Space n) :
    ∃ F : Matrix Spin (Spin×Spin) ℂ,backward n A B s t=W*F := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
    · obtain ⟨F,hF⟩:=hi (s 0) (t 0)
      refine ⟨F*backward n (Fin.tail A) (Fin.tail B) (Fin.tail s) (Fin.tail t),?_⟩
      rw [backward_succ,hF,Matrix.mul_assoc]
    · obtain ⟨F,hF⟩:=ih (Fin.tail A) (Fin.tail B) (Fin.tail C)
        (fun k=>hf k.succ) j hi (Fin.tail s) (Fin.tail t)
      refine ⟨block (C 0) (s 0) (t 0)*F,?_⟩
      rw [backward_succ,hF,←Matrix.mul_assoc,hf 0,Matrix.mul_assoc]

theorem row_quotient_factor (n : ℕ) (Z : Matrix Spin (Spin×Spin) ℂ)
    (A B C : Fin n→Local)
    (hf : ∀ i s t,Z*localForward (A i) (B i) s t=block (C i) s t*Z)
    (i : Fin n)
    (hi : ∀ s t,∃ F : Matrix (Spin×Spin) Spin ℂ,localForward (A i) (B i) s t=F*Z)
    (s t : Space n) :
    ∃ F : Matrix (Spin×Spin) Spin ℂ,forward n A B s t=F*Z := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ i with rfl|⟨j,rfl⟩
    · obtain ⟨F,hF⟩:=hi (s 0) (t 0)
      refine ⟨F*row n (Fin.tail C) (Fin.tail s) (Fin.tail t),?_⟩
      rw [forward_succ,hF,Matrix.mul_assoc,row_quotient_fusion n Z
        (Fin.tail A) (Fin.tail B) (Fin.tail C) (fun k=>hf k.succ),←Matrix.mul_assoc]
    · obtain ⟨F,hF⟩:=ih (Fin.tail A) (Fin.tail B) (Fin.tail C)
        (fun k=>hf k.succ) j hi (Fin.tail s) (Fin.tail t)
      refine ⟨localForward (A 0) (B 0) (s 0) (t 0)*F,?_⟩
      rw [forward_succ,hF,←Matrix.mul_assoc]
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open Reflection Reflection.Fusion
open scoped Matrix BigOperators
noncomputable def specialFinish (s t : Spin) : Matrix Spin Pair ℂ := fun j p=>
  if p.2=s then sourceWbar (p.1,t) j else 0

lemma local_first_node (s t : Spin) :
    localBackward (spectralR (2*L)) (spectralR 0) s t=sourceW*specialFinish s t := by
  rw [source_R_two,source_R_zero]
  ext ⟨a,b⟩ ⟨d,e⟩
  rw [show localBackward (sourceW*sourceWbarᵀ) swapR s t (a,b) (d,e)=
      if e=s then (sourceW*sourceWbarᵀ) (a,b) (d,t) else 0 from
    localBackward_with_swap (sourceW*sourceWbarᵀ) s t a b d e]
  by_cases he : e=s
  · simp [Matrix.mul_apply,specialFinish,he]
  · simp [Matrix.mul_apply,specialFinish,he]

theorem source_first_node_range (n : ℕ) (ξ : Fin n→ℝ) (i : Fin n) (u : ℝ)
    (hnode : u=L-ξ i)
    (hm : ∀ j,Q ((u-L)+ξ j)≠0) (hu : ∀ j,Q (u+ξ j)≠0)
    (hp : ∀ j,Q ((u+L)+ξ j)≠0) (s t : Space n) :
    ∃ F : Matrix Spin Pair ℂ,
      backward n (exactSites n ξ (u+L)) (exactSites n ξ (u-L)) s t=sourceW*F := by
  apply row_range_factor n sourceW (exactSites n ξ (u+L)) (exactSites n ξ (u-L))
    (exactSites n ξ u) ?_ i ?_ s t
  · intro j a b
    have em : (u+ξ j)-L=(u-L)+ξ j := by ring
    have ep : (u+ξ j)+L=(u+L)+ξ j := by ring
    simpa only [exactSites,em,ep] using local_source_fusion (u+ξ j)
      (by simpa only [em] using hm j) (hu j) (by simpa only [ep] using hp j) a b
  · intro a b
    refine ⟨specialFinish a b,?_⟩
    have em : (u-L)+ξ i=0 := by rw [hnode];ring
    have ep : (u+L)+ξ i=2*L := by rw [hnode];ring
    simpa only [exactSites,em,ep] using local_first_node a b
end CriticalHoneycomb.Transfer.RowExchange

end

section
namespace CriticalHoneycomb.Transfer.RowExchange
open Reflection Reflection.Fusion
open scoped Matrix BigOperators
lemma source_R_L (i j k l : Spin) :
    spectralR L (i,j) (k,l)=
      Reflection.phase^(spinValue k-spinValue i)*(sourceW*sourceWbarᵀ) (i.rev,l) (k.rev,j) := by
  have hh:=source_crossing (2*L) i j k l
  rw [show b-2*L=L by unfold b L;ring,source_R_two] at hh
  exact hh
lemma omegaBar_sum (d : Spin) (f : Spin→ℂ) :
    (∑ v,sourceOmegaBar (d,v)*f v)=Reflection.phase^(spinValue d)*f d.rev := by
  fin_cases d <;> simp [sourceOmegaBar,spinValue,Fin.sum_univ_three,Fin.rev]
noncomputable def secondFinish (s t : Spin) : Matrix Pair Spin ℂ := fun p j=>
  sourceOmega (p.1,s)*Reflection.phase^(spinValue j-spinValue p.2)*sourceW (p.2.rev,t) j.rev
lemma local_second_node_entry (s t a b d e : Spin) :
    localForward (spectralR Reflection.b) (spectralR L) s t (a,b) (d,e)=
      sourceOmega (a,s)*Reflection.phase^(spinValue d)*spectralR L (b,d.rev) (e,t) := by
  simp only [localForward,block,Matrix.sum_apply,Matrix.kronecker,
    Matrix.kroneckerMap,Matrix.of_apply,source_R_b]
  change (∑ v,sourceOmega (a,s)*sourceOmegaBar (d,v)*spectralR L (b,v) (e,t))=_
  calc
    _=sourceOmega (a,s)*(∑ v,sourceOmegaBar (d,v)*spectralR L (b,v) (e,t)) := by
      simp only [Finset.mul_sum,mul_assoc]
    _=_ := by rw [omegaBar_sum];ring

lemma local_second_node (s t : Spin) :
    localForward (spectralR b) (spectralR L) s t=secondFinish s t*sourceWbarᵀ := by
  ext ⟨a,b⟩ ⟨d,e⟩
  rw [local_second_node_entry,source_R_L]
  simp only [Matrix.mul_apply,Matrix.transpose_apply,secondFinish,Finset.mul_sum]
  calc
    (∑ j,sourceOmega (a,s)*Reflection.phase^(spinValue d)*
        (Reflection.phase^(spinValue e-spinValue b)*(sourceW (b.rev,t) j*sourceWbar (e.rev,d.rev) j)))=
      ∑ j,sourceOmega (a,s)*Reflection.phase^(spinValue j.rev-spinValue b)*sourceW (b.rev,t) j*
        sourceWbar (d,e) j.rev := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        _=sourceOmega (a,s)*sourceW (b.rev,t) j*
            (Reflection.phase^(spinValue d)*Reflection.phase^(spinValue e-spinValue b)*sourceWbar (e.rev,d.rev) j) := by ring
        _=sourceOmega (a,s)*sourceW (b.rev,t) j*
            (Reflection.phase^(spinValue j.rev-spinValue b)*sourceWbar (d,e) j.rev) := by
          rw [sourceWbar_crossing_phase]
        _=_ := by ring
    _=∑ j,sourceOmega (a,s)*Reflection.phase^(spinValue j-spinValue b)*sourceW (b.rev,t) j.rev*
        sourceWbar (d,e) j := by
      simpa only [Fin.rev_rev] using sum_fin_rev (fun j=>
        sourceOmega (a,s)*Reflection.phase^(spinValue j-spinValue b)*sourceW (b.rev,t) j.rev*sourceWbar (d,e) j)

theorem source_second_node_quotient (n : ℕ) (ξ : Fin n→ℝ) (i : Fin n) (u : ℝ)
    (hnode : u=L+ξ i)
    (hm : ∀ j,Q (((b-u)-L)+ξ j)≠0) (hu : ∀ j,Q ((b-u)+ξ j)≠0)
    (hp : ∀ j,Q (((b-u)+L)+ξ j)≠0) (s t : Space n) :
    ∃ F : Matrix Pair Spin ℂ,
      forward n (exactSites n ξ ((b-u)+L)) (exactSites n ξ ((b-u)-L)) s t=F*sourceWbarᵀ := by
  apply row_quotient_factor n sourceWbarᵀ (exactSites n ξ ((b-u)+L)) (exactSites n ξ ((b-u)-L))
    (exactSites n ξ (b-u)) ?_ i ?_ s t
  · intro j a c
    have em : ((b-u)+ξ j)-L=((b-u)-L)+ξ j := by ring
    have ep : ((b-u)+ξ j)+L=((b-u)+L)+ξ j := by ring
    simpa only [exactSites,em,ep] using local_source_quotient_fusion ((b-u)+ξ j)
      (by simpa only [em] using hm j) (hu j) (by simpa only [ep] using hp j) a c
  · intro a c
    refine ⟨secondFinish a c,?_⟩
    have em : ((b-u)-L)+ξ i=L := by rw [hnode];unfold b L;ring
    have ep : ((b-u)+L)+ξ i=b := by rw [hnode];ring
    simpa only [exactSites,em,ep] using local_second_node a c
end CriticalHoneycomb.Transfer.RowExchange

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection Reflection.Fusion RowExchange BoundaryJet ClosedFourRow FusionContraction
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
lemma first_node_projection (N : ℕ) (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ)
    (hnode : u=L-ξ i) (hm : ∀ j,Q ((u-L)+ξ j)≠0) (hu : ∀ j,Q (u+ξ j)≠0)
    (hp : ∀ j,Q ((u+L)+ξ j)≠0) (s t : Space N) :
    sourceW*sourceJ*backward N (exactSites N ξ (u+L)) (exactSites N ξ (u-L)) s t=
      backward N (exactSites N ξ (u+L)) (exactSites N ξ (u-L)) s t := by
  obtain ⟨F,hF⟩:=source_first_node_range N ξ i u hnode hm hu hp s t
  rw [hF]
  calc
    _=sourceW*(sourceJ*sourceW)*F := by simp only [Matrix.mul_assoc]
    _=_ := by rw [sourceJ_W,Matrix.mul_one]
lemma second_node_projection (N : ℕ) (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ)
    (hnode : u=L+ξ i) (hm : ∀ j,Q (((b-u)-L)+ξ j)≠0)
    (hu : ∀ j,Q ((b-u)+ξ j)≠0) (hp : ∀ j,Q (((b-u)+L)+ξ j)≠0)
    (s t : Space N) :
    forward N (exactSites N ξ ((b-u)+L)) (exactSites N ξ ((b-u)-L)) s t*
      sourceJᵀ*sourceWbarᵀ=
      forward N (exactSites N ξ ((b-u)+L)) (exactSites N ξ ((b-u)-L)) s t := by
  obtain ⟨F,hF⟩:=source_second_node_quotient N ξ i u hnode hm hu hp s t
  rw [hF]
  simp only [Matrix.mul_assoc,sourceWbar_J,Matrix.one_mul]
lemma JRow_fusion (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hm : ∀ j,Q ((u-L)+ξ j)≠0) (hu : ∀ j,Q (u+ξ j)≠0)
    (hp : ∀ j,Q ((u+L)+ξ j)≠0) (s t : Space N) :
    backwardPair (JRow N ξ (u+L)) (JRow N ξ (u-L)) s t*sourceW.map C=
      sourceW.map C*JRow N ξ u s t := by
  rw [backward_JRow]
  change _=sourceW.map C*(row N (exactSites N ξ u) s t).map C
  rw [←Matrix.map_mul,←Matrix.map_mul,source_row_fusion N ξ u hm hu hp]
lemma JRow_quotient_fusion (N : ℕ) (ξ : Fin N→ℝ) (u : ℝ)
    (hm : ∀ j,Q ((u-L)+ξ j)≠0) (hu : ∀ j,Q (u+ξ j)≠0)
    (hp : ∀ j,Q ((u+L)+ξ j)≠0) (s t : Space N) :
    sourceWbarᵀ.map C*forwardPair (JRow N ξ (u+L)) (JRow N ξ (u-L)) s t=
      JRow N ξ u s t*sourceWbarᵀ.map C := by
  rw [forward_JRow]
  change _=(row N (exactSites N ξ u) s t).map C*sourceWbarᵀ.map C
  rw [←Matrix.map_mul,←Matrix.map_mul,source_row_quotient_fusion N ξ u hm hu hp]

theorem closed_fusion_compression (N : ℕ) (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ)
    (hnode : u=L-ξ i ∨ u=L+ξ i) (hm : Nonsingular N ξ (u-L))
    (hp : Nonsingular N ξ (u+L)) (hu : Nonsingular N ξ u)
    (hQt : Q (2*u)≠0) (hQr : Q (2*(b-u))≠0) :
    close4 (matrixBoundary (markedFusionVector eL (2*(b-u)) ((b-u)+L) ((b-u)-L)))
      (matrixBoundary (markedFusionVector eR (2*u) (u-L) (u+L)))
      (pairAB (backwardPair (JRow N ξ (u+L)) (JRow N ξ (u-L)))*
        pairCD (forwardPair (JRow N ξ ((b-u)+L)) (JRow N ξ ((b-u)-L))))=T N ξ u := by
  have hpm : b-(u+L)=(b-u)-L := by ring
  have hmm : b-(u-L)=(b-u)+L := by ring
  have hmR : ∀ j,Q (((b-u)-L)+ξ j)≠0 := by
    intro j;simpa only [hpm] using (hp.2.2 j).2
  have hpR : ∀ j,Q (((b-u)+L)+ξ j)≠0 := by
    intro j;simpa only [hmm] using (hm.2.2 j).2
  have hrm : sine (gamma+((b-u)-L))≠0 := by simpa only [hpm] using hp.2.1
  have hrp : sine (gamma+((b-u)+L))≠0 := by simpa only [hmm] using hm.2.1
  have hL:=marked_fusion_left eL (by simpa only [pow_two] using eL_sq) (b-u)
    hQr hu.2.1 hrm hrp
  have hR:=marked_fusion_right eR (by simpa only [pow_two] using eR_sq) u hQt hu.1 hm.1 hp.1
  funext s t
  rw [close4_fusion_contract,T_closePair]
  change _=closePair (forwardPair (JRow N ξ u) (JRow N ξ (b-u)))
    (fun p=>wallMatrix eL (b-u) p.1 p.2) (fun p=>wallMatrix eR u p.1 p.2) s t
  rw [closePair_fusion_contract]
  apply Finset.sum_congr rfl;intro v hv
  have hF:=JRow_fusion N ξ u (fun j=>(hm.2.2 j).1) (fun j=>(hu.2.2 j).1)
    (fun j=>(hp.2.2 j).1) s v
  have hG:=JRow_quotient_fusion N ξ (b-u) hmR (fun j=>(hu.2.2 j).2) hpR v t
  rcases hnode with hn|hn
  · have hJ : sourceJ.map C*sourceW.map C=1 := by rw [←Matrix.map_mul,sourceJ_W,Matrix.map_one] <;> simp
    have hP : sourceW.map C*sourceJ.map C*
        backwardPair (JRow N ξ (u+L)) (JRow N ξ (u-L)) s v=
        backwardPair (JRow N ξ (u+L)) (JRow N ξ (u-L)) s v := by
      rw [backward_JRow,←Matrix.map_mul,←Matrix.map_mul]
      rw [first_node_projection N ξ i u hn (fun j=>(hm.2.2 j).1)
        (fun j=>(hu.2.2 j).1) (fun j=>(hp.2.2 j).1)]
    exact range_compression (sourceW.map C) (sourceJ.map C) (sourceWbarᵀ.map C)
      _ _ _ _ _ _ _ _ hJ hP hF hG hL hR
  · have hV : sourceWbarᵀ.map C*sourceJᵀ.map C=1 := by
      rw [←Matrix.map_mul,sourceWbar_J,Matrix.map_one] <;> simp
    have hQ : forwardPair (JRow N ξ ((b-u)+L)) (JRow N ξ ((b-u)-L)) v t*
        sourceJᵀ.map C*sourceWbarᵀ.map C=
        forwardPair (JRow N ξ ((b-u)+L)) (JRow N ξ ((b-u)-L)) v t := by
      rw [forward_JRow,←Matrix.map_mul,←Matrix.map_mul]
      rw [second_node_projection N ξ i u hn hmR (fun j=>(hu.2.2 j).2) hpR]
    exact quotient_compression (sourceW.map C) (sourceWbarᵀ.map C) (sourceJᵀ.map C)
      _ _ _ _ _ _ _ _ hV hQ hF hG hL hR
end CriticalHoneycomb.Transfer.SpectralFamily

end

section
namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection Reflection.Fusion RowExchange BoundaryJet ClosedFourRow
open scoped Matrix BigOperators
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem closed_fusion_generic (N : ℕ) (ξ : Fin N→ℝ) (i : Fin N) (u : ℝ)
    (hnode : u=L-ξ i ∨ u=L+ξ i) (hm : Nonsingular N ξ (u-L))
    (hp : Nonsingular N ξ (u+L)) (hu : Nonsingular N ξ u)
    (hQt : Q (2*u)≠0) (hQr : Q (2*(b-u))≠0) :
    T N ξ (u-L)*T N ξ (u+L)=T N ξ u := by
  have hpm : b-(u+L)=(b-u)-L := by ring
  have hmm : b-(u-L)=(b-u)+L := by ring
  have hd : Q (b-2*u)≠0 := by rw [reflected_Q];exact hQt
  have hnd : Q (-(b-2*u))≠0 := by
    rw [show -(b-2*u)=b-2*(b-u) by ring,reflected_Q]
    exact hQr
  have hGFc : (spectralR (-(b-2*u)))ᵀ*spectralR (b-2*u)=1 :=
    mul_eq_one_comm.mp (spectral_unitarity (b-2*u) hd hnd)
  have hGF : (spectralR (-(b-2*u)))ᵀ.map C*(spectralR (b-2*u)).map C=1 := by
    rw [←Matrix.map_mul,hGFc,Matrix.map_one] <;> simp
  have he : ∀ s t,(spectralR (b-2*u)).map C*
      forwardPair (JRow N ξ ((b-u)+L)) (JRow N ξ (u+L)) s t=
      backwardPair (JRow N ξ ((b-u)+L)) (JRow N ξ (u+L)) s t*(spectralR (b-2*u)).map C := by
    have hx : ((b-u)+L)-(u+L)=b-2*u := by ring
    have hr : ∀ j,Q (((b-u)+L)+ξ j)≠0 := by
      intro j;simpa only [hmm] using (hm.2.2 j).2
    simpa only [hx] using JRow_exchange N ξ ((b-u)+L) (u+L) hr
      (fun j=>(hp.2.2 j).1) (by simpa only [hx] using hd)
  rw [T_closePair,T_closePair,hpm,hmm]
  rw [middle_close (JRow N ξ (u+L)) (JRow N ξ (u-L))
    (JRow N ξ ((b-u)+L)) (JRow N ξ ((b-u)-L))
    ((spectralR (b-2*u)).map C) ((spectralR (-(b-2*u)))ᵀ.map C) hGF he]
  rw [marked_middle_left,marked_middle_right]
  exact closed_fusion_compression N ξ i u hnode hm hp hu hQt hQr
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection RowExchange BoundaryJet Filter Topology
open scoped Matrix BigOperators
lemma continuousAt_row_curve (N : ℕ) (Ξ : ℝ→Fin N→ℝ) (f : ℝ→ℝ) (x : ℝ)
    (hΞ : ∀ i,ContinuousAt (fun y=>Ξ y i) x) (hf : ContinuousAt f x)
    (hQ : ∀ i,Q (f x+Ξ x i)≠0) (s t : Space N) :
    ContinuousAt (fun y=>row N (exactSites N (Ξ y) (f y)) s t) x := by
  apply continuousAt_row
  intro i
  exact (continuousAt_spectralR _ (hQ i)).comp (f:=fun y=>f y+Ξ y i) (hf.add (hΞ i))
lemma continuousAt_bulkRows_curve (N : ℕ) (Ξ : ℝ→Fin N→ℝ) (f : ℝ→ℝ) (x : ℝ)
    (hΞ : ∀ i,ContinuousAt (fun y=>Ξ y i) x) (hf : ContinuousAt f x)
    (hns : Nonsingular N (Ξ x) (f x)) (s t : Space N) :
    ContinuousAt (fun y=>bulkRows N (Ξ y) (f y) s t) x := by
  apply continuousAt_pi.2;intro p
  apply continuousAt_pi.2;intro q
  unfold bulkRows forward
  simp only [Matrix.sum_apply]
  apply tendsto_finsetSum;intro v hv
  exact (matrix_entry_continuousAt (continuousAt_row_curve N Ξ f x hΞ hf
    (fun i=>(hns.2.2 i).1) s v) p.1 q.1).mul
      (matrix_entry_continuousAt (continuousAt_row_curve N Ξ (fun y=>b-f y) x hΞ
        (continuousAt_const.sub hf) (fun i=>(hns.2.2 i).2) v t) p.2 q.2)
lemma continuousAt_T_curve (N : ℕ) (Ξ : ℝ→Fin N→ℝ) (f : ℝ→ℝ) (x : ℝ)
    (hΞ : ∀ i,ContinuousAt (fun y=>Ξ y i) x) (hf : ContinuousAt f x)
    (hns : Nonsingular N (Ξ x) (f x)) :
    ContinuousAt (fun y=>T N (Ξ y) (f y)) x := by
  apply continuousAt_pi.2;intro s
  apply continuousAt_pi.2;intro t
  unfold T
  apply tendsto_finsetSum;intro p hp
  apply tendsto_finsetSum;intro q hq
  exact (((continuousAt_K eL (b-f x) hns.2.1 p).comp (f:=fun y=>b-f y)
    (continuousAt_const.sub hf)).mul
      (continuous_C.continuousAt.comp (matrix_entry_continuousAt
        (continuousAt_bulkRows_curve N Ξ f x hΞ hf hns s t) p q))).mul
          ((continuousAt_K eR (f x) hns.1 q).comp (f:=f) hf)
lemma eventually_nonsingular_curve (N : ℕ) (Ξ : ℝ→Fin N→ℝ) (f : ℝ→ℝ) (x : ℝ)
    (hΞ : ∀ i,ContinuousAt (fun y=>Ξ y i) x) (hf : ContinuousAt f x)
    (hns : Nonsingular N (Ξ x) (f x)) :
    ∀ᶠ y in 𝓝 x,Nonsingular N (Ξ y) (f y) := by
  have h0 := (continuous_sine.continuousAt.comp (continuousAt_const.add hf)).eventually_ne hns.1
  have h1 := (continuous_sine.continuousAt.comp
    (continuousAt_const.add (continuousAt_const.sub hf))).eventually_ne hns.2.1
  have h2 : ∀ᶠ y in 𝓝 x,∀ i,Q (f y+Ξ y i)≠0 ∧ Q ((b-f y)+Ξ y i)≠0 := by
    apply Filter.eventually_all.2;intro i
    exact ((continuous_Q.continuousAt.comp (hf.add (hΞ i))).eventually_ne (hns.2.2 i).1).and
      ((continuous_Q.continuousAt.comp ((continuousAt_const.sub hf).add (hΞ i))).eventually_ne
        (hns.2.2 i).2)
  exact h0.and (h1.and h2)
lemma dense_fusion_regular : Dense {u : ℝ|Q (2*u)≠0 ∧ Q (2*(b-u))≠0} := by
  have h0:=Q_zero_countable.preimage (f:=fun u : ℝ=>2*u) (fun x y h=>by linarith)
  have h1:=Q_zero_countable.preimage (f:=fun u : ℝ=>2*(b-u)) (fun x y h=>by linarith)
  have hd:=(h0.union h1).dense_compl ℝ
  convert hd using 1
  ext u
  simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_preimage,Set.mem_ofPred_eq]
  tauto
end CriticalHoneycomb.Transfer.SpectralFamily

end

section

namespace CriticalHoneycomb.Transfer.SpectralFamily
open Reflection BoundaryJet Filter Topology
open scoped Matrix BigOperators
lemma fusion_along_nodes (N : ℕ) (Ξ : ℝ→Fin N→ℝ) (i : Fin N) (x : ℝ)
    (hΞ : ∀ j,ContinuousAt (fun y=>Ξ y j) x)
    (hnode : ∀ y,y=L-Ξ y i ∨ y=L+Ξ y i)
    (hm : Nonsingular N (Ξ x) (x-L)) (hp : Nonsingular N (Ξ x) (x+L))
    (hu : Nonsingular N (Ξ x) x) :
    T N (Ξ x) (x-L)*T N (Ξ x) (x+L)=T N (Ξ x) x := by
  let D : Set ℝ := {y | Q (2*y)≠0 ∧ Q (2*(b-y))≠0}
  have hd : Dense D := dense_fusion_regular
  have : Filter.NeBot (𝓝[D] x) := mem_closure_iff_nhdsWithin_neBot.mp (hd x)
  have cm := continuousAt_T_curve N Ξ (fun y=>y-L) x hΞ
    (continuousAt_id.sub continuousAt_const) hm
  have cp := continuousAt_T_curve N Ξ (fun y=>y+L) x hΞ
    (continuousAt_id.add continuousAt_const) hp
  have cu := continuousAt_T_curve N Ξ id x hΞ continuousAt_id hu
  have hf : Tendsto (fun y=>T N (Ξ y) (y-L)*T N (Ξ y) (y+L)) (𝓝[D] x)
      (𝓝 (T N (Ξ x) (x-L)*T N (Ξ x) (x+L))) :=
    (cm.mul cp).mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun y=>T N (Ξ y) y) (𝓝[D] x) (𝓝 (T N (Ξ x) x)) :=
    cu.mono_left nhdsWithin_le_nhds
  have he : (fun y=>T N (Ξ y) (y-L)*T N (Ξ y) (y+L)) =ᶠ[𝓝[D] x]
      (fun y=>T N (Ξ y) y) := by
    have hmem : ∀ᶠ y in 𝓝[D] x,y∈D := self_mem_nhdsWithin
    have em := (eventually_nonsingular_curve N Ξ (fun y=>y-L) x hΞ
      (continuousAt_id.sub continuousAt_const) hm).filter_mono (nhdsWithin_le_nhds (s:=D))
    have ep := (eventually_nonsingular_curve N Ξ (fun y=>y+L) x hΞ
      (continuousAt_id.add continuousAt_const) hp).filter_mono (nhdsWithin_le_nhds (s:=D))
    have eu := (eventually_nonsingular_curve N Ξ id x hΞ continuousAt_id hu).filter_mono
      (nhdsWithin_le_nhds (s:=D))
    filter_upwards [hmem,em,ep,eu] with y hy hym hyp hyu
    exact closed_fusion_generic N (Ξ y) i y (hnode y) hym hyp hyu hy.1 hy.2
  exact tendsto_nhds_unique_of_eventuallyEq hf hg he

theorem source_global_spectral_fusion : GlobalSpectralFusion := by
  intro N ξ i u hnode hm hp hu
  rcases hnode with hn|hn
  · let Ξ : ℝ→Fin N→ℝ := fun y j=>ξ j+(u-y)
    have hx : Ξ u=ξ := by funext j;simp [Ξ]
    have hy : ∀ y,y=L-Ξ y i ∨ y=L+Ξ y i := by
      intro y;left;dsimp [Ξ];linarith
    simpa only [hx] using fusion_along_nodes N Ξ i u
      (fun j=>continuousAt_const.add (continuousAt_const.sub continuousAt_id)) hy
      (by simpa only [hx] using hm) (by simpa only [hx] using hp) (by simpa only [hx] using hu)
  · let Ξ : ℝ→Fin N→ℝ := fun y j=>ξ j+(y-u)
    have hx : Ξ u=ξ := by funext j;simp [Ξ]
    have hy : ∀ y,y=L-Ξ y i ∨ y=L+Ξ y i := by
      intro y;right;dsimp [Ξ];linarith
    simpa only [hx] using fusion_along_nodes N Ξ i u
      (fun j=>continuousAt_const.add (continuousAt_id.sub continuousAt_const)) hy
      (by simpa only [hx] using hm) (by simpa only [hx] using hp) (by simpa only [hx] using hu)
end CriticalHoneycomb.Transfer.SpectralFamily

end

end OAI
