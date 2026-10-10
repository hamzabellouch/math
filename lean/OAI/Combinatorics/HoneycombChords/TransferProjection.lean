import OAI.Combinatorics.HoneycombChords.ColumnPositivity
import OAI.Combinatorics.HoneycombChords.PlanarRows
import OAI.Combinatorics.HoneycombChords.SpectralRows

namespace OAI

/-! Transfer projection for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization PhysicalTiles Filter Topology
open scoped Matrix
noncomputable def columnDelta {n : ℕ} (east : Column n) : DiluteState :=
  fun xs=>if xs=List.ofFn (fun j=>spinEquiv.symm (east j)) then 1 else 0
lemma columnDelta_vector {n : ℕ} (east : Column n) :
    columnVector n (columnDelta east)=(fun west=>if west=east then 1 else 0) := by
  classical
  funext west
  have he : List.ofFn (fun j=>spinEquiv.symm (west j))=
      List.ofFn (fun j=>spinEquiv.symm (east j)) ↔ west=east := by
    rw [List.ofFn_injective.eq_iff]
    constructor
    · intro h
      funext j
      exact spinEquiv.symm.injective (congrFun h j)
    · rintro rfl
      rfl
  simp [columnVector,columnDelta,he]

noncomputable def physicalDoubleMatrix (n : ℕ) : Matrix (Column n) (Column n) ℂ :=
  fun west east=>hardDoubleRow physicalWeights n (columnDelta east)
    (List.ofFn (fun j=>spinEquiv.symm (west j)))
lemma physicalDoubleMatrix_eq (n : ℕ) : physicalDoubleMatrix n=rowTransfer n^2 := by
  classical
  ext west east
  have hh:=congrFun (column_pow_mulVec n 2 (columnDelta east)) west
  rw [columnDelta_vector] at hh
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hh
  change _ = (columnKernel n 1 1^2) west east
  rw [hh]
  unfold physicalDoubleMatrix columnVector
  rw [hardDoubleRow_eq_columns physicalWeights n _ _ (by simp)]
  rfl

theorem physical_double_rank_one (W : ℕ) :
    Tendsto (fun m=>physicalDoubleMatrix (W+1)^m) atTop (𝓝 (archProjection W)) := by
  rw [physicalDoubleMatrix_eq]
  have ht : Tendsto (fun m : ℕ=>2*m) atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_id
    intro m
    dsimp
    omega
  simpa only [Function.comp_def,pow_mul] using (physical_matrix_limit W).comp ht
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PhysicalTiles Filter Topology
open scoped Matrix
lemma projection_mul_double (W : ℕ) :
    archProjection W*physicalDoubleMatrix (W+1)=archProjection W := by
  rw [physicalDoubleMatrix_eq,pow_two,←mul_assoc,projection_mul_transfer,projection_mul_transfer]
lemma double_mul_projection (W : ℕ) :
    physicalDoubleMatrix (W+1)*archProjection W=archProjection W := by
  rw [physicalDoubleMatrix_eq,pow_two,mul_assoc,transfer_mul_projection,transfer_mul_projection]
lemma double_vector_limit (W : ℕ) (v : Column (W+1)→ℂ) :
    Tendsto (fun H=>(physicalDoubleMatrix (W+1)^H).mulVec v) atTop
      (𝓝 ((archProjection W).mulVec v)) := by
  apply tendsto_pi_nhds.mpr
  intro s
  apply tendsto_finsetSum
  intro n hn
  exact ((tendsto_pi_nhds.mp ((tendsto_pi_nhds.mp (physical_double_rank_one W)) s)) n).mul_const (v n)
lemma double_fixed_projected (W : ℕ) (v : Column (W+1)→ℂ)
    (hv : (physicalDoubleMatrix (W+1)).mulVec v=v) : (archProjection W).mulVec v=v := by
  have hi : ∀ H,(physicalDoubleMatrix (W+1)^H).mulVec v=v := by
    intro H
    induction H with
    | zero => simp
    | succ H ih => rw [pow_succ',←Matrix.mulVec_mulVec,ih,hv]
  have hl:=double_vector_limit W v
  simp_rw [hi] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds
noncomputable def gapMatrix (W : ℕ) : Matrix (Column (W+1)) (Column (W+1)) ℂ :=
  1-physicalDoubleMatrix (W+1)+archProjection W
lemma projection_mul_gap (W : ℕ) : archProjection W*gapMatrix W=archProjection W := by
  simp [gapMatrix,mul_add,mul_sub,projection_mul_double,projection_idempotent]
lemma gap_kernel (W : ℕ) (v : Column (W+1)→ℂ)
    (hv : (gapMatrix W).mulVec v=0) : v=0 := by
  have hp : (archProjection W).mulVec v=0 := by
    rw [←projection_mul_gap W,←Matrix.mulVec_mulVec,hv,Matrix.mulVec_zero]
  have hc : (physicalDoubleMatrix (W+1)).mulVec v=v := by
    simp only [gapMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,hp,add_zero] at hv
    exact (sub_eq_zero.mp hv).symm
  rw [←double_fixed_projected W v hc,hp]

theorem physical_gap_det_ne_zero (W : ℕ) : (gapMatrix W).det≠0 := by
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w h
  apply sub_eq_zero.mp
  apply gap_kernel W
  rw [Matrix.mulVec_sub,h,sub_self]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.PlanarNormalization
open scoped Matrix
lemma planarRow_smul (i : ℕ) (ts : List TileWeights) (z : ℂ) (f : DiluteState) :
    planarRow i ts (fun xs=>z*f xs)=(fun xs=>z*planarRow i ts f xs) := by
  induction ts generalizing i f with
  | nil => rfl
  | cons t ts ih => simp only [planarRow,act_smul,ih]
lemma planarRow_add (i : ℕ) (ts : List TileWeights) (f g : DiluteState) :
    planarRow i ts (fun xs=>f xs+g xs)=(fun xs=>planarRow i ts f xs+planarRow i ts g xs) := by
  induction ts generalizing i f g with
  | nil => rfl
  | cons t ts ih => simp only [planarRow,act_add,ih]
noncomputable def fixedSeed (a : Spin) (f : DiluteState) : DiluteState
  | b::xs => if b=a then f xs else 0
  | [] => 0
noncomputable def fixedColumn (t : TileWeights) (n : ℕ) (s z : Spin) (f : DiluteState) : DiluteState :=
  fun xs=>planarRow 0 (List.replicate n t) (fixedSeed s f) (xs++[z])
lemma fixedColumn_eq_kernel (t : TileWeights) (n : ℕ) (south north : Spin)
    (f : DiluteState) (west : Fin n→Spin) :
    fixedColumn t n south north f (List.ofFn west)=
      ∑ east : Fin n→Spin,columnKernelSpin t n south north west east*f (List.ofFn east) := by
  classical
  unfold fixedColumn
  rw [planarRow_eq_columnContraction]
  unfold columnContraction columnKernelSpin
  apply Finset.sum_congr rfl
  intro east heast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro vertical hvertical
  simp only [fixedSeed]
  split_ifs <;> simp_all
lemma fixedColumn_none (t : TileWeights) (n : ℕ) (f : DiluteState) :
    fixedColumn t n none none f=vacuumColumn t n f := by
  have he : fixedSeed none f=addOne f := by
    funext xs
    cases xs with
    | nil => rfl
    | cons a xs => cases a <;> rfl
  unfold fixedColumn vacuumColumn removeOne
  rw [he]

lemma fixed_double_columns (t : TileWeights) (n : ℕ) (f : DiluteState)
    (s₁ s₂ z₁ z₂ : Spin) (xs : List Spin) (hx : xs.length=n) :
    sourceTwoRows (List.replicate n t) (List.replicate n t)
      (fixedSeed s₁ (fixedSeed s₂ f)) (z₁::z₂::xs)=
      fixedColumn t n s₁ z₁ (fixedColumn t n s₂ z₂ f) xs := by
  rw [←two_rows_eq (List.replicate n t) (List.replicate n t) (by simp) (by simp) _ xs hx z₁ z₂]
  rw [show xs++[z₁,z₂]=(xs++[z₁])++[z₂] by simp]
  rw [planarRow_suffix 0 _ _ (xs++[z₁]) [z₂] (by simp [hx])]
  unfold fixedColumn
  apply planarRow_congr_of_length 0 (n+1) _ _ _ _ _ (by simp [hx])
  intro ys hy
  cases ys with
  | nil => simp at hy
  | cons a ys =>
    simp only [List.cons_append,planarRow_under,fixedSeed]
    by_cases ha : a=s₁
    · subst a
      simp only [ite_true]
      rfl
    · simp only [ha,ite_false]
      exact congrFun (planarRow_zero 0 (List.replicate n t)) (ys++[z₂])
end CriticalHoneycomb.Transfer.PlanarNormalization
namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization
open scoped Matrix
lemma fixed_column_mulVec (H : ℕ) (south north : PlanarNormalization.Spin) (f : DiluteState) :
    (columnKernel H (spinEquiv south) (spinEquiv north)).mulVec (columnVector H f)=
      columnVector H (fixedColumn physicalWeights H south north f) := by
  classical
  funext w
  obtain ⟨west,rfl⟩ := (columnSpinEquiv H).surjective w
  simp only [columnVector,columnSpinEquiv_apply,Equiv.symm_apply_apply]
  rw [fixedColumn_eq_kernel]
  unfold Matrix.mulVec dotProduct
  rw [←(columnSpinEquiv H).sum_comp]
  apply Finset.sum_congr rfl
  intro east heast
  change columnKernel H (spinEquiv south) (spinEquiv north)
    (columnSpinEquiv H west) (columnSpinEquiv H east) * _ = _
  rw [columnKernel_eq_spin]
  change _ * f (List.ofFn (fun j => spinEquiv.symm (spinEquiv (east j)))) = _
  simp only [Equiv.symm_apply_apply]
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet
open scoped Matrix
noncomputable def markedColumn (H : ℕ) : Matrix (Column H) (Column H) Jet :=
  fun w e=>form (columnKernel H 1 1 w e) (columnKernel H 2 1 w e)
    (columnKernel H 1 2 w e) (columnKernel H 2 2 w e)
noncomputable def boundaryProduct (H m : ℕ) (south north : Column m) : Matrix (Column H) (Column H) ℂ :=
  (List.ofFn (fun i=>columnKernel H (south i) (north i))).prod
lemma boundaryProduct_zero (H : ℕ) (s n : Column 0) : boundaryProduct H 0 s n=1 := rfl
lemma boundaryProduct_cons (H m : ℕ) (a b : Fin 3) (s n : Column m) :
    boundaryProduct H (m+1) (Fin.cons a s) (Fin.cons b n)=
      columnKernel H a b*boundaryProduct H m s n := by
  simp [boundaryProduct,List.ofFn_succ]
lemma vacuum_cons (m : ℕ) : (fun _ : Fin (m+1)=> (1:Fin 3))=Fin.cons 1 (fun _ : Fin m=>1) := by
  ext i
  cases i using Fin.cases <;> rfl
lemma singleColumn_zero (m : ℕ) : singleColumn (0:Fin (m+1))=Fin.cons 2 (fun _ : Fin m=>1) := by
  ext i
  cases i using Fin.cases <;> simp [singleColumn]
lemma singleColumn_succ {m : ℕ} (j : Fin m) : singleColumn j.succ=Fin.cons 1 (singleColumn j) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [singleColumn,Ne.symm (Fin.succ_ne_zero j)]
  | succ i => simp [singleColumn]
noncomputable def portSumLeft (H m : ℕ) : Matrix (Column H) (Column H) ℂ :=
  ∑ j : Fin m,boundaryProduct H m (singleColumn j) (fun _=>1)
noncomputable def portSumRight (H m : ℕ) : Matrix (Column H) (Column H) ℂ :=
  ∑ j : Fin m,boundaryProduct H m (fun _=>1) (singleColumn j)
noncomputable def portSumBoth (H m : ℕ) : Matrix (Column H) (Column H) ℂ :=
  ∑ j : Fin m,∑ k : Fin m,boundaryProduct H m (singleColumn j) (singleColumn k)
lemma boundaryProduct_vacuum (H m : ℕ) : boundaryProduct H m (fun _=>1) (fun _=>1)=rowTransfer H^m := by
  simp [boundaryProduct,rowTransfer,List.ofFn_const,List.prod_replicate]
lemma portSumLeft_succ (H m : ℕ) : portSumLeft H (m+1)=
    columnKernel H 2 1*rowTransfer H^m+rowTransfer H*portSumLeft H m := by
  simp only [portSumLeft,Fin.sum_univ_succ,singleColumn_zero,singleColumn_succ,vacuum_cons m,
    boundaryProduct_cons,boundaryProduct_vacuum,←Finset.mul_sum,rowTransfer]
lemma portSumRight_succ (H m : ℕ) : portSumRight H (m+1)=
    columnKernel H 1 2*rowTransfer H^m+rowTransfer H*portSumRight H m := by
  simp only [portSumRight,Fin.sum_univ_succ,singleColumn_zero,singleColumn_succ,vacuum_cons m,
    boundaryProduct_cons,boundaryProduct_vacuum,←Finset.mul_sum,rowTransfer]
lemma portSumBoth_succ (H m : ℕ) : portSumBoth H (m+1)=
    columnKernel H 2 2*rowTransfer H^m+columnKernel H 2 1*portSumRight H m+
    columnKernel H 1 2*portSumLeft H m+rowTransfer H*portSumBoth H m := by
  simp only [portSumBoth,Fin.sum_univ_succ,singleColumn_zero,singleColumn_succ,
    boundaryProduct_cons,boundaryProduct_vacuum,Finset.sum_add_distrib,←Finset.mul_sum,
    portSumLeft,portSumRight,rowTransfer]
  abel
lemma marked_power_coords (H m : ℕ) :
    (fun w e=>base ((markedColumn H^m) w e))=rowTransfer H^m ∧
    (fun w e=>left ((markedColumn H^m) w e))=portSumLeft H m ∧
    (fun w e=>right ((markedColumn H^m) w e))=portSumRight H m ∧
    (fun w e=>both ((markedColumn H^m) w e))=portSumBoth H m := by
  classical
  induction m with
  | zero =>
    simp only [pow_zero,portSumLeft,portSumRight,portSumBoth,Fin.sum_univ_zero]
    constructor
    · ext w e
      by_cases h:w=e <;> simp [Matrix.one_apply,h,base]
    constructor
    · ext w e
      by_cases h:w=e <;> simp [Matrix.one_apply,h,left]
    constructor
    · ext w e
      by_cases h:w=e <;> simp [Matrix.one_apply,h,right]
    · ext w e
      by_cases h:w=e <;> simp [Matrix.one_apply,h,both]
  | succ m ih =>
    rcases ih with ⟨h₀,h₁,h₂,h₃⟩
    have e₀ w e : base ((markedColumn H^m) w e)=(rowTransfer H^m) w e := congrFun (congrFun h₀ w) e
    have e₁ w e : left ((markedColumn H^m) w e)=portSumLeft H m w e := congrFun (congrFun h₁ w) e
    have e₂ w e : right ((markedColumn H^m) w e)=portSumRight H m w e := congrFun (congrFun h₂ w) e
    have e₃ w e : both ((markedColumn H^m) w e)=portSumBoth H m w e := congrFun (congrFun h₃ w) e
    simp only [pow_succ',portSumLeft_succ,portSumRight_succ,portSumBoth_succ]
    refine ⟨?_,?_,?_,?_⟩ <;> ext w e
    · simp only [Matrix.mul_apply,base_sum,base_mul,markedColumn,base_form,e₀,rowTransfer]
    · simp only [Matrix.mul_apply,left_sum,left_mul,markedColumn,base_form,left_form,e₀,e₁,
        Finset.sum_add_distrib,Matrix.add_apply,rowTransfer]
      ac_rfl
    · simp only [Matrix.mul_apply,right_sum,right_mul,markedColumn,base_form,right_form,e₀,e₂,
        Finset.sum_add_distrib,Matrix.add_apply,rowTransfer]
      ac_rfl
    · simp only [Matrix.mul_apply,both_sum,both_mul,markedColumn,base_form,left_form,right_form,
        both_form,e₀,e₁,e₂,e₃,Finset.sum_add_distrib,Matrix.add_apply,rowTransfer]
      ac_rfl

theorem marked_power_mixed (H m : ℕ) (w e : Column H) :
    both ((markedColumn H^m) w e)=∑ j : Fin m,∑ k : Fin m,
      prescribedPartition m H w e (singleColumn j) (singleColumn k) := by
  have hh:=congrFun (congrFun (marked_power_coords H m).2.2.2 w) e
  simpa only [portSumBoth,Matrix.sum_apply,prescribedPartition_eq_transfer,boundaryProduct] using hh
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open PlanarNormalization BoundaryJet
open scoped Matrix

noncomputable def fixedDoubleMatrix (H : ℕ) (s₁ s₂ z₁ z₂ : Spin) :
    Matrix (Column H) (Column H) ℂ := fun west east=>
  sourceTwoRows (List.replicate H physicalWeights) (List.replicate H physicalWeights)
    (fixedSeed s₁ (fixedSeed s₂ (columnDelta east)))
    (z₁::z₂::List.ofFn (fun j=>spinEquiv.symm (west j)))
lemma fixedDoubleMatrix_eq (H : ℕ) (s₁ s₂ z₁ z₂ : Spin) :
    fixedDoubleMatrix H s₁ s₂ z₁ z₂=
      columnKernel H (spinEquiv s₁) (spinEquiv z₁)*
      columnKernel H (spinEquiv s₂) (spinEquiv z₂) := by
  classical
  funext west east
  have hh:=congrFun (fixed_column_mulVec H s₁ z₁
    (fixedColumn physicalWeights H s₂ z₂ (columnDelta east))) west
  rw [←fixed_column_mulVec H s₂ z₂,columnDelta_vector,Matrix.mulVec_mulVec] at hh
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true] at hh
  rw [hh]
  unfold fixedDoubleMatrix columnVector
  exact fixed_double_columns _ _ _ _ _ _ _ _ (by simp)

noncomputable def physicalMarkedK (e : Jet) : Spin→Spin→Jet
  | none,none => 1
  | some true,none => e
  | none,some true => e
  | _,_ => 0

noncomputable def markedDoubleMatrix (H : ℕ) : Matrix (Column H) (Column H) Jet :=
  fun west east=>∑ s₁ : Spin,∑ s₂ : Spin,∑ z₁ : Spin,∑ z₂ : Spin,
    physicalMarkedK eL s₁ s₂*physicalMarkedK eR z₁ z₂*
      C (fixedDoubleMatrix H s₁ s₂ z₁ z₂ west east)
lemma markedDoubleMatrix_eq (H : ℕ) : markedDoubleMatrix H=markedColumn H^2 := by
  classical
  funext west east
  simp only [markedDoubleMatrix,Fintype.sum_option,Fintype.sum_bool,physicalMarkedK,
    zero_mul,mul_zero,one_mul,add_zero,fixedDoubleMatrix_eq,spinEquiv_apply,spinIndex,
    Matrix.mul_apply,map_sum,pow_two]
  have bL : base eL=0 := rfl
  have lL : left eL=1 := rfl
  have rL : right eL=0 := rfl
  have xL : both eL=0 := rfl
  have bR : base eR=0 := rfl
  have lR : left eR=0 := rfl
  have rR : right eR=1 := rfl
  have xR : both eR=0 := rfl
  apply jet_ext <;>
    simp only [base_add,left_add,right_add,both_add,base_mul,left_mul,right_mul,both_mul,
      base_sum,left_sum,right_sum,both_sum,base_C,left_C,right_C,both_C,
      markedColumn,base_form,left_form,right_form,both_form,
      bL,lL,rL,xL,bR,lR,rR,xR,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,
      Finset.sum_add_distrib] <;>
    try simp only [zero_add,add_zero,Finset.sum_const_zero]
  all_goals abel
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open Filter Topology
open scoped Matrix

def spinCharge (i : Fin 3) : ℤ := (i.val:ℤ)-1
def columnCharge {H : ℕ} (s : Column H) : ℤ := ∑ j,spinCharge (s j)
lemma sourceR_charge (a h v c d : ℂ) (w n s e : Fin 3)
    (hz : Planar.sourceR a h v c d (n,w) (s,e)≠0) :
    spinCharge w+spinCharge n=spinCharge s+spinCharge e := by
  fin_cases w <;> fin_cases n <;> fin_cases s <;> fin_cases e <;>
    simp_all [Planar.sourceR,spinCharge]
lemma columnKernel_charge {H : ℕ} (s n : Fin 3) (w e : Column H)
    (hz : columnKernel H s n w e≠0) :
    columnCharge w+spinCharge n=columnCharge e+spinCharge s := by
  classical
  obtain ⟨vertical,_,hv⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
  have hs : (Fin.snoc (α:=fun _=>Fin 3) vertical n) 0=s := by
    by_contra hn
    simp [hn] at hv
  have hp : columnProduct w e vertical n≠0 := by simpa [hs] using hv
  have hl : ∀ j : Fin H,spinCharge (w j)+spinCharge ((Fin.snoc (α:=fun _=>Fin 3) vertical n) j.succ)=
      spinCharge (vertical j)+spinCharge (e j) := by
    intro j
    apply sourceR_charge
    exact (Finset.prod_ne_zero_iff.mp hp) j (Finset.mem_univ j)
  have hadd:=congrArg (fun f : Fin H→ℤ=>∑ j,f j) (funext hl)
  simp only [Finset.sum_add_distrib] at hadd
  have ha:=Fin.sum_univ_succ (fun j : Fin (H+1)=>spinCharge ((Fin.snoc (α:=fun _=>Fin 3) vertical n) j))
  have hb:=Fin.sum_univ_castSucc (fun j : Fin (H+1)=>spinCharge ((Fin.snoc (α:=fun _=>Fin 3) vertical n) j))
  simp only [Fin.snoc_castSucc,Fin.snoc_last] at hb
  rw [hs] at ha
  unfold columnCharge
  omega

def HasShift {H : ℕ} (M : Matrix (Column H) (Column H) ℂ) (q : ℤ) : Prop :=
  ∀ w e,M w e≠0→columnCharge w=columnCharge e+q
lemma kernel_hasShift (H : ℕ) (s n : Fin 3) :
    HasShift (columnKernel H s n) (spinCharge s-spinCharge n) := by
  intro w e hz
  have hh:=columnKernel_charge s n w e hz
  omega
lemma shift_mul {H : ℕ} {M N : Matrix (Column H) (Column H) ℂ} {q r : ℤ}
    (hM : HasShift M q) (hN : HasShift N r) : HasShift (M*N) (q+r) := by
  classical
  intro w e hz
  obtain ⟨s,_,hs⟩:=Finset.exists_ne_zero_of_sum_ne_zero hz
  have hm:=hM w s (mul_ne_zero_iff.mp hs).1
  have hn:=hN s e (mul_ne_zero_iff.mp hs).2
  omega
lemma shift_add {H : ℕ} {M N : Matrix (Column H) (Column H) ℂ} {q : ℤ}
    (hM : HasShift M q) (hN : HasShift N q) : HasShift (M+N) q := by
  intro w e hz
  by_cases hm : M w e=0
  · apply hN
    intro hn
    exact hz (by simp [Matrix.add_apply,hm,hn])
  · exact hM w e hm
lemma transfer_power_shift (H m : ℕ) : HasShift (rowTransfer H^m) 0 := by
  classical
  induction m with
  | zero =>
    intro w e hz
    have he : w=e := by
      by_contra hn
      simp [pow_zero,hn] at hz
    subst e
    simp
  | succ m ih =>
    rw [pow_succ']
    simpa [rowTransfer,spinCharge] using shift_mul (kernel_hasShift H 1 1) ih
@[simp] lemma charge_vacuum (H : ℕ) : columnCharge (fun _ : Fin H=>1)=0 := by
  simp [columnCharge,spinCharge]
lemma archColumn_charge {W : ℕ} (s : Column (W+1)) (hs : columnCharge s≠0) : archColumn W s=0 := by
  have hz : ∀ m,(rowTransfer (W+1)^m) s (fun _=>1)=0 := by
    intro m
    by_contra hn
    have hh:=transfer_power_shift (W+1) m s (fun _=>1) hn
    simp only [charge_vacuum,add_zero] at hh
    exact hs hh
  have hl:=archColumn_limit W s
  simp only [hz] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds
lemma archRow_charge {W : ℕ} (s : Column (W+1)) (hs : columnCharge s≠0) : archRow W s=0 := by
  have hz : ∀ m,(rowTransfer (W+1)^m) (fun _=>1) s=0 := by
    intro m
    by_contra hn
    have hh:=transfer_power_shift (W+1) m (fun _=>1) s hn
    simp only [charge_vacuum,add_zero] at hh
    exact hs hh.symm
  have hl:=archRow_limit W s
  simp only [hz] at hl
  exact tendsto_nhds_unique hl tendsto_const_nhds
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
