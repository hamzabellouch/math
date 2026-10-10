import OAI.Combinatorics.HoneycombChords.TransferProjection

namespace OAI

/-! Boundary expansion for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet
open scoped Matrix
noncomputable def markedLeft (H : ℕ) : Matrix (Column H) (Column H) ℂ :=
  fun w e=>left (markedDoubleMatrix H w e)
noncomputable def markedRight (H : ℕ) : Matrix (Column H) (Column H) ℂ :=
  fun w e=>right (markedDoubleMatrix H w e)
noncomputable def markedMixed (H : ℕ) : Matrix (Column H) (Column H) ℂ :=
  fun w e=>both (markedDoubleMatrix H w e)
lemma marked_base (H : ℕ) :
    (fun w e=>base (markedDoubleMatrix H w e))=physicalDoubleMatrix H := by
  rw [markedDoubleMatrix_eq,physicalDoubleMatrix_eq]
  exact (marked_power_coords H 2).1
lemma markedLeft_eq (H : ℕ) : markedLeft H=
    rowTransfer H*columnKernel H 2 1+columnKernel H 2 1*rowTransfer H := by
  funext w e
  simp only [markedLeft,markedDoubleMatrix_eq,pow_two,Matrix.mul_apply,left_sum,left_mul,
    markedColumn,base_form,left_form,Finset.sum_add_distrib,Matrix.add_apply,rowTransfer]
lemma markedRight_eq (H : ℕ) : markedRight H=
    rowTransfer H*columnKernel H 1 2+columnKernel H 1 2*rowTransfer H := by
  funext w e
  simp only [markedRight,markedDoubleMatrix_eq,pow_two,Matrix.mul_apply,right_sum,right_mul,
    markedColumn,base_form,right_form,Finset.sum_add_distrib,Matrix.add_apply,rowTransfer]
lemma markedLeft_shift (H : ℕ) : HasShift (markedLeft H) 1 := by
  rw [markedLeft_eq]
  have h0 : HasShift (rowTransfer H) 0 := by simpa using transfer_power_shift H 1
  have h1 : HasShift (columnKernel H 2 1) 1 := by
    simpa [spinCharge] using kernel_hasShift H 2 1
  exact shift_add (by simpa using shift_mul h0 h1) (by simpa using shift_mul h1 h0)
lemma markedRight_shift (H : ℕ) : HasShift (markedRight H) (-1) := by
  rw [markedRight_eq]
  have h0 : HasShift (rowTransfer H) 0 := by simpa using transfer_power_shift H 1
  have h1 : HasShift (columnKernel H 1 2) (-1) := by
    simpa [spinCharge] using kernel_hasShift H 1 2
  exact shift_add (by simpa using shift_mul h0 h1) (by simpa using shift_mul h1 h0)
lemma projection_shift_zero {W : ℕ} {M : Matrix (Column (W+1)) (Column (W+1)) ℂ}
    {q : ℤ} (hM : HasShift M q) (hq : q≠0) :
    ∑ s,archRow W s*(M.mulVec (archColumn W)) s=0 := by
  classical
  simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro t ht
  by_cases hs0 : columnCharge s=0
  · by_cases ht0 : columnCharge t=0
    · have hm : M s t=0 := by
        by_contra hn
        have hh:=hM s t hn
        simp only [hs0,ht0,zero_add] at hh
        exact hq hh.symm
      simp [hm]
    · simp [archColumn_charge t ht0]
  · simp [archRow_charge s hs0]
noncomputable def archDual (W : ℕ) (v : Column (W+1)→ℂ) : ℂ :=
  ∑ s,archRow W s*v s
lemma archDual_add (W : ℕ) (v w : Column (W+1)→ℂ) :
    archDual W (v+w)=archDual W v+archDual W w := by
  simp [archDual,mul_add,Finset.sum_add_distrib]
lemma archDual_sub (W : ℕ) (v w : Column (W+1)→ℂ) :
    archDual W (v-w)=archDual W v-archDual W w := by
  simp [archDual,mul_sub,Finset.sum_sub_distrib]
lemma archDual_smul (W : ℕ) (z : ℂ) (v : Column (W+1)→ℂ) :
    archDual W (z•v)=z*archDual W v := by
  simp only [archDual,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring
lemma archDual_A (W : ℕ) : archDual W (archColumn W)=1 := arch_pairing W
lemma archDual_left_A (W : ℕ) :
    archDual W ((markedLeft (W+1)).mulVec (archColumn W))=0 :=
  projection_shift_zero (markedLeft_shift (W+1)) (by norm_num)
lemma archDual_right_A (W : ℕ) :
    archDual W ((markedRight (W+1)).mulVec (archColumn W))=0 :=
  projection_shift_zero (markedRight_shift (W+1)) (by norm_num)
lemma archDual_gap (W : ℕ) (v : Column (W+1)→ℂ) :
    archDual W ((gapMatrix W).mulVec v)=archDual W v := by
  have hh:=congrFun (congrArg (fun M=>M.mulVec v) (projection_mul_gap W)) (fun _=>1)
  rw [←Matrix.mulVec_mulVec,projection_mulVec,projection_mulVec] at hh
  simpa [archColumn_vacuum,Pi.smul_apply,smul_eq_mul,archDual] using hh
lemma archDual_double (W : ℕ) (v : Column (W+1)→ℂ) :
    archDual W ((physicalDoubleMatrix (W+1)).mulVec v)=archDual W v := by
  have hh:=congrFun (congrArg (fun M=>M.mulVec v) (projection_mul_double W)) (fun _=>1)
  rw [←Matrix.mulVec_mulVec,projection_mulVec,projection_mulVec] at hh
  simpa [archColumn_vacuum,Pi.smul_apply,smul_eq_mul,archDual] using hh
noncomputable def reducedSolve (W : ℕ) (v : Column (W+1)→ℂ) : Column (W+1)→ℂ :=
  (gapMatrix W)⁻¹|>fun M=>M.mulVec v
lemma gap_reducedSolve (W : ℕ) (v : Column (W+1)→ℂ) :
    (gapMatrix W).mulVec (reducedSolve W v)=v := by
  rw [reducedSolve,Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (physical_gap_det_ne_zero W)),Matrix.one_mulVec]
lemma archDual_reducedSolve (W : ℕ) (v : Column (W+1)→ℂ) :
    archDual W (reducedSolve W v)=archDual W v := by
  rw [←archDual_gap W (reducedSolve W v),gap_reducedSolve]
lemma reducedSolve_equation (W : ℕ) (v : Column (W+1)→ℂ) (hv : archDual W v=0) :
    (physicalDoubleMatrix (W+1)).mulVec (reducedSolve W v)+v=reducedSolve W v := by
  have hg:=gap_reducedSolve W v
  have hp : (archProjection W).mulVec (reducedSolve W v)=0 := by
    rw [projection_mulVec]
    change (archDual W (reducedSolve W v))•archColumn W=0
    rw [archDual_reducedSolve,hv,zero_smul]
  simp only [gapMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,hp,add_zero] at hg
  rw [sub_eq_iff_eq_add] at hg
  exact (add_comm _ _).trans hg.symm
noncomputable def eigenLeft (W : ℕ) : Column (W+1)→ℂ :=
  reducedSolve W ((markedLeft (W+1)).mulVec (archColumn W))
noncomputable def eigenRight (W : ℕ) : Column (W+1)→ℂ :=
  reducedSolve W ((markedRight (W+1)).mulVec (archColumn W))
noncomputable def eigenSource (W : ℕ) : Column (W+1)→ℂ :=
  (markedMixed (W+1)).mulVec (archColumn W)+
    (markedLeft (W+1)).mulVec (eigenRight W)+(markedRight (W+1)).mulVec (eigenLeft W)
noncomputable def eigenCoefficient (W : ℕ) : ℂ := archDual W (eigenSource W)
noncomputable def eigenMixed (W : ℕ) : Column (W+1)→ℂ :=
  reducedSolve W (eigenSource W-eigenCoefficient W•archColumn W)
noncomputable def markedEigenvector (W : ℕ) : Column (W+1)→Jet :=
  fun s=>form (archColumn W s) (eigenLeft W s) (eigenRight W s) (eigenMixed W s)
lemma eigenLeft_equation (W : ℕ) :
    (physicalDoubleMatrix (W+1)).mulVec (eigenLeft W)+
      (markedLeft (W+1)).mulVec (archColumn W)=eigenLeft W :=
  reducedSolve_equation _ _ (archDual_left_A W)
lemma eigenRight_equation (W : ℕ) :
    (physicalDoubleMatrix (W+1)).mulVec (eigenRight W)+
      (markedRight (W+1)).mulVec (archColumn W)=eigenRight W :=
  reducedSolve_equation _ _ (archDual_right_A W)
lemma eigenMixed_equation (W : ℕ) :
    (physicalDoubleMatrix (W+1)).mulVec (eigenMixed W)+eigenSource W=
      eigenMixed W+eigenCoefficient W•archColumn W := by
  have hz : archDual W (eigenSource W-eigenCoefficient W•archColumn W)=0 := by
    simp [archDual_sub,archDual_smul,archDual_A,eigenCoefficient]
  have hh:=reducedSolve_equation W _ hz
  change (physicalDoubleMatrix (W+1)).mulVec (eigenMixed W)+
    (eigenSource W-eigenCoefficient W•archColumn W)=eigenMixed W at hh
  rw [←add_sub_assoc] at hh
  exact sub_eq_iff_eq_add.mp hh
lemma double_archColumn (W : ℕ) :
    (physicalDoubleMatrix (W+1)).mulVec (archColumn W)=archColumn W := by
  rw [physicalDoubleMatrix_eq,pow_two,←Matrix.mulVec_mulVec,archColumn_eigen,archColumn_eigen]

theorem source_marked_eigenvector (W : ℕ) :
    (markedDoubleMatrix (W+1)).mulVec (markedEigenvector W)=
      fun s=>form 1 0 0 (eigenCoefficient W)*markedEigenvector W s := by
  funext s
  have h0:=congrFun (double_archColumn W) s
  have h1:=congrFun (eigenLeft_equation W) s
  have h2:=congrFun (eigenRight_equation W) s
  have h3:=congrFun (eigenMixed_equation W) s
  have hb w e : base (markedDoubleMatrix (W+1) w e)=physicalDoubleMatrix (W+1) w e :=
    congrFun (congrFun (marked_base (W+1)) w) e
  apply jet_ext <;>
    simp only [Matrix.mulVec,dotProduct,base_sum,left_sum,right_sum,both_sum,base_mul,left_mul,
      right_mul,both_mul,markedEigenvector,base_form,left_form,right_form,both_form,hb,
      zero_mul,one_mul,add_zero,Finset.sum_add_distrib]
  · exact h0
  · exact h1
  · exact h2
  · convert h3 using 1 ;
      simp only [eigenSource,Pi.add_apply,Matrix.mulVec,dotProduct,markedMixed,markedLeft,markedRight] ; abel
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet
open scoped Matrix
lemma gap_archColumn (W : ℕ) : (gapMatrix W).mulVec (archColumn W)=archColumn W := by
  simp only [gapMatrix,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,double_archColumn,sub_self,zero_add]
  rw [projection_mulVec,arch_pairing,one_smul]
lemma inv_gap_archColumn (W : ℕ) : (gapMatrix W)⁻¹.mulVec (archColumn W)=archColumn W := by
  conv_lhs => rw [←gap_archColumn W]
  rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (physical_gap_det_ne_zero W)),Matrix.one_mulVec]
lemma archRow_double (W : ℕ) : (archRow W) ᵥ* (physicalDoubleMatrix (W+1))=archRow W := by
  funext s
  have h:=congrFun (congrFun (projection_mul_double W) (fun _=>1)) s
  simpa [archProjection,archColumn_vacuum,Matrix.mul_apply,Matrix.vecMul,dotProduct] using h
lemma vecMul_projection (W : ℕ) (v : Column (W+1)→ℂ) :
    v ᵥ* (archProjection W)=(v ⬝ᵥ archColumn W)•archRow W := by
  funext s
  simp only [Matrix.vecMul,dotProduct,archProjection,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  ring
noncomputable def dualSolve (W : ℕ) (v : Column (W+1)→ℂ) : Column (W+1)→ℂ :=
  v ᵥ* (gapMatrix W)⁻¹
lemma dualSolve_gap (W : ℕ) (v : Column (W+1)→ℂ) :
    (dualSolve W v) ᵥ* (gapMatrix W)=v := by
  rw [dualSolve,Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (physical_gap_det_ne_zero W)),Matrix.vecMul_one]
lemma dualSolve_pair (W : ℕ) (v w : Column (W+1)→ℂ) :
    dualSolve W v ⬝ᵥ w=v ⬝ᵥ reducedSolve W w := by
  exact (Matrix.dotProduct_mulVec _ _ _).symm
lemma dualSolve_A (W : ℕ) (v : Column (W+1)→ℂ) :
    dualSolve W v ⬝ᵥ archColumn W=v ⬝ᵥ archColumn W := by
  rw [dualSolve,←Matrix.dotProduct_mulVec,inv_gap_archColumn]
lemma dualSolve_equation (W : ℕ) (v : Column (W+1)→ℂ) (hv : v ⬝ᵥ archColumn W=0) :
    (dualSolve W v) ᵥ* (physicalDoubleMatrix (W+1))+v=dualSolve W v := by
  have hg:=dualSolve_gap W v
  have hp : (dualSolve W v) ᵥ* (archProjection W)=0 := by
    rw [vecMul_projection,dualSolve_A,hv,zero_smul]
  simp only [gapMatrix,Matrix.vecMul_add,Matrix.vecMul_sub,Matrix.vecMul_one,hp,add_zero] at hg
  rw [sub_eq_iff_eq_add] at hg
  exact (add_comm _ _).trans hg.symm
noncomputable def dualLeft (W : ℕ) : Column (W+1)→ℂ :=
  dualSolve W ((archRow W) ᵥ* (markedLeft (W+1)))
noncomputable def dualRight (W : ℕ) : Column (W+1)→ℂ :=
  dualSolve W ((archRow W) ᵥ* (markedRight (W+1)))
noncomputable def dualSource (W : ℕ) : Column (W+1)→ℂ :=
  (archRow W) ᵥ* (markedMixed (W+1))+
    (dualLeft W) ᵥ* (markedRight (W+1))+(dualRight W) ᵥ* (markedLeft (W+1))
lemma dualSource_pair (W : ℕ) : dualSource W ⬝ᵥ archColumn W=eigenCoefficient W := by
  simp only [dualSource,eigenCoefficient,eigenSource,archDual_add,add_dotProduct,
    ←Matrix.dotProduct_mulVec,dualLeft,dualRight,dualSolve_pair]
  change archDual W ((markedMixed (W+1)).mulVec (archColumn W))+
    _+_=archDual W ((markedMixed (W+1)).mulVec (archColumn W))+_+_
  rfl
noncomputable def dualMixed (W : ℕ) : Column (W+1)→ℂ :=
  dualSolve W (dualSource W-eigenCoefficient W•archRow W)
noncomputable def dualEigenvector (W : ℕ) : Column (W+1)→Jet :=
  fun s=>form (archRow W s) (dualLeft W s) (dualRight W s) (dualMixed W s)
lemma dualLeft_equation (W : ℕ) :
    (dualLeft W) ᵥ* (physicalDoubleMatrix (W+1))+
      (archRow W) ᵥ* (markedLeft (W+1))=dualLeft W := by
  apply dualSolve_equation
  rw [←Matrix.dotProduct_mulVec]
  exact archDual_left_A W
lemma dualRight_equation (W : ℕ) :
    (dualRight W) ᵥ* (physicalDoubleMatrix (W+1))+
      (archRow W) ᵥ* (markedRight (W+1))=dualRight W := by
  apply dualSolve_equation
  rw [←Matrix.dotProduct_mulVec]
  exact archDual_right_A W
lemma dualMixed_equation (W : ℕ) :
    (dualMixed W) ᵥ* (physicalDoubleMatrix (W+1))+dualSource W=
      dualMixed W+eigenCoefficient W•archRow W := by
  have hz : (dualSource W-eigenCoefficient W•archRow W) ⬝ᵥ archColumn W=0 := by
    rw [sub_dotProduct,smul_dotProduct,dualSource_pair]
    change eigenCoefficient W-eigenCoefficient W*archDual W (archColumn W)=0
    rw [archDual_A,mul_one,sub_self]
  have hh:=dualSolve_equation W _ hz
  change (dualMixed W) ᵥ* (physicalDoubleMatrix (W+1))+
    (dualSource W-eigenCoefficient W•archRow W)=dualMixed W at hh
  rw [←add_sub_assoc] at hh
  exact sub_eq_iff_eq_add.mp hh

theorem source_dual_eigenvector (W : ℕ) :
    (dualEigenvector W) ᵥ* (markedDoubleMatrix (W+1))=
      fun s=>form 1 0 0 (eigenCoefficient W)*dualEigenvector W s := by
  funext s
  have h0:=congrFun (archRow_double W) s
  have h1:=congrFun (dualLeft_equation W) s
  have h2:=congrFun (dualRight_equation W) s
  have h3:=congrFun (dualMixed_equation W) s
  have hb w e : base (markedDoubleMatrix (W+1) w e)=physicalDoubleMatrix (W+1) w e :=
    congrFun (congrFun (marked_base (W+1)) w) e
  apply jet_ext <;>
    simp only [Matrix.vecMul,dotProduct,base_sum,left_sum,right_sum,both_sum,base_mul,left_mul,
      right_mul,both_mul,dualEigenvector,base_form,left_form,right_form,both_form,hb,
      zero_mul,one_mul,add_zero,Finset.sum_add_distrib]
  · exact h0
  · simpa only [Pi.add_apply,Matrix.vecMul,dotProduct,markedLeft,add_comm] using h1
  · simpa only [Pi.add_apply,Matrix.vecMul,dotProduct,markedRight,add_comm] using h2
  · convert h3 using 1 ;
      simp only [dualSource,Pi.add_apply,Matrix.vecMul,dotProduct,markedMixed,markedLeft,markedRight] ; abel
end CriticalHoneycomb.Transfer.RasterGrid

end

section
namespace CriticalHoneycomb.BoundaryJet
open Filter Topology
open scoped Matrix Matrix.Norms.Operator
lemma powers_of_power_small {R : Type*} [NormedRing R] [NormOneClass R] (x : R)
    {n : ℕ} (hn : n≠0) (hx : ‖x^n‖<1) : Tendsto (fun m : ℕ=>x^m) atTop (𝓝 0) := by
  let C : ℝ := ∑ r∈Finset.range n,‖x^r‖
  have hb (m : ℕ) : ‖x^m‖≤‖x^n‖^(m/n)*C := by
    have he : m=n*(m/n)+m%n := (Nat.div_add_mod m n).symm
    calc
      ‖x^m‖ = ‖(x^n)^(m/n)*x^(m%n)‖ := by conv_lhs => rw [he];rw [pow_add,pow_mul]
      _ ≤ ‖(x^n)^(m/n)‖*‖x^(m%n)‖ := norm_mul_le _ _
      _ ≤ ‖x^n‖^(m/n)*C := by
        apply mul_le_mul (norm_pow_le _ _) _ (norm_nonneg _) (by positivity)
        exact Finset.single_le_sum (fun r hr=>norm_nonneg _) (Finset.mem_range.mpr (Nat.mod_lt m (Nat.pos_of_ne_zero hn)))
  have hl:=((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (x^n)) hx).comp
    (Nat.tendsto_div_const_atTop hn)).mul_const C
  simp only [zero_mul] at hl
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun m=>norm_nonneg _) hb hl)
lemma continuous_base : Continuous base :=
  TrivSqZeroExt.continuous_fst.comp TrivSqZeroExt.continuous_fst
lemma continuous_left : Continuous left :=
  TrivSqZeroExt.continuous_fst.comp TrivSqZeroExt.continuous_snd
lemma continuous_right : Continuous right :=
  TrivSqZeroExt.continuous_snd.comp TrivSqZeroExt.continuous_fst
lemma continuous_both : Continuous both :=
  TrivSqZeroExt.continuous_snd.comp TrivSqZeroExt.continuous_snd
lemma continuous_C : Continuous C :=
  TrivSqZeroExt.continuous_inl.comp TrivSqZeroExt.continuous_inl
noncomputable def scaleHom (z : ℂ) : Jet→+*Jet where
  toFun a := form (base a) (z*left a) (z*right a) (z^2*both a)
  map_zero' := by apply jet_ext <;> simp [form,base,left,right,both,C,eL,eR]
  map_one' := by apply jet_ext <;> simp [form,base,left,right,both,C,eL,eR]
  map_add' a b := by apply jet_ext <;> simp [mul_add]
  map_mul' a b := by apply jet_ext <;> simp <;> ring
@[simp] lemma base_scale (z : ℂ) (a : Jet) : base (scaleHom z a)=base a := by simp [scaleHom]
@[simp] lemma left_scale (z : ℂ) (a : Jet) : left (scaleHom z a)=z*left a := by simp [scaleHom]
@[simp] lemma right_scale (z : ℂ) (a : Jet) : right (scaleHom z a)=z*right a := by simp [scaleHom]
@[simp] lemma both_scale (z : ℂ) (a : Jet) : both (scaleHom z a)=z^2*both a := by simp [scaleHom]
lemma scale_zero (a : Jet) : scaleHom 0 a=C (base a) := by apply jet_ext <;> simp
lemma scale_inverse (z : ℂ) (hz : z≠0) (a : Jet) : scaleHom z⁻¹ (scaleHom z a)=a := by
  apply jet_ext <;> simp [hz]
lemma continuous_scale (z : ℂ) : Continuous (scaleHom z) := by
  dsimp [scaleHom,form]
  exact ((continuous_C.comp continuous_base).add
    (continuous_const.mul (continuous_C.comp (continuous_const.mul continuous_left)))).add
      (continuous_const.mul (continuous_C.comp (continuous_const.mul continuous_right))) |>.add
        (continuous_const.mul (continuous_C.comp (continuous_const.mul continuous_both)))
lemma continuous_scale_parameter (a : Jet) : Continuous (fun z : ℂ=>scaleHom z a) := by
  change Continuous (fun z : ℂ=>form (base a) (z*left a) (z*right a) (z^2*both a))
  unfold form
  exact ((continuous_const.add (continuous_const.mul (continuous_C.comp (continuous_id.mul_const _)))).add
    (continuous_const.mul (continuous_C.comp (continuous_id.mul_const _)))).add
      (continuous_const.mul (continuous_C.comp ((continuous_id.pow 2).mul_const _)))
noncomputable def scaleMatrix {ι : Type*} (z : ℂ) (M : Matrix ι ι Jet) : Matrix ι ι Jet :=
  M.map (scaleHom z)
lemma scaleMatrix_pow {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ℂ) (M : Matrix ι ι Jet) (m : ℕ) :
    scaleMatrix z (M^m)=(scaleMatrix z M)^m := by
  exact (scaleHom z).mapMatrix.map_pow M m
lemma scaleMatrix_inverse {ι : Type*} (z : ℂ) (hz : z≠0) (M : Matrix ι ι Jet) :
    scaleMatrix z⁻¹ (scaleMatrix z M)=M := by
  funext i j
  exact scale_inverse z hz (M i j)
lemma continuous_scaleMatrix {ι : Type*} (z : ℂ) : Continuous (scaleMatrix (ι:=ι) z) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_scale z).comp ((continuous_apply j).comp (continuous_apply i))
lemma continuous_scaleMatrix_parameter {ι : Type*} (M : Matrix ι ι Jet) :
    Continuous (fun z : ℂ=>scaleMatrix z M) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_scale_parameter (M i j)

theorem stable_jet_powers {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι Jet)
    (hM : Tendsto (fun n : ℕ=>fun i j=>base ((M^n) i j)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ=>M^n) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ=>scaleMatrix 0 (M^n)) atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hh:=(continuous_C.tendsto 0).comp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hM i) j)
    simpa only [scaleMatrix,Matrix.map_apply,scale_zero,map_zero,Pi.zero_apply,Matrix.zero_apply,Function.comp_def] using hh
  have hev : ∀ᶠ n : ℕ in atTop,‖scaleMatrix 0 (M^n)‖<1 := by
    exact h0.norm.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨n,hn,hsmall⟩:=((eventually_ge_atTop 1).and hev).exists
  have hn0 : n≠0 := by omega
  have hcont : ContinuousAt (fun z : ℂ=>‖scaleMatrix z (M^n)‖) 0 :=
    ((continuous_scaleMatrix_parameter (M^n)).norm).continuousAt
  have hez : ∀ᶠ z : ℂ in 𝓝 (0:ℂ),‖scaleMatrix z (M^n)‖<1 :=
    hcont.eventually (gt_mem_nhds hsmall)
  obtain ⟨z,hz,hzn⟩ : ∃ z : ℂ,‖scaleMatrix z (M^n)‖<1 ∧ z≠0 := by
    have ht : ∀ᶠ z : ℂ in 𝓝[≠] (0:ℂ),‖scaleMatrix z (M^n)‖<1 ∧ z≠0 :=
      (hez.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    exact ht.exists
  have hp:=powers_of_power_small (scaleMatrix z M) hn0 (by simpa only [scaleMatrix_pow] using hz)
  have hg:=(continuous_scaleMatrix z⁻¹).tendsto (0:Matrix ι ι Jet) |>.comp hp
  have he (m : ℕ) : scaleMatrix z⁻¹ (scaleMatrix z M^m)=M^m := by
    rw [←scaleMatrix_pow,scaleMatrix_inverse z hzn]
  simp only [Function.comp_def,he] at hg
  simpa only [scaleMatrix,Matrix.map_zero,map_zero] using hg
end CriticalHoneycomb.BoundaryJet

end

end OAI
