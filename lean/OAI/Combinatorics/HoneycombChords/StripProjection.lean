import OAI.Combinatorics.HoneycombChords.BoundaryExpansion
import OAI.Combinatorics.HoneycombChords.SpectralCommutation

namespace OAI

/-! Strip projection for critical honeycomb strips.

The formulas follow the finite strip transfer calculation in the companion paper
on uniform marked polygon estimates. -/

section
namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet Filter Topology
open scoped Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : IsScalarTower Jet Jet Jet where
  smul_assoc a b c := mul_assoc a b c
local instance : SMulCommClass Jet Jet Jet where
  smul_comm a b c := by simp only [smul_eq_mul]; ring
local instance {ι : Type*} [Fintype ι] :
    IsScalarTower Jet (Matrix ι ι Jet) (Matrix ι ι Jet) where
  smul_assoc a b c := Matrix.smul_mul a b c
local instance {ι : Type*} [Fintype ι] :
    SMulCommClass Jet (Matrix ι ι Jet) (Matrix ι ι Jet) where
  smul_comm a b c := (Matrix.mul_smul b a c).symm
noncomputable def inverseAtOne (a : Jet) : Jet :=
  form 1 (-left a) (-right a) (2*left a*right a-both a)
lemma inverseAtOne_mul (a : Jet) (ha : base a=1) : inverseAtOne a*a=1 := by
  apply jet_ext <;> simp [inverseAtOne,ha] <;> try rfl
  all_goals change _=0;ring
noncomputable def eigenPair (W : ℕ) : Jet := dualEigenvector W ⬝ᵥ markedEigenvector W
lemma eigenPair_base (W : ℕ) : base (eigenPair W)=1 := by
  simp only [eigenPair,dotProduct,base_sum,base_mul,dualEigenvector,markedEigenvector,base_form]
  exact arch_pairing W
noncomputable def normalizedDual (W : ℕ) : Column (W+1)→Jet :=
  fun s=>inverseAtOne (eigenPair W)*dualEigenvector W s
lemma normalized_pair (W : ℕ) : normalizedDual W ⬝ᵥ markedEigenvector W=1 := by
  simp only [normalizedDual,dotProduct,mul_assoc,←Finset.mul_sum]
  exact inverseAtOne_mul _ (eigenPair_base W)
lemma normalized_dual_eigen (W : ℕ) :
    normalizedDual W ᵥ* markedDoubleMatrix (W+1)=
      fun s=>form 1 0 0 (eigenCoefficient W)*normalizedDual W s := by
  funext s
  have hh:=congrFun (source_dual_eigenvector W) s
  simp only [normalizedDual,Matrix.vecMul,dotProduct,mul_assoc,←Finset.mul_sum]
  change inverseAtOne (eigenPair W)*(dualEigenvector W ᵥ* markedDoubleMatrix (W+1)) s=_
  rw [hh]
  ring
noncomputable def markedProjection (W : ℕ) : Matrix (Column (W+1)) (Column (W+1)) Jet :=
  fun w e=>markedEigenvector W w*normalizedDual W e
noncomputable def markedEigenvalue (W : ℕ) : Jet := form 1 0 0 (eigenCoefficient W)
lemma markedProjection_base (W : ℕ) :
    (fun w e=>base (markedProjection W w e))=archProjection W := by
  funext w e
  simp [markedProjection,normalizedDual,inverseAtOne,markedEigenvector,dualEigenvector,archProjection]
lemma markedProjection_idempotent (W : ℕ) : markedProjection W*markedProjection W=markedProjection W := by
  funext w e
  simp only [Matrix.mul_apply,markedProjection]
  calc
    (∑ s,markedEigenvector W w*normalizedDual W s*(markedEigenvector W s*normalizedDual W e))=
        markedEigenvector W w*(normalizedDual W ⬝ᵥ markedEigenvector W)*normalizedDual W e := by
      simp only [dotProduct,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _=markedEigenvector W w*normalizedDual W e := by rw [normalized_pair,mul_one]
lemma markedProjection_mul (W : ℕ) :
    markedProjection W*markedDoubleMatrix (W+1)=markedEigenvalue W•markedProjection W := by
  funext w e
  simp only [Matrix.mul_apply,markedProjection,mul_assoc,←Finset.mul_sum]
  change markedEigenvector W w*(normalizedDual W ᵥ* markedDoubleMatrix (W+1)) e=_
  rw [normalized_dual_eigen]
  simp only [markedEigenvalue,Matrix.smul_apply,smul_eq_mul,markedProjection]
  ring
lemma mul_markedProjection (W : ℕ) :
    markedDoubleMatrix (W+1)*markedProjection W=markedEigenvalue W•markedProjection W := by
  funext w e
  simp only [Matrix.mul_apply,markedProjection,←mul_assoc,←Finset.sum_mul]
  change (markedDoubleMatrix (W+1)).mulVec (markedEigenvector W) w*normalizedDual W e=_
  rw [source_marked_eigenvector]
  simp only [markedEigenvalue,Matrix.smul_apply,smul_eq_mul,markedProjection]
  ring
noncomputable def markedRemainder (W : ℕ) : Matrix (Column (W+1)) (Column (W+1)) Jet :=
  markedDoubleMatrix (W+1)-markedEigenvalue W•markedProjection W
lemma marked_remainder_orthogonal (W : ℕ) :
    markedProjection W*markedRemainder W=0 ∧ markedRemainder W*markedProjection W=0 := by
  constructor
  · rw [markedRemainder,mul_sub,Matrix.mul_smul (markedProjection W) (markedEigenvalue W),markedProjection_idempotent,markedProjection_mul,sub_self]
  · rw [markedRemainder,sub_mul,Matrix.smul_mul (markedEigenvalue W) (markedProjection W),markedProjection_idempotent,mul_markedProjection,sub_self]
lemma double_pow_projection (W m : ℕ) :
    physicalDoubleMatrix (W+1)^m*archProjection W=archProjection W := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,mul_assoc,double_mul_projection,ih]
lemma double_remainder_power (W m : ℕ) :
    (physicalDoubleMatrix (W+1)-archProjection W)^(m+1)=
      physicalDoubleMatrix (W+1)^(m+1)-archProjection W := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,ih,sub_mul,mul_sub,mul_sub,double_pow_projection,projection_mul_double,projection_idempotent]
    rw [←pow_succ]
    abel
lemma double_remainder_limit (W : ℕ) :
    Tendsto (fun m : ℕ=>(physicalDoubleMatrix (W+1)-archProjection W)^m) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hh:=(physical_double_rank_one W).comp (tendsto_add_atTop_nat 1) |>.sub_const (archProjection W)
  simpa [Function.comp_def,sub_self,double_remainder_power] using hh
noncomputable def jetBaseHom : Jet→+*ℂ where
  toFun:=base
  map_one':=rfl
  map_zero':=rfl
  map_add':=base_add
  map_mul':=base_mul
lemma markedRemainder_base (W : ℕ) :
    (markedRemainder W).map jetBaseHom=physicalDoubleMatrix (W+1)-archProjection W := by
  funext w e
  change base (markedDoubleMatrix (W+1) w e-markedEigenvalue W*markedProjection W w e)=_
  rw [show base (markedDoubleMatrix (W+1) w e-markedEigenvalue W*markedProjection W w e)=
    base (markedDoubleMatrix (W+1) w e)-base (markedEigenvalue W*markedProjection W w e) from
    map_sub baseAdd _ _]
  simp only [markedEigenvalue,base_mul,base_form,one_mul]
  exact congrFun (congrFun (congrArg₂ (·-·) (marked_base (W+1)) (markedProjection_base W)) w) e

theorem marked_remainder_limit (W : ℕ) :
    Tendsto (fun m : ℕ=>markedRemainder W^m) atTop (𝓝 0) := by
  apply stable_jet_powers
  have he (m : ℕ) : (fun w e=>base ((markedRemainder W^m) w e))=
      (physicalDoubleMatrix (W+1)-archProjection W)^m := by
    change (jetBaseHom.mapMatrix) (markedRemainder W^m)=_
    rw [map_pow]
    congr 1
    exact markedRemainder_base W
  exact (double_remainder_limit W).congr (fun m=>(he m).symm)
lemma orthogonal_pow_add {R : Type*} [Ring R] (a b : R) (hab : a*b=0) (hba : b*a=0) (m : ℕ) :
    (a+b)^(m+1)=a^(m+1)+b^(m+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ,ih,add_mul,mul_add,mul_add]
    have h1 : a^(m+1)*b=0 := by rw [pow_succ,mul_assoc,hab,mul_zero]
    have h2 : b^(m+1)*a=0 := by rw [pow_succ,mul_assoc,hba,mul_zero]
    rw [h1,h2,add_zero,zero_add,←pow_succ,←pow_succ]
lemma markedProjection_pow (W m : ℕ) : markedProjection W^(m+1)=markedProjection W := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ,ih,markedProjection_idempotent]
lemma marked_power_split (W m : ℕ) :
    markedDoubleMatrix (W+1)^(m+1)=
      markedEigenvalue W^(m+1)•markedProjection W+markedRemainder W^(m+1) := by
  have hde : markedDoubleMatrix (W+1)=markedEigenvalue W•markedProjection W+markedRemainder W := by
    unfold markedRemainder
    abel
  rw [hde,orthogonal_pow_add]
  · rw [smul_pow,markedProjection_pow]
  · rw [Matrix.smul_mul (markedEigenvalue W) (markedProjection W),(marked_remainder_orthogonal W).1,smul_zero]
  · rw [Matrix.mul_smul (markedRemainder W) (markedEigenvalue W),(marked_remainder_orthogonal W).2,smul_zero]
lemma markedEigenvalue_pow (W m : ℕ) :
    markedEigenvalue W^m=form 1 0 0 ((m:ℂ)*eigenCoefficient W) := by
  induction m with
  | zero =>
    apply jet_ext <;> simp [markedEigenvalue] <;> rfl
  | succ m ih =>
    rw [pow_succ,ih]
    apply jet_ext <;> simp [markedEigenvalue,Nat.cast_add,Nat.cast_one]; ring
end CriticalHoneycomb.Transfer.RasterGrid

end

section

namespace CriticalHoneycomb.Transfer.RasterGrid
open BoundaryJet
open scoped Matrix
attribute [local instance 2000] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
attribute [default_instance 101] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid
local instance : IsScalarTower Jet Jet Jet where
  smul_assoc a b c := mul_assoc a b c
local instance : SMulCommClass Jet Jet Jet where
  smul_comm a b c := by simp only [smul_eq_mul];ring
lemma jetBaseHom_apply (a : Jet) : jetBaseHom a=base a := rfl
lemma jet_kernel_lift {ι : Type*} [Fintype ι]
    (M : Matrix ι ι Jet)
    (hb : ∀ x : ι→ℂ, (M.map jetBaseHom)*ᵥx=0 → x=0)
    (x : ι→Jet) (hx : M*ᵥx=0) : x=0 := by
  have h₀ : (fun s=>base (x s))=0 := by
    apply hb
    funext s
    have h:=congrArg base (congrFun hx s)
    simpa only [Matrix.mulVec,dotProduct,base_sum,base_mul,Pi.zero_apply,
      Matrix.map_apply,jetBaseHom_apply,show base (0:Jet)=0 from rfl] using h
  have h₁ : (fun s=>left (x s))=0 := by
    apply hb
    funext s
    have h:=congrArg left (congrFun hx s)
    simpa only [Matrix.mulVec,dotProduct,left_sum,left_mul,Pi.zero_apply,
      Matrix.map_apply,jetBaseHom_apply,show left (0:Jet)=0 from rfl,congrFun h₀,mul_zero,add_zero] using h
  have h₂ : (fun s=>right (x s))=0 := by
    apply hb
    funext s
    have h:=congrArg right (congrFun hx s)
    simpa only [Matrix.mulVec,dotProduct,right_sum,right_mul,Pi.zero_apply,
      Matrix.map_apply,jetBaseHom_apply,show right (0:Jet)=0 from rfl,congrFun h₀,mul_zero,add_zero] using h
  have h₃ : (fun s=>both (x s))=0 := by
    apply hb
    funext s
    have h:=congrArg both (congrFun hx s)
    simpa only [Matrix.mulVec,dotProduct,both_sum,both_mul,Pi.zero_apply,
      Matrix.map_apply,jetBaseHom_apply,show both (0:Jet)=0 from rfl,congrFun h₀,congrFun h₁,congrFun h₂,
      mul_zero,add_zero] using h
  funext s
  exact jet_ext _ 0 (congrFun h₀ s) (congrFun h₁ s) (congrFun h₂ s) (congrFun h₃ s)
noncomputable def markedGap (W : ℕ) : Matrix (Column (W+1)) (Column (W+1)) Jet :=
  markedEigenvalue W•(1 : Matrix _ _ Jet)-markedDoubleMatrix (W+1)+markedProjection W
lemma markedGap_base (W : ℕ) : (markedGap W).map jetBaseHom=gapMatrix W := by
  funext s t
  change base (markedEigenvalue W*(1 : Matrix _ _ Jet) s t-
    markedDoubleMatrix (W+1) s t+markedProjection W s t)=_
  rw [base_add,show base (markedEigenvalue W*(1 : Matrix _ _ Jet) s t-
    markedDoubleMatrix (W+1) s t)=
    base (markedEigenvalue W*(1 : Matrix _ _ Jet) s t)-base (markedDoubleMatrix (W+1) s t)
      from map_sub baseAdd _ _]
  simp only [base_mul,markedEigenvalue,base_form,one_mul]
  rw [congrFun (congrFun (marked_base (W+1)) s) t,
    congrFun (congrFun (markedProjection_base W) s) t]
  simp only [gapMatrix,Matrix.one_apply,Matrix.add_apply,Matrix.sub_apply]
  split_ifs <;> rfl
lemma markedGap_kernel (W : ℕ) (x : Column (W+1)→Jet)
    (hx : markedGap W*ᵥx=0) : x=0 := by
  apply jet_kernel_lift (markedGap W) _ x hx
  intro y hy
  rw [markedGap_base] at hy
  exact gap_kernel W y hy
lemma marked_fixed_projected (W : ℕ) (x : Column (W+1)→Jet)
    (hx : markedDoubleMatrix (W+1)*ᵥx=markedEigenvalue W•x) :
    markedProjection W*ᵥx=x := by
  have hp : markedGap W*ᵥ(markedProjection W*ᵥx)=markedProjection W*ᵥx := by
    rw [Matrix.mulVec_mulVec]
    have hg : markedGap W*markedProjection W=markedProjection W := by
      rw [markedGap,add_mul,sub_mul,markedProjection_idempotent,mul_markedProjection,
        Matrix.smul_mul (markedEigenvalue W) (1 : Matrix _ _ Jet),one_mul,sub_self,zero_add]
    rw [hg]
  have hg : markedGap W*ᵥx=markedProjection W*ᵥx := by
    rw [markedGap,Matrix.add_mulVec,Matrix.sub_mulVec,Matrix.smul_mulVec,
      Matrix.one_mulVec,hx,sub_self,zero_add]
  apply sub_eq_zero.mp
  apply markedGap_kernel W
  rw [Matrix.mulVec_sub,hp,hg,sub_self]
noncomputable def commonScalar (W : ℕ)
    (M : Matrix (Column (W+1)) (Column (W+1)) Jet) : Jet :=
  normalizedDual W ⬝ᵥ (M*ᵥmarkedEigenvector W)
lemma markedProjection_mulVec (W : ℕ) (x : Column (W+1)→Jet) :
    markedProjection W*ᵥx=(normalizedDual W ⬝ᵥ x)•markedEigenvector W := by
  funext s
  simp only [markedProjection,Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  ring

lemma commuting_common_line (W : ℕ)
    (M : Matrix (Column (W+1)) (Column (W+1)) Jet)
    (hM : Commute (markedDoubleMatrix (W+1)) M) :
    M*ᵥmarkedEigenvector W=commonScalar W M•markedEigenvector W := by
  have hx : markedDoubleMatrix (W+1)*ᵥ(M*ᵥmarkedEigenvector W)=
      markedEigenvalue W•(M*ᵥmarkedEigenvector W) := by
    rw [Matrix.mulVec_mulVec,hM.eq,←Matrix.mulVec_mulVec,source_marked_eigenvector]
    change M*ᵥ(markedEigenvalue W•markedEigenvector W)=_
    rw [Matrix.mulVec_smul]
  have hp:=marked_fixed_projected W (M*ᵥmarkedEigenvector W) hx
  rw [markedProjection_mulVec] at hp
  exact hp.symm
end CriticalHoneycomb.Transfer.RasterGrid

end

end OAI
