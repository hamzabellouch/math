import OAI.Analysis.InterpolatedFactors.Jacobi

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

open Filter Topology
namespace FreeGroupFactorMain.BicommutantAtom
open InnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local notation "Op" => E →L[ℂ] E

theorem rankOne_commute_fixed (A : Op) (hA : IsSelfAdjoint A) (x y : E)
    (hx : A x=x) (hy : A y=y) : Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (inner ℂ y z • x)=inner ℂ y (A z) • x
  rw [map_smul,hx,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ y z • x=inner ℂ (star A y) z • x
  rw [hA.star_eq,hy]

theorem rankOne_commute_zero (A : Op) (hA : IsSelfAdjoint A) (x y : E)
    (hx : A x=0) (hy : A y=0) : Commute A (rankOne ℂ x y) := by
  apply ContinuousLinearMap.ext
  intro z
  change A (inner ℂ y z • x)=inner ℂ y (A z) • x
  rw [map_smul,hx,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ y z • (0:E)=inner ℂ (star A y) z • x
  rw [hA.star_eq,hy,inner_zero_left,zero_smul,smul_zero]

omit [CompleteSpace E] in

theorem scalar_of_rankOne_commutes (d T : Op)
    (h : ∀ x y : E, Commute T (rankOne ℂ (d x) (d y))) :
    ∃ c : ℂ,T*d=c • d := by
  by_cases hd : d=0
  · exact ⟨0,by simp [hd]⟩
  have hx : ∃ x : E,d x≠0 := by
    by_contra! hn
    apply hd
    ext x
    exact hn x
  obtain ⟨x,hx⟩ := hx
  let η := d x
  let a := inner ℂ η η
  have ha : a≠0 := by
    dsimp [a,η]
    exact fun hh => hx ((inner_self_eq_zero (𝕜 := ℂ)).mp hh)
  let b := inner ℂ η (T η)
  refine ⟨a⁻¹*b,?_⟩
  ext z
  have he := DFunLike.congr_fun (h z x).eq η
  change T (a • d z)=b • d z at he
  rw [map_smul] at he
  change T (d z)=(a⁻¹*b) • d z
  calc
    _ = a⁻¹ • (a • T (d z)) := by rw [smul_smul,inv_mul_cancel₀ ha,one_smul]
    _ = _ := by rw [he,smul_smul]

theorem common_kernel_scalar (p s d T : Op) (hp : IsSelfAdjoint p) (hs : IsSelfAdjoint s)
    (hpd : p*d=d) (hsd : s*d=0)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p {s}) : Set Op)) :
    ∃ c : ℂ,T*d=c • d := by
  apply scalar_of_rankOne_commutes d T
  intro x y
  have hpx (z : E) : p (d z)=d z := DFunLike.congr_fun hpd z
  have hsx (z : E) : s (d z)=0 := DFunLike.congr_fun hsd z
  have hR : rankOne ℂ (d x) (d y)∈StarSubalgebra.centralizer ℂ (insert p {s}) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro A hA
    rcases Set.mem_insert_iff.mp hA with hA | hA
    · subst A
      have hh := rankOne_commute_fixed p hp (d x) (d y) (hpx x) (hpx y)
      exact ⟨hh.eq,by simpa only [hp.star_eq] using hh.eq⟩
    · have hA' : A=s := hA
      subst A
      have hh := rankOne_commute_zero s hs (d x) (d y) (hsx x) (hsx y)
      exact ⟨hh.eq,by simpa only [hs.star_eq] using hh.eq⟩
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hR).1.symm
end FreeGroupFactorMain.BicommutantAtom
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification.Polar
variable {ι : Type u_2} [DecidableEq ι]

theorem P_mem_edge (u v : ℝ) (i : ι) : (P : Operator ι)∈edgeAlgebra u v i :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert _ _))

theorem edge_sum_mem_edge (u v : ℝ) (i : ι) :
    offDiagonal u v i+star (offDiagonal u v i)∈edgeAlgebra u v i :=
  StarAlgebra.adjoin_le_centralizer_centralizer ℂ _
    (StarAlgebra.subset_adjoin ℂ _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem offDiagonal_mul_P (u v : ℝ) (i : ι) : offDiagonal u v i*P=0 :=
  CornerRerouting.right_zero (offDiagonal_right u v i)

theorem offDiagonal_mem_edge (u v : ℝ) (i : ι) : offDiagonal u v i∈edgeAlgebra u v i := by
  have hz : P*star (offDiagonal u v i)=0 := by
    simpa only [star_mul,star_zero (Operator ι),projection_P.isSelfAdjoint.star_eq]
      using congrArg star (offDiagonal_mul_P u v i)
  have he : P*(offDiagonal u v i+star (offDiagonal u v i))=offDiagonal u v i := by
    rw [mul_add,offDiagonal_left,hz,add_zero]
  rw [← he]
  exact mul_mem (P_mem_edge u v i) (edge_sum_mem_edge u v i)

theorem edgePolar_mem_edge (u v : ℝ) (i : ι) : edgePolar u v i∈edgeAlgebra u v i :=
  partialIsometry_mem_centralizer _ (offDiagonal_mem_edge u v i)

theorem edgeRange_mem_edge (u v : ℝ) (i : ι) : edgeRange u v i∈edgeAlgebra u v i :=
  mul_mem (edgePolar_mem_edge u v i) (star_mem (edgePolar_mem_edge u v i))

def edgeDefect (u v : ℝ) (i : ι) : Operator ι := P-edgeRange u v i

theorem edgeDefect_projection (u v : ℝ) (i : ι) : IsStarProjection (edgeDefect u v i) :=
  (edgeRange_projection u v i).sub_of_mul_eq_right projection_P (edgeRange_le_P u v i)

theorem edgeDefect_mem_edge (u v : ℝ) (i : ι) : edgeDefect u v i∈edgeAlgebra u v i :=
  sub_mem (P_mem_edge u v i) (edgeRange_mem_edge u v i)

theorem edgeRange_mul_offDiagonal (u v : ℝ) (i : ι) :
    edgeRange u v i*offDiagonal u v i=offDiagonal u v i := by
  have hf := partialIsometry_factorization (offDiagonal u v i)
  change edgePolar u v i*modulus (offDiagonal u v i)=offDiagonal u v i at hf
  calc
    _ = edgeRange u v i*(edgePolar u v i*modulus (offDiagonal u v i)) := by rw [hf]
    _ = edgePolar u v i*modulus (offDiagonal u v i) := by
      rw [← mul_assoc]
      exact congrArg (fun U => U*modulus (offDiagonal u v i)) (partialIsometry_partial _)
    _ = _ := hf

theorem P_mul_edgeDefect (u v : ℝ) (i : ι) : P*edgeDefect u v i=edgeDefect u v i := by
  rw [edgeDefect,mul_sub,projection_P.isIdempotentElem.eq,edgeRange_le_P]

theorem edgeDefect_mul_P (u v : ℝ) (i : ι) : edgeDefect u v i*P=edgeDefect u v i := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(edgeDefect_projection u v i).isSelfAdjoint.star_eq]
    using congrArg star (P_mul_edgeDefect u v i)

theorem edgeSum_mul_defect (u v : ℝ) (i : ι) :
    (offDiagonal u v i+star (offDiagonal u v i))*edgeDefect u v i=0 := by
  have hx : offDiagonal u v i*edgeDefect u v i=0 := by
    rw [← P_mul_edgeDefect u v i,← mul_assoc,offDiagonal_mul_P,zero_mul]
  have hxp : star (offDiagonal u v i)*P=star (offDiagonal u v i) := by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (offDiagonal_left u v i)
  have hxr : star (offDiagonal u v i)*edgeRange u v i=star (offDiagonal u v i) := by
    simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq]
      using congrArg star (edgeRange_mul_offDiagonal u v i)
  rw [add_mul,hx,zero_add,edgeDefect,mul_sub,hxp,hxr,sub_self]

theorem edge_algebra_scalar_on_defect (u v : ℝ) (i : ι) (T : edgeAlgebra u v i) :
    ∃ c : ℂ,(T : Operator ι)*edgeDefect u v i=c • edgeDefect u v i :=
  BicommutantAtom.common_kernel_scalar P (offDiagonal u v i+star (offDiagonal u v i))
    (edgeDefect u v i) T projection_P.isSelfAdjoint
    (by show star (_+_)=_;simp only [star_add,star_star,add_comm])
    (P_mul_edgeDefect u v i) (edgeSum_mul_defect u v i) T.property

theorem edgeDefect_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    vacuumTrace u v (edgeDefect u v i)=((u^2-v^2 : ℝ):ℂ) := by
  unfold edgeDefect vacuumTrace
  rw [sub_apply,inner_sub_right]
  change vacuumTrace u v P-vacuumTrace u v (edgeRange u v i)=_
  rw [vacuumTrace_P,edgePolar_trace u v hv hvu]
  push_cast
  rfl

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.JacobiNonatom
open Filter Topology

 theorem semicircular_eigenvector_zero (a z : ℂ) (ha : a≠0)
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 0))
    (hfirst : a*x 1=z*x 0)
    (hstep : ∀ n,a*x (n+2)=z*x (n+1)-a*x n) : ∀ n,x n=0 := by
  have hi := invariant_zero a z ha x hstep hx
  have hb : a*invariant a z x 0=a^2*(x 0)^2 := by
    calc
      _ = a^2*(x 0)^2+(a*x 1)^2-z*x 0*(a*x 1) := by simp only [invariant];ring
      _ = _ := by rw [hfirst];ring
  rw [hi,mul_zero] at hb
  have h0 : x 0=0 := by
    exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hb.symm).resolve_left (pow_ne_zero 2 ha))
  have h1 : x 1=0 := by
    rw [h0,mul_zero] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left ha
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n hn hn1 =>
    have h := hstep n
    rw [hn,hn1,mul_zero,mul_zero,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left ha

end FreeGroupFactorMain.JacobiNonatom
namespace FreeGroupFactorMain.IsometricSemicircle
open Filter Topology
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (L : E →L[ℂ] E) (hL : star L*L=1) (ξ : E) (hξ : inner ℂ ξ ξ=1)
  (hroot : star L ξ=0)

def chain (n : ℕ) : E := (L^n) ξ

omit [CompleteSpace E] in
theorem chain_zero : chain L ξ 0=ξ := by simp [chain]
omit [CompleteSpace E] in
theorem chain_succ (n : ℕ) : chain L ξ (n+1)=L (chain L ξ n) := by
  simp only [chain,pow_succ',mul_apply_eq_comp]

include hL in
theorem inner_map (x y : E) : inner ℂ (L x) (L y)=inner ℂ x y := by
  apply (ContinuousLinearMap.inner_map_map_iff_adjoint_comp_self L).mpr
  exact hL

include hroot in
theorem inner_root_succ (n : ℕ) : inner ℂ ξ (chain L ξ (n+1))=0 := by
  rw [chain_succ,← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star L ξ) (chain L ξ n)=0
  rw [hroot,inner_zero_left]

include hL hξ hroot in
theorem chain_inner (n m : ℕ) : inner ℂ (chain L ξ n) (chain L ξ m)=if n=m then 1 else 0 := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa only [chain_zero,ite_true] using hξ
    | succ m => simpa only [chain_zero,Nat.succ_ne_zero,Nat.zero_ne_add_one,ite_false]
        using inner_root_succ L ξ hroot m
  | succ n ih =>
    cases m with
    | zero =>
      rw [chain_zero,← inner_conj_symm,inner_root_succ L ξ hroot]
      simp
    | succ m =>
      rw [chain_succ,chain_succ,inner_map L hL,ih]
      simp

include hL hξ hroot in
theorem chain_orthonormal : Orthonormal ℂ (chain L ξ) :=
  orthonormal_iff_ite.mpr (chain_inner L hL ξ hξ hroot)

include hL hξ hroot in
theorem chain_coeff_decay (η : E) : Tendsto (fun n => inner ℂ (chain L ξ n) η) atTop (𝓝 0) := by
  have h := ((chain_orthonormal L hL ξ hξ hroot).inner_products_summable η).tendsto_atTop_zero
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
  have hn : Tendsto (fun n => ‖inner ℂ (chain L ξ n) η‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

include hL in
theorem adjoint_chain_succ (n : ℕ) : star L (chain L ξ (n+1))=chain L ξ n := by
  rw [chain_succ]
  change (star L*L) (chain L ξ n)=_
  rw [hL,one_apply_eq_self]

include hroot in
theorem sum_chain_zero : (L+star L) (chain L ξ 0)=chain L ξ 1 := by
  rw [chain_zero,add_apply,hroot,add_zero,chain_succ,chain_zero]

include hL in
theorem sum_chain_succ (n : ℕ) :
    (L+star L) (chain L ξ (n+1))=chain L ξ (n+2)+chain L ξ n := by
  rw [add_apply,adjoint_chain_succ L hL]
  exact congrArg (fun x => x+chain L ξ n) (chain_succ L ξ (n+1)).symm

include hL hξ hroot in

theorem eigen_root_zero (z : ℂ) (η : E) (he : (L+star L) η=z • η) : inner ℂ ξ η=0 := by
  have hself : star (L+star L)=L+star L := by simp [add_comm]
  have h (n : ℕ) : inner ℂ ((L+star L) (chain L ξ n)) η=
      z*inner ℂ (chain L ξ n) η := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ (chain L ξ n) (star (L+star L) η)=_
    rw [hself,he,inner_smul_right]
  have hb : (1:ℂ)*inner ℂ (chain L ξ 1) η=z*inner ℂ (chain L ξ 0) η := by
    rw [one_mul]
    simpa only [sum_chain_zero L ξ hroot] using h 0
  have ht (n : ℕ) : (1:ℂ)*inner ℂ (chain L ξ (n+2)) η=
      z*inner ℂ (chain L ξ (n+1)) η-(1:ℂ)*inner ℂ (chain L ξ n) η := by
    have hn := h (n+1)
    rw [sum_chain_succ L hL,inner_add_left] at hn
    linear_combination hn
  simpa only [chain_zero] using JacobiNonatom.semicircular_eigenvector_zero 1 z one_ne_zero
    (fun n => inner ℂ (chain L ξ n) η) (chain_coeff_decay L hL ξ hξ hroot η) hb ht 0

end FreeGroupFactorMain.IsometricSemicircle
namespace FreeGroupFactorMain.SupportedSemicircle
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (d L : (E →L[ℂ] E)) (hd : IsStarProjection d) (hleft : d*L=L) (hright : L*d=L)
  (hL : star L*L=d)

def extension : (E →L[ℂ] E) := L+(1-d)

include hd hleft hL in
theorem extension_isometry : star (extension d L)*extension d L=1 := by
  have hsright : star L*d=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hleft
  have hqL : (1-d)*L=0 := by rw [sub_mul,one_mul,hleft,sub_self]
  have hLq : star L*(1-d)=0 := by rw [mul_sub,mul_one,hsright,sub_self]
  rw [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_mul,mul_add,mul_add,
    hL,hLq,hqL,hd.one_sub.isIdempotentElem.eq,add_zero,zero_add,add_sub_cancel]

include hd hleft hright in
theorem supported_sum_left : d*(L+star L)=L+star L := by
  have hs : d*star L=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hright
  rw [mul_add,hleft,hs]

include hd hleft hright in
theorem supported_sum_right : (L+star L)*d=L+star L := by
  have hs : star L*d=star L := by
    simpa only [star_mul,hd.isSelfAdjoint.star_eq] using congrArg star hleft
  rw [add_mul,hright,hs]

include hd hleft hright hL in

theorem eigen_root_zero (ξ : E) (hξ : inner ℂ ξ ξ=1) (hdξ : d ξ=ξ)
    (hroot : star L ξ=0) (z : ℂ) (η : E) (he : (L+star L) η=z • η) :
    inner ℂ ξ η=0 := by
  have hqξ : (1-d : (E →L[ℂ] E)) ξ=0 := by rw [sub_apply,one_apply_eq_self,hdξ,sub_self]
  have hroot' : star (extension d L) ξ=0 := by
    rw [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_apply,hroot,hqξ,add_zero]
  have hqη : (1-d : (E →L[ℂ] E)) (d η)=0 := by
    change ((1-d)*d) η=0
    rw [sub_mul,one_mul,hd.isIdempotentElem.eq,sub_self,zero_apply]
  have he' : (extension d L+star (extension d L)) (d η)=z • d η := by
    have hs : (L+star L) (d η)=z • d η := by
      calc
        _ = (L+star L) η := DFunLike.congr_fun (supported_sum_right d L hd hleft hright) η
        _ = d ((L+star L) η) := (DFunLike.congr_fun (supported_sum_left d L hd hleft hright) η).symm
        _ = _ := by rw [he,map_smul]
    simp only [extension,star_add,hd.one_sub.isSelfAdjoint.star_eq,add_apply,hqη,add_zero] at ⊢
    exact hs
  have hz := IsometricSemicircle.eigen_root_zero (extension d L)
    (extension_isometry d L hd hleft hL) ξ hξ hroot' z (d η) he'
  rw [← ContinuousLinearMap.adjoint_inner_left] at hz
  change inner ℂ (star d ξ) η=0 at hz
  rwa [hd.isSelfAdjoint.star_eq,hdξ] at hz

end FreeGroupFactorMain.SupportedSemicircle
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_5} [DecidableEq ι]

theorem vacuumTrace_supported_root (u v : ℝ) (T : Operator ι)
    (hl : P*T=T) (hr : T*P=T) :
    vacuumTrace u v T=(u:ℂ)^2*(T (lp.single 2 ([],true) 1)) ([],true) := by
  have hnil : T (lp.single 2 ([],false) 1)=0 := by
    rw [← hr,mul_apply_eq_comp,P_nil_false,map_zero]
  have hcoord : (T (lp.single 2 ([],true) 1)) ([],false)=0 := by
    have hh := DFunLike.congr_fun hl (lp.single 2 ([],true) 1)
    have hc := congrArg (fun ξ : H ι => ξ ([],false)) hh
    simpa only [mul_apply_eq_comp,P,CoordinateProjection.proj_apply,
      Set.indicator_of_notMem (by simp [start] : ([], false) ∉ {w : Path ι | start w = true})] using hc.symm
  rw [vacuumTrace_root_expansion,hnil,hcoord]
  simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,add_zero,pow_two]

def defectCreation (u v : ℝ) (i j : ι) : Operator ι :=
  edgeDefect u v i*edgeCreation j true true*edgeDefect u v i

theorem defectCreation_left (u v : ℝ) (i j : ι) :
    edgeDefect u v i*defectCreation u v i j=defectCreation u v i j := by
  rw [defectCreation,← mul_assoc,← mul_assoc,(edgeDefect_projection u v i).isIdempotentElem.eq]

theorem defectCreation_right (u v : ℝ) (i j : ι) :
    defectCreation u v i j*edgeDefect u v i=defectCreation u v i j := by
  rw [defectCreation,mul_assoc,(edgeDefect_projection u v i).isIdempotentElem.eq]

theorem defectCreation_covariance (u v : ℝ) (i j : ι) :
    star (defectCreation u v i j)*defectCreation u v i j=
      ((edgeDefect u v i (lp.single 2 ([],true) 1)) ([],true)) • edgeDefect u v i := by
  let d := edgeDefect u v i
  have hid : d*d=d := (edgeDefect_projection u v i).isIdempotentElem.eq
  have hstar : star d=d := (edgeDefect_projection u v i).isSelfAdjoint.star_eq
  have hcov := diagonal_edge_contraction u v i j j
    ⟨d,edgeDefect_mem_edge u v i⟩ true true
  simp only [true_and,ite_true,vertex] at hcov
  change star (edgeCreation j true true)*d*edgeCreation j true true=_ at hcov
  change star (d*edgeCreation j true true*d)*(d*edgeCreation j true true*d)=_
  calc
    _ = d*(star (edgeCreation j true true)*d*edgeCreation j true true)*d := by
      simp only [star_mul,hstar,mul_assoc,← mul_assoc d d,hid]
    _ = _ := by
      rw [hcov,mul_smul_comm,smul_mul_assoc]
      change _ • (edgeDefect u v i*P*edgeDefect u v i)=_
      rw [edgeDefect_mul_P,hid]

theorem defectCreation_root (u v : ℝ) (i j : ι) :
    star (defectCreation u v i j) (edgeDefect u v i (lp.single 2 ([],true) 1))=0 := by
  have hroot := diagonal_annihilation_edge_root u v i j
    (⟨edgeDefect u v i,edgeDefect_mem_edge u v i⟩ : edgeAlgebra u v i) true true
  change star (edgeCreation j true true) (edgeDefect u v i (lp.single 2 ([], true) 1))=0 at hroot
  rw [defectCreation,star_mul,star_mul,(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    mul_apply_eq_comp,mul_apply_eq_comp]
  have hd : edgeDefect u v i (edgeDefect u v i (lp.single 2 ([],true) 1))=
      edgeDefect u v i (lp.single 2 ([],true) 1) :=
    DFunLike.congr_fun (edgeDefect_projection u v i).isIdempotentElem.eq _
  rw [hd,hroot,map_zero]

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.SupportedSemicircle
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem unnormalized_eigen_root_zero (d L : E →L[ℂ] E) (hd : IsStarProjection d)
    (hleft : d*L=L) (hright : L*d=L) (ξ : E) (hξ : ξ≠0) (hdξ : d ξ=ξ)
    (hL : star L*L=inner ℂ ξ ξ • d) (hroot : star L ξ=0)
    (z : ℂ) (η : E) (he : (L+star L) η=z • η) : inner ℂ ξ η=0 := by
  let c : ℂ := (‖ξ‖:ℂ)⁻¹
  have hn : (‖ξ‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hξ)
  have hc : c≠0 := inv_ne_zero hn
  have hsc : star c=c := by simp only [c,star_inv₀,Complex.star_def,Complex.conj_ofReal]
  have hu : c*c*inner ℂ ξ ξ=1 := by
    rw [inner_self_eq_norm_sq_to_K]
    dsimp [c]
    field_simp
  have hnorm : inner ℂ (c • ξ) (c • ξ)=1 := by
    rw [inner_smul_left,inner_smul_right]
    change star c*(c*inner ℂ ξ ξ)=1
    rw [hsc,← mul_assoc,hu]
  have hcov : star (c • L)*(c • L)=d := by
    rw [star_smul,hsc,smul_mul_assoc,mul_smul_comm,hL,smul_smul,smul_smul]
    rw [hu,one_smul]
  have hl : d*(c • L)=c • L := by rw [mul_smul_comm,hleft]
  have hr : (c • L)*d=c • L := by rw [smul_mul_assoc,hright]
  have hdv : d (c • ξ)=c • ξ := by rw [map_smul,hdξ]
  have hov : star (c • L) (c • ξ)=0 := by
    rw [star_smul,hsc,_root_.smul_apply,map_smul,hroot,smul_zero,smul_zero]
  have hev : ((c • L)+star (c • L)) η=(c*z) • η := by
    rw [star_smul,hsc,← smul_add,_root_.smul_apply,he,smul_smul]
  have hh := eigen_root_zero d (c • L) hd hl hr hcov (c • ξ) hnorm hdv hov (c*z) η hev
  rw [inner_smul_left] at hh
  change star c*inner ℂ ξ η=0 at hh
  rw [hsc] at hh
  exact (mul_eq_zero.mp hh).resolve_left hc

end FreeGroupFactorMain.SupportedSemicircle
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

theorem edgeDefect_root_ne_zero (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    edgeDefect u v i (lp.single 2 ([],true) 1)≠0 := by
  intro hzero
  have he := vacuumTrace_supported_root u v (edgeDefect u v i)
    (P_mul_edgeDefect u v i) (edgeDefect_mul_P u v i)
  rw [edgeDefect_trace u v hv hvu,hzero] at he
  simp only [lp.coeFn_zero,Pi.zero_apply,mul_zero,Complex.ofReal_eq_zero] at he
  nlinarith

theorem edgeDefect_root_inner (u v : ℝ) (i : ι) :
    inner ℂ (edgeDefect u v i (lp.single 2 ([],true) 1))
      (edgeDefect u v i (lp.single 2 ([],true) 1))=
        (edgeDefect u v i (lp.single 2 ([],true) 1)) ([],true) := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 ([],true) 1)
    ((star (edgeDefect u v i)*edgeDefect u v i) (lp.single 2 ([],true) 1))=_
  rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,
    (edgeDefect_projection u v i).isIdempotentElem.eq]
  simp only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]

theorem defectSemicircle_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i j : ι) (z : ℂ) (η : H ι)
    (he : (defectCreation u v i j+star (defectCreation u v i j)) η=z • η) :
    inner ℂ (edgeDefect u v i (lp.single 2 ([],true) 1)) η=0 := by
  apply SupportedSemicircle.unnormalized_eigen_root_zero
    (edgeDefect u v i) (defectCreation u v i j) (edgeDefect_projection u v i)
    (defectCreation_left u v i j) (defectCreation_right u v i j)
    _ (edgeDefect_root_ne_zero u v hv hvu i) _ _ (defectCreation_root u v i j) z η he
  · exact DFunLike.congr_fun (edgeDefect_projection u v i).isIdempotentElem.eq _
  · rw [edgeDefect_root_inner]
    exact defectCreation_covariance u v i j

end FreeGroupFactorMain.WeightedFock

end

end OAI
