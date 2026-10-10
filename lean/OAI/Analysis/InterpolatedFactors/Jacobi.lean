import OAI.Analysis.InterpolatedFactors.Rerouting

namespace OAI

noncomputable section

universe u_1 u_2 u_3

open Filter Topology
namespace FreeGroupFactorMain.JacobiNonatom

def invariant (a c : ℂ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  a*((x n)^2+(x (n+1))^2)-c*x n*x (n+1)

 theorem invariant_step (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n) (n : ℕ) :
    invariant a c x (n+1)=invariant a c x n := by
  apply mul_left_cancel₀ ha
  calc
    a*invariant a c x (n+1)=a*invariant a c x n+
      (a*x (n+2)-a*x n)*(a*x (n+2)+a*x n-c*x (n+1)) := by
      simp only [invariant,Nat.add_assoc]
      ring
    _ = a*invariant a c x n := by rw [h];ring

 theorem invariant_constant (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n) (n : ℕ) :
    invariant a c x n=invariant a c x 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [invariant_step a c ha x h,ih]

 theorem invariant_zero (a c : ℂ) (ha : a≠0) (x : ℕ → ℂ)
    (h : ∀ n,a*x (n+2)=c*x (n+1)-a*x n)
    (hx : Tendsto x atTop (𝓝 0)) : invariant a c x 0=0 := by
  have hx' := hx.comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto (invariant a c x) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun n => a*((x n)^2+(x (n+1))^2)) atTop
        (𝓝 (a*((0:ℂ)^2+0^2))) :=
      tendsto_const_nhds.mul ((hx.pow 2).add (hx'.pow 2))
    have h₂ : Tendsto (fun n => c*x n*x (n+1)) atTop (𝓝 (c*0*0)) :=
      (tendsto_const_nhds.mul hx).mul hx'
    change Tendsto (fun n => a*((x n)^2+(x (n+1))^2)-c*x n*x (n+1)) atTop (𝓝 0)
    simpa only [zero_pow (by decide : (2:ℕ)≠0),zero_add,mul_zero,sub_zero]
      using h₁.sub h₂
  have he : invariant a c x=(fun _ : ℕ => invariant a c x 0) :=
    funext (invariant_constant a c ha x h)
  rw [he] at hl
  exact tendsto_nhds_unique tendsto_const_nhds hl

 theorem nonzero_eigenvector_zero (u v z : ℂ) (hu : u≠0) (hv : v≠0) (hz : z≠0)
    (x : ℕ → ℂ) (hx : Tendsto x atTop (𝓝 0))
    (hfirst : (u*v)*x 1=(z-u^2)*x 0)
    (hstep : ∀ n,(u*v)*x (n+2)=(z-u^2-v^2)*x (n+1)-(u*v)*x n) :
    ∀ n,x n=0 := by
  have hi := invariant_zero (u*v) (z-u^2-v^2) (mul_ne_zero hu hv) x hstep hx
  have hb : (u*v)*invariant (u*v) (z-u^2-v^2) x 0=z*v^2*(x 0)^2 := by
    calc
      _ = (u*v)^2*(x 0)^2+((u*v)*x 1)^2-
        (z-u^2-v^2)*x 0*((u*v)*x 1) := by simp only [invariant];ring
      _ = _ := by rw [hfirst];ring
  rw [hi,mul_zero] at hb
  have h0 : x 0=0 := by
    have hz : (x 0)^2=0 := (mul_eq_zero.mp hb.symm).resolve_left
      (mul_ne_zero hz (pow_ne_zero 2 hv))
    exact (sq_eq_zero_iff).mp hz
  have h1 : x 1=0 := by
    rw [h0,mul_zero] at hfirst
    exact (mul_eq_zero.mp hfirst).resolve_left (mul_ne_zero hu hv)
  intro n
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n hn hn1 =>
    have h := hstep n
    rw [hn,hn1,mul_zero,mul_zero,sub_self] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hu hv)

end FreeGroupFactorMain.JacobiNonatom
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Filter Topology
open scoped ENNReal
variable {ι : Type u_1} [DecidableEq ι]

def jacobiList (i : ι) : ℕ → List (ι × Bool)
  | 0 => []
  | n+1 => (i,false)::(i,true)::jacobiList i n

def jacobiPath (i : ι) (n : ℕ) : Path ι := (jacobiList i n,false)
def oddJacobiPath (i : ι) (n : ℕ) : Path ι := ((i,true)::jacobiList i n,false)
def jacobiBasis (i : ι) (n : ℕ) : H ι := lp.single 2 (jacobiPath i n) 1
def oddJacobiBasis (i : ι) (n : ℕ) : H ι := lp.single 2 (oddJacobiPath i n) 1

omit [DecidableEq ι] in
@[simp] theorem jacobiList_length (i : ι) (n : ℕ) : (jacobiList i n).length=2*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [jacobiList,List.length_cons,ih];omega

omit [DecidableEq ι] in
 theorem jacobiPath_injective (i : ι) : Function.Injective (jacobiPath i) := by
  intro n m h
  have hh := congrArg (fun w : Path ι => w.1.length) h
  simp only [jacobiPath,jacobiList_length] at hh
  omega

omit [DecidableEq ι] in
@[simp] theorem jacobiPath_start (i : ι) (n : ℕ) : start (jacobiPath i n)=false := by
  cases n <;> rfl
omit [DecidableEq ι] in
@[simp] theorem oddJacobiPath_start (i : ι) (n : ℕ) : start (oddJacobiPath i n)=true := rfl

 theorem offDiagonal_jacobi_zero (u v : ℝ) (i : ι) :
    offDiagonal u v i (jacobiBasis i 0)=(u:ℂ) • oddJacobiBasis i 0 := by
  simp only [offDiagonal_edges,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,
    oddJacobiPath,_root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_nil,
    smul_zero,add_zero]
  rfl

 theorem offDiagonal_jacobi_succ (u v : ℝ) (i : ι) (n : ℕ) :
    offDiagonal u v i (jacobiBasis i (n+1))=
      (u:ℂ) • oddJacobiBasis i (n+1)+(v:ℂ) • oddJacobiBasis i n := by
  simp only [offDiagonal_edges,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,
    oddJacobiPath,_root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_cons,
    start,ite_true,eq_self,true_and]

 theorem offDiagonalStar_oddJacobi (u v : ℝ) (i : ι) (n : ℕ) :
    star (offDiagonal u v i) (oddJacobiBasis i n)=
      (u:ℂ) • jacobiBasis i n+(v:ℂ) • jacobiBasis i (n+1) := by
  cases n <;>
    simp only [offDiagonal_edges,star_add (R := Operator ι),star_smul,star_star,Complex.star_def,
      Complex.conj_ofReal,jacobiBasis,jacobiPath,jacobiList,oddJacobiBasis,oddJacobiPath,
      _root_.smul_apply,add_apply,edgeCreation_single,edgeAnnihilation_cons,
      start,ite_true,eq_self,true_and]

 def edgeSquare (u v : ℝ) (i : ι) : Operator ι := star (offDiagonal u v i)*offDiagonal u v i

 theorem edgeSquare_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (edgeSquare u v i) := by
  simp [IsSelfAdjoint,edgeSquare,star_mul]

 theorem edgeSquare_jacobi_zero (u v : ℝ) (i : ι) :
    edgeSquare u v i (jacobiBasis i 0)=
      ((u:ℂ)^2) • jacobiBasis i 0+((u:ℂ)*v) • jacobiBasis i 1 := by
  rw [edgeSquare,mul_apply_eq_comp,offDiagonal_jacobi_zero,map_smul,offDiagonalStar_oddJacobi]
  simp only [smul_add,smul_smul,pow_two]

 theorem edgeSquare_jacobi_succ (u v : ℝ) (i : ι) (n : ℕ) :
    edgeSquare u v i (jacobiBasis i (n+1))=
      ((u:ℂ)*v) • jacobiBasis i n+
        ((u:ℂ)^2+(v:ℂ)^2) • jacobiBasis i (n+1)+
          ((u:ℂ)*v) • jacobiBasis i (n+2) := by
  rw [edgeSquare,mul_apply_eq_comp,offDiagonal_jacobi_succ,map_add,map_smul,
    map_smul,offDiagonalStar_oddJacobi,offDiagonalStar_oddJacobi]
  simp only [smul_add,smul_smul,pow_two,add_smul,Nat.add_assoc]
  module

omit [DecidableEq ι] in
 theorem jacobi_coordinates_decay (i : ι) (ξ : H ι) :
    Tendsto (fun n => ξ (jacobiPath i n)) atTop (𝓝 0) := by
  have hs : Summable (fun w : Path ι => ‖ξ w‖^2) := by
    simpa using (lp.memℓp ξ).summable (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal)
  have ht := (hs.comp_injective (jacobiPath_injective i)).tendsto_atTop_zero
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  have hn : Tendsto (fun n => ‖ξ (jacobiPath i n)‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

 theorem edgeSquare_eigen_coordinates (u v : ℝ) (i : ι) (z : ℂ) (ξ : H ι)
    (hξ : edgeSquare u v i ξ=z • ξ) :
    ((u:ℂ)*v)*ξ (jacobiPath i 1)=(z-(u:ℂ)^2)*ξ (jacobiPath i 0) ∧
      ∀ n,((u:ℂ)*v)*ξ (jacobiPath i (n+2))=
        (z-(u:ℂ)^2-(v:ℂ)^2)*ξ (jacobiPath i (n+1))-
          ((u:ℂ)*v)*ξ (jacobiPath i n) := by
  have he (n : ℕ) : inner ℂ (edgeSquare u v i (jacobiBasis i n)) ξ=
      z*ξ (jacobiPath i n) := by
    rw [← (edgeSquare_selfAdjoint u v i).star_eq,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_left,hξ,inner_smul_right]
    simp [jacobiBasis,lp.inner_single_left,RCLike.inner_apply]
  constructor
  · have h := he 0
    rw [edgeSquare_jacobi_zero] at h
    simp [jacobiBasis,lp.inner_single_left,
      RCLike.inner_apply] at h
    linear_combination h
  · intro n
    have h := he (n+1)
    rw [edgeSquare_jacobi_succ] at h
    simp [jacobiBasis,lp.inner_single_left,
      RCLike.inner_apply] at h
    linear_combination h

 theorem edgeSquare_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (z : ℂ) (hz : z≠0) (ξ : H ι) (hξ : edgeSquare u v i ξ=z • ξ) :
    ξ ([],false)=0 := by
  have h := edgeSquare_eigen_coordinates u v i z ξ hξ
  exact JacobiNonatom.nonzero_eigenvector_zero (u:ℂ) (v:ℂ) z
    (Complex.ofReal_ne_zero.mpr hu) (Complex.ofReal_ne_zero.mpr hv) hz
    (fun n => ξ (jacobiPath i n)) (jacobi_coordinates_decay i ξ) h.1 h.2 0

end

section
open FreeFock
variable {ι : Type u_2}

def flipPath : Path ι ≃ Path ι where
  toFun w := (w.1.map (fun a => (a.1,!a.2)),!w.2)
  invFun w := (w.1.map (fun a => (a.1,!a.2)),!w.2)
  left_inv w := by
    rcases w with ⟨l,b⟩
    simp only [List.map_map,Function.comp_def,Bool.not_not]
    simp
  right_inv w := by
    rcases w with ⟨l,b⟩
    simp only [List.map_map,Function.comp_def,Bool.not_not]
    simp

@[simp] theorem flipPath_apply (w : Path ι) : flipPath w=(w.1.map (fun a => (a.1,!a.2)),!w.2) := rfl

@[simp] theorem flipPath_involutive (w : Path ι) : flipPath (flipPath w)=w := by
  rcases w with ⟨l,b⟩
  simp only [flipPath_apply,List.map_map,Function.comp_def,Bool.not_not]
  simp

@[simp] theorem flipPath_symm (w : Path ι) : flipPath.symm w=flipPath w := by
  apply flipPath.injective
  rw [Equiv.apply_symm_apply,flipPath_involutive]

@[simp] theorem start_flipPath (w : Path ι) : start (flipPath w)=!(start w) := by
  rcases w with ⟨l,b⟩
  cases l <;> rfl

def flipSpatial : H ι ≃ₗᵢ[ℂ] H ι := hilbertReindex flipPath

@[simp] theorem flipSpatial_apply (ξ : H ι) (w : Path ι) : flipSpatial ξ w=ξ (flipPath w) := by
  simp only [flipSpatial,hilbertReindex_apply,flipPath_symm]

variable [DecidableEq ι]

theorem flipSpatial_single (w : Path ι) (z : ℂ) :
    flipSpatial (lp.single 2 w z)=lp.single 2 (flipPath w) z := by
  ext a
  simp only [flipSpatial_apply,lp.single_apply,Pi.single_apply]
  by_cases h : flipPath w=a
  · subst a
    simp only [flipPath_involutive,ite_true]
  · have hh : w≠flipPath a := by
      intro he
      apply h
      rw [he,flipPath_involutive]
    simp_all [eq_comm]

theorem flipSpatial_vertex_intertwines (r : Bool) (ξ : H ι) :
    flipSpatial (vertex r ξ)=vertex (!r) (flipSpatial ξ) := by
  have he : flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap*(vertex r : Operator ι)=
      vertex (!r)*flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply operator_basis_ext
    intro w
    simp only [mul_apply_eq_comp,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,vertex_single,flipSpatial_single,start_flipPath]
    split_ifs with h h' h' <;> simp_all [flipSpatial_single]
  exact DFunLike.congr_fun he ξ

theorem flipSpatial_conjugates_vertex (r : Bool) :
    flipSpatial.conjStarAlgEquiv (vertex r : Operator ι)=vertex (!r) := by
  ext ξ
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [flipSpatial_vertex_intertwines,LinearIsometryEquiv.apply_symm_apply]

theorem flipSpatial_creation_intertwines (i : ι) (r : Bool) (ξ : H ι) :
    flipSpatial (creation i r ξ)=creation i (!r) (flipSpatial ξ) := by
  have he : flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap*creation i r=
      creation i (!r)*flipSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply operator_basis_ext
    intro w
    simp only [mul_apply_eq_comp,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe,creation_single,flipSpatial_single,flipPath_apply,List.map_cons]
  exact DFunLike.congr_fun he ξ

theorem flipSpatial_conjugates_creation (i : ι) (r : Bool) :
    flipSpatial.conjStarAlgEquiv (creation i r)=creation i (!r) := by
  ext ξ
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
  rw [flipSpatial_creation_intertwines,LinearIsometryEquiv.apply_symm_apply]

theorem flipSpatial_conjugates_edgeCreation (i : ι) (r s : Bool) :
    flipSpatial.conjStarAlgEquiv (edgeCreation i r s)=edgeCreation i (!r) (!s) := by
  rw [edgeCreation,map_mul,flipSpatial_conjugates_creation,flipSpatial_conjugates_vertex]
  rfl

theorem flipSpatial_conjugates_offDiagonal (u v : ℝ) (i : ι) :
    flipSpatial.conjStarAlgEquiv (offDiagonal u v i)=star (offDiagonal v u i) := by
  simp only [offDiagonal_edges,map_add,map_smul,map_star,flipSpatial_conjugates_edgeCreation,
    Bool.not_true,Bool.not_false,star_add (R := Operator ι),star_smul,star_star,Complex.star_def,Complex.conj_ofReal]
  exact add_comm _ _

theorem flipSpatial_conjugates_edgeSquare (u v : ℝ) (i : ι) :
    flipSpatial.conjStarAlgEquiv (edgeSquare u v i)=offDiagonal v u i*star (offDiagonal v u i) := by
  rw [edgeSquare,map_mul,map_star,flipSpatial_conjugates_offDiagonal,star_star]

theorem leftEdgeSquare_eigen_root_zero (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : ι) (z : ℂ) (hz : z≠0) (ξ : H ι)
    (hξ : (offDiagonal u v i*star (offDiagonal u v i)) ξ=z • ξ) : ξ ([],true)=0 := by
  have he : edgeSquare v u i (flipSpatial.symm ξ)=z • flipSpatial.symm ξ := by
    apply flipSpatial.injective
    rw [map_smul,LinearIsometryEquiv.apply_symm_apply]
    have hh := DFunLike.congr_fun (flipSpatial_conjugates_edgeSquare v u i) ξ
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using hh.trans hξ
  have hh := edgeSquare_eigen_root_zero v u hv hu i z hz (flipSpatial.symm ξ) he
  have hh' : flipSpatial.symm ξ=flipSpatial ξ := by
    apply flipSpatial.injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    ext w
    simp only [flipSpatial_apply,flipPath_involutive]
  rw [hh',flipSpatial_apply] at hh
  exact hh

end
open FreeFock Amplification.Polar
variable {ι : Type u_3} [DecidableEq ι]

def leftModulus (u v : ℝ) (i : ι) : Operator ι := offDiagonal u v i*star (edgePolar u v i)

theorem leftModulus_selfAdjoint (u v : ℝ) (i : ι) : IsSelfAdjoint (leftModulus u v i) :=
  edge_left_modulus_selfAdjoint u v i

theorem leftModulus_square (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    leftModulus u v i*leftModulus u v i=offDiagonal u v i*star (offDiagonal u v i) := by
  calc
    _ = leftModulus u v i*star (leftModulus u v i) := by rw [(leftModulus_selfAdjoint u v i).star_eq]
    _ = (offDiagonal u v i*star (edgePolar u v i))*(edgePolar u v i*star (offDiagonal u v i)) := by
      simp only [leftModulus,star_mul,star_star]
    _ = _ := by
      rw [mul_assoc,← mul_assoc (star (edgePolar u v i)),edgePolar_initial u v hv hvu,
        ← mul_assoc,offDiagonal_right]

theorem leftModulus_mul_range (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    leftModulus u v i*edgeRange u v i=leftModulus u v i := by
  rw [leftModulus,edgeRange,mul_assoc,← mul_assoc (star (edgePolar u v i)),
    edgePolar_initial u v hv hvu,← mul_assoc,offDiagonal_right]

theorem range_mul_leftModulus (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    edgeRange u v i*leftModulus u v i=leftModulus u v i := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (leftModulus_selfAdjoint u v i).star_eq] using congrArg star (leftModulus_mul_range u v hv hvu i)

theorem starPolar_mul_leftModulus (u v : ℝ) (hv : 0≤v) (hvu : v<u) (i : ι) :
    star (edgePolar u v i)*leftModulus u v i=star (offDiagonal u v i) := by
  rw [← (leftModulus_selfAdjoint u v i).star_eq,leftModulus,star_mul,star_star,
    ← mul_assoc,edgePolar_initial u v hv hvu]
  simpa only [star_mul,projection_P.one_sub.isSelfAdjoint.star_eq]
    using congrArg star (offDiagonal_right u v i)

theorem range_zero_of_starEdge_zero (u v : ℝ) (i : ι) (η : H ι)
    (hη : star (offDiagonal u v i) η=0) : edgeRange u v i η=0 := by
  rw [edgeRange,edgePolar,partialIsometry_final]
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  rw [closedRange_eq_orthogonal_ker,Submodule.orthogonal_orthogonal]
  exact hη

theorem leftModulus_eigen_root_zero (u v : ℝ) (hv : 0<v) (hvu : v<u)
    (i : ι) (z : ℂ) (η : H ι) (he : leftModulus u v i η=z • η) :
    inner ℂ (edgeRange u v i (lp.single 2 ([],true) 1)) η=0 := by
  rw [← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 ([],true) 1) (star (edgeRange u v i) η)=0
  rw [(edgeRange_projection u v i).isSelfAdjoint.star_eq]
  by_cases hz : z=0
  · have hf : leftModulus u v i η=0 := by simpa only [hz,zero_smul] using he
    have hx : star (offDiagonal u v i) η=0 := by
      rw [← starPolar_mul_leftModulus u v hv.le hvu i,mul_apply_eq_comp,hf,map_zero]
    rw [range_zero_of_starEdge_zero u v i η hx,inner_zero_right]
  · have hs : (offDiagonal u v i*star (offDiagonal u v i)) η=(z*z) • η := by
      rw [← leftModulus_square u v hv.le hvu i,mul_apply_eq_comp,he,map_smul,he,smul_smul]
    have hr : edgeRange u v i η=η := by
      apply smul_right_injective (H ι) hz
      change z • edgeRange u v i η=z • η
      rw [← map_smul,← he]
      exact DFunLike.congr_fun (range_mul_leftModulus u v hv.le hvu i) η
    rw [hr]
    simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using
      leftEdgeSquare_eigen_root_zero u v (hv.trans hvu).ne' hv.ne' i (z*z) (mul_ne_zero hz hz) η hs

end FreeGroupFactorMain.WeightedFock

end

end OAI
