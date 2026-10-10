import OAI.Analysis.TracialSplitting.VectorApproximation

namespace OAI

universe uA uE uK uN


section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

noncomputable section

open scoped TensorProduct InnerProductSpace

open UniformSpace.Completion

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

noncomputable section

open scoped ComplexOrder InnerProductSpace

open UniformSpace.Completion

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open UniformSpace.Completion UnitalTomsWinter

namespace NuclearTrace

section Coefficients

variable {A : Type uA} {K : Type uK} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))

variable {N : Type uN} [Fintype N] (k : N → K) (a : N → A)

def coefficientMap : A →ₗ[ℂ] A where
  toFun x := ∑ i, ∑ j, (⟪k i,α x (k j)⟫_ℂ) • (star (a i)*a j)
  map_add' x y := by
    simp [map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by
    simp [smul_smul,Finset.smul_sum]

lemma coefficientMap_star (x : A) :
    star (coefficientMap α k a x) = coefficientMap α k a (star x) := by
  classical
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,star_sum,star_smul,
    star_mul,star_star,map_star,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun c : ℂ => c • (star (a i)*a j)) (inner_conj_symm _ _)

lemma coefficientMap_selfAdjoint (x : A) (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (coefficientMap α k a x) := by
  exact (coefficientMap_star α k a x).trans (congrArg _ hx.star_eq)

end Coefficients

section GNSDensity

variable {A : Type uA} {K : Type uK} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

variable (f : A →ₚ[ℂ] ℂ)

def algebraTensorVector : K ⊗[ℂ] A →ₗ[ℂ] SpatialHilbert K f.GNS :=
  toComplₗᵢ.toLinearMap.comp (TensorProduct.map (LinearMap.id : K →ₗ[ℂ] K)
    (toComplₗᵢ.toLinearMap.comp f.toPreGNS.toLinearMap))

@[simp] lemma algebraTensorVector_tmul (k : K) (a : A) :
    algebraTensorVector (K := K) f (k ⊗ₜ[ℂ] a) =
      ((k ⊗ₜ[ℂ] (f.toPreGNS a : f.GNS) : K ⊗[ℂ] f.GNS) : SpatialHilbert K f.GNS) := rfl

lemma algebraTensorVector_dense : DenseRange (algebraTensorVector (K := K) f) := by
  let M := (algebraTensorVector (K := K) f).range.topologicalClosure
  have hmem (k : K) (h : f.GNS) :
      (((k ⊗ₜ[ℂ] h : K ⊗[ℂ] f.GNS) : SpatialHilbert K f.GNS)) ∈ M := by
    induction h using UniformSpace.Completion.induction_on with
    | hp =>
      apply ((algebraTensorVector (K := K) f).range.isClosed_topologicalClosure).preimage
      fun_prop
    | ih h =>
      apply Submodule.le_topologicalClosure
      exact ⟨k ⊗ₜ[ℂ] f.ofPreGNS h,by simp⟩
  intro z
  change z ∈ M
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact (algebraTensorVector (K := K) f).range.isClosed_topologicalClosure
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul k h => exact hmem k h
    | add z w hz hw => simpa only [coe_add] using M.add_mem hz hw

end GNSDensity

section CoefficientValue

variable {A : Type uA} {K : Type uK} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (f : A →ₚ[ℂ] ℂ)

variable (T : f.GNS →L[ℂ] f.GNS) (hT : ∀ a, Commute T (f.gnsStarAlgHom a))

include hT in
lemma gns_commutant_coefficient (a b : A) :
    ⟪(f.toPreGNS a : f.GNS),T (f.toPreGNS b : f.GNS)⟫_ℂ =
      ⟪Pureness.stateGNSVector f,T (f.gnsStarAlgHom (star a*b) (Pureness.stateGNSVector f))⟫_ℂ := by
  rw [← Pureness.stateGNS_apply_vector f a,← Pureness.stateGNS_apply_vector f b]
  rw [← ContinuousLinearMap.adjoint_inner_right,map_mul,map_star,
    ContinuousLinearMap.star_eq_adjoint]
  change ⟪Pureness.stateGNSVector f,
    star (f.gnsStarAlgHom a) (T (f.gnsStarAlgHom b (Pureness.stateGNSVector f)))⟫_ℂ = _
  rw [← map_star]
  have he := congrArg (fun R : f.GNS →L[ℂ] f.GNS =>
    R (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) (hT (star a)).eq
  change T (f.gnsStarAlgHom (star a) (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) =
    f.gnsStarAlgHom (star a) (T (f.gnsStarAlgHom b (Pureness.stateGNSVector f))) at he
  rw [map_star,ContinuousLinearMap.star_eq_adjoint] at he
  rw [map_star,ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun y => ⟪Pureness.stateGNSVector f,y⟫_ℂ) he.symm

include hT in
lemma spatial_coefficient_value {N : Type uN} [Fintype N] (k : N → K) (a : N → A) (x : A) :
    let ζ := algebraTensorVector f (∑ i, k i ⊗ₜ[ℂ] a i)
    ⟪ζ,spatialTensorOp (α x) T ζ⟫_ℂ =
      ⟪Pureness.stateGNSVector f,
        T (f.gnsStarAlgHom (coefficientMap α k a x) (Pureness.stateGNSVector f))⟫_ℂ := by
  classical
  dsimp only
  simp only [map_sum,algebraTensorVector_tmul,inner_sum,sum_inner]
  simp only [spatialTensorOp_coe,TensorProduct.mapL_tmul,UniformSpace.Completion.inner_coe,
    TensorProduct.inner_tmul]
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,map_sum,map_smul,
    sum_apply,smul_apply,inner_sum,inner_smul_right_eq_smul,smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [gns_commutant_coefficient f T hT]

end CoefficientValue

end NuclearTrace

noncomputable section

open scoped ComplexOrder TensorProduct InnerProductSpace

open Pureness UnitalTomsWinter

namespace NuclearTrace

section NuclearSeparation

variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype I]

theorem nuclear_coefficient_dual_bound (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) (x : I → selfAdjoint A)
    (l : I → selfAdjoint A →ₗ[ℝ] ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hl : ∀ i, ∀ a : selfAdjoint A, 0 ≤ (a : A) → |l i a| ≤ C * (f a).re)
    (hsep : ∀ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
      ∑ i, l i ⟨coefficientMap α k a (x i),coefficientMap_selfAdjoint α k a _ (x i).property⟩ ≤ 0) :
    ∑ i, l i (x i) ≤ 0 := by
  classical
  let : Module ℝ (SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS) :=
    Module.complexToReal _
  have hrep (i : I) : ∃ T : f.GNS →L[ℂ] f.GNS, IsSelfAdjoint T ∧
      (∀ a, Commute T (f.gnsStarAlgHom a)) ∧
      ∀ a : selfAdjoint A, l i a =
        (⟪stateGNSVector f,T (f.gnsStarAlgHom a (stateGNSVector f))⟫_ℂ).re := by
    obtain ⟨T,hT,_,_,hcomm,hval⟩ := real_functional_in_commutant f (l i) C (hl i) hC
    exact ⟨T,hT,hcomm,hval⟩
  choose T hTsa hTcomm hTval using hrep
  let B := StarSubalgebra.centralizer ℂ (Set.range f.gnsStarAlgHom)
  let _ : IsClosed (B : Set (f.GNS →L[ℂ] f.GNS)) := Set.isClosed_centralizer _
  let _ : CStarAlgebra B := StarSubalgebra.cstarAlgebra B
  let ρ : B →⋆ₐ[ℂ] (f.GNS →L[ℂ] f.GNS) := B.subtype
  have hρ (a : A) (b : B) : Commute (f.gnsStarAlgHom a) (ρ b) := by
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp b.property _ ⟨a,rfl⟩).1
  have hTB (i : I) : T i ∈ B := by
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    rintro _ ⟨a,rfl⟩
    refine ⟨(hTcomm i a).symm.eq,?_⟩
    simpa only [map_star] using (hTcomm i (star a)).symm.eq
  let Ti (i : I) : B := ⟨T i,hTB i⟩
  let j := spatialStarTensorHom α ρ
  have hj : Function.Injective j := spatialStarTensorHom_injective_of_faithful α ρ hα
    Subtype.val_injective
  let _ : CStarAlgebra (SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS) := inferInstance
  obtain ⟨σ,_,hσ⟩ := nuclear_cyclic_extension hA f.gnsStarAlgHom ρ hρ
    (stateGNSVector f) (stateGNSVector_norm f hf) j hj
  let S : SpatialHilbert K f.GNS →L[ℂ] SpatialHilbert K f.GNS :=
    ∑ i, spatialTensorOp (α (x i)) (T i)
  have hSsa : IsSelfAdjoint S := by
    apply isSelfAdjoint_sum
    intro i _
    change star (spatialTensorOp (α (x i)) (T i)) = _
    rw [← spatialTensorOp_star,(hTsa i).star_eq,← map_star,(x i).property.star_eq]
  have hquadDense (z : K ⊗[ℂ] A) :
      (⟪algebraTensorVector f z,S (algebraTensorVector f z)⟫_ℂ).re ≤ 0 := by
    obtain ⟨n,k,a,rfl⟩ := TensorProduct.exists_sum_tmul_eq z
    have he (i : I) := spatial_coefficient_value α f (T i) (hTcomm i) k a (x i)
    change (⟪algebraTensorVector f (∑ j, k j ⊗ₜ[ℂ] a j),
      (∑ i, spatialTensorOp (α (x i)) (T i))
        (algebraTensorVector f (∑ j, k j ⊗ₜ[ℂ] a j))⟫_ℂ).re ≤ 0
    simp only [sum_apply,inner_sum,Complex.re_sum,he]
    have hv (i : I) := (hTval i ⟨coefficientMap α k a (x i),
      coefficientMap_selfAdjoint α k a _ (x i).property⟩).symm
    dsimp only at hv
    simp only [hv]
    exact hsep n k a
  have hquad (ζ : SpatialHilbert K f.GNS) : (⟪ζ,S ζ⟫_ℂ).re ≤ 0 := by
    exact (algebraTensorVector_dense (K := K) f).induction_on ζ
      (isClosed_le (show Continuous (fun ζ : SpatialHilbert K f.GNS =>
        (⟪ζ,S ζ⟫_ℂ).re) by fun_prop) continuous_const) hquadDense
  have hSle : S ≤ 0 := by
    simpa only [zero_smul] using operator_le_of_unit_quadratic hSsa
      (c := 0) (fun ζ _ => hquad ζ)
  have heval (i : I) : (σ (spatialTensorOp (α (x i)) (T i))).re = l i (x i) := by
    have he := hσ (x i : A) (Ti i)
    change σ (spatialStarTensorHom α ρ ((x i : A) ⊗ₜ[ℂ] Ti i)) = _ at he
    rw [spatialStarTensorHom_tmul] at he
    have hcomm := congrArg (fun R : f.GNS →L[ℂ] f.GNS => R (stateGNSVector f))
      (hTcomm i (x i)).eq
    exact (congrArg Complex.re
      (he.trans (congrArg (fun y => ⟪stateGNSVector f,y⟫_ℂ) hcomm.symm))).trans
      (hTval i (x i)).symm
  have hh := (σ.monotone hSle).1
  change (σ S).re ≤ (σ 0).re at hh
  simpa only [S,map_sum,Complex.re_sum,heval,map_zero,Complex.zero_re] using hh

end NuclearSeparation

end NuclearTrace

noncomputable section

open scoped Pointwise

namespace NuclearTrace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma linear_bound_of_seminorm_ball (p : Seminorm ℝ E) (f : E →L[ℝ] ℝ)
    {ε b : ℝ} (hε : 0 < ε) (hb : 0 < b)
    (h : ∀ y, p y < ε → |f y| < b) :
    ∀ y, |f y| ≤ (2*b/ε) * p y := by
  intro y
  by_cases hz : p y = 0
  · have hfy : f y = 0 := by
      by_contra hne
      have ha : 0 < |f y| := abs_pos.mpr hne
      let t := (b+1) / |f y|
      have ht : 0 < t := div_pos (by linarith) ha
      have hy : p (t • y) < ε := by
        rw [map_smul_eq_mul,hz,mul_zero]
        exact hε
      have hh := h (t • y) hy
      rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos ht] at hh
      have he : t * |f y| = b+1 := div_mul_cancel₀ (b+1) ha.ne'
      rw [he] at hh
      linarith
    simp [hfy,hz]
  · have hp : 0 < p y := lt_of_le_of_ne (apply_nonneg p y) (Ne.symm hz)
    let t := ε / (2*p y)
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) hp)
    have hy : p (t • y) < ε := by
      rw [map_smul_eq_mul,Real.norm_eq_abs,abs_of_pos ht]
      have he : t * p y = ε/2 := by dsimp [t]; field_simp
      rw [he]
      linarith
    have hh := h (t • y) hy
    rw [map_smul,smul_eq_mul,abs_mul,abs_of_pos ht] at hh
    have he : b/t = (2*b/ε)*p y := by dsimp [t]; field_simp
    exact (lt_of_mul_lt_mul_left (show t * |f y| < t * ((2*b/ε)*p y) by
      rw [← he,mul_div_cancel₀ _ ht.ne']; exact hh) ht.le).le

theorem seminorm_cone_approximation_of_dual (p : Seminorm ℝ E) (hp : Continuous p)
    (S : Set E) (hS : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ S, t • s ∈ S) (x : E)
    (hx : ∀ f : E →L[ℝ] ℝ, (∃ C : ℝ, 0 ≤ C ∧ ∀ y, |f y| ≤ C * p y) →
      (∀ s ∈ S, f s ≤ 0) → f x ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ s ∈ S, p (x-s) < ε := by
  classical
  by_contra hn
  let U : Set E := S + p.ball 0 ε
  have hU : Convex ℝ U := hS.add (p.convex_ball 0 ε)
  have hUopen : IsOpen U := by
    dsimp [U]
    rw [p.ball_zero_eq]
    exact (hp.isOpen_preimage _ isOpen_Iio).add_left
  have hxU : x ∉ U := by
    rintro ⟨s,hs,y,hy,hxy⟩
    apply hn
    refine ⟨s,hs,?_⟩
    have he : x-s = y := by change s + y = x at hxy; rw [← hxy]; abel
    simpa only [he,Seminorm.mem_ball_zero] using hy
  obtain ⟨f,hf⟩ := geometric_hahn_banach_open_point hU hUopen hxU
  have h0ball : (0 : E) ∈ p.ball 0 ε := by simpa using hε
  have h0U : (0 : E) ∈ U := ⟨0,h0,0,h0ball,by simp⟩
  have hfx : 0 < f x := by simpa only [map_zero] using hf 0 h0U
  have hbound : ∀ y, p y < ε → |f y| < f x := by
    intro y hy
    have hyU : y ∈ U := ⟨0,h0,y,by simpa using hy,by simp⟩
    have hnU : -y ∈ U := ⟨0,h0,-y,by simpa using hy,by simp⟩
    have hpos := hf y hyU
    have hneg := hf (-y) hnU
    rw [map_neg] at hneg
    exact abs_lt.mpr ⟨by linarith,hpos⟩
  have hcone : ∀ s ∈ S, f s ≤ 0 := by
    intro s hs
    by_contra hnp
    have hfs : 0 < f s := lt_of_not_ge hnp
    let t := (f x+1) / f s
    have ht : 0 < t := div_pos (by linarith) hfs
    have hts : t • s ∈ U := ⟨t • s,hsmul t ht.le s hs,0,h0ball,by simp⟩
    have htfx := hf (t • s) hts
    rw [map_smul,smul_eq_mul] at htfx
    have he : t * f s = f x+1 := div_mul_cancel₀ (f x+1) hfs.ne'
    rw [he] at htfx
    linarith
  have hnfx := hx f ⟨2*f x/ε,by positivity,
    linear_bound_of_seminorm_ball p f hε hfx hbound⟩ hcone
  exact (not_le_of_gt hfx) hnfx

end NuclearTrace

noncomputable section

open scoped ComplexOrder

namespace CurrentMain

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma traceOneNorm_smul_real (τ : Pureness.TracialState A) (c : ℝ) (a : A) :
    traceOneNorm τ (c • a) = ‖c‖ * traceOneNorm τ a := by
  simp [traceOneNorm,CFC.abs_smul,τ.functional.map_smul_of_tower]

lemma traceOneNorm_le_norm (τ : Pureness.TracialState A) (a : A) :
    traceOneNorm τ a ≤ ‖a‖ := by
  exact (Complex.re_le_norm _).trans ((trace_norm_le_norm τ _).trans_eq CFC.norm_abs)

def tracialOneSeminorm (τ : Pureness.TracialState A) : Seminorm ℝ (selfAdjoint A) where
  toFun a := traceOneNorm τ a
  map_zero' := by simp [traceOneNorm]
  neg' a := traceOneNorm_neg τ a
  add_le' a b := traceOneNorm_add_le τ a.property b.property
  smul' c a := traceOneNorm_smul_real τ c a

@[simp] lemma tracialOneSeminorm_apply (τ : Pureness.TracialState A) (a : selfAdjoint A) :
    tracialOneSeminorm τ a = traceOneNorm τ a := rfl

lemma tracialOneSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialOneSeminorm τ) := by
  apply Seminorm.continuous_of_le (p := tracialOneSeminorm τ)
    (q := normSeminorm ℝ (selfAdjoint A)) continuous_norm
  intro a
  exact traceOneNorm_le_norm τ a

lemma tracialOneSeminorm_of_nonneg (τ : Pureness.TracialState A) (a : selfAdjoint A)
    (ha : 0 ≤ (a : A)) : tracialOneSeminorm τ a = (τ.functional a).re := by
  simp [tracialOneSeminorm_apply,traceOneNorm,CFC.abs_of_nonneg (a : A) ha]

end CurrentMain

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
