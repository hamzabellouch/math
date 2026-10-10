import OAI.Analysis.InterpolatedFactors.Fock

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.Amplification.Polar

section

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
abbrev Operator (E : Type u_2) [NormedAddCommGroup E] [InnerProductSpace ℂ E] := E →L[ℂ] E

def modulus (T : Operator E) : Operator E := CFC.sqrt (star T*T)

theorem modulus_star (T : Operator E) : star (modulus T) = modulus T :=
  (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)).star_eq

theorem modulus_sq (T : Operator E) : modulus T*modulus T = star T*T :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)

theorem modulus_norm (T : Operator E) (x : E) : ‖modulus T x‖ = ‖T x‖ := by
  have hinner : inner ℂ (modulus T x) (modulus T x) = inner ℂ (T x) (T x) := by
    calc
      _ = inner ℂ ((star (modulus T)*modulus T) x) x := by
        exact (ContinuousLinearMap.adjoint_inner_left (modulus T) x (modulus T x)).symm
      _ = inner ℂ ((star T*T) x) x := by rw [modulus_star,modulus_sq]
      _ = _ := ContinuousLinearMap.adjoint_inner_left T x (T x)
  have hs : ‖modulus T x‖^2 = ‖T x‖^2 := by
    simpa only [inner_self_eq_norm_sq] using congrArg (RCLike.re : ℂ → ℝ) hinner
  nlinarith [norm_nonneg (modulus T x),norm_nonneg (T x)]

def closedRange (T : Operator E) : Submodule ℂ E := T.toLinearMap.range.topologicalClosure

instance closedRange_complete (T : Operator E) : CompleteSpace (closedRange T) :=
  (Submodule.isClosed_topologicalClosure _).isComplete.completeSpace_coe

def intoClosedRange (T : Operator E) : E →L[ℂ] closedRange T :=
  T.codRestrict (closedRange T) (fun x => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

omit [CompleteSpace E] in
theorem intoClosedRange_dense (T : Operator E) : DenseRange (intoClosedRange T) := by
  rw [DenseRange,Subtype.dense_iff,← Set.range_comp]
  change (closedRange T : Set E) ⊆ closure (Set.range (fun x : E => T x))
  rw [closedRange,Submodule.topologicalClosure_coe]
  exact Set.Subset.rfl

def polarSpatial (T : Operator E) : closedRange (modulus T) ≃ₗᵢ[ℂ] closedRange T :=
  (LinearEquiv.refl ℂ E).extendOfIsometry (intoClosedRange (modulus T)).toLinearMap
    (intoClosedRange T).toLinearMap (intoClosedRange_dense _) (intoClosedRange_dense _)
    (fun x => (modulus_norm T x).symm)

theorem polarSpatial_modulus (T : Operator E) (x : E) :
    polarSpatial T (intoClosedRange (modulus T) x) = intoClosedRange T x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

def partialIsometry (T : Operator E) : Operator E :=
  (closedRange T).subtypeL.comp ((polarSpatial T).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (closedRange (modulus T)).orthogonalProjectionOnto)

theorem partialIsometry_factorization (T : Operator E) : partialIsometry T * modulus T = T := by
  apply ContinuousLinearMap.ext
  intro x
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto (modulus T x)) : E) = T x
  have he : (closedRange (modulus T)).orthogonalProjectionOnto (modulus T x) = intoClosedRange (modulus T) x :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (intoClosedRange (modulus T) x)
  rw [he,polarSpatial_modulus]
  rfl

theorem partialIsometry_on_range (T : Operator E) (x : closedRange (modulus T)) :
    partialIsometry T x = (polarSpatial T x : E) := by
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x) : E) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem partialIsometry_inner (T : Operator E) (x y : E) :
    inner ℂ (partialIsometry T x) (partialIsometry T y) =
      inner ℂ ((closedRange (modulus T)).starProjection x) y := by
  change inner ℂ (polarSpatial T ((closedRange (modulus T)).orthogonalProjectionOnto x))
      (polarSpatial T ((closedRange (modulus T)).orthogonalProjectionOnto y)) = _
  rw [(polarSpatial T).inner_map_map]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

theorem partialIsometry_initial (T : Operator E) :
    star (partialIsometry T)*partialIsometry T = (closedRange (modulus T)).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left,partialIsometry_inner]

theorem partialIsometry_adjoint (T : Operator E) (x : E) :
    star (partialIsometry T) x =
      ((polarSpatial T).symm ((closedRange T).orthogonalProjectionOnto x) : E) := by
  apply ext_inner_right ℂ
  intro y
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ x ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto y) : E) = _
  rw [← Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto y)) x]
  rw [← (polarSpatial T).symm.inner_map_map,(polarSpatial T).symm_apply_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left _ _

theorem partialIsometry_final (T : Operator E) :
    partialIsometry T*star (partialIsometry T) = (closedRange T).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  rw [mul_apply_eq_comp,partialIsometry_adjoint,partialIsometry_on_range,
    (polarSpatial T).apply_symm_apply]
  rfl

end
section
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem modulus_commute {T S : Operator E} (h : Commute T S) (hstar : Commute (star T) S) :
    Commute (modulus T) S :=
  (hstar.mul_left h).cfcₙ_nnreal NNReal.sqrt

omit [CompleteSpace E] in
 theorem closedRange_invariant {T S : Operator E} (h : Commute T S) :
    ∀ x ∈ closedRange T, S x ∈ closedRange T := by
  have hi : T.toLinearMap.range ∈ Module.End.invtSubmodule S := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨_,⟨x,rfl⟩,rfl⟩
    refine ⟨S x,?_⟩
    exact DFunLike.congr_fun h.eq x
  exact Submodule.topologicalClosure_mem_invtSubmodule hi

 theorem orthogonal_invariant (K : Submodule ℂ E) (S : Operator E)
    (h : ∀ x ∈ K, star S x ∈ K) : ∀ x ∈ Kᗮ, S x ∈ Kᗮ := by
  intro x hx
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro y hy
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hx (star S y) (h y hy)

 theorem starProjection_commute (K : Submodule ℂ E) [K.HasOrthogonalProjection] (S : Operator E)
    (h : ∀ x ∈ K, S x ∈ K) (hstar : ∀ x ∈ K, star S x ∈ K) :
    Commute K.starProjection S := by
  apply ContinuousLinearMap.ext
  intro x
  change K.starProjection (S x) = S (K.starProjection x)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact h _ (K.orthogonalProjectionOnto x).property
  · rw [← map_sub]
    exact orthogonal_invariant K S hstar _ (K.sub_starProjection_mem_orthogonal x)

 theorem partialIsometry_projection (T : Operator E) :
    partialIsometry T * (closedRange (modulus T)).starProjection = partialIsometry T := by
  apply ContinuousLinearMap.ext
  intro x
  change ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto
    ((closedRange (modulus T)).orthogonalProjectionOnto x)) : E) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

 theorem partialIsometry_commute {T S : Operator E}
    (h : Commute T S) (hstar : Commute (star T) S)
    (hs : Commute T (star S)) (hstars : Commute (star T) (star S)) :
    Commute (partialIsometry T) S := by
  have hm := modulus_commute h hstar
  have hms := modulus_commute hs hstars
  have hp := starProjection_commute (closedRange (modulus T)) S
    (closedRange_invariant hm) (closedRange_invariant hms)
  have he : Set.EqOn (partialIsometry T * S) (S * partialIsometry T)
      (closedRange (modulus T) : Set E) := by
    apply Set.EqOn.closure _ (partialIsometry T * S).continuous (S * partialIsometry T).continuous
    rintro _ ⟨x,rfl⟩
    change partialIsometry T (S (modulus T x)) = S (partialIsometry T (modulus T x))
    have hmx : modulus T (S x) = S (modulus T x) := DFunLike.congr_fun hm.eq x
    rw [← hmx]
    change (partialIsometry T * modulus T) (S x) = S ((partialIsometry T * modulus T) x)
    rw [partialIsometry_factorization]
    exact DFunLike.congr_fun h.eq x
  apply ContinuousLinearMap.ext
  intro x
  have hx := he ((closedRange (modulus T)).orthogonalProjectionOnto x).property
  change (partialIsometry T * S) x = (S * partialIsometry T) x
  calc
    _ = (partialIsometry T * (closedRange (modulus T)).starProjection * S) x := by
      rw [partialIsometry_projection]
    _ = (partialIsometry T * S * (closedRange (modulus T)).starProjection) x := by
      rw [mul_assoc,hp.eq,← mul_assoc]
    _ = (S * partialIsometry T * (closedRange (modulus T)).starProjection) x := hx
    _ = _ := by rw [mul_assoc,partialIsometry_projection]

end
section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem partialIsometry_mem_centralizer (s : Set (Operator E)) {T : Operator E}
    (hT : T ∈ StarSubalgebra.centralizer ℂ s) :
    partialIsometry T ∈ StarSubalgebra.centralizer ℂ s := by
  have ht := (StarSubalgebra.mem_centralizer_iff ℂ).mp hT
  have hts := (StarSubalgebra.mem_centralizer_iff ℂ).mp
    (star_mem hT)
  rw [StarSubalgebra.mem_centralizer_iff]
  intro S hS
  have h₁ : Commute T S := (ht S hS).1.symm
  have h₂ : Commute (star T) S := (hts S hS).1.symm
  have h₃ : Commute T (star S) := (ht S hS).2.symm
  have h₄ : Commute (star T) (star S) := (hts S hS).2.symm
  exact ⟨(partialIsometry_commute h₁ h₂ h₃ h₄).eq.symm,
    (partialIsometry_commute h₃ h₄ (by simpa using h₁) (by simpa using h₂)).eq.symm⟩

 theorem closedRange_eq_orthogonal_ker (T : Operator E) :
    closedRange T = (star T).kerᗮ := by
  simpa only [closedRange,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint]
    using (ContinuousLinearMap.orthogonal_ker (star T)).symm

 theorem modulus_ker (T : Operator E) : (modulus T).ker = T.ker := by
  ext x
  change modulus T x = 0 ↔ T x = 0
  calc
    _ ↔ ‖modulus T x‖ = 0 := norm_eq_zero.symm
    _ ↔ ‖T x‖ = 0 := by rw [modulus_norm]
    _ ↔ _ := norm_eq_zero

 theorem modulus_closedRange (T : Operator E) : closedRange (modulus T) = T.kerᗮ := by
  rw [closedRange_eq_orthogonal_ker,modulus_star,modulus_ker]

 theorem closedRange_projection_mem_centralizer (s : Set (Operator E)) {T : Operator E}
    (hT : T ∈ StarSubalgebra.centralizer ℂ s) :
    (closedRange T).starProjection ∈ StarSubalgebra.centralizer ℂ s := by
  rw [← partialIsometry_final]
  have hu := partialIsometry_mem_centralizer s hT
  exact mul_mem hu (star_mem hu)

 theorem partialIsometry_nonzero {T : Operator E} (hT : T ≠ 0) : partialIsometry T ≠ 0 := by
  intro h
  apply hT
  rw [← partialIsometry_factorization T,h,zero_mul]

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem fixed_on_closedRange {q T : Operator E} (h : q*T=T) (x : closedRange T) : q x=x := by
  have he : Set.EqOn q id (Set.range T) := by
    rintro _ ⟨y,rfl⟩
    exact DFunLike.congr_fun h y
  have hc := he.closure q.continuous continuous_id
  apply hc
  have hx := x.property
  change (x : E) ∈ (↑(T.toLinearMap.range.topologicalClosure) : Set E) at hx
  rw [Submodule.topologicalClosure_coe] at hx
  exact hx

 theorem partialIsometry_left_support {q T : Operator E} (h : q*T=T) :
    q*partialIsometry T=partialIsometry T := by
  apply ContinuousLinearMap.ext
  intro x
  exact fixed_on_closedRange h ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x))

 theorem modulus_right_support {p T : Operator E} (h : T*p=T) : modulus T*p=modulus T := by
  apply ContinuousLinearMap.ext
  intro x
  have hz : T (p x-x)=0 := by rw [map_sub]; exact sub_eq_zero.mpr (DFunLike.congr_fun h x)
  have hn : ‖modulus T (p x-x)‖=0 := by rw [modulus_norm,hz,norm_zero]
  change modulus T (p x)=modulus T x
  simpa only [map_sub,sub_eq_zero] using norm_eq_zero.mp hn

 theorem partialIsometry_right_support {p T : Operator E} (hp : IsSelfAdjoint p) (h : T*p=T) :
    partialIsometry T*p=partialIsometry T := by
  have hm := congrArg star (modulus_right_support h)
  simp only [star_mul,hp.star_eq,modulus_star] at hm
  have ha : p*star (partialIsometry T)=star (partialIsometry T) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [mul_apply_eq_comp,partialIsometry_adjoint]
    exact fixed_on_closedRange hm ((polarSpatial T).symm ((closedRange T).orthogonalProjectionOnto x))
  have he := congrArg star ha
  simpa only [star_mul,star_star,hp.star_eq] using he

 theorem partialIsometry_partial (T : Operator E) :
    partialIsometry T*star (partialIsometry T)*partialIsometry T=partialIsometry T := by
  rw [partialIsometry_final]
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.starProjection_eq_self_iff.mpr
  exact ((polarSpatial T) ((closedRange (modulus T)).orthogonalProjectionOnto x)).property

end FreeGroupFactorMain.Amplification.Polar

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
open Amplification.Polar
variable {ι : Type u_6} [DecidableEq ι]

 theorem weighted_creation_norm (i : ι) (r : Bool) (ξ : H ι) :
    ‖creation i r ξ‖=‖ξ‖ := (hilbertEmbedding (prepend i r)).norm_map ξ

 theorem weighted_creation_opNorm_le (i : ι) (r : Bool) : ‖creation i r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  rw [weighted_creation_norm,one_mul]

 theorem P_creation_true (i : ι) : (P : Operator ι)*creation i true=creation i true := by
  apply operator_basis_ext
  rintro ⟨w,e⟩
  simp only [mul_apply_eq_comp,creation_single,P_cons,ite_true]

 def offDiagonal (u v : ℝ) (i : ι) : Operator ι := P*S u v i*(1-P)

 theorem offDiagonal_formula (u v : ℝ) (i : ι) :
    offDiagonal u v i=(u:ℂ) • (creation i true*(1-P)) +
      (v:ℂ) • (P*star (creation i false)) := by
  have ht : star (creation i true)*(1-P : Operator ι)=0 := by
    have hh := congrArg star (P_creation_true i)
    simp only [star_mul,projection_P.isSelfAdjoint.star_eq] at hh
    rw [mul_sub,mul_one,hh,sub_self]
  have hf : star (creation i false)*(1-P : Operator ι)=star (creation i false) := by
    have hh := congrArg star (P_creation_false i)
    simp only [star_mul,projection_P.isSelfAdjoint.star_eq,star_zero (Operator ι)] at hh
    rw [mul_sub,mul_one,hh,sub_zero]
  simp only [offDiagonal,S,mul_add,add_mul,star_add (R := Operator ι),star_smul,Complex.star_def,
    Complex.conj_ofReal,mul_smul_comm,smul_mul_assoc,P_creation_true,P_creation_false,
    mul_assoc,ht,hf,mul_zero,zero_mul,smul_zero,add_zero,zero_add]

 theorem offDiagonal_right (u v : ℝ) (i : ι) :
    offDiagonal u v i*(1-P)=offDiagonal u v i := by
  unfold offDiagonal
  simp only [mul_assoc,projection_P.one_sub.isIdempotentElem.eq]

 theorem offDiagonal_left (u v : ℝ) (i : ι) :
    P*offDiagonal u v i=offDiagonal u v i := by
  rw [offDiagonal,← mul_assoc,← mul_assoc,projection_P.isIdempotentElem.eq]

 theorem offDiagonal_lower_bound (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (i : ι) (ξ : H ι) (hξ : (1-P : Operator ι) ξ=ξ) :
    (u-v)*‖ξ‖ ≤ ‖offDiagonal u v i ξ‖ := by
  have hP : ‖(P : Operator ι)‖ ≤ 1 := CoordinateProjection.norm_proj_le _
  have hc : ‖star (creation i false) ξ‖ ≤ ‖ξ‖ := by
    calc
      _ ≤ ‖star (creation i false)‖*‖ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖ξ‖ := mul_le_mul_of_nonneg_right (by simpa only [ContinuousLinearMap.star_eq_adjoint,LinearIsometryEquiv.norm_map] using weighted_creation_opNorm_le i false) (norm_nonneg _)
      _ = _ := one_mul _
  have hpc : ‖P (star (creation i false) ξ)‖ ≤ ‖ξ‖ := by
    calc
      _ ≤ ‖(P : Operator ι)‖*‖star (creation i false) ξ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1*‖star (creation i false) ξ‖ := mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ ‖ξ‖ := by simpa only [one_mul] using hc
  rw [offDiagonal_formula]
  change (u-v)*‖ξ‖ ≤ ‖(u:ℂ) • creation i true ((1-P : Operator ι) ξ)+
    (v:ℂ) • P (star (creation i false) ξ)‖
  rw [hξ]
  have hb := norm_sub_norm_le ((u:ℂ) • creation i true ξ)
    (-((v:ℂ) • P (star (creation i false) ξ)))
  simp only [norm_neg,sub_neg_eq_add,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hu,abs_of_nonneg hv,weighted_creation_norm] at hb
  have hpv := mul_le_mul_of_nonneg_left hpc hv
  nlinarith

 theorem offDiagonal_ker (u v : ℝ) (hv : 0 ≤ v) (hvu : v<u) (i : ι) :
    (offDiagonal u v i).ker = (1-P : Operator ι).ker := by
  ext ξ
  change offDiagonal u v i ξ=0 ↔ (1-P : Operator ι) ξ=0
  constructor
  · intro hξ
    have hproj : (1-P : Operator ι) ((1-P : Operator ι) ξ)=(1-P : Operator ι) ξ :=
      DFunLike.congr_fun projection_P.one_sub.isIdempotentElem.eq ξ
    have hb := offDiagonal_lower_bound u v (hv.trans hvu.le) hv i ((1-P : Operator ι) ξ) hproj
    have hx : offDiagonal u v i ((1-P : Operator ι) ξ)=0 := by
      have he : offDiagonal u v i ((1-P : Operator ι) ξ)=offDiagonal u v i ξ :=
        DFunLike.congr_fun (offDiagonal_right u v i) ξ
      exact he.trans hξ
    rw [hx,norm_zero] at hb
    have hn : ‖(1-P : Operator ι) ξ‖=0 := by nlinarith [norm_nonneg ((1-P : Operator ι) ξ)]
    exact norm_eq_zero.mp hn
  · intro hξ
    have he := DFunLike.congr_fun (offDiagonal_right u v i) ξ
    simpa only [mul_apply_eq_comp,hξ,map_zero] using he.symm

 theorem offDiagonal_mem_ambient (u v : ℝ) (i : ι) :
    offDiagonal u v i ∈ ambientAlgebra u v :=
  mul_mem (mul_mem (P_mem_ambient u v) (S_mem_ambient u v i))
    (sub_mem (one_mem _) (P_mem_ambient u v))

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_7} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem kernel_orthogonal_projection {q : Operator E} (hq : IsStarProjection q) :
    q.kerᗮ.starProjection=q := by
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · rw [Submodule.mem_orthogonal]
    intro y hy
    have hyq : q y=0 := hy
    rw [← ContinuousLinearMap.adjoint_inner_left]
    change inner ℂ (star q y) x=0
    rw [hq.isSelfAdjoint.star_eq,hyq,inner_zero_left]
  · rw [Submodule.orthogonal_orthogonal]
    change q (x-q x)=0
    rw [map_sub]
    have he : q (q x)=q x := DFunLike.congr_fun hq.isIdempotentElem.eq x
    rw [he,sub_self]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
open Amplification.Polar
variable {ι : Type u_8} [DecidableEq ι]

 def edgePolar (u v : ℝ) (i : ι) : Operator ι := partialIsometry (offDiagonal u v i)

 theorem edgePolar_mem_ambient (u v : ℝ) (i : ι) :
    edgePolar u v i ∈ ambientAlgebra u v :=
  partialIsometry_mem_centralizer _ (offDiagonal_mem_ambient u v i)

 theorem edgePolar_initial (u v : ℝ) (hv : 0 ≤ v) (hvu : v<u) (i : ι) :
    star (edgePolar u v i)*edgePolar u v i=1-P := by
  simp only [edgePolar,partialIsometry_initial,modulus_closedRange,
    offDiagonal_ker u v hv hvu,kernel_orthogonal_projection projection_P.one_sub]

 theorem edgePolar_left (u v : ℝ) (i : ι) : P*edgePolar u v i=edgePolar u v i :=
  partialIsometry_left_support (offDiagonal_left u v i)

 theorem edgePolar_right (u v : ℝ) (i : ι) : edgePolar u v i*(1-P)=edgePolar u v i :=
  partialIsometry_right_support projection_P.one_sub.isSelfAdjoint (offDiagonal_right u v i)

 def edgeRange (u v : ℝ) (i : ι) : Operator ι := edgePolar u v i*star (edgePolar u v i)

 theorem edgeRange_projection (u v : ℝ) (i : ι) : IsStarProjection (edgeRange u v i) := by
  rw [edgeRange,edgePolar,partialIsometry_final]
  exact isStarProjection_starProjection

 theorem edgeRange_mem_ambient (u v : ℝ) (i : ι) : edgeRange u v i ∈ ambientAlgebra u v :=
  mul_mem (edgePolar_mem_ambient u v i) (star_mem (edgePolar_mem_ambient u v i))

 theorem edgeRange_le_P (u v : ℝ) (i : ι) : P*edgeRange u v i=edgeRange u v i := by
  rw [edgeRange,← mul_assoc,edgePolar_left]

 theorem edgePolar_trace (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) :
    vacuumTrace u v (edgeRange u v i)=(v^2:ℝ) := by
  have ht := ambient_trace_mul u v (ne_of_gt (hv.trans hvu)) hv.ne'
    ⟨edgePolar u v i,edgePolar_mem_ambient u v i⟩
    ⟨star (edgePolar u v i),star_mem (edgePolar_mem_ambient u v i)⟩
  change vacuumTrace u v (edgePolar u v i*star (edgePolar u v i))=
    vacuumTrace u v (star (edgePolar u v i)*edgePolar u v i) at ht
  rw [edgePolar_initial u v hv.le hvu] at ht
  rw [edgeRange,ht]
  simp only [vacuumTrace,sub_apply,one_apply_eq_self,
    inner_sub_right]
  change vacuumTrace u v 1-vacuumTrace u v P=(v^2:ℝ)
  rw [vacuumTrace_one,vacuumTrace_P]
  push_cast
  ring

end
open FreeFock
open scoped ENNReal
open Amplification.Polar
variable {ι : Type u_9} [DecidableEq ι]

 theorem annihilation_apply (i : ι) (r : Bool) (ξ : H ι) (w : Path ι) :
    (star (creation i r) ξ) w = ξ ((i,r)::w.1,w.2) := by
  have h := ContinuousLinearMap.adjoint_inner_right (creation i r) (lp.single 2 w 1) ξ
  rw [creation_single,lp.inner_single_left,lp.inner_single_left] at h
  simpa only [ContinuousLinearMap.star_eq_adjoint,RCLike.inner_apply,star_one,map_one,one_mul,mul_one] using h

 theorem creation_apply_prepend (i : ι) (r : Bool) (ξ : H ι) (w : Path ι) :
    (creation i r ξ) ((i,r)::w.1,w.2) = ξ w := by
  have h := ContinuousLinearMap.adjoint_inner_left (creation i r) ξ
    (lp.single 2 ((i,r)::w.1,w.2) 1)
  change inner ℂ (star (creation i r) (lp.single 2 ((i,r)::w.1,w.2) 1)) ξ = _ at h
  rw [annihilation_single_cons,ite_eq_left rfl,lp.inner_single_left,lp.inner_single_left] at h
  simpa only [RCLike.inner_apply,star_one,map_one,one_mul,mul_one] using h.symm

omit [DecidableEq ι] in
 theorem P_apply_prepend_true (i : ι) (ξ : H ι) (w : Path ι) :
    (P ξ) ((i,true)::w.1,w.2) = ξ ((i,true)::w.1,w.2) := by
  simp only [P,CoordinateProjection.proj_apply,Set.indicator_apply,Set.mem_ofPred_eq,start,ite_true]

 def alternatingExtension (i : ι) (w : Path ι) : ℕ → Path ι
  | 0 => w
  | n+1 => ((i,false)::(i,true)::(alternatingExtension i w n).1,(alternatingExtension i w n).2)

omit [DecidableEq ι] in
 theorem alternatingExtension_length (i : ι) (w : Path ι) (n : ℕ) :
    (alternatingExtension i w n).1.length=2*n+w.1.length := by
  induction n with
  | zero => simp [alternatingExtension]
  | succ n ih => simp only [alternatingExtension,List.length_cons,ih]; omega

omit [DecidableEq ι] in
 theorem alternatingExtension_injective (i : ι) (w : Path ι) :
    Function.Injective (alternatingExtension i w) := by
  intro n m h
  have hh := congrArg (fun a : Path ι => a.1.length) h
  simp only [alternatingExtension_length] at hh
  omega

 theorem offDiagonal_balanced_recurrence (u : ℝ) (hu : u≠0) (i : ι)
    (ξ : H ι) (hs : (1-P : Operator ι) ξ=ξ)
    (hx : offDiagonal u u i ξ=0) (w : Path ι) :
    ξ ((i,false)::(i,true)::w.1,w.2) = -ξ w := by
  have he := congrArg (fun η : H ι => η ((i,true)::w.1,w.2)) hx
  rw [offDiagonal_formula] at he
  change (u:ℂ)*(creation i true ((1-P : Operator ι) ξ)) ((i,true)::w.1,w.2) +
    (u:ℂ)*(P (star (creation i false) ξ)) ((i,true)::w.1,w.2)=0 at he
  rw [hs,creation_apply_prepend,P_apply_prepend_true,annihilation_apply,← mul_add] at he
  have he' := (mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr hu)
  linear_combination he'

 theorem offDiagonal_balanced_injective (u : ℝ) (hu : u≠0) (i : ι)
    (ξ : H ι) (hs : (1-P : Operator ι) ξ=ξ)
    (hx : offDiagonal u u i ξ=0) : ξ=0 := by
  ext w
  have he (n : ℕ) : ‖ξ (alternatingExtension i w n)‖=‖ξ w‖ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [alternatingExtension,offDiagonal_balanced_recurrence u hu i ξ hs hx,norm_neg,ih]
  have hsum : Summable (fun w : Path ι => ‖ξ w‖^2) := by
    have hh := (memℓp_gen_iff (by norm_num : 0 < (2:ℝ≥0∞).toReal)).mp (lp.memℓp ξ)
    simpa using hh
  have hj := hsum.comp_injective (alternatingExtension_injective i w)
  have hc : Summable (fun _ : ℕ => ‖ξ w‖^2) := by
    simpa only [Function.comp_def,he] using hj
  have hz : ‖ξ w‖^2=0 := (summable_const_iff _).mp hc
  have hn : ‖ξ w‖=0 := by nlinarith [norm_nonneg (ξ w)]
  have hh : ξ w=0 := norm_eq_zero.mp hn
  exact hh

 theorem offDiagonal_ker_balanced (u : ℝ) (hu : u≠0) (i : ι) :
    (offDiagonal u u i).ker=(1-P : Operator ι).ker := by
  ext ξ
  change offDiagonal u u i ξ=0 ↔ (1-P : Operator ι) ξ=0
  constructor
  · intro hx
    apply offDiagonal_balanced_injective u hu i
    · exact DFunLike.congr_fun projection_P.one_sub.isIdempotentElem.eq ξ
    · have he : offDiagonal u u i ((1-P : Operator ι) ξ)=offDiagonal u u i ξ :=
        DFunLike.congr_fun (offDiagonal_right u u i) ξ
      rw [he,hx]
  · intro hx
    have he : offDiagonal u u i ((1-P : Operator ι) ξ)=offDiagonal u u i ξ :=
      DFunLike.congr_fun (offDiagonal_right u u i) ξ
    rw [← he,hx,map_zero]

 theorem edgePolar_initial_balanced (u : ℝ) (hu : u≠0) (i : ι) :
    star (edgePolar u u i)*edgePolar u u i=1-P := by
  simp only [edgePolar,partialIsometry_initial,modulus_closedRange,
    offDiagonal_ker_balanced u hu i,kernel_orthogonal_projection projection_P.one_sub]

 theorem edgePolar_trace_balanced (u : ℝ) (hu : u≠0) (i : ι) :
    vacuumTrace u u (edgeRange u u i)=(u^2:ℝ) := by
  have ht := ambient_trace_mul u u hu hu
    ⟨edgePolar u u i,edgePolar_mem_ambient u u i⟩
    ⟨star (edgePolar u u i),star_mem (edgePolar_mem_ambient u u i)⟩
  change vacuumTrace u u (edgePolar u u i*star (edgePolar u u i))=
    vacuumTrace u u (star (edgePolar u u i)*edgePolar u u i) at ht
  rw [edgePolar_initial_balanced u hu i] at ht
  rw [edgeRange,ht]
  simp only [vacuumTrace,sub_apply,one_apply_eq_self,inner_sub_right]
  change vacuumTrace u u 1-vacuumTrace u u P=(u^2:ℝ)
  rw [vacuumTrace_one,vacuumTrace_P]
  push_cast
  ring

 theorem edgeRange_balanced (u : ℝ) (hu : u≠0) (i : ι) : edgeRange u u i=P := by
  have hproj := (edgeRange_projection u u i).sub_of_mul_eq_right projection_P (edgeRange_le_P u u i)
  have hm : P-edgeRange u u i ∈ ambientAlgebra u u :=
    sub_mem (P_mem_ambient u u) (edgeRange_mem_ambient u u i)
  have htrace : vacuumTrace u u (star (P-edgeRange u u i)*(P-edgeRange u u i))=0 := by
    rw [hproj.isSelfAdjoint.star_eq,hproj.isIdempotentElem.eq]
    simp only [vacuumTrace,sub_apply,inner_sub_right]
    change vacuumTrace u u P-vacuumTrace u u (edgeRange u u i)=0
    rw [vacuumTrace_P,edgePolar_trace_balanced u hu i,sub_self]
  have hz := ambient_trace_faithful u u hu hu ⟨P-edgeRange u u i,hm⟩ htrace
  have hz' : P-edgeRange u u i=0 := congrArg Subtype.val hz
  exact (sub_eq_zero.mp hz').symm

end FreeGroupFactorMain.WeightedFock

end

end OAI
