import OAI.Combinatorics.Sidorenko.Signs

namespace OAI


section

namespace SidorenkoCounterexample
open Module LinearMap
section Projections
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def FormSelfAdjoint (Q : LinearMap.BilinForm K V) (T : V →ₗ[K] V) : Prop :=
  ∀ x y, Q (T x) y = Q x (T y)

theorem selfAdjoint_projection_ker (Q : LinearMap.BilinForm K V) (hQ : Q.Nondegenerate)
    (T : V →ₗ[K] V) (hT : FormSelfAdjoint Q T) :
    T.ker = Q.orthogonal T.range := by
  ext x
  constructor
  · intro hx y hy
    obtain ⟨z,rfl⟩ := hy
    rw [hT,show T x=0 from hx,map_zero]
  · intro hx
    apply hQ.2
    intro y
    rw [←hT]
    exact hx (T y) ⟨y,rfl⟩

variable [FiniteDimensional K V]
theorem selfAdjoint_projection_nondegenerate (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) (T : V →ₗ[K] V)
    (hT : FormSelfAdjoint Q T) (hi : IsIdempotentElem T) :
    (Q.restrict T.range).Nondegenerate := by
  apply (Q.restrict_nondegenerate_iff_isCompl_orthogonal hs.isRefl).mpr
  rw [←selfAdjoint_projection_ker Q hQ T hT]
  exact hi.isCompl

noncomputable def formProjection (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) : V →ₗ[K] V :=
  U.projection (Q.orthogonal U) (Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU)

theorem formProjection_idempotent (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    IsIdempotentElem (formProjection Q hs U hU) := Submodule.isIdempotentElem_projection _

theorem formProjection_range (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    (formProjection Q hs U hU).range=U := Submodule.range_projection _

theorem formProjection_selfAdjoint (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (U : Submodule K V) (hU : (Q.restrict U).Nondegenerate) :
    FormSelfAdjoint Q (formProjection Q hs U hU) := by
  intro x y
  let h := Q.isCompl_orthogonal_of_restrict_nondegenerate hs.isRefl hU
  let p := U.projection (Q.orthogonal U) h
  have hx : x-p x ∈ Q.orthogonal U := Submodule.sub_projection_mem h x
  have hy : y-p y ∈ Q.orthogonal U := Submodule.sub_projection_mem h y
  have hpx : p x ∈ U := Submodule.projection_apply_mem h x
  have hpy : p y ∈ U := Submodule.projection_apply_mem h y
  have h1 := hy (p x) hpx
  have h2 := hx (p y) hpy
  simp only [map_sub] at h1 h2
  change Q (p x) y=Q x (p y)
  calc
    _ = Q (p x) (p y) := sub_eq_zero.mp h1
    _ = Q (p y) (p x) := hs.eq _ _
    _ = Q (p y) x := (sub_eq_zero.mp h2).symm
    _ = _ := hs.eq _ _

def SelfAdjointIdempotent (Q : LinearMap.BilinForm K V) :=
  {T : V →ₗ[K] V // IsIdempotentElem T ∧ FormSelfAdjoint Q T}

noncomputable def selfAdjointProjectionEquiv (Q : LinearMap.BilinForm K V)
    (hs : Q.IsSymm) (hQ : Q.Nondegenerate) :
    SelfAdjointIdempotent Q ≃ {U : Submodule K V // (Q.restrict U).Nondegenerate} where
  toFun T := ⟨T.val.range,selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1⟩
  invFun U := ⟨formProjection Q hs U.val U.property,formProjection_idempotent Q hs U.val U.property,
    formProjection_selfAdjoint Q hs U.val U.property⟩
  left_inv T := by
    apply Subtype.ext
    let hU := selfAdjoint_projection_nondegenerate Q hs hQ T.val T.property.2 T.property.1
    apply ((formProjection_idempotent Q hs T.val.range hU).ext_iff T.property.1).mpr
    constructor
    · exact formProjection_range Q hs T.val.range hU
    · rw [selfAdjoint_projection_ker Q hQ _ (formProjection_selfAdjoint Q hs T.val.range hU),
        formProjection_range,←selfAdjoint_projection_ker Q hQ T.val T.property.2]
  right_inv U := Subtype.ext (formProjection_range Q hs U.val U.property)
end Projections
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section MatrixProjection
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_formSelfAdjoint_iff (Q : Matrix n n K) (T : (n → K) →ₗ[K] (n → K)) :
    FormSelfAdjoint Q.toBilin' T ↔ T.toMatrix'ᵀ*Q=Q*T.toMatrix' := by
  change (∀ x y, Q.toBilin'.compLeft T x y = Q.toBilin'.compRight T x y) ↔ _
  rw [←LinearMap.BilinForm.ext_iff]
  rw [←LinearMap.BilinForm.toMatrix'.injective.eq_iff]
  simp only [LinearMap.BilinForm.toMatrix'_compLeft,LinearMap.BilinForm.toMatrix'_compRight,
    LinearMap.BilinForm.toMatrix'_toBilin']

theorem matrix_selfAdjoint_of_symmetric (Q A : Matrix n n K) (hQ : Q.IsSymm) (hA : A.IsSymm) :
    FormSelfAdjoint Q.toBilin' (A*Q).toLin' := by
  rw [matrix_formSelfAdjoint_iff,LinearMap.toMatrix'_toLin',Matrix.transpose_mul,hQ,hA,
    Matrix.mul_assoc]

theorem matrix_projection_idempotent (Q A : Matrix n n K) (hA : A*Q*A=A) :
    IsIdempotentElem (A*Q).toLin' := by
  change (A*Q).toLin'.comp (A*Q).toLin' = (A*Q).toLin'
  rw [←Matrix.toLin'_mul]
  congr 1
  rw [←Matrix.mul_assoc,hA]

def CenterProjection (Q : Matrix n n K) :=
  {A : Matrix n n K // A.IsSymm ∧ A*Q*A=A}

noncomputable def centerToProjection (Q : Matrix n n K) (hQ : Q.IsSymm)
    (A : CenterProjection Q) : SelfAdjointIdempotent Q.toBilin' :=
  ⟨(A.val*Q).toLin',matrix_projection_idempotent Q A.val A.property.2,
    matrix_selfAdjoint_of_symmetric Q A.val hQ A.property.1⟩

theorem projection_to_center_symmetric (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹).IsSymm := by
  have h := (matrix_formSelfAdjoint_iff Q T.val).mp T.property.2
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  change (T.val.toMatrix'*Q⁻¹)ᵀ=T.val.toMatrix'*Q⁻¹
  rw [Matrix.transpose_mul,hQ.inv]
  calc
    Q⁻¹*T.val.toMatrix'ᵀ = Q⁻¹*(T.val.toMatrix'ᵀ*Q)*Q⁻¹ := by
      simp only [Matrix.mul_assoc,Matrix.mul_nonsing_inv Q hu,Matrix.mul_one]
    _ = Q⁻¹*(Q*T.val.toMatrix')*Q⁻¹ := by rw [h]
    _ = _ := by rw [←Matrix.mul_assoc Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.one_mul]

theorem projection_to_center_identity (Q : Matrix n n K) (hdet : Q.det≠0)
    (T : SelfAdjointIdempotent Q.toBilin') :
    (T.val.toMatrix'*Q⁻¹)*Q*(T.val.toMatrix'*Q⁻¹)=T.val.toMatrix'*Q⁻¹ := by
  have hi : T.val.toMatrix'*T.val.toMatrix'=T.val.toMatrix' := by
    rw [←LinearMap.toMatrix'_comp]
    exact congrArg LinearMap.toMatrix' T.property.1
  have hu : IsUnit Q.det := isUnit_iff_ne_zero.mpr hdet
  rw [Matrix.mul_assoc _ Q⁻¹ Q,Matrix.nonsing_inv_mul Q hu,Matrix.mul_one,
    ←Matrix.mul_assoc,hi]

noncomputable def centerProjectionEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃ SelfAdjointIdempotent Q.toBilin' where
  toFun := centerToProjection Q hQ
  invFun T := ⟨T.val.toMatrix'*Q⁻¹,projection_to_center_symmetric Q hQ hdet T,
    projection_to_center_identity Q hdet T⟩
  left_inv A := by
    apply Subtype.ext
    change (A.val*Q).toLin'.toMatrix'*Q⁻¹=A.val
    rw [LinearMap.toMatrix'_toLin',Matrix.mul_assoc,Matrix.mul_nonsing_inv Q
      (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one]
  right_inv T := by
    apply Subtype.ext
    change (T.val.toMatrix'*Q⁻¹*Q).toLin'=T.val
    rw [Matrix.mul_assoc,Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hdet),Matrix.mul_one,
      Matrix.toLin'_toMatrix']

noncomputable def centerSubspaceEquiv (Q : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) : CenterProjection Q ≃
      {U : Submodule K (n → K) // (Q.toBilin'.restrict U).Nondegenerate} :=
  (centerProjectionEquiv Q hQ hdet).trans
    (selfAdjointProjectionEquiv Q.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ)
      (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hdet)))
end MatrixProjection
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section Range
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem matrix_toLin_surjective (Q : Matrix n n K) (hQ : Q.det≠0) :
    Function.Surjective Q.toLin' := by
  intro x
  refine ⟨Q⁻¹.toLin' x,?_⟩
  change (Q.toLin'.comp Q⁻¹.toLin') x=x
  rw [←Matrix.toLin'_mul,Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ),Matrix.toLin'_one]
  rfl

theorem matrix_mul_range (A Q : Matrix n n K) (hQ : Q.det≠0) :
    (A*Q).toLin'.range=A.toLin'.range := by
  rw [Matrix.toLin'_mul,LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (matrix_toLin_surjective Q hQ))]

theorem centerSubspaceEquiv_val (Q : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (A : CenterProjection Q) : (centerSubspaceEquiv Q hQ hdet A).val=A.val.toLin'.range :=
  matrix_mul_range A.val Q hdet

theorem center_restriction_nondegenerate (Q A : Matrix n n K) (hQ : Q.IsSymm)
    (hdet : Q.det≠0) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).Nondegenerate := by
  have h := (centerSubspaceEquiv Q hQ hdet ⟨A,hA,hi⟩).property
  rw [centerSubspaceEquiv_val Q hQ hdet ⟨A,hA,hi⟩] at h
  exact h

theorem center_form_pullback (Q A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    (Q.toBilin'.restrict A.toLin'.range).compl₁₂ A.toLin'.rangeRestrict A.toLin'.rangeRestrict =
      A.toBilin' := by
  change Q.toBilin'.comp A.toLin' A.toLin' = _
  rw [Matrix.toBilin'_comp,hA,hi]

theorem center_second_equation (Q R A : Matrix n n K) (hA : A.IsSymm) (hi : A*Q*A=A) :
    A*R*A=A ↔ ((Q-R).toBilin'.restrict A.toLin'.range)=0 := by
  have hp : (Q-R).toBilin'.comp A.toLin' A.toLin' = (A-A*R*A).toBilin' := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,sub_mul,hi]
  constructor
  · intro h
    rw [h,sub_self,map_zero] at hp
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    obtain ⟨x0,hx⟩ := x.property
    obtain ⟨y0,hy⟩ := y.property
    change (Q-R).toBilin' x.val y.val=0
    rw [←hx,←hy]
    exact congrArg (fun B : LinearMap.BilinForm K (n → K) => B x0 y0) hp
  · intro h
    have hz : (Q-R).toBilin'.comp A.toLin' A.toLin'=0 := by
      apply LinearMap.ext
      intro x
      apply LinearMap.ext
      intro y
      exact congrArg (fun B : LinearMap.BilinForm K A.toLin'.range =>
        B (A.toLin'.rangeRestrict x) (A.toLin'.rangeRestrict y)) h
    rw [hz] at hp
    have he := Matrix.toBilin'.injective (hp.symm.trans (map_zero Matrix.toBilin').symm)
    exact (sub_eq_zero.mp he).symm

variable [Fintype K] [DecidableEq K]
theorem center_discriminant (Q A : Matrix n n K) (hQ : Q.IsSymm) (hdet : Q.det≠0)
    (hA : A.IsSymm) (hi : A*Q*A=A) :
    discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) =
      discriminantSign (Q.toBilin'.restrict A.toLin'.range)
        ((Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _) := by
  let f := A.toLin'.rangeRestrict
  let B := Q.toBilin'.restrict A.toLin'.range
  have hs : B.IsSymm := (Matrix.isSymm_toBilin'_iff_isSymm.mpr hQ).restrict _
  have hb : B.Nondegenerate := center_restriction_nondegenerate Q A hQ hdet hA hi
  have h := discriminantSign_pullback B hs hb f A.toLin'.surjective_rangeRestrict
    (Module.finBasis K A.toLin'.range)
  rw [discriminantSign_nondegenerate B hs hb (Module.finBasis K A.toLin'.range)]
  rw [←h]
  congr 1
  exact (center_form_pullback Q A hA hi).symm
end Range
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module LinearMap
open scoped Matrix
section FormSum
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem discriminantSign_complements (Q : LinearMap.BilinForm K V) (hs : Q.IsSymm)
    (hQ : Q.Nondegenerate) (U W : Submodule K V) (hc : IsCompl U W)
    (hU : (Q.restrict U).Nondegenerate) (hW : (Q.restrict W).Nondegenerate)
    (ho : ∀ u : U, ∀ w : W, Q u.val w.val=0) :
    discriminantSign Q hs = discriminantSign (Q.restrict U) (hs.restrict U) *
      discriminantSign (Q.restrict W) (hs.restrict W) := by
  have he := discriminantSign_isometry
    (orthogonalSumForm (Q.restrict U) (Q.restrict W)) Q
    (orthogonalSumForm_isSymm _ _ (hs.restrict U) (hs.restrict W)) hs
    (orthogonalSumForm_nondegenerate _ _ hU hW) hQ (U.prodEquivOfIsCompl W hc)
    (fun x y => by
      simp only [Submodule.coe_prodEquivOfIsCompl',map_add,LinearMap.add_apply,
        orthogonalSumForm_apply,LinearMap.BilinForm.restrict_apply,LinearMap.domRestrict_apply]
      rw [ho x.1 y.2,hs.eq x.2.val y.1.val,ho y.1 x.2]
      ring)
  rw [discriminantSign_orthogonalSum _ _ _ _ hU hW] at he
  exact he.symm
end FormSum
section Complement
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem center_complement_equation (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : (B-A)*B⁻¹*(B-A)=B-A := by
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  rw [sub_mul,Matrix.mul_nonsing_inv B hu,sub_mul,one_mul,mul_sub,hi,
    Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B hu,Matrix.mul_one]
  abel

theorem center_complement_ranges (B A : Matrix n n K) (hB : B.det≠0)
    (hi : A*B⁻¹*A=A) : IsCompl A.toLin'.range (B-A).toLin'.range := by
  let T := (A*B⁻¹).toLin'
  have ht := matrix_projection_idempotent B⁻¹ A hi
  have hiB : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hr := matrix_mul_range A B⁻¹ hiB
  have hc : (B-A).toLin'.range = T.ker := by
    rw [ht.ker_eq_range,←matrix_mul_range (B-A) B⁻¹ hiB]
    congr 1
    change ((B-A)*B⁻¹).toLin' = LinearMap.id-(A*B⁻¹).toLin'
    rw [sub_mul,Matrix.mul_nonsing_inv B (isUnit_iff_ne_zero.mpr hB),map_sub,Matrix.toLin'_one]
  rw [hc]
  simpa only [T,hr] using (matrix_projection_idempotent B⁻¹ A hi).isCompl

theorem center_complement_orthogonal (B A : Matrix n n K) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    ∀ u : A.toLin'.range, ∀ w : (B-A).toLin'.range, B⁻¹.toBilin' u.val w.val=0 := by
  have hp : B⁻¹.toBilin'.comp A.toLin' (B-A).toLin'=0 := by
    rw [Matrix.toBilin'_comp,hA,mul_sub,hi,
      Matrix.mul_assoc A B⁻¹ B,Matrix.nonsing_inv_mul B (isUnit_iff_ne_zero.mpr hB),
      Matrix.mul_one,sub_self,map_zero]
  intro u w
  obtain ⟨x,hx⟩ := u.property
  obtain ⟨y,hy⟩ := w.property
  rw [←hx,←hy]
  exact congrArg (fun Q : LinearMap.BilinForm K (n → K) => Q x y) hp
end Complement
section Signs
variable {K n : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype n] [DecidableEq n]

theorem quadraticChar_inverse {a : K} (ha : a≠0) : quadraticChar K a⁻¹=quadraticChar K a := by
  have hm : quadraticChar K a * quadraticChar K a⁻¹=1 := by
    rw [←map_mul,mul_inv_cancel₀ ha,map_one]
  rcases quadraticChar_dichotomy ha with h | h <;> rw [h] at hm ⊢ <;> linarith

theorem center_complement_sign (B A : Matrix n n K) (hs : B.IsSymm) (hB : B.det≠0)
    (hA : A.IsSymm) (hi : A*B⁻¹*A=A) :
    quadraticChar K B.det =
      discriminantSign A.toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA) *
        discriminantSign (B-A).toBilin' (Matrix.isSymm_toBilin'_iff_isSymm.mpr (hs.sub hA)) := by
  have hsQ : B⁻¹.IsSymm := hs.inv
  have hnQ : B⁻¹.det≠0 := by simpa only [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using inv_ne_zero hB
  have hiC := center_complement_equation B A hB hi
  rw [center_discriminant B⁻¹ A hsQ hnQ hA hi,
    center_discriminant B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC]
  rw [←discriminantSign_complements B⁻¹.toBilin'
    (Matrix.isSymm_toBilin'_iff_isSymm.mpr hsQ)
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    A.toLin'.range (B-A).toLin'.range (center_complement_ranges B A hB hi)
    (center_restriction_nondegenerate B⁻¹ A hsQ hnQ hA hi)
    (center_restriction_nondegenerate B⁻¹ (B-A) hsQ hnQ (hs.sub hA) hiC)
    (center_complement_orthogonal B A hB hA hi)]
  rw [discriminantSign_nondegenerate _ _
    (Matrix.nondegenerate_toBilin'_iff.mpr (Matrix.nondegenerate_iff_det_ne_zero.mpr hnQ))
    (Pi.basisFun K n)]
  change quadraticChar K B.det = quadraticChar K (B⁻¹.toBilin'.toMatrix').det
  rw [LinearMap.BilinForm.toMatrix'_toBilin',Matrix.det_nonsing_inv,Ring.inverse_eq_inv,quadraticChar_inverse hB]
end Signs
end SidorenkoCounterexample

end



section

namespace SidorenkoCounterexample
open Module
open scoped BigOperators
section Split
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
def dualKerEquiv (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) : (φ.ker × K) ≃ₗ[K] V where
  toFun p := p.1.val+p.2 • x
  invFun y := (⟨y-φ y • x, by simp [LinearMap.mem_ker,hx]⟩,φ y)
  left_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_add,map_smul,smul_eq_mul,hx,mul_one,
        show φ p.1.val=0 from p.1.property,zero_add,add_sub_cancel_right]
    · simp [hx]
  right_inv y := by simp
  map_add' p q := by simp only [Prod.fst_add,Prod.snd_add,Submodule.coe_add,add_smul]; abel
  map_smul' a p := by simp only [Prod.smul_fst,Prod.smul_snd,Submodule.coe_smul,
    smul_add,smul_smul,smul_eq_mul,RingHom.id_apply]
@[simp] theorem dualKerEquiv_apply (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (p : φ.ker × K) : dualKerEquiv φ x hx p = p.1.val + p.2 • x := rfl

def rankOneForm (φ : V →ₗ[K] K) : SymForm K V :=
  ⟨(LinearMap.mul K K).compl₁₂ φ φ, by constructor; intro x y; exact mul_comm _ _⟩
@[simp] theorem rankOneForm_apply (φ : V →ₗ[K] K) (x y : V) :
    (rankOneForm φ).val x y = φ x * φ y := rfl

theorem dualKer_finrank [FiniteDimensional K V] (φ : V →ₗ[K] K) (x : V) (hx : φ x=1) :
    finrank K φ.ker+1=finrank K V := by
  have h := (dualKerEquiv φ x hx).finrank_eq
  simpa only [Module.finrank_prod,Module.finrank_self] using h
end Split
section Signs
variable {K V : Type*} [Field K] [Fintype K] [DecidableEq K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

noncomputable def dualKerBasis (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) : Basis (ι ⊕ PUnit.{1}) K V :=
  (b.prod (Basis.singleton PUnit.{1} K)).map (dualKerEquiv φ x hx)
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
@[simp] theorem dualKerBasis_inl (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) (i : ι) : dualKerBasis φ x hx b (.inl i) = (b i).val := by
  simp [dualKerBasis,Basis.prod_apply]
omit [Fintype K] [DecidableEq K] [FiniteDimensional K V] in
@[simp] theorem dualKerBasis_inr (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    {ι : Type*} (b : Basis ι K φ.ker) (i : PUnit.{1}) : dualKerBasis φ x hx b (.inr i) = x := by
  simp [dualKerBasis,Basis.prod_apply]

omit [Fintype K] [DecidableEq K] in
theorem rankOne_shift_matrix (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (a : K) :
    (Q+a • rankOneForm φ).val.toMatrix (dualKerBasis φ x hx (Module.finBasis K φ.ker)) =
      borderRaw ((symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker))
        (fun i => Q.val (Module.finBasis K φ.ker i).val x) (Q.val x x+a) := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,borderRaw,
        Matrix.fromBlocks_apply₁₁]
      change Q.val _ _ + a * (φ (Module.finBasis K φ.ker i).val * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp only [zero_mul,mul_zero,add_zero]; rfl
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₁₂,Matrix.of_apply]
      change Q.val _ x+a*(φ (Module.finBasis K φ.ker i).val * φ x) = _
      rw [show φ (Module.finBasis K φ.ker i).val=0 from (Module.finBasis K φ.ker i).property]
      simp
  | inr i => cases j with
    | inl j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inl,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₁,Matrix.of_apply]
      change Q.val x _+a*(φ x * φ (Module.finBasis K φ.ker j).val) = _
      rw [show φ (Module.finBasis K φ.ker j).val=0 from (Module.finBasis K φ.ker j).property]
      simpa using Q.property.eq x (Module.finBasis K φ.ker j).val
    | inr j =>
      simp only [LinearMap.BilinForm.toMatrix_apply,dualKerBasis_inr,borderRaw,
        Matrix.fromBlocks_apply₂₂,Matrix.of_apply]
      change Q.val x x+a*(φ x * φ x) = Q.val x x+a
      rw [hx,one_mul,mul_one]

theorem rankOne_shift_mean (φ : V →ₗ[K] K) (x : V) (hx : φ x=1)
    (Q : SymForm K V) (hQ : (symFormPull φ.ker.subtype Q).val.Nondegenerate)
    (hK : ringChar K ≠ 2) {ξ : ℤ} (hξ : ξ=1 ∨ ξ = -1) :
    uniformMean (fun a : K => formSignIndicator ξ (Q+a • rankOneForm φ)) =
      (1-1/(Fintype.card K : ℝ))/2 := by
  let b := Module.finBasis K φ.ker
  let M : SymMatrix K (finrank K φ.ker) := ⟨(symFormPull φ.ker.subtype Q).val.toMatrix b,
    ((symFormPull φ.ker.subtype Q).val.isSymm_toMatrix_iff_isSymm b).mpr
      (symFormPull φ.ker.subtype Q).property⟩
  let z : Fin (finrank K φ.ker) → K := fun i => Q.val (b i).val x
  have hM : M.val.det ≠ 0 := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hQ
  have he (a : K) : formSignIndicator ξ (Q+a • rankOneForm φ) =
      characterSignIndicator ξ (M.val.det * (a- (z ⬝ᵥ (M.val⁻¹.mulVec z)-Q.val x x))) := by
    rw [formSignIndicator_matrix (dualKerBasis φ x hx b) hξ,rankOne_shift_matrix]
    have hd : (borderRaw M.val z (Q.val x x+a)).det =
        (symmetricBorder M z (Q.val x x+a)).val.det := by
      symm; exact Matrix.det_submatrix_equiv_self _ _
    rw [show (symFormPull φ.ker.subtype Q).val.toMatrix (Module.finBasis K φ.ker)=M.val from rfl,
      show (fun i => Q.val (Module.finBasis K φ.ker i).val x)=z from rfl,hd,
      symmetricBorder_det M z _ hM]
    congr 2; ring
  rw [uniformMean_congr he,uniformMean_affine _ _ hM,uniformMean_characterSignIndicator hK hξ]
end Signs
end SidorenkoCounterexample

end

end OAI
