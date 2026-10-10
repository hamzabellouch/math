import OAI.Analysis.FreeGroupFactor.Main

namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

@[simp] theorem corner_one_val (p : A) (hp : IsStarProjection p) :
    ((1 : Corner p hp) : A) = p := rfl

@[simp] theorem corner_mul_val (p : A) (hp : IsStarProjection p) (x y : Corner p hp) :
    ((x*y : Corner p hp) : A) = (x : A)*(y : A) := rfl

 theorem map_projection (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    IsStarProjection (Φ p) := hp.map Φ

def cornerCongr (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    Corner p hp ≃⋆ₐ[ℂ] Corner (Φ p) (map_projection Φ p hp) where
  toFun x := ⟨Φ x,by
    constructor
    · rw [← map_mul,x.property.1]
    · rw [← map_mul,x.property.2]⟩
  invFun y := ⟨Φ.symm y,by
    constructor
    · have hy := congrArg Φ.symm y.property.1
      simpa only [map_mul,Φ.symm_apply_apply] using hy
    · have hy := congrArg Φ.symm y.property.2
      simpa only [map_mul,Φ.symm_apply_apply] using hy⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul Φ (x : A) (y : A))
  map_add' x y := Subtype.ext (map_add Φ (x : A) (y : A))
  map_smul' z x := Subtype.ext (map_smul Φ z (x : A))
  map_star' x := Subtype.ext (map_star Φ (x : A))

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

 theorem cornerCongr_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯A 𝒯B Φ) :
    @Continuous _ _ (cornerTopology 𝒯A p hp)
      (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)) (cornerCongr Φ p hp) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

 theorem normalizedCornerTrace_one (τ : A → ℂ) (t : ℝ) (ht : 0 < t)
    (p : A) (hp : IsStarProjection p) (hτ : τ p = (t : ℂ)) :
    normalizedCornerTrace τ t p hp 1 = 1 := by
  change (t : ℂ)⁻¹ * τ p = 1
  rw [hτ,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht.ne')]

 theorem cornerCongr_trace (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (τA : A → ℂ) (τB : B → ℂ) (hτ : ∀ x, τB (Φ x) = τA x) (t : ℝ)
    (x : Corner p hp) :
    normalizedCornerTrace τB t (Φ p) (map_projection Φ p hp) (cornerCongr Φ p hp x) =
      normalizedCornerTrace τA t p hp x := by
  change (t : ℂ)⁻¹ * τB (Φ x) = (t : ℂ)⁻¹ * τA x
  rw [hτ]

end

open scoped ENNReal

def HasAmplificationIso (G : Type u_12) (H : Type u_13) [Group G] [Group H] (t : ℝ)
    (p : stabilization G) (hp : IsStarProjection p) : Prop :=
  ∃ Φ : Corner p hp ≃⋆ₐ[ℂ] groupVonNeumann H,
    (∀ T, canonicalTrace (Φ T) = normalizedCornerTrace stabilizedTrace t p hp T) ∧
    @Continuous _ _ (cornerTopology (stabilizationTopology G) p hp)
      (groupUltraweakTopology H) Φ

end Amplification

namespace FreeFock
open scoped ENNReal

abbrev Hilbert (α : Type u_14) := lp (fun _ : α => ℂ) 2
variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

def subalgebraEquiv (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a, e a∈N ↔ a∈M) : M ≃⋆ₐ[ℂ] N where
  toFun a := ⟨e a,(he a).mpr a.property⟩
  invFun b := ⟨e.symm b,(he _).mp (by rw [StarAlgEquiv.apply_symm_apply];exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (e.map_mul (a:A) (b:A))
  map_add' a b := Subtype.ext (e.map_add (a:A) (b:A))
  map_smul' c a := Subtype.ext (map_smul e c (a:A))
  map_star' a := Subtype.ext (e.map_star' (a:A))

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
local instance instDecidableEqNestedHilbert (α : Type u_20) : DecidableEq α := Classical.decEq α

variable {I : Type u_21} {J : Type u_22}
abbrev NestedHilbert (I : Type u_23) (J : Type u_24) := lp (fun _ : I => GroupHilbert J) 2

def nestedDirac (ij : I × J) : NestedHilbert I J := by
  classical
  exact lp.single 2 ij.1 (lp.single 2 ij.2 1)

theorem nestedDirac_inner (x y : I × J) :
    inner ℂ (nestedDirac x) (nestedDirac y) = if x = y then 1 else 0 := by
  classical
  rcases x with ⟨i,j⟩
  rcases y with ⟨k,l⟩
  by_cases hik : i = k
  · subst k
    simp [nestedDirac,lp.inner_single_left,lp.single_apply,Pi.single_apply,RCLike.inner_apply]
  · simp [nestedDirac,lp.inner_single_left,lp.single_apply,hik]

theorem nestedDirac_inner_apply (ij : I × J) (ξ : NestedHilbert I J) :
    inner ℂ (nestedDirac ij) ξ = ξ ij.1 ij.2 := by
  classical
  simp [nestedDirac,lp.inner_single_left,RCLike.inner_apply]

theorem nestedDirac_orthogonal :
    (Submodule.span ℂ (Set.range (nestedDirac (I := I) (J := J))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro ξ hξ
  apply show ξ = 0 → ξ ∈ (⊥ : Submodule ℂ (NestedHilbert I J)) from fun h => h ▸ Submodule.zero_mem _
  ext i j
  have hh := ((Submodule.mem_orthogonal _ _).mp hξ) (nestedDirac (i,j))
    (Submodule.subset_span (Set.mem_range_self (i,j)))
  simpa only [nestedDirac_inner_apply,lp.coeFn_zero,Pi.zero_apply] using hh

def nestedBasis (I : Type u_25) (J : Type u_26) : HilbertBasis (I × J) ℂ (NestedHilbert I J) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_iff_ite.mpr nestedDirac_inner) nestedDirac_orthogonal

@[simp] theorem nestedBasis_apply (ij : I × J) : nestedBasis I J ij = nestedDirac ij := by
  simp [nestedBasis]

def hilbertFlatten (I : Type u_27) (J : Type u_28) : NestedHilbert I J ≃ₗᵢ[ℂ] GroupHilbert (I × J) :=
  (nestedBasis I J).repr

@[simp] theorem hilbertFlatten_apply (ξ : NestedHilbert I J) (ij : I × J) :
    hilbertFlatten I J ξ ij = ξ ij.1 ij.2 := by
  rw [hilbertFlatten,HilbertBasis.repr_apply_apply,nestedBasis_apply,nestedDirac_inner_apply]

@[simp] theorem hilbertFlatten_symm_apply (ξ : GroupHilbert (I × J)) (i : I) (j : J) :
    (hilbertFlatten I J).symm ξ i j = ξ (i,j) := by
  have hh := congrArg (fun v : GroupHilbert (I × J) => v (i,j))
    ((hilbertFlatten I J).apply_symm_apply ξ)
  simpa only [hilbertFlatten_apply] using hh

def diagonalValue (A : GroupOperator J) (ξ : NestedHilbert I J) : NestedHilbert I J :=
  ⟨fun i => A (ξ i),((lp.memℓp ξ).norm.const_smul ‖A‖).mono (fun i => A.le_opNorm (ξ i))⟩

theorem diagonalValue_norm_le (A : GroupOperator J) (ξ : NestedHilbert I J) :
    ‖diagonalValue A ξ‖ ≤ ‖A‖*‖ξ‖ := by
  have hh := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) (x := diagonalValue A ξ) (y := (‖A‖ : ℝ) • ξ) (fun i => by
    change ‖A (ξ i)‖ ≤ ‖(‖A‖ : ℝ) • ξ i‖
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using A.le_opNorm (ξ i))
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg A)] using hh

theorem diagonalValue_add (operator : GroupOperator J) (left right : NestedHilbert I J) :
    diagonalValue operator (left + right) = diagonalValue operator left + diagonalValue operator right := by
  ext row column
  exact congrArg (fun vector : GroupHilbert J => vector column)
    (map_add operator (left row) (right row))

theorem diagonalValue_smul (operator : GroupOperator J) (scalar : ℂ) (vector : NestedHilbert I J) :
    diagonalValue operator (scalar • vector) = scalar • diagonalValue operator vector := by
  ext row column
  exact congrArg (fun image : GroupHilbert J => image column)
    (map_smul operator scalar (vector row))

theorem continuous_diagonalValue (operator : GroupOperator J) :
    Continuous (diagonalValue (I := I) operator) :=
  (LinearMap.mkContinuous
    { toFun := diagonalValue operator
      map_add' := diagonalValue_add operator
      map_smul' := diagonalValue_smul operator }
    ‖operator‖ (diagonalValue_norm_le operator) :
      NestedHilbert I J →L[ℂ] NestedHilbert I J).continuous

def diagonalOp (I : Type u_29) (A : GroupOperator J) :
    NestedHilbert I J →L[ℂ] NestedHilbert I J where
  toFun := diagonalValue A
  map_add' := diagonalValue_add A
  map_smul' := diagonalValue_smul A
  cont := continuous_diagonalValue A

@[simp] theorem diagonalOp_apply (A : GroupOperator J) (ξ : NestedHilbert I J) (i : I) :
    diagonalOp I A ξ i = A (ξ i) := rfl

theorem diagonalOp_star (A : GroupOperator J) :
    diagonalOp I (star A) = star (diagonalOp I A) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  change inner ℂ (diagonalOp I (star A) ξ) η =
    inner ℂ ((ContinuousLinearMap.adjoint (diagonalOp I A)) ξ) η
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [lp.inner_eq_tsum,diagonalOp_apply]
  apply tsum_congr
  intro i
  simpa only [ContinuousLinearMap.star_eq_adjoint,lp.inner_eq_tsum] using ContinuousLinearMap.adjoint_inner_left A (η i) (ξ i)

def diagonalHom (I : Type u_30) (J : Type u_31) : GroupOperator J →⋆ₐ[ℂ] (NestedHilbert I J →L[ℂ] NestedHilbert I J) where
  toFun := diagonalOp I
  map_one' := by ext ξ i j; rfl
  map_mul' A B := by ext ξ i j; rfl
  map_zero' := by ext ξ i j; rfl
  map_add' A B := by ext ξ i j; rfl
  commutes' z := by ext ξ i j; rfl
  map_star' := diagonalOp_star

def productAmplification (I : Type u_32) (J : Type u_33) : GroupOperator J →⋆ₐ[ℂ] GroupOperator (I × J) :=
  (hilbertFlatten I J).conjStarAlgEquiv.toStarAlgHom.comp (diagonalHom I J)

@[simp] theorem productAmplification_apply (A : GroupOperator J) (ξ : GroupHilbert (I × J))
    (i : I) (j : J) :
    productAmplification I J A ξ (i,j) =
      A ((hilbertFlatten I J).symm ξ i) j := by
  change hilbertFlatten I J (diagonalOp I A ((hilbertFlatten I J).symm ξ)) (i,j) = _
  rw [hilbertFlatten_apply,diagonalOp_apply]

end
section
open scoped ENNReal
local instance (α : Type u_34) : DecidableEq α := Classical.decEq α
variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

theorem stabilizedRightTranslations_eq_range :
    stabilizedRightTranslations G = Set.range (fun g : G => productAmplification ℕ G (rightRegular g)) := by
  ext T
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rw [hg]
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]
  · rintro ⟨g,rfl⟩
    refine ⟨g,?_⟩
    intro ξ x
    rcases x with ⟨i,j⟩
    simp only [productAmplification_apply,rightRegular_apply,hilbertFlatten_symm_apply]

end

section
open scoped ENNReal
variable {G : Type u_38}

def pairedIndex (G : Type u_39) : (ℕ × (ℕ × G)) ≃ (ℕ × G) :=
  (Equiv.prodAssoc ℕ ℕ G).symm.trans (Equiv.prodCongr Nat.pairEquiv (Equiv.refl G))

def stabilizationFlatten (G : Type u_40) : GroupHilbert (ℕ × (ℕ × G)) ≃ₗᵢ[ℂ] GroupHilbert (ℕ × G) :=
  hilbertReindex (pairedIndex G)

@[simp] theorem pairedIndex_symm_apply (k : ℕ) (g : G) : (pairedIndex G).symm (k,g)=((Nat.unpair k).1,(Nat.unpair k).2,g) := rfl

variable [Group G]

def doubleRight (g : G) : GroupOperator (ℕ × (ℕ × G)) :=
  productAmplification ℕ (ℕ × G) (productAmplification ℕ G (rightRegular g))

theorem doubleRight_star (g : G) : star (doubleRight g)=doubleRight g⁻¹ := by
  simp only [doubleRight,←map_star,rightRegular_star]

theorem flatten_doubleRight (g : G) :
    (stabilizationFlatten G).conjStarAlgEquiv (doubleRight g)=productAmplification ℕ G (rightRegular g) := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext x
  rcases x with ⟨k,h⟩
  change hilbertReindex (pairedIndex G)
    (doubleRight g ((hilbertReindex (pairedIndex G)).symm ξ)) (k,h)=_
  simp only [hilbertReindex_apply,pairedIndex_symm_apply,doubleRight,productAmplification_apply,
    hilbertFlatten_symm_apply,rightRegular_apply]
  change ξ (Nat.pair (Nat.unpair k).1 (Nat.unpair k).2,h*g)=ξ (k,h*g)
  rw [Nat.pair_unpair]

def doubleStabilization (G : Type u_41) [Group G] : StarSubalgebra ℂ (GroupOperator (ℕ × (ℕ × G))) :=
  StarSubalgebra.centralizer ℂ (Set.range (doubleRight (G := G)))

theorem mem_stabilization_iff_right (T : GroupOperator (ℕ × G)) :
    T ∈ stabilization G ↔ ∀g : G,productAmplification ℕ G (rightRegular g)*T=T*productAmplification ℕ G (rightRegular g) := by
  rw [stabilization,StarSubalgebra.mem_centralizer_iff,stabilizedRightTranslations_eq_range]
  constructor
  · intro h g
    exact (h _ ⟨g,rfl⟩).1
  · rintro h _ ⟨g,rfl⟩
    refine ⟨h g,?_⟩
    rw [←map_star,rightRegular_star]
    exact h g⁻¹

theorem mem_doubleStabilization_iff_right (T : GroupOperator (ℕ × (ℕ × G))) :
    T ∈ doubleStabilization G ↔ ∀g : G,doubleRight g*T=T*doubleRight g := by
  rw [doubleStabilization,StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h g
    exact (h _ ⟨g,rfl⟩).1
  · rintro h _ ⟨g,rfl⟩
    exact ⟨h g,by rw [doubleRight_star]; exact h g⁻¹⟩

theorem flatten_mem_stabilization (T : GroupOperator (ℕ × (ℕ × G))) :
    T ∈ doubleStabilization G ↔ (stabilizationFlatten G).conjStarAlgEquiv T ∈ stabilization G := by
  rw [mem_doubleStabilization_iff_right,mem_stabilization_iff_right]
  constructor
  · intro h g
    have hh := congrArg (stabilizationFlatten G).conjStarAlgEquiv (h g)
    simpa only [map_mul,flatten_doubleRight] using hh
  · intro h g
    apply (stabilizationFlatten G).conjStarAlgEquiv.injective
    change (stabilizationFlatten G).conjStarAlgEquiv (doubleRight g*T) =
      (stabilizationFlatten G).conjStarAlgEquiv (T*doubleRight g)
    simp only [map_mul,flatten_doubleRight]
    exact h g

def flattenStabilizationIso : doubleStabilization G ≃⋆ₐ[ℂ] stabilization G :=
  subalgebraEquiv (doubleStabilization G) (stabilization G)
    (stabilizationFlatten G).conjStarAlgEquiv (fun T => (flatten_mem_stabilization T).symm)

def doubleDiagonal (T : stabilization G) : doubleStabilization G :=
  ⟨productAmplification ℕ (ℕ × G) T,by
    rw [mem_doubleStabilization_iff_right]
    intro g
    change productAmplification ℕ (ℕ × G) (productAmplification ℕ G (rightRegular g))*productAmplification ℕ (ℕ × G) (T : GroupOperator _)=_
    rw [←map_mul]
    change _=productAmplification ℕ (ℕ × G) (T : GroupOperator _)*productAmplification ℕ (ℕ × G) (productAmplification ℕ G (rightRegular g))
    rw [←map_mul,(mem_stabilization_iff_right _).mp T.property g]⟩

def repeatFlatten (p : stabilization G) : stabilization G := flattenStabilizationIso (doubleDiagonal p)

theorem doubleDiagonal_projection (p : stabilization G) (hp : IsStarProjection p) : IsStarProjection (doubleDiagonal p) := by
  have hh := (hp.map (stabilization G).subtype).map (productAmplification ℕ (ℕ × G))
  constructor
  · exact Subtype.ext hh.isIdempotentElem.eq
  · exact Subtype.ext hh.isSelfAdjoint.star_eq

theorem repeatFlatten_projection (p : stabilization G) (hp : IsStarProjection p) : IsStarProjection (repeatFlatten p) := by
  let equiv : doubleStabilization G ≃⋆ₐ[ℂ] stabilization G := flattenStabilizationIso
  have projection := doubleDiagonal_projection p hp
  constructor
  · exact (equiv.map_mul' _ _).symm.trans (congrArg equiv projection.isIdempotentElem.eq)
  · exact (equiv.map_star' _).symm.trans (congrArg equiv projection.isSelfAdjoint.star_eq)

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

abbrev CornerStabilization (p : stabilization G) (hp : IsStarProjection p) :=
  Corner (repeatFlatten p) (repeatFlatten_projection p hp)

@[instance_reducible] def cornerStabilizationTopology (p : stabilization G) (hp : IsStarProjection p) :
    TopologicalSpace (CornerStabilization p hp) :=
  cornerTopology (stabilizationTopology G) (repeatFlatten p) (repeatFlatten_projection p hp)

def cornerStabilizationProjectionTrace (a : ℝ) (p : stabilization G) (hp : IsStarProjection p)
    (q : CornerStabilization p hp) : ℝ≥0∞ :=
  (ENNReal.ofReal a)⁻¹ * stabilizedProjectionTrace q.val

def cornerStabilizationTrace (a : ℝ) (p : stabilization G) (hp : IsStarProjection p)
    (x : CornerStabilization p hp) : ℂ := (a:ℂ)⁻¹ * stabilizedTrace x.val

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

def Model.Valid : Model → Prop
  | .integer n => 2≤n
  | .continuous r => 1<r
  | .infinity => True

def Model.Stabilization : Model → Type
  | .integer n => stabilization (FreeGroupRank n)
  | .continuous r => CornerStabilization (selectedProjection (interpolationScale r)).val
      (selectedProjection (interpolationScale r)).property
  | .infinity => stabilization (FreeGroup ℕ)

instance modelStabilizationCStarAlgebra (m : Model) : CStarAlgebra m.Stabilization := by
  cases m <;> dsimp only [Model.Stabilization] <;> infer_instance

@[instance_reducible] def Model.stabilizationTopology : (m : Model) → TopologicalSpace m.Stabilization
  | .integer n => Amplification.stabilizationTopology (FreeGroupRank n)
  | .continuous r => cornerStabilizationTopology (selectedProjection (interpolationScale r)).val
      (selectedProjection (interpolationScale r)).property
  | .infinity => Amplification.stabilizationTopology (FreeGroup ℕ)

def Model.projectionTrace : (m : Model) → m.Stabilization → ℝ≥0∞
  | .integer _ => stabilizedProjectionTrace
  | .continuous r => cornerStabilizationProjectionTrace (interpolationScale r)
      (selectedProjection (interpolationScale r)).val (selectedProjection (interpolationScale r)).property
  | .infinity => stabilizedProjectionTrace

def Model.stabilizationTrace : (m : Model) → m.Stabilization → ℂ
  | .integer _ => stabilizedTrace
  | .continuous r => cornerStabilizationTrace (interpolationScale r)
      (selectedProjection (interpolationScale r)).val (selectedProjection (interpolationScale r)).property
  | .infinity => stabilizedTrace

abbrev Model.Iso (m n : Model) := NormalTracialEquiv m.trace n.trace m.topology n.topology

abbrev Model.AmplificationIso (m : Model) (t : ℝ) (p : m.Stabilization) (hp : IsStarProjection p) :=
  NormalTracialEquiv (normalizedCornerTrace m.stabilizationTrace t p hp) m.trace
    (cornerTopology m.stabilizationTopology p hp) m.topology

def Model.fundamentalGroup (m : Model) : Set ℝ :=
  {t | 0<t ∧ ∃ (p : m.Stabilization) (hp : IsStarProjection p),
    m.projectionTrace p=ENNReal.ofReal t ∧ Nonempty (m.AmplificationIso t p hp)}

abbrev interpolatedStabilization (r : ℝ≥0∞) := (parameterModel r).Stabilization
abbrev interpolatedProjectionTrace (r : ℝ≥0∞) := (parameterModel r).projectionTrace
abbrev interpolatedStabilizationTrace (r : ℝ≥0∞) := (parameterModel r).stabilizationTrace
abbrev interpolatedStabilizationTopology (r : ℝ≥0∞) := (parameterModel r).stabilizationTopology
abbrev fundamentalGroup (r : ℝ≥0∞) := (parameterModel r).fundamentalGroup

noncomputable def standardCornerScale (n : ℕ) (r : ℝ) : ℝ := Real.sqrt (((n:ℝ)-1)/(r-1))
end Interpolation

end FreeGroupFactorMain

end

end OAI
