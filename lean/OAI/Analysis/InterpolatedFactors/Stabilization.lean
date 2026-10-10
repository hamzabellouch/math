import OAI.Analysis.InterpolatedFactors.Subalgebras

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31

namespace FreeGroupFactorMain
namespace InfiniteICC

 theorem reduced_append_fresh {α : Type u_1} {L : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (a : α) (b : Bool) (ha : ∀ x ∈ L, x.1 ≠ a) : FreeGroup.IsReduced (L++[(a,b)]) := by
  induction L with
  | nil => exact FreeGroup.IsReduced.singleton
  | cons x L ih =>
    cases L with
    | nil =>
      rw [List.cons_append,List.nil_append,FreeGroup.isReduced_cons_cons]
      exact ⟨fun he => (ha x (by simp) he).elim,FreeGroup.IsReduced.singleton⟩
    | cons y L =>
      rw [FreeGroup.isReduced_cons_cons] at hL
      simp only [List.cons_append]
      rw [FreeGroup.isReduced_cons_cons]
      exact ⟨hL.1,ih hL.2 (fun z hz => ha z (List.mem_cons_of_mem _ hz))⟩

 theorem reduced_conjugate_fresh {α : Type u_2} {L : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (hne : L ≠ []) (a : α) (ha : ∀ x ∈ L, x.1 ≠ a) :
    FreeGroup.IsReduced ((a,true)::(L++[(a,false)])) := by
  cases L with
  | nil => exact (hne rfl).elim
  | cons x L =>
    rw [List.cons_append,FreeGroup.isReduced_cons_cons]
    refine ⟨fun he => (ha x (by simp) he.symm).elim,?_⟩
    exact reduced_append_fresh hL a false ha

 theorem conjugate_word (g : FreeGroup ℕ) (hg : g ≠ 1) (a : ℕ)
    (ha : ∀ x ∈ g.toWord, x.1 ≠ a) :
    (FreeGroup.of a*g*(FreeGroup.of a)⁻¹).toWord=
      (a,true)::(g.toWord++[(a,false)]) := by
  have he : FreeGroup.of a*g*(FreeGroup.of a)⁻¹ =
      FreeGroup.mk ((a,true)::(g.toWord++[(a,false)])) := by
    rw [← List.singleton_append,← List.append_assoc,← FreeGroup.mul_mk,← FreeGroup.mul_mk,
      FreeGroup.mk_toWord]
    rfl
  rw [he,FreeGroup.toWord_mk]
  exact (reduced_conjugate_fresh FreeGroup.isReduced_toWord (FreeGroup.toWord_eq_nil_iff.not.mpr hg) a ha).reduce_eq

 theorem infinite_conjugates (g : FreeGroup ℕ) (hg : g ≠ 1) :
    ∃ c : ℕ → FreeGroup ℕ, Function.Injective c ∧ ∀ n, ∃ a, c n=a*g*a⁻¹ := by
  classical
  let S : Finset ℕ := (g.toWord.map Prod.fst).toFinset
  let M := S.sup id
  let a (n : ℕ) := M+1+n
  have hfresh (n : ℕ) (x) (hx : x ∈ g.toWord) : x.1 ≠ a n := by
    have hm : x.1 ≤ M := Finset.le_sup (f := id) (by simpa only [S,List.mem_toFinset,List.mem_map] using ⟨x,hx,rfl⟩)
    dsimp [a]
    omega
  refine ⟨fun n => FreeGroup.of (a n)*g*(FreeGroup.of (a n))⁻¹,?_,fun n => ⟨FreeGroup.of (a n),rfl⟩⟩
  intro m n h
  have hw := congrArg FreeGroup.toWord h
  rw [conjugate_word g hg (a m) (hfresh m),conjugate_word g hg (a n) (hfresh n)] at hw
  have he : a m=a n := congrArg Prod.fst (List.cons.inj hw).1
  dsimp [a] at he
  omega

end InfiniteICC

 theorem central_coefficient_conjugate {G : Type u_3} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G, Commute T S) (a g : G) :
    ((T : GroupOperator G) deltaOne) (a*g*a⁻¹)=((T : GroupOperator G) deltaOne) g := by
  have he : (T : GroupOperator G)*leftRegular a=leftRegular a*(T : GroupOperator G) :=
    congrArg (fun A : groupVonNeumann G => (A : GroupOperator G)) (hT (groupUnitary a)).eq
  have hd : leftRegular a deltaOne=lp.single 2 a 1 := by
    ext x
    simp [leftRegular_apply,deltaOne,lp.single_apply,Pi.single_apply,inv_mul_eq_one,eq_comm]
  have hx := congrArg (fun A : GroupOperator G => A deltaOne (a*g)) he
  simp only [mul_apply_eq_comp,hd,leftRegular_apply,inv_mul_cancel_left] at hx
  rw [groupVN_matrix] at hx
  exact hx

 theorem group_center_scalar_of_infinite_conjugates {G : Type u_4} [Group G]
    (hICC : ∀ g : G, g ≠ 1 → ∃ c : ℕ → G, Function.Injective c ∧ ∀ n, ∃ a, c n=a*g*a⁻¹)
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G, Commute T S) :
    T=canonicalTrace T • (1 : groupVonNeumann G) := by
  classical
  have hz (g : G) (hg : g ≠ 1) : ((T : GroupOperator G) deltaOne) g=0 := by
    obtain ⟨c,hc,hconj⟩ := hICC g hg
    have hs : Summable (fun x : G => ‖((T : GroupOperator G) deltaOne) x‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.memℓp ((T : GroupOperator G) deltaOne)).summable (by norm_num)
    have hcst : Summable (fun _ : ℕ => ‖((T : GroupOperator G) deltaOne) g‖^2) := by
      have hh := hs.comp_injective hc
      change Summable (fun n : ℕ => ‖((T : GroupOperator G) deltaOne) (c n)‖^2) at hh
      have he : (fun n : ℕ => ‖((T : GroupOperator G) deltaOne) (c n)‖^2) =
          (fun _ : ℕ => ‖((T : GroupOperator G) deltaOne) g‖^2) := by
        funext n
        obtain ⟨a,ha⟩ := hconj n
        rw [ha,central_coefficient_conjugate T hT]
      rwa [he] at hh
    have hh := (summable_const_iff _).mp hcst
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (((T : GroupOperator G) deltaOne) g)])
  apply sub_eq_zero.mp
  apply groupVN_separating
  rw [← deltaOne_eq]
  ext g
  change ((T : GroupOperator G) deltaOne) g-canonicalTrace T*deltaOne g=(0 : ℂ)
  by_cases hg : g=1
  · subst g
    simp only [deltaOne,lp.single_apply,Pi.single_eq_same,mul_one,canonicalTrace]
    exact sub_self _
  · rw [hz g hg]
    simp [deltaOne,lp.single_apply,hg]

 theorem infinite_free_group_center_scalar (T : groupVonNeumann (FreeGroup ℕ))
    (hT : ∀ S : groupVonNeumann (FreeGroup ℕ), Commute T S) :
    T=canonicalTrace T • (1 : groupVonNeumann (FreeGroup ℕ)) :=
  group_center_scalar_of_infinite_conjugates InfiniteICC.infinite_conjugates T hT

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_9} [CStarAlgebra A]

def equivalentCorner (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : A) (hu : star u*u=p) (hu' : u*star u=q) : Corner p hp ≃⋆ₐ[ℂ] Corner q hq where
  toFun x := ⟨u*(x : A)*star u,by
    constructor
    · rw [← hu']
      calc
        (u*star u)*(u*(x : A)*star u) = u*((star u*u)*(x : A))*star u := by noncomm_ring
        _ = u*(x : A)*star u := by rw [hu,x.property.1]
    · rw [← hu']
      calc
        (u*(x : A)*star u)*(u*star u) = u*((x : A)*(star u*u))*star u := by noncomm_ring
        _ = u*(x : A)*star u := by rw [hu,x.property.2]⟩
  invFun y := ⟨star u*(y : A)*u,by
    constructor
    · rw [← hu]
      calc
        (star u*u)*(star u*(y : A)*u) = star u*((u*star u)*(y : A))*u := by noncomm_ring
        _ = star u*(y : A)*u := by rw [hu',y.property.1]
    · rw [← hu]
      calc
        (star u*(y : A)*u)*(star u*u) = star u*((y : A)*(u*star u))*u := by noncomm_ring
        _ = star u*(y : A)*u := by rw [hu',y.property.2]⟩
  left_inv x := by
    apply Subtype.ext
    change star u*(u*(x : A)*star u)*u = (x : A)
    rw [← mul_assoc,← mul_assoc,hu,x.property.1,mul_assoc,hu,x.property.2]
  right_inv y := by
    apply Subtype.ext
    change u*(star u*(y : A)*u)*star u = (y : A)
    rw [← mul_assoc,← mul_assoc,hu',y.property.1,mul_assoc,hu',y.property.2]
  map_mul' x y := by
    apply Subtype.ext
    change u*((x : A)*(y : A))*star u = (u*(x : A)*star u)*(u*(y : A)*star u)
    simp only [mul_assoc]
    rw [← mul_assoc (star u),hu,← mul_assoc p,y.property.1]
  map_add' x y := by
    apply Subtype.ext
    change u*((x : A)+(y : A))*star u = _
    simp only [mul_add,add_mul]
    rfl
  map_smul' z x := by
    apply Subtype.ext
    change u*(z • (x : A))*star u = _
    simp only [mul_smul_comm,smul_mul_assoc]
    rfl
  map_star' x := by
    apply Subtype.ext
    change u*star (x : A)*star u = star (u*(x : A)*star u)
    simp only [star_mul,star_star,mul_assoc]

 theorem equivalentCorner_trace (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : A) (hu : star u*u=p) (hu' : u*star u=q)
    (τ : A → ℂ) (hτ : ∀ x y, τ (x*y)=τ (y*x)) (t : ℝ) (x : Corner p hp) :
    normalizedCornerTrace τ t q hq (equivalentCorner p q hp hq u hu hu' x) =
      normalizedCornerTrace τ t p hp x := by
  change (t : ℂ)⁻¹ * τ (u*(x : A)*star u) = (t : ℂ)⁻¹ * τ (x : A)
  rw [hτ,← mul_assoc,hu,x.property.1]

 theorem equivalentCorner_normal (p q : A) (hp : IsStarProjection p) (hq : IsStarProjection q)
    (u : A) (hu : star u*u=p) (hu' : u*star u=q)
    (𝒯 : TopologicalSpace A)
    (hmul : @Continuous _ _ 𝒯 𝒯 (fun x : A => u*x*star u)) :
    @Continuous _ _ (cornerTopology 𝒯 p hp) (cornerTopology 𝒯 q hq)
      (equivalentCorner p q hp hq u hu hu') := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
  exact (hmul.comp continuous_subtype_val).subtype_mk _

end
section
open scoped ENNReal ComplexConjugate
local instance (α : Type u_10) : DecidableEq α := Classical.decEq α

variable {I : Type u_11} {J : Type u_12}
end
section
open scoped ENNReal

local instance (α : Type u_13) : DecidableEq α := Classical.decEq α
variable {I : Type u_14} {J : Type u_15}

def contractionFamilyValue (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (ξ : NestedHilbert I J) : NestedHilbert I J :=
  ⟨fun i => A i (ξ i),(lp.memℓp ξ).norm.mono (fun i =>
    ((A i).le_opNorm (ξ i)).trans (by simpa using mul_le_mul_of_nonneg_right (hA i) (norm_nonneg (ξ i))))⟩

theorem contractionFamilyValue_norm_le (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (ξ : NestedHilbert I J) : ‖contractionFamilyValue A hA ξ‖ ≤ ‖ξ‖ := by
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  exact ((A i).le_opNorm (ξ i)).trans (by simpa using mul_le_mul_of_nonneg_right (hA i) (norm_nonneg (ξ i)))

def contractionFamily (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1) :
    NestedHilbert I J →L[ℂ] NestedHilbert I J :=
  LinearMap.mkContinuous
    { toFun := contractionFamilyValue A hA
      map_add' := fun ξ η => by ext i j; exact congrArg (fun v : GroupHilbert J => v j) (map_add (A i) (ξ i) (η i))
      map_smul' := fun z ξ => by ext i j; exact congrArg (fun v : GroupHilbert J => v j) (map_smul (A i) z (ξ i)) }
    1 (fun ξ => by simpa using contractionFamilyValue_norm_le A hA ξ)

@[simp] theorem contractionFamily_apply (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (ξ : NestedHilbert I J) (i : I) : contractionFamily A hA ξ i = A i (ξ i) := rfl

theorem contractionFamily_star (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1) :
    contractionFamily (fun i => star (A i)) (by intro i; exact (norm_star (A i)).le.trans (hA i)) =
      star (contractionFamily A hA) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_right ℂ
  intro η
  change inner ℂ (contractionFamily (fun i => star (A i)) _ ξ) η =
    inner ℂ ((ContinuousLinearMap.adjoint (contractionFamily A hA)) ξ) η
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp only [lp.inner_eq_tsum,contractionFamily_apply]
  apply tsum_congr
  intro i
  simpa only [ContinuousLinearMap.star_eq_adjoint,lp.inner_eq_tsum] using
    ContinuousLinearMap.adjoint_inner_left (A i) (η i) (ξ i)

theorem contractionFamily_projection (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hp : ∀ i, IsStarProjection (A i)) : IsStarProjection (contractionFamily A hA) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro ξ
    ext i j
    change (A i) (A i (ξ i)) j = A i (ξ i) j
    exact congrArg (fun B : GroupOperator J => B (ξ i) j) (hp i).isIdempotentElem.eq
  · change star (contractionFamily A hA) = contractionFamily A hA
    rw [← contractionFamily_star]
    congr 1
    funext i
    exact (hp i).isSelfAdjoint.star_eq

def productFamily (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1) : GroupOperator (I × J) :=
  (hilbertFlatten I J).conjStarAlgEquiv (contractionFamily A hA)

@[simp] theorem productFamily_apply (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (ξ : GroupHilbert (I × J)) (i : I) (j : J) :
    productFamily A hA ξ (i,j) = A i ((hilbertFlatten I J).symm ξ i) j := by
  change hilbertFlatten I J (contractionFamily A hA ((hilbertFlatten I J).symm ξ)) (i,j) = _
  rw [hilbertFlatten_apply,contractionFamily_apply]

theorem productFamily_projection (A : I → GroupOperator J) (hA : ∀ i, ‖A i‖ ≤ 1)
    (hp : ∀ i, IsStarProjection (A i)) : IsStarProjection (productFamily A hA) :=
  (contractionFamily_projection A hA hp).map (hilbertFlatten I J).conjStarAlgEquiv

variable {G : Type u_16} [Group G]

theorem productFamily_mem_stabilization (A : ℕ → groupVonNeumann G)
    (hA : ∀ i, ‖(A i : GroupOperator G)‖ ≤ 1) :
    productFamily (fun i => (A i : GroupOperator G)) hA ∈ stabilization G := by
  rw [stabilization,StarSubalgebra.mem_centralizer_iff,stabilizedRightTranslations_eq_range]
  intro S hS
  obtain ⟨g,rfl⟩ := hS
  have hc (g : G) : productAmplification ℕ G (rightRegular g) *
      productFamily (fun i => (A i : GroupOperator G)) hA =
      productFamily (fun i => (A i : GroupOperator G)) hA *
        productAmplification ℕ G (rightRegular g) := by
    apply ContinuousLinearMap.ext
    intro ξ
    ext x
    rcases x with ⟨i,j⟩
    simp only [mul_apply_eq_comp,productAmplification_apply,productFamily_apply,
      rightRegular_apply,hilbertFlatten_symm_apply]
    have he : (hilbertFlatten ℕ G).symm (productAmplification ℕ G (rightRegular g) ξ) i =
        rightRegular g ((hilbertFlatten ℕ G).symm ξ i) := by
      ext k
      simp only [productAmplification_apply,hilbertFlatten_symm_apply,rightRegular_apply]
    rw [he]
    simpa only [mul_apply_eq_comp,rightRegular_apply] using congrArg
      (fun B : GroupOperator G => B ((hilbertFlatten ℕ G).symm ξ i) j)
      (groupVN_commute_right (A i) g)
  constructor
  · exact hc g
  · rw [← map_star,rightRegular_star]
    exact hc g⁻¹

end
section
open scoped ENNReal
variable {I : Type u_17} {J : Type u_18}

def productSingle (I : Type u_19) (J : Type u_20) (j : I) : GroupHilbert J →L[ℂ] GroupHilbert (I × J) := by
  classical
  exact (hilbertFlatten I J).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (lp.singleContinuousLinearMap ℂ (fun _ : I => GroupHilbert J) 2 j)

@[simp] theorem productSingle_apply [DecidableEq I] (j i : I) (ξ : GroupHilbert J) (k : J) :
    productSingle I J j ξ (i,k) = if i = j then ξ k else 0 := by
  classical
  by_cases hi : i = j <;> simp [productSingle,hilbertFlatten_apply,lp.single_apply,hi]

def matrixEntry (T : GroupOperator (I × J)) (i j : I) : GroupOperator J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    ((hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (T.comp (productSingle I J j)))

@[simp] theorem matrixEntry_apply (T : GroupOperator (I × J)) (i j : I)
    (ξ : GroupHilbert J) (k : J) :
    matrixEntry T i j ξ k = T (productSingle I J j ξ) (i,k) := by
  exact hilbertFlatten_symm_apply _ _ _

theorem productSingle_single [DecidableEq I] [DecidableEq J] [DecidableEq (I × J)]
    (j : I) (g : J) : productSingle I J j (lp.single 2 g 1) = lp.single 2 (j,g) 1 := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  simp only [productSingle_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq]
  split_ifs <;> simp_all

theorem matrixEntry_ext (T U : GroupOperator (I × J))
    (h : ∀ i j, matrixEntry T i j = matrixEntry U i j) : T = U := by
  classical
  apply operator_matrix_ext
  intro x
  rcases x with ⟨j,g⟩
  rw [← productSingle_single]
  ext y
  rcases y with ⟨i,k⟩
  simpa only [matrixEntry_apply] using congrArg (fun A : GroupOperator J => A (lp.single 2 g 1) k) (h i j)

theorem productAmplification_productSingle (S : GroupOperator J) (j : I) (ξ : GroupHilbert J) :
    productAmplification I J S (productSingle I J j ξ) = productSingle I J j (S ξ) := by
  classical
  ext x
  rcases x with ⟨i,k⟩
  rw [productAmplification_apply,productSingle_apply]
  have he : (hilbertFlatten I J).symm (productSingle I J j ξ) i = if i=j then ξ else 0 := by
    ext l
    simp only [hilbertFlatten_symm_apply,productSingle_apply]
    split_ifs <;> rfl
  rw [he]
  split_ifs <;> simp

theorem matrixEntry_diagonal_mul (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (productAmplification I J S * T) i j = S * matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_apply]
  rfl

theorem matrixEntry_mul_diagonal (S : GroupOperator J) (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (T * productAmplification I J S) i j = matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext k
  simp only [matrixEntry_apply,mul_apply_eq_comp,productAmplification_productSingle]

variable {G : Type u_21} [Group G]

theorem mem_stabilization_iff_matrix (T : GroupOperator (ℕ × G)) :
    T ∈ stabilization G ↔ ∀ i j, matrixEntry T i j ∈ groupVonNeumann G := by
  rw [stabilization,StarSubalgebra.mem_centralizer_iff,stabilizedRightTranslations_eq_range]
  constructor
  · intro h i j
    rw [mem_groupVN_iff_commute_right]
    intro g
    have hh := (h _ ⟨g,rfl⟩).1
    have he := congrArg (fun A => matrixEntry A i j) hh
    simpa only [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal] using he
  · intro h S hS
    obtain ⟨g,rfl⟩ := hS
    have hc (g : G) : productAmplification ℕ G (rightRegular g) * T =
        T * productAmplification ℕ G (rightRegular g) := by
      apply matrixEntry_ext
      intro i j
      rw [matrixEntry_diagonal_mul,matrixEntry_mul_diagonal]
      exact (mem_groupVN_iff_commute_right _).mp (h i j) g
    exact ⟨hc g,by rw [← map_star,rightRegular_star]; exact hc g⁻¹⟩

end
section
variable {I : Type u_22} {J : Type u_23}

 def productCoordinate (I : Type u_24) (J : Type u_25) (i : I) : GroupHilbert (I × J) →L[ℂ] GroupHilbert J :=
  (lp.evalCLM ℂ (fun _ : I => GroupHilbert J) 2 i).comp
    (hilbertFlatten I J).symm.toContinuousLinearEquiv.toContinuousLinearMap

 theorem productCoordinate_apply (i : I) (ξ : GroupHilbert (I × J)) (j : J) :
    productCoordinate I J i ξ j=ξ (i,j) := hilbertFlatten_symm_apply _ _ _

 def matrixUnit (I : Type u_26) (J : Type u_27) (i j : I) : GroupOperator (I × J) :=
  (productSingle I J i).comp (productCoordinate I J j)

 theorem matrixUnit_apply [DecidableEq I] (i j k : I) (ξ : GroupHilbert (I × J)) (g : J) :
    matrixUnit I J i j ξ (k,g)=if k=i then ξ (j,g) else 0 := by
  simp only [matrixUnit,ContinuousLinearMap.comp_apply,productSingle_apply,productCoordinate_apply]

 theorem matrixUnit_productSingle [DecidableEq I] (i j l : I) (ξ : GroupHilbert J) :
    matrixUnit I J i j (productSingle I J l ξ)=if j=l then productSingle I J i ξ else 0 := by
  by_cases h : j=l
  · subst l
    rw [ite_eq_left rfl]
    ext x
    rcases x with ⟨k,g⟩
    simp only [matrixUnit_apply,productSingle_apply,ite_true]
  · rw [ite_eq_right h]
    ext x
    rcases x with ⟨k,g⟩
    simp only [matrixUnit_apply,productSingle_apply,ite_eq_right h,ite_self,lp.coeFn_zero,Pi.zero_apply]

 theorem matrixEntry_matrixUnit_mul [DecidableEq I] (i j k l : I) (T : GroupOperator (I × J)) :
    matrixEntry (matrixUnit I J i j*T) k l=if k=i then matrixEntry T j l else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,mul_apply_eq_comp,matrixUnit_apply]
  split_ifs <;> simp only [matrixEntry_apply,zero_apply,lp.coeFn_zero,Pi.zero_apply]

 theorem matrixEntry_mul_matrixUnit [DecidableEq I] (i j k l : I) (T : GroupOperator (I × J)) :
    matrixEntry (T*matrixUnit I J i j) k l=if j=l then matrixEntry T k i else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,mul_apply_eq_comp,matrixUnit_productSingle]
  split_ifs <;> simp

 theorem matrixEntry_matrixUnit [DecidableEq I] (i j k l : I) :
    matrixEntry (matrixUnit I J i j) k l=if k=i ∧ j=l then 1 else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  simp only [matrixEntry_apply,matrixUnit_apply,productSingle_apply]
  split_ifs <;> simp_all

 theorem matrixEntry_productAmplification [DecidableEq I] (S : GroupOperator J) (i j : I) :
    matrixEntry (productAmplification I J S) i j=if i=j then S else 0 := by
  apply ContinuousLinearMap.ext
  intro ξ
  ext g
  rw [matrixEntry_apply,productAmplification_productSingle,productSingle_apply]
  split_ifs <;> rfl

 variable {G : Type u_28} [Group G]

 theorem matrixUnit_mem_stabilization (i j : ℕ) : matrixUnit ℕ G i j ∈ stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_matrixUnit]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

 theorem diagonal_mem_stabilization (S : groupVonNeumann G) :
    productAmplification ℕ G (S : GroupOperator G) ∈ stabilization G := by
  rw [mem_stabilization_iff_matrix]
  intro k l
  rw [matrixEntry_productAmplification]
  split_ifs
  · exact S.property
  · exact zero_mem _

 theorem stabilization_center_diagonal (T : stabilization G)
    (hc : ∀ S : stabilization G, Commute T S) :
    (T : GroupOperator (ℕ × G))=productAmplification ℕ G (matrixEntry (T : GroupOperator (ℕ × G)) 0 0) := by
  have hm (i j : ℕ) : (T : GroupOperator (ℕ × G))*matrixUnit ℕ G i j=
      matrixUnit ℕ G i j*(T : GroupOperator (ℕ × G)) :=
    congrArg (fun A : stabilization G => (A : GroupOperator (ℕ × G))) (hc ⟨_,matrixUnit_mem_stabilization i j⟩).eq
  have hoff (i j : ℕ) (hij : i ≠ j) : matrixEntry (T : GroupOperator (ℕ × G)) i j=0 := by
    have he := congrArg (fun A => matrixEntry A i j) (hm j j)
    simpa only [matrixEntry_mul_matrixUnit,matrixEntry_matrixUnit_mul,ite_true,ite_eq_right hij] using he
  have hdiag (i : ℕ) : matrixEntry (T : GroupOperator (ℕ × G)) i i=matrixEntry (T : GroupOperator (ℕ × G)) 0 0 := by
    have he := congrArg (fun A => matrixEntry A i 0) (hm i 0)
    simpa only [matrixEntry_mul_matrixUnit,matrixEntry_matrixUnit_mul,ite_true] using he
  apply matrixEntry_ext
  intro i j
  rw [matrixEntry_productAmplification]
  split_ifs with hij
  · subst j
    exact hdiag i
  · exact hoff i j hij

 theorem stabilization_center_scalar
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (T : stabilization G) (hc : ∀ S : stabilization G, Commute T S) :
    ∃ c : ℂ, (T : GroupOperator (ℕ × G))=c • (1 : GroupOperator (ℕ × G)) := by
  let A : groupVonNeumann G := ⟨matrixEntry (T : GroupOperator (ℕ × G)) 0 0,
    (mem_stabilization_iff_matrix _).mp T.property 0 0⟩
  have hA : ∀ S : groupVonNeumann G, Commute A S := by
    intro S
    apply Subtype.ext
    have he := congrArg (fun U : stabilization G => matrixEntry (U : GroupOperator (ℕ × G)) 0 0)
      (hc ⟨_,diagonal_mem_stabilization S⟩).eq
    change matrixEntry ((T : GroupOperator (ℕ × G))*productAmplification ℕ G (S : GroupOperator G)) 0 0=
      matrixEntry (productAmplification ℕ G (S : GroupOperator G)*(T : GroupOperator (ℕ × G))) 0 0 at he
    change matrixEntry (T : GroupOperator (ℕ × G)) 0 0*(S : GroupOperator G)=
      (S : GroupOperator G)*matrixEntry (T : GroupOperator (ℕ × G)) 0 0
    simpa only [matrixEntry_mul_diagonal,matrixEntry_diagonal_mul] using he
  obtain ⟨c,hcA⟩ := hbase A hA
  refine ⟨c,?_⟩
  rw [stabilization_center_diagonal T hc]
  have he : matrixEntry (T : GroupOperator (ℕ × G)) 0 0=c • (1 : GroupOperator G) :=
    congrArg (fun U : groupVonNeumann G => (U : GroupOperator G)) hcA
  rw [he,map_smul,map_one]

 theorem stabilization_center_projection
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G, Commute T S) →
      ∃ c : ℂ, T=c • (1 : groupVonNeumann G))
    (P : GroupOperator (ℕ × G)) (hP : P ∈ stabilization G) (hp : IsStarProjection P)
    (hc : ∀ S ∈ stabilization G, Commute P S) : P=0 ∨ P=1 := by
  classical
  have hc' : ∀ S : stabilization G, Commute (⟨P,hP⟩ : stabilization G) S :=
    fun S => Subtype.ext (hc S S.property).eq
  obtain ⟨c,he⟩ := stabilization_center_scalar hbase ⟨P,hP⟩ hc'
  change P=c • (1 : GroupOperator (ℕ × G)) at he
  have hh := congrArg (fun A : GroupOperator (ℕ × G) => A (lp.single 2 (0,1) (1 : ℂ)) (0,1)) hp.isIdempotentElem
  rw [he] at hh
  have hcc : c*c=c := by
    change c*(c*(lp.single 2 (0,1) (1 : ℂ) : GroupHilbert (ℕ × G)) (0,1))=
      c*(lp.single 2 (0,1) (1 : ℂ) : GroupHilbert (ℕ × G)) (0,1) at hh
    simpa only [lp.single_apply,Pi.single_eq_same,mul_one] using hh
  have hzero : c*(c-1)=0 := by linear_combination hcc
  rcases mul_eq_zero.mp hzero with hz|ho
  · left
    simpa only [hz,zero_smul ℂ (A := GroupOperator (ℕ × G))] using he
  · right
    have ho : c=1 := sub_eq_zero.mp ho
    simpa only [ho,one_smul] using he

 theorem infinite_stabilization_center_projection (P : GroupOperator (ℕ × FreeGroup ℕ))
    (hP : P ∈ stabilization (FreeGroup ℕ)) (hp : IsStarProjection P)
    (hc : ∀ S ∈ stabilization (FreeGroup ℕ), Commute P S) : P=0 ∨ P=1 :=
  stabilization_center_projection (fun T hT => ⟨canonicalTrace T,infinite_free_group_center_scalar T hT⟩) P hP hp hc

end
open scoped ENNReal
variable {I : Type u_29} {J : Type u_30}

 theorem hilbert_ofReal_norm_sq (ξ : lp (fun _ : I => GroupHilbert J) 2) :
    ENNReal.ofReal (‖ξ‖^2)=∑' i, ENNReal.ofReal (‖ξ i‖^2) := by
  have hs : HasSum (fun i => ‖ξ i‖^2) (‖ξ‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using lp.hasSum_norm (by norm_num : (0:ℝ)<(2:ℝ≥0∞).toReal) ξ
  rw [← hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable]

 theorem productSingle_inner_right (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ ξ (productSingle I J i η)=inner ℂ (productCoordinate I J i ξ) η := by
  classical
  change inner ℂ ξ ((hilbertFlatten I J) (lp.single 2 i η))=
    inner ℂ (((hilbertFlatten I J).symm ξ) i) η
  have he := (hilbertFlatten I J).inner_map_map ((hilbertFlatten I J).symm ξ) (lp.single 2 i η)
  simpa only [LinearIsometryEquiv.apply_symm_apply,lp.inner_single_right] using he

 theorem productSingle_inner_left (i : I) (ξ : GroupHilbert (I × J)) (η : GroupHilbert J) :
    inner ℂ (productSingle I J i η) ξ=inner ℂ η (productCoordinate I J i ξ) := by
  have he := congrArg (star : ℂ → ℂ) (productSingle_inner_right i ξ η)
  change (starRingEnd ℂ) (inner ℂ ξ (productSingle I J i η))=
    (starRingEnd ℂ) (inner ℂ (productCoordinate I J i ξ) η) at he
  simpa only [inner_conj_symm] using he

 theorem matrixEntry_star (T : GroupOperator (I × J)) (i j : I) :
    matrixEntry (star T) i j=star (matrixEntry T j i) := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro η
  have he (T : GroupOperator (I × J)) (i j : I) (ξ : GroupHilbert J) :
      matrixEntry T i j ξ=productCoordinate I J i (T (productSingle I J j ξ)) := rfl
  rw [he,← productSingle_inner_left,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right,productSingle_inner_right]
  change inner ℂ (matrixEntry T j i η) ξ=inner ℂ η (star (matrixEntry T j i) ξ)
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]

 variable {G : Type u_31} [Group G] [DecidableEq G]

 theorem stabilizedProjectionTrace_eq_matrix (T : stabilization G) :
    stabilizedProjectionTrace T=∑' j : ℕ, ∑' i : ℕ,
      ENNReal.ofReal (‖matrixEntry (T : GroupOperator (ℕ × G)) i j (lp.single 2 (1 : G) (1 : ℂ))‖^2) := by
  classical
  apply tsum_congr
  intro j
  rw [← (hilbertFlatten ℕ G).symm.norm_map,hilbert_ofReal_norm_sq]
  apply tsum_congr
  intro i
  congr 2
  congr 1
  ext g
  rw [matrixEntry_apply,productSingle_single,hilbertFlatten_symm_apply]
  apply congrArg (fun ξ : GroupHilbert (ℕ × G) => (T : GroupOperator (ℕ × G)) ξ (i,g))
  ext x
  simp only [lp.single_apply,Pi.single_apply]
  split_ifs <;> rfl

 theorem groupVN_adjoint_delta_norm (T : groupVonNeumann G) :
    ‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2=
    ‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 := by
  classical
  have ht : canonicalTrace (T*star T)=(‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ) := by
    simpa only [star_star,StarMemClass.coe_star] using canonicalTrace_star_mul (star T)
  have he' : (‖(T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ)=
      (‖(star T : GroupOperator G) (lp.single 2 (1 : G) (1 : ℂ))‖^2 : ℂ) := by
    rw [← canonicalTrace_star_mul,← ht]
    exact canonicalTrace_mul (star T) T
  have hh := congrArg Complex.re he'
  simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh.symm

 theorem stabilizedProjectionTrace_star (T : stabilization G) :
    stabilizedProjectionTrace (star T)=stabilizedProjectionTrace T := by
  classical
  rw [stabilizedProjectionTrace_eq_matrix,stabilizedProjectionTrace_eq_matrix,ENNReal.tsum_comm]
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  congr 1
  simp only [StarMemClass.coe_star]
  rw [matrixEntry_star]
  exact groupVN_adjoint_delta_norm ⟨_,(mem_stabilization_iff_matrix _).mp T.property j i⟩

end FreeGroupFactorMain.Amplification

end

end OAI
