import Mathlib
import OAI.RepresentationTheory.GraphModels.Bundles

namespace OAI

noncomputable section

/-! Regular coordinates and finite amplification of graph models. -/

namespace GraphNormality
section
open ArithmeticGerms GermBundles
variable {G H : Type*} [Group G] [Group H]
variable (C : VirtualGraph G H) (r : CosetSection C.codomain)

def firstCoordinateMap (x : (H ⧸ C.codomain) × G) : (G × H) ⧸ C.graph :=
  QuotientGroup.mk (x.2, r.repr x.1)

theorem firstCoordinateMap_injective : Function.Injective (firstCoordinateMap C r) := by
  rintro ⟨i, g⟩ ⟨j, g'⟩ he
  have hm : (g⁻¹ * g', (r.repr i)⁻¹ * r.repr j) ∈ C.graph :=
    QuotientGroup.eq.mp he
  have hb : (r.repr i)⁻¹ * r.repr j ∈ C.codomain :=
    ⟨_, hm, rfl⟩
  have hij : i = j := by
    rw [← r.repr_spec i, ← r.repr_spec j]
    exact QuotientGroup.eq.mpr hb
  subst j
  have hg : g⁻¹ * g' = 1 := by
    have h := C.snd_injective (a₁ := ⟨_, hm⟩) (a₂ := 1) (by simp)
    exact congrArg (fun x : C.graph => x.val.1) h
  exact Prod.ext rfl (inv_mul_eq_one.mp hg)

theorem firstCoordinateMap_surjective : Function.Surjective (firstCoordinateMap C r) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    let q : H ⧸ C.codomain := QuotientGroup.mk x.2
    have hb : (r.repr q)⁻¹ * x.2 ∈ C.codomain :=
      QuotientGroup.eq.mp (r.repr_spec q)
    obtain ⟨c, hc, he⟩ := hb
    refine ⟨(q, x.1 * c.1⁻¹), ?_⟩
    apply QuotientGroup.eq.mpr
    change (((x.1 * c.1⁻¹)⁻¹ * x.1), (r.repr q)⁻¹ * x.2) ∈ C.graph
    have hf : (x.1 * c.1⁻¹)⁻¹ * x.1 = c.1 := by group
    rw [hf, ← he]
    exact hc

def firstCoordinates : ((H ⧸ C.codomain) × G) ≃ ((G × H) ⧸ C.graph) :=
  Equiv.ofBijective (firstCoordinateMap C r)
    ⟨firstCoordinateMap_injective C r, firstCoordinateMap_surjective C r⟩

theorem firstCoordinates_smul (a : G) (x : (H ⧸ C.codomain) × G) :
    (a, (1 : H)) • firstCoordinates C r x = firstCoordinates C r (x.1, a * x.2) := by
  change QuotientGroup.mk ((a, (1 : H)) * (x.2, r.repr x.1)) =
    QuotientGroup.mk (a * x.2, r.repr x.1)
  simp

end

section
section
attribute [local instance] Classical.propDecidable

local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

section Reindex
variable {X Y V W : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W]

def transportLp (e : X ≃ Y) (u : X → V ≃ₗᵢ[ℂ] W) :
    lp (fun _ : X => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : Y => W) 2 where
  toLinearEquiv :=
    { toFun := fun v => ⟨fun y => u (e.symm y) (v (e.symm y)), by
        apply memℓp_gen
        convert! ((lp.memℓp v).summable (by norm_num)).comp_injective e.symm.injective using 1
        simp only [LinearIsometryEquiv.norm_map]; rfl⟩
      invFun := fun v => ⟨fun x => (u x).symm (v (e x)), by
        apply memℓp_gen
        convert! ((lp.memℓp v).summable (by norm_num)).comp_injective e.injective using 1
        simp only [LinearIsometryEquiv.norm_map]; rfl⟩
      left_inv := by
        intro v
        apply lp.ext
        funext x
        change (u x).symm (u (e.symm (e x)) (v (e.symm (e x)))) = _
        simp
      right_inv := by
        intro v
        apply lp.ext
        funext y
        change u (e.symm y) ((u (e.symm y)).symm (v (e (e.symm y)))) = _
        simp
      map_add' := by
        intro v w
        apply lp.ext
        funext y
        exact map_add _ _ _
      map_smul' := by
        intro a v
        apply lp.ext
        funext y
        exact map_smul _ _ _ }
  norm_map' := by
    intro v
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    change (∑' y, ‖u (e.symm y) (v (e.symm y))‖ ^ (2 : ENNReal).toReal) = _
    simp only [LinearIsometryEquiv.norm_map]
    exact e.symm.tsum_eq (fun x => ‖v x‖ ^ (2 : ENNReal).toReal)

theorem transportLp_apply (e : X ≃ Y) (u : X → V ≃ₗᵢ[ℂ] W)
    (v : lp (fun _ : X => V) 2) (x : X) :
    transportLp e u v (e x) = u x (v x) := by
  change u (e.symm (e x)) (v (e.symm (e x))) = _
  simp

theorem transportLp_single (e : X ≃ Y) (u : X → V ≃ₗᵢ[ℂ] W)
    (x : X) (v : V) :
    transportLp e u (lp.single 2 x v) = lp.single 2 (e x) (u x v) := by
  apply lp.ext
  funext y
  by_cases hy : y = e x
  · subst y
    rw [transportLp_apply, lp.single_apply_self, lp.single_apply_self]
  · have hxy : e.symm y ≠ x := by
      intro h
      exact hy ((e.apply_symm_apply y).symm.trans (congrArg e h))
    change u (e.symm y) ((lp.single 2 x v : lp (fun _ : X => V) 2) (e.symm y)) = _
    rw [lp.single_apply_ne (E := fun _ : X => V) 2 x v hxy, map_zero,
      lp.single_apply_ne (E := fun _ : Y => W) 2 (e x) _ hy]
end Reindex

open ArithmeticGerms GermBundles
variable {G H I V : Type*} [Group G] [Group H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def prodRatio (μ : ScalarCocycle G) (ω : ScalarCocycle H) : ScalarCocycle (G × H) where
  val g h := μ.val g.1 h.1 / ω.val g.2 h.2
  mul_assoc g h j := by
    dsimp
    rw [div_mul_div_comm, div_mul_div_comm, μ.mul_assoc, ω.mul_assoc]
  one_left g := by simp [μ.one_left, ω.one_left]
  one_right g := by simp [μ.one_right, ω.one_right]

def regularPerm (a : G) : I × G ≃ I × G where
  toFun x := (x.1, a * x.2)
  invFun x := (x.1, a⁻¹ * x.2)
  left_inv x := by simp
  right_inv x := by simp

def regularAction (μ : ScalarCocycle G) (a : G) :
    lp (fun _ : I × G => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : I × G => V) 2 :=
  transportLp (regularPerm a) (fun x => circleUnitary (μ.val a x.2))

theorem regularAction_single (μ : ScalarCocycle G) (a : G) (i : I) (g : G) (v : V) :
    regularAction μ a (lp.single 2 (i,g) v) =
      lp.single 2 (i,a*g) ((μ.val a g : ℂ) • v) := by
  exact transportLp_single (regularPerm (I := I) a)
    (fun x => circleUnitary (V := V) (μ.val a x.2)) (i, g) v

variable (C : VirtualGraph G H) (r : CosetSection C.codomain)
variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))

def firstRegularUnitary :
    lp (fun _ : (H ⧸ C.codomain) × G => V) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2 :=
  transportLp (firstCoordinates C r) (fun x =>
    B.fibre (x.2, 1) (firstCoordinates C r (x.1, 1)) (firstCoordinates C r x) (by
      simpa using firstCoordinates_smul C r x.2 (x.1, 1)))

theorem firstRegularUnitary_single (i : H ⧸ C.codomain) (g : G) (v : V) :
    firstRegularUnitary C r μ ω B (lp.single 2 (i,g) v) =
      B.action (g,1) (lp.single 2 (firstCoordinates C r (i,1)) v) := by
  rw [firstRegularUnitary, transportLp_single]
  exact (B.action_single (g,1) _ _ _ v).symm

theorem firstRegularUnitary_intertwines (a : G)
    (v : lp (fun _ : (H ⧸ C.codomain) × G => V) 2) :
    B.action (a,1) (firstRegularUnitary C r μ ω B v) =
      firstRegularUnitary C r μ ω B (regularAction μ a v) := by
  have he :
      (B.action (a,1)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (firstRegularUnitary C r μ ω B).toContinuousLinearEquiv.toContinuousLinearMap =
      (firstRegularUnitary C r μ ω B).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (regularAction μ a).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    rintro ⟨i,g⟩
    apply ContinuousLinearMap.ext
    intro w
    change B.action (a,1) (firstRegularUnitary C r μ ω B (lp.single 2 (i,g) w)) =
      firstRegularUnitary C r μ ω B (regularAction μ a (lp.single 2 (i,g) w))
    rw [firstRegularUnitary_single, B.action_mul, regularAction_single,
      firstRegularUnitary_single, lp.single_smul, map_smul]
    simp [prodRatio, ω.one_left]
  exact DFunLike.congr_fun he v

end

open ArithmeticGerms GermBundles
local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {G H V : Type*} [Group G] [Group H]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable (C : VirtualGraph G H) (r : CosetSection C.domain)

def secondCoordinateMap (x : (G ⧸ C.domain) × H) : (G × H) ⧸ C.graph :=
  QuotientGroup.mk (r.repr x.1, x.2)

theorem secondCoordinateMap_injective : Function.Injective (secondCoordinateMap C r) := by
  rintro ⟨i, h⟩ ⟨j, h'⟩ he
  have hm : ((r.repr i)⁻¹ * r.repr j, h⁻¹ * h') ∈ C.graph :=
    QuotientGroup.eq.mp he
  have hb : (r.repr i)⁻¹ * r.repr j ∈ C.domain := ⟨_, hm, rfl⟩
  have hij : i = j := by
    rw [← r.repr_spec i, ← r.repr_spec j]
    exact QuotientGroup.eq.mpr hb
  subst j
  have hh : h⁻¹ * h' = 1 := by
    have hh := C.fst_injective (a₁ := ⟨_, hm⟩) (a₂ := 1) (by simp)
    exact congrArg (fun x : C.graph => x.val.2) hh
  exact Prod.ext rfl (inv_mul_eq_one.mp hh)

theorem secondCoordinateMap_surjective : Function.Surjective (secondCoordinateMap C r) := by
  intro x
  induction x using QuotientGroup.induction_on with
  | H x =>
    let q : G ⧸ C.domain := QuotientGroup.mk x.1
    have hb : (r.repr q)⁻¹ * x.1 ∈ C.domain :=
      QuotientGroup.eq.mp (r.repr_spec q)
    obtain ⟨c, hc, he⟩ := hb
    refine ⟨(q, x.2 * c.2⁻¹), ?_⟩
    apply QuotientGroup.eq.mpr
    change ((r.repr q)⁻¹ * x.1, ((x.2 * c.2⁻¹)⁻¹ * x.2)) ∈ C.graph
    have hf : (x.2 * c.2⁻¹)⁻¹ * x.2 = c.2 := by group
    rw [hf, ← he]
    exact hc

def secondCoordinates : ((G ⧸ C.domain) × H) ≃ ((G × H) ⧸ C.graph) :=
  Equiv.ofBijective (secondCoordinateMap C r)
    ⟨secondCoordinateMap_injective C r, secondCoordinateMap_surjective C r⟩

theorem secondCoordinates_smul (a : H) (x : (G ⧸ C.domain) × H) :
    ((1 : G), a) • secondCoordinates C r x = secondCoordinates C r (x.1, a * x.2) := by
  change QuotientGroup.mk (((1 : G), a) * (r.repr x.1, x.2)) =
    QuotientGroup.mk (r.repr x.1, a * x.2)
  simp

def inverseCocycle (ω : ScalarCocycle H) : ScalarCocycle H where
  val h k := (ω.val h k)⁻¹
  mul_assoc h k l := by
    simpa only [mul_inv] using congrArg Inv.inv (ω.mul_assoc h k l)
  one_left h := by simp [ω.one_left]
  one_right h := by simp [ω.one_right]

variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))

def secondRegularUnitary :
    lp (fun _ : (G ⧸ C.domain) × H => V) 2 ≃ₗᵢ[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2 :=
  transportLp (secondCoordinates C r) (fun x =>
    B.fibre (1, x.2) (secondCoordinates C r (x.1, 1)) (secondCoordinates C r x) (by
      simpa using secondCoordinates_smul C r x.2 (x.1, 1)))

theorem secondRegularUnitary_single (i : G ⧸ C.domain) (h : H) (v : V) :
    secondRegularUnitary C r μ ω B (lp.single 2 (i,h) v) =
      B.action (1,h) (lp.single 2 (secondCoordinates C r (i,1)) v) := by
  rw [secondRegularUnitary, transportLp_single]
  exact (B.action_single (1,h) _ _ _ v).symm

theorem secondRegularUnitary_intertwines (a : H)
    (v : lp (fun _ : (G ⧸ C.domain) × H => V) 2) :
    B.action (1,a) (secondRegularUnitary C r μ ω B v) =
      secondRegularUnitary C r μ ω B (regularAction (inverseCocycle ω) a v) := by
  have he :
      (B.action (1,a)).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (secondRegularUnitary C r μ ω B).toContinuousLinearEquiv.toContinuousLinearMap =
      (secondRegularUnitary C r μ ω B).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (regularAction (inverseCocycle ω) a).toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num)
    rintro ⟨i,h⟩
    apply ContinuousLinearMap.ext
    intro w
    change B.action (1,a) (secondRegularUnitary C r μ ω B (lp.single 2 (i,h) w)) =
      secondRegularUnitary C r μ ω B (regularAction (inverseCocycle ω) a (lp.single 2 (i,h) w))
    rw [secondRegularUnitary_single, B.action_mul, regularAction_single,
      secondRegularUnitary_single, lp.single_smul, map_smul]
    simp [prodRatio, inverseCocycle, μ.one_left]
  exact DFunLike.congr_fun he v

theorem coordinate_actions_commute (g : G) (h : H)
    (v : lp (fun _ : (G × H) ⧸ C.graph => V) 2) :
    B.action (g,1) (B.action (1,h) v) = B.action (1,h) (B.action (g,1) v) := by
  rw [B.action_mul, B.action_mul]
  simp [prodRatio, μ.one_left, μ.one_right, ω.one_left, ω.one_right]

end

section
open GermBundles
open scoped InnerProductSpace
local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

section ScalarMultiplicity
variable {I J G V : Type*} [Fintype J]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (b : OrthonormalBasis J ℂ V)

def bundleBasisVector (x : (I × J) × G) : lp (fun _ : I × G => V) 2 :=
  lp.single 2 (x.1.1, x.2) (b x.1.2)

omit [CompleteSpace V] in
theorem bundleBasisVector_orthonormal : Orthonormal ℂ (bundleBasisVector (I := I) (G := G) b) := by
  rw [orthonormal_iff_ite]
  rintro ⟨⟨i,j⟩,g⟩ ⟨⟨k,l⟩,h⟩
  change ⟪lp.single (E := fun _ : I × G => V) 2 (i,g) (b j),
    lp.single (E := fun _ : I × G => V) 2 (k,h) (b l)⟫_ℂ = _
  rw [lp.inner_single_left]
  by_cases hi : i = k
  · subst k
    by_cases hg : g = h
    · subst h
      rw [lp.single_apply_self]
      simpa only [Prod.mk.injEq, true_and, and_true] using
        (orthonormal_iff_ite.mp b.orthonormal j l)
    · rw [lp.single_apply_ne (E := fun _ : I × G => V) 2 (i,h) (b l)
          (fun hh => hg (congrArg Prod.snd hh))]
      simp [hg]
  · rw [lp.single_apply_ne (E := fun _ : I × G => V) 2 (k,h) (b l)
        (fun hh => hi (congrArg Prod.fst hh))]
    simp [hi]

omit [CompleteSpace V] in
theorem bundleBasisVector_total :
    (Submodule.span ℂ (Set.range (bundleBasisVector (I := I) (G := G) b)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  apply lp.ext
  funext x
  change v x = 0
  apply b.repr.injective
  ext j
  rw [b.repr_apply_apply, map_zero]
  have h := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self ((x.1,j),x.2))) hv
  simpa only [bundleBasisVector, Prod.eta, lp.inner_single_left, PiLp.zero_apply] using h

def regularHilbertBasis : HilbertBasis ((I × J) × G) ℂ (lp (fun _ : I × G => V) 2) :=
  HilbertBasis.mkOfOrthogonalEqBot (bundleBasisVector_orthonormal b) (bundleBasisVector_total b)

@[simp] theorem regularHilbertBasis_apply (x : (I × J) × G) :
    regularHilbertBasis b x = bundleBasisVector b x := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) x

def scalarization : lp (fun _ : I × G => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : (I × J) × G => ℂ) 2 :=
  (regularHilbertBasis b).repr

theorem scalarization_apply (v : lp (fun _ : I × G => V) 2) (i : I) (j : J) (g : G) :
    scalarization b v ((i,j),g) = ⟪b j, v (i,g)⟫_ℂ := by
  change (regularHilbertBasis b).repr v ((i,j),g) = _
  rw [HilbertBasis.repr_apply_apply, regularHilbertBasis_apply]
  exact lp.inner_single_left _ _ _

end ScalarMultiplicity

section ScalarRegular
variable {I G V : Type*} [Group G]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem regularAction_apply (μ : ScalarCocycle G) (a : G)
    (v : lp (fun _ : I × G => V) 2) (i : I) (g : G) :
    regularAction μ a v (i,a*g) = (μ.val a g : ℂ) • v (i,g) := by
  exact transportLp_apply (regularPerm a) (fun x => circleUnitary (μ.val a x.2)) v (i,g)

end ScalarRegular

variable {I J G V : Type*} [Fintype J] [Group G]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (b : OrthonormalBasis J ℂ V)

theorem scalarization_intertwines (μ : ScalarCocycle G) (a : G)
    (v : lp (fun _ : I × G => V) 2) :
    scalarization b (regularAction μ a v) = regularAction μ a (scalarization b v) := by
  apply lp.ext
  funext x
  obtain ⟨y,rfl⟩ := (regularPerm (I := I × J) a).surjective x
  rcases y with ⟨⟨i,j⟩,g⟩
  change scalarization b (regularAction μ a v) ((i,j),a*g) =
    regularAction μ a (scalarization b v) ((i,j),a*g)
  rw [scalarization_apply, regularAction_apply, inner_smul_right,
    regularAction_apply, scalarization_apply]
  rfl

end

section
open scoped InnerProductSpace
local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

variable {K G : Type*} [Fintype K]

def finiteSumBasisVector (x : K × G) : PiLp 2 (fun _ : K => lp (fun _ : G => ℂ) 2) :=
  PiLp.single 2 x.1 (lp.single 2 x.2 1)

theorem finiteSumBasisVector_inner (x : K × G)
    (v : PiLp 2 (fun _ : K => lp (fun _ : G => ℂ) 2)) :
    ⟪finiteSumBasisVector x, v⟫_ℂ = v x.1 x.2 := by
  rw [PiLp.inner_apply, Finset.sum_eq_single x.1]
  · simp [finiteSumBasisVector, lp.inner_single_left]
  · intro i hi hix
    simp [finiteSumBasisVector, hix]
  · simp

theorem finiteSumBasisVector_orthonormal :
    Orthonormal ℂ (finiteSumBasisVector (K := K) (G := G)) := by
  rw [orthonormal_iff_ite]
  rintro ⟨i,g⟩ ⟨j,h⟩
  rw [finiteSumBasisVector_inner]
  by_cases hi : i = j
  · subst j
    simp [finiteSumBasisVector, lp.single_apply, Pi.single_apply]
  · simp [finiteSumBasisVector, hi]

theorem finiteSumBasisVector_total :
    (Submodule.span ℂ (Set.range (finiteSumBasisVector (K := K) (G := G))))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  change v = 0
  ext i g
  change v i g = 0
  have h := Submodule.inner_right_of_mem_orthogonal
    (Submodule.subset_span (Set.mem_range_self (i,g))) hv
  simpa only [finiteSumBasisVector_inner] using h

def finiteSumHilbertBasis :
    HilbertBasis (K × G) ℂ (PiLp 2 (fun _ : K => lp (fun _ : G => ℂ) 2)) :=
  HilbertBasis.mkOfOrthogonalEqBot finiteSumBasisVector_orthonormal finiteSumBasisVector_total

@[simp] theorem finiteSumHilbertBasis_apply (x : K × G) :
    finiteSumHilbertBasis x = finiteSumBasisVector x := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) x

def finiteRegrouping : lp (fun _ : K × G => ℂ) 2 ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : K => lp (fun _ : G => ℂ) 2) :=
  finiteSumHilbertBasis.repr.symm

theorem finiteRegrouping_apply (v : lp (fun _ : K × G => ℂ) 2) (i : K) (g : G) :
    finiteRegrouping v i g = v (i,g) := by
  have h := congrArg (fun f : lp (fun _ : K × G => ℂ) 2 => f (i,g))
    (finiteSumHilbertBasis.repr.apply_symm_apply v)
  rw [HilbertBasis.repr_apply_apply, finiteSumHilbertBasis_apply,
    finiteSumBasisVector_inner] at h
  exact h

end

section
open scoped InnerProductSpace
variable {K L : Type*} [Fintype K]
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]

def amplify (T : L →L[ℂ] L) :
    PiLp 2 (fun _ : K => L) →L[ℂ] PiLp 2 (fun _ : K => L) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : K => L)).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.pi (fun i : K => T.comp (ContinuousLinearMap.proj i))).comp
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : K => L)).toContinuousLinearMap)

omit [Fintype K] [CompleteSpace L] in
@[simp] theorem amplify_apply (T : L →L[ℂ] L) (v : PiLp 2 (fun _ : K => L)) (i : K) :
    amplify T v i = T (v i) := rfl

def amplification : (L →L[ℂ] L) →⋆ₐ[ℂ]
    (PiLp 2 (fun _ : K => L) →L[ℂ] PiLp 2 (fun _ : K => L)) where
  toFun := amplify
  map_one' := by ext v i; rfl
  map_mul' T S := by ext v i; rfl
  map_add' T S := by ext v i; rfl
  map_zero' := by ext v i; rfl
  commutes' z := by ext v i; rfl
  map_star' T := by
    change amplify (K := K) (ContinuousLinearMap.adjoint T) =
      ContinuousLinearMap.adjoint (amplify (K := K) T)
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro v w
    simp only [PiLp.inner_apply, amplify_apply, ContinuousLinearMap.adjoint_inner_left]

theorem amplification_wot_continuous :
    Continuous (fun T : L →WOT[ℂ] L =>
      ContinuousLinearMapWOT.ofCLM (amplification (K := K) (L := L) (ContinuousLinearMapWOT.toCLM T))) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro v w
  change Continuous (fun T : L →WOT[ℂ] L => ∑ i : K, ⟪w i, T (v i)⟫_ℂ)
  apply continuous_finsetSum
  intro i hi
  exact ContinuousLinearMapWOT.continuous_iff.mp continuous_id (v i) (w i)

end

section
open scoped InnerProductSpace
local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

open GermBundles

section ScalarTwistedRegular
variable {G K : Type*} [Group G] [Fintype K]

def scalarRegular (μ : ScalarCocycle G) (a : G) :
    lp (fun _ : G => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : G => ℂ) 2 :=
  transportLp (Equiv.mulLeft a) (fun g => circleUnitary (μ.val a g))

theorem scalarRegular_apply (μ : ScalarCocycle G) (a : G)
    (v : lp (fun _ : G => ℂ) 2) (g : G) :
    scalarRegular μ a v (a*g) = (μ.val a g : ℂ) * v g := by
  exact transportLp_apply (Equiv.mulLeft a) (fun g => circleUnitary (μ.val a g)) v g

theorem finiteRegrouping_intertwines (μ : ScalarCocycle G) (a : G)
    (v : lp (fun _ : K × G => ℂ) 2) :
    finiteRegrouping (regularAction μ a v) =
      amplify (scalarRegular μ a).toContinuousLinearEquiv.toContinuousLinearMap
        (finiteRegrouping v) := by
  ext i g
  obtain ⟨h,rfl⟩ := (Equiv.mulLeft a).surjective g
  change finiteRegrouping (regularAction μ a v) i (a*h) =
    scalarRegular μ a (finiteRegrouping v i) (a*h)
  rw [finiteRegrouping_apply, regularAction_apply, scalarRegular_apply,
    finiteRegrouping_apply]
  rfl

end ScalarTwistedRegular

variable {L W : Type*}
variable [NormedAddCommGroup L] [InnerProductSpace ℂ L] [CompleteSpace L]
variable [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

theorem unitaryConjugation_wot_continuous (U : L ≃ₗᵢ[ℂ] W) :
    Continuous (fun T : L →WOT[ℂ] L =>
      ContinuousLinearMapWOT.ofCLM (U.conjStarAlgEquiv (ContinuousLinearMapWOT.toCLM T))) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro v w
  have h : (fun T : L →WOT[ℂ] L =>
      ⟪w, U.conjStarAlgEquiv (ContinuousLinearMapWOT.toCLM T) v⟫_ℂ) =
      (fun T : L →WOT[ℂ] L => ⟪U.symm w, T (U.symm v)⟫_ℂ) := by
    funext T
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
    conv_lhs => lhs; rw [← U.apply_symm_apply w]
    exact U.inner_map_map _ _
  change Continuous (fun T : L →WOT[ℂ] L =>
    ⟪w, U.conjStarAlgEquiv (ContinuousLinearMapWOT.toCLM T) v⟫_ℂ)
  rw [h]
  exact ContinuousLinearMapWOT.continuous_iff.mp continuous_id (U.symm v) (U.symm w)

end

open ArithmeticGerms GermBundles
local instance (priority := 2000) (X : Type*) : DecidableEq X := Classical.decEq X

section FiniteRegularModules
variable {I J G V : Type*} [Fintype I] [Fintype J] [Group G]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (b : OrthonormalBasis J ℂ V)

def regularToFinite : lp (fun _ : I × G => V) 2 ≃ₗᵢ[ℂ]
    PiLp 2 (fun _ : I × J => lp (fun _ : G => ℂ) 2) :=
  (scalarization b).trans finiteRegrouping

theorem regularToFinite_intertwines (μ : ScalarCocycle G) (a : G)
    (v : lp (fun _ : I × G => V) 2) :
    regularToFinite b (regularAction μ a v) =
      amplify (scalarRegular μ a).toContinuousLinearEquiv.toContinuousLinearMap
        (regularToFinite b v) := by
  change finiteRegrouping (scalarization b (regularAction μ a v)) = _
  rw [scalarization_intertwines, finiteRegrouping_intertwines]
  rfl

end FiniteRegularModules

variable {G H V J : Type*} [Group G] [Group H] [Fintype J]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable (C : VirtualGraph G H)
local instance : Fintype (G ⧸ C.domain) := Subgroup.fintypeQuotientOfFiniteIndex
local instance : Fintype (H ⧸ C.codomain) := Subgroup.fintypeQuotientOfFiniteIndex

variable (μ : ScalarCocycle G) (ω : ScalarCocycle H)
variable (B : ProjectiveBundle (prodRatio μ ω) (fun _ : (G × H) ⧸ C.graph => V))
variable (b : OrthonormalBasis J ℂ V)

def firstFiniteRegularUnitary :
    PiLp 2 (fun _ : (H ⧸ C.codomain) × J => lp (fun _ : G => ℂ) 2) ≃ₗᵢ[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2 :=
  (regularToFinite b).symm.trans
    (firstRegularUnitary C (chooseCosetSection C.codomain) μ ω B)

theorem firstFiniteRegularUnitary_intertwines (a : G)
    (v : PiLp 2 (fun _ : (H ⧸ C.codomain) × J => lp (fun _ : G => ℂ) 2)) :
    B.action (a,1) (firstFiniteRegularUnitary C μ ω B b v) =
      firstFiniteRegularUnitary C μ ω B b
        (amplify (scalarRegular μ a).toContinuousLinearEquiv.toContinuousLinearMap v) := by
  change B.action (a,1) (firstRegularUnitary C _ μ ω B ((regularToFinite b).symm v)) =
    firstRegularUnitary C _ μ ω B ((regularToFinite b).symm _)
  rw [firstRegularUnitary_intertwines]
  congr 1
  apply (regularToFinite b).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    regularToFinite_intertwines b μ a ((regularToFinite b).symm v)

def secondFiniteRegularUnitary :
    PiLp 2 (fun _ : (G ⧸ C.domain) × J => lp (fun _ : H => ℂ) 2) ≃ₗᵢ[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2 :=
  (regularToFinite b).symm.trans
    (secondRegularUnitary C (chooseCosetSection C.domain) μ ω B)

theorem secondFiniteRegularUnitary_intertwines (a : H)
    (v : PiLp 2 (fun _ : (G ⧸ C.domain) × J => lp (fun _ : H => ℂ) 2)) :
    B.action (1,a) (secondFiniteRegularUnitary C μ ω B b v) =
      secondFiniteRegularUnitary C μ ω B b
        (amplify (scalarRegular (inverseCocycle ω) a).toContinuousLinearEquiv.toContinuousLinearMap v) := by
  change B.action (1,a) (secondRegularUnitary C _ μ ω B ((regularToFinite b).symm v)) =
    secondRegularUnitary C _ μ ω B ((regularToFinite b).symm _)
  rw [secondRegularUnitary_intertwines]
  congr 1
  apply (regularToFinite b).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    regularToFinite_intertwines b (inverseCocycle ω) a ((regularToFinite b).symm v)

def firstExtension : (lp (fun _ : G => ℂ) 2 →L[ℂ] lp (fun _ : G => ℂ) 2) →⋆ₐ[ℂ]
    (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →L[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2) :=
  (firstFiniteRegularUnitary C μ ω B b).conjStarAlgEquiv.toStarAlgHom.comp
    (amplification (K := (H ⧸ C.codomain) × J))

def secondExtension : (lp (fun _ : H => ℂ) 2 →L[ℂ] lp (fun _ : H => ℂ) 2) →⋆ₐ[ℂ]
    (lp (fun _ : (G × H) ⧸ C.graph => V) 2 →L[ℂ]
      lp (fun _ : (G × H) ⧸ C.graph => V) 2) :=
  (secondFiniteRegularUnitary C μ ω B b).conjStarAlgEquiv.toStarAlgHom.comp
    (amplification (K := (G ⧸ C.domain) × J))

theorem firstExtension_generator (a : G) :
    firstExtension C μ ω B b (scalarRegular μ a).toContinuousLinearEquiv.toContinuousLinearMap =
      (B.action (a,1)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change firstFiniteRegularUnitary C μ ω B b
    (amplify _ ((firstFiniteRegularUnitary C μ ω B b).symm v)) = B.action (a,1) v
  rw [← firstFiniteRegularUnitary_intertwines, LinearIsometryEquiv.apply_symm_apply]

theorem secondExtension_generator (a : H) :
    secondExtension C μ ω B b
      (scalarRegular (inverseCocycle ω) a).toContinuousLinearEquiv.toContinuousLinearMap =
      (B.action (1,a)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  change secondFiniteRegularUnitary C μ ω B b
    (amplify _ ((secondFiniteRegularUnitary C μ ω B b).symm v)) = B.action (1,a) v
  rw [← secondFiniteRegularUnitary_intertwines, LinearIsometryEquiv.apply_symm_apply]

theorem firstExtension_wot_continuous :
    Continuous (fun T : lp (fun _ : G => ℂ) 2 →WOT[ℂ] lp (fun _ : G => ℂ) 2 =>
      ContinuousLinearMapWOT.ofCLM (firstExtension C μ ω B b T.toCLM)) :=
  (unitaryConjugation_wot_continuous (firstFiniteRegularUnitary C μ ω B b)).comp
    (amplification_wot_continuous (K := (H ⧸ C.codomain) × J))

theorem secondExtension_wot_continuous :
    Continuous (fun T : lp (fun _ : H => ℂ) 2 →WOT[ℂ] lp (fun _ : H => ℂ) 2 =>
      ContinuousLinearMapWOT.ofCLM (secondExtension C μ ω B b T.toCLM)) :=
  (unitaryConjugation_wot_continuous (secondFiniteRegularUnitary C μ ω B b)).comp
    (amplification_wot_continuous (K := (G ⧸ C.domain) × J))

end GraphNormality

end

end OAI
