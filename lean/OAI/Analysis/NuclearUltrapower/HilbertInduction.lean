import Mathlib

namespace OAI

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v

/-- A coordinate permutation with unitary entries on a Hilbert direct sum. -/
def lpUnitary {ι : Type u} {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V) :
    lp (fun _ : ι => V) 2 ≃ₗᵢ[ℂ] lp (fun _ : ι => V) 2 := by
  have hm (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V) (x : lp (fun _ : ι => V) 2) :
      Memℓp (fun i => T i (x (e i))) 2 := by
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    have hx := (lp.memℓp x).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hh := hx.comp_injective e.injective
    apply hh.congr
    intro i
    exact congrArg (fun r : ℝ => r ^ (2 : ℝ≥0∞).toReal) ((T i).norm_map (x (e i))).symm
  let L : lp (fun _ : ι => V) 2 ≃ₗ[ℂ] lp (fun _ : ι => V) 2 := {
    toFun x := ⟨fun i => T i (x (e i)), hm e T x⟩
    invFun x := ⟨fun i => (T (e.symm i)).symm (x (e.symm i)),
      hm e.symm (fun i => (T (e.symm i)).symm) x⟩
    left_inv x := by ext i; simp
    right_inv x := by ext i; simp
    map_add' x y := by ext i; exact map_add (T i) _ _
    map_smul' c x := by ext i; exact map_smul (T i) _ _ }
  refine ⟨L, fun x => ?_⟩
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  -- Compute the square of the norm by the defining l2 sum.
  have hnorm (y : lp (fun _ : ι => V) 2) : ‖y‖ ^ 2 = ∑' i, ‖y i‖ ^ 2 := by
    simpa using lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) y
  rw [hnorm, hnorm]
  simpa only [L, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometryEquiv.norm_map] using e.tsum_eq (fun i => ‖x i‖ ^ 2)

@[simp] theorem lpUnitary_apply {ι : Type u} {V : Type v} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (e : Equiv.Perm ι) (T : ι → V ≃ₗᵢ[ℂ] V)
    (x : lp (fun _ : ι => V) 2) (i : ι) : lpUnitary e T x i = T i (x (e i)) := rfl

section Induction
variable {G : Type u} [Group G] (H : Subgroup G)

/-- A normalized transversal; the identity coset is represented by the identity. -/
def cosetRep (i : G ⧸ H) : G := by
  classical
  exact if i = (QuotientGroup.mk 1 : G ⧸ H) then 1 else i.out

@[simp] theorem cosetRep_identity : cosetRep H (QuotientGroup.mk 1) = 1 := by
  simp [cosetRep]

theorem cosetRep_mk (i : G ⧸ H) : QuotientGroup.mk (cosetRep H i) = i := by
  classical
  unfold cosetRep
  split_ifs with hi
  · exact hi.symm
  · exact QuotientGroup.out_eq' i

/-- The transversal cocycle, with source coordinate `i` and target `g • i`. -/
def cosetCocycle (g : G) (i : G ⧸ H) : H :=
  ⟨(cosetRep H (g • i))⁻¹ * g * cosetRep H i, by
    rw [mul_assoc]
    apply QuotientGroup.eq.mp
    change (QuotientGroup.mk (cosetRep H (g • i)) : G ⧸ H) = g • (QuotientGroup.mk (cosetRep H i) : G ⧸ H)
    rw [cosetRep_mk, cosetRep_mk]⟩

@[simp] theorem cosetCocycle_one (i : G ⧸ H) : cosetCocycle H 1 i = 1 := by
  apply Subtype.ext
  simp [cosetCocycle]

theorem cosetCocycle_mul (g h : G) (i : G ⧸ H) :
    cosetCocycle H (g * h) i = cosetCocycle H g (h • i) * cosetCocycle H h i := by
  apply Subtype.ext
  simp only [cosetCocycle, Subgroup.coe_mul, mul_smul]
  group

variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (α : H →* (V ≃ₗᵢ[ℂ] V))

/-- Unitary induction with no finite-index assumption. -/
def inducedUnitary : G →* (lp (fun _ : G ⧸ H => V) 2 ≃ₗᵢ[ℂ]
    lp (fun _ : G ⧸ H => V) 2) where
  toFun g := lpUnitary (MulAction.toPerm g⁻¹)
    (fun i => α (cosetCocycle H g (g⁻¹ • i)))
  map_one' := by ext x i; simp
  map_mul' g h := by
    ext x i
    simp only [lpUnitary_apply, MulAction.toPerm_apply,
      mul_inv_rev, mul_smul]
    rw [cosetCocycle_mul, map_mul]
    simp

@[simp] theorem inducedUnitary_apply (g : G) (x : lp (fun _ : G ⧸ H => V) 2) (i : G ⧸ H) :
    inducedUnitary H α g x i = α (cosetCocycle H g (g⁻¹ • i)) (x (g⁻¹ • i)) := rfl

/-- Subgroup elements fix the identity left coset. -/
@[simp] theorem subgroup_smul_identity (h : H) :
    (h : G) • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 := by
  change (QuotientGroup.mk ((h:G) * 1) : G ⧸ H) = QuotientGroup.mk 1
  apply QuotientGroup.eq.mpr
  simp

@[simp] theorem cosetCocycle_identity (h : H) :
    cosetCocycle H (h:G) (QuotientGroup.mk 1) = h := by
  apply Subtype.ext
  simp only [cosetCocycle, subgroup_smul_identity, cosetRep_identity, inv_one, one_mul, mul_one]

@[simp] theorem cosetRep_smul_identity (i : G ⧸ H) :
    cosetRep H i • (QuotientGroup.mk 1 : G ⧸ H) = i := by
  change (QuotientGroup.mk (cosetRep H i * 1) : G ⧸ H) = i
  simpa using cosetRep_mk H i

@[simp] theorem induced_identity_coordinate (h : H)
    (x : lp (fun _ : G ⧸ H => V) 2) :
    inducedUnitary H α (h:G) x (QuotientGroup.mk 1) = α h (x (QuotientGroup.mk 1)) := by
  rw [inducedUnitary_apply]
  have hh : (h:G)⁻¹ • (QuotientGroup.mk 1 : G ⧸ H) = QuotientGroup.mk 1 :=
    subgroup_smul_identity H h⁻¹
  rw [hh, cosetCocycle_identity]

/-- Translation of a coordinate to the identity has cocycle one. -/
theorem induced_translate_coordinate (i : G ⧸ H)
    (x : lp (fun _ : G ⧸ H => V) 2) :
    inducedUnitary H α (cosetRep H i)⁻¹ x (QuotientGroup.mk 1) = x i := by
  rw [inducedUnitary_apply, inv_inv, cosetRep_smul_identity]
  have hc : cosetCocycle H (cosetRep H i)⁻¹ i = 1 := by
    apply Subtype.ext
    have hi : (cosetRep H i)⁻¹ • i = (QuotientGroup.mk 1 : G ⧸ H) := by
      calc
        _ = (cosetRep H i)⁻¹ • (cosetRep H i • (QuotientGroup.mk 1 : G ⧸ H)) :=
          congrArg (fun j : G ⧸ H => (cosetRep H i)⁻¹ • j) (cosetRep_smul_identity H i).symm
        _ = _ := inv_smul_smul _ _
    simp [cosetCocycle, hi]
  rw [hc, map_one]
  rfl

/-- The original representation embeds on the identity coordinate. -/
def inductionInclusion : V →ₗᵢ[ℂ] lp (fun _ : G ⧸ H => V) 2 := by
  classical
  refine { toLinearMap := lp.lsingle (𝕜 := ℂ) (E := fun _ : G ⧸ H => V) 2 (QuotientGroup.mk 1), norm_map' := ?_ }
  intro v
  exact lp.norm_single (E := fun _ : G ⧸ H => V) (p := 2) (by norm_num) (QuotientGroup.mk 1) v

@[simp] theorem inductionInclusion_apply (v : V) (i : G ⧸ H) :
    inductionInclusion H v i = Pi.single (M := fun _ : G ⧸ H => V) (QuotientGroup.mk 1) v i := rfl

theorem inductionInclusion_intertwines (h : H) (v : V) :
    inductionInclusion H (α h v) = inducedUnitary H α (h:G) (inductionInclusion H v) := by
  classical
  ext i
  by_cases hi : i = (QuotientGroup.mk 1 : G ⧸ H)
  · subst i
    rw [induced_identity_coordinate]
    simp
  · have hh : (h:G)⁻¹ • i ≠ (QuotientGroup.mk 1 : G ⧸ H) := by
      intro he
      have := congrArg (fun j : G ⧸ H => (h:G) • j) he
      exact hi (by simpa only [smul_inv_smul, subgroup_smul_identity] using this)
    simp only [inductionInclusion_apply, Pi.single_eq_of_ne hi, inducedUnitary_apply,
      Pi.single_eq_of_ne hh, map_zero]

end Induction
end NuclearUltrapower
end
end

section

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped ENNReal InnerProductSpace
namespace NuclearUltrapower
universe u v
abbrev L2 (I : Type u) := lp (fun _ : I => ℂ) 2

/-- Coordinate lines in a Hilbert direct sum. -/
def l2Single {I : Type u} (i : I) : ℂ →ₗᵢ[ℂ] L2 I := by
  classical
  exact ⟨lp.lsingle (𝕜 := ℂ) (E := fun _ : I => ℂ) 2 i,
    fun c => lp.norm_single (E := fun _ : I => ℂ) (p := 2) (by norm_num) i c⟩

@[simp] theorem l2Single_apply {I : Type u} (i : I) (c : ℂ) :
    l2Single i c = lp.single 2 i c := rfl

theorem l2Single_orthogonal {I : Type u} :
    OrthogonalFamily ℂ (fun _ : I => ℂ) (l2Single (I := I)) := by
  classical
  intro i j hij x y
  rw [l2Single_apply, l2Single_apply, lp.inner_single_left]
  simp [lp.single_apply, hij]

/-- An injection of coordinate sets induces an honest Hilbert isometry. -/
def l2Embedding {I : Type u} {J : Type v} (e : I ↪ J) : L2 I →ₗᵢ[ℂ] L2 J :=
  (show OrthogonalFamily ℂ (fun _ : I => ℂ) (fun i => l2Single (e i)) from
    fun _ _ hij x y => l2Single_orthogonal (e.injective.ne hij) x y).linearIsometry

@[simp] theorem l2Embedding_single {I : Type u} {J : Type v} (e : I ↪ J)
    (i : I) (c : ℂ) : l2Embedding e (lp.single 2 i c) = lp.single 2 (e i) c := by
  classical
  exact OrthogonalFamily.linearIsometry_apply_single
    (G := fun _ : I => ℂ) (V := fun i => l2Single (e i)) _ c

/-- The adjoint of coordinate extension is coordinate restriction. -/
@[simp] theorem l2Embedding_adjoint_apply {I : Type u} {J : Type v} (e : I ↪ J)
    (x : L2 J) (i : I) : (l2Embedding e).toContinuousLinearMap.adjoint x i = x (e i) := by
  classical
  have h := ContinuousLinearMap.adjoint_inner_right (l2Embedding e).toContinuousLinearMap
    (lp.single 2 i (1 : ℂ)) x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, l2Embedding_single,
    lp.inner_single_left, RCLike.inner_apply', map_one, one_mul] using h

/-- Bounded maps on a Hilbert direct sum are determined by coordinate vectors. -/
theorem l2_clm_ext {I : Type u} {E : Type v} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T U : L2 I →L[ℂ] E} (h : ∀ i c, T (lp.single 2 i c) = U (lp.single 2 i c)) : T = U := by
  classical
  apply lp.ext_continuousLinearMap (p := 2) ENNReal.ofNat_ne_top
  intro i
  apply ContinuousLinearMap.ext
  intro c
  exact h i c

end NuclearUltrapower
end
end

end OAI
