import OAI.Algebra.AuslanderReiten.Triangular.TriangularProjective
import OAI.Algebra.AuslanderReiten.Complete.CompleteResolution

namespace OAI

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {K L M U V : Type*}
variable [AddCommGroup K] [Module k K] [Module R K] [IsScalarTower k R K]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup U] [Module k U] [Module R U] [IsScalarTower k R U]
variable [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

theorem eHomLift (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d)
    [Module.Finite R U] [Module.Projective R U]
    {ψ : BalancedTensor k R F U →ₗ[R] V}
    (g : TriangularE k R F L →ₗ[Triangular R F] TriangularModule k R F U V ψ)
    (hg : g.comp (eMap e) = 0) :
    ∃ G : TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F U V ψ,
      G.comp (eMap d) = g := by
  have ha : (TriangularModule.topMap g).comp e = 0 := by
    ext x
    have hx := congrArg TriangularModule.top (DFunLike.congr_fun hg ⟨x, 0⟩)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply, TriangularModule.top_zero,
      eMap, eHom, TriangularModule.hom, LinearMap.coe_mk, AddHom.coe_mk,
      map_zero, TriangularModule.topMap_apply] using hx
  obtain ⟨b, hb⟩ := h.projective (TriangularModule.topMap g) ha
  refine ⟨eHom b, ?_⟩
  apply eHomEquiv.injective
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hb x

omit [Module k K] [IsScalarTower k R K] [Module k L] [IsScalarTower k R L]
  [Module k M] [IsScalarTower k R M] in
theorem jHomLift (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d)
    [Module.Finite R V] [Module.Projective R V]
    {ψ : BalancedTensor k R F U →ₗ[R] V}
    (g : TriangularJ k R F L →ₗ[Triangular R F] TriangularModule k R F U V ψ)
    (hg : g.comp (jMap e) = 0) :
    ∃ G : TriangularJ k R F M →ₗ[Triangular R F] TriangularModule k R F U V ψ,
      G.comp (jMap d) = g := by
  have ha : (TriangularModule.bottomMap g).comp e = 0 := by
    ext x
    exact congrArg TriangularModule.bottom (DFunLike.congr_fun hg ⟨0, x⟩)
  obtain ⟨b, hb⟩ := h.projective (TriangularModule.bottomMap g) ha
  refine ⟨jHom b, ?_⟩
  apply jHomEquiv.injective
  apply LinearMap.ext
  intro x
  exact DFunLike.congr_fun hb x

omit [IsScalarTower k R F] [SMulCommClass k Rᵐᵒᵖ F] in
theorem regular_decomposition (a : Triangular R F) :
    eRegularInclusion (eRegularProjection (k := k) a) +
      jRegularInclusion (jRegularProjection (k := k) a) = a := by
  ext <;> simp [eRegularInclusion, eRegularProjection, jRegularInclusion, jRegularProjection]

theorem eHomExact (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d) :
    HomExactAt (eMap (k := k) (F := F) e) (eMap d) := by
  intro g hg
  let g₁ := (eRegularProjection (k := k)).comp g
  have hg₁ : g₁.comp (eMap e) = 0 := by
    dsimp [g₁]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  obtain ⟨G, hG⟩ := eHomLift e d h g₁ hg₁
  refine ⟨eRegularInclusion.comp G, ?_⟩
  have hg₂ : (jRegularProjection (k := k)).comp g = 0 := hom_E_J_eq_zero _
  apply LinearMap.ext
  intro x
  have hGx := DFunLike.congr_fun hG x
  change G (eMap d x) = g₁ x at hGx
  change eRegularInclusion (G (eMap d x)) = g x
  rw [hGx]
  have hsplit := regular_decomposition (k := k) (g x)
  have hzero := DFunLike.congr_fun hg₂ x
  change jRegularProjection (g x) = 0 at hzero
  simpa only [hzero, map_zero, add_zero, g₁, LinearMap.comp_apply] using hsplit

omit [Module k K] [IsScalarTower k R K] [Module k L] [IsScalarTower k R L]
  [Module k M] [IsScalarTower k R M] in
theorem jHomExact [Module.Finite R F] [Module.Projective R F]
    (e : K →ₗ[R] L) (d : L →ₗ[R] M) (h : HomExactAt e d) :
    HomExactAt (jMap (k := k) (F := F) e) (jMap d) := by
  intro g hg
  let : Module.Finite R (BalancedTensor k R F R) :=
    Module.Finite.equiv (BalancedTensor.runitLeft (S := R)).symm
  let : Module.Projective R (BalancedTensor k R F R) :=
    Module.Projective.of_equiv (BalancedTensor.runitLeft (S := R)).symm
  let g₁ := (eRegularProjection (k := k)).comp g
  let g₂ := (jRegularProjection (k := k)).comp g
  have hg₁ : g₁.comp (jMap e) = 0 := by
    dsimp [g₁]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  have hg₂ : g₂.comp (jMap e) = 0 := by
    dsimp [g₂]
    rw [LinearMap.comp_assoc, hg, LinearMap.comp_zero]
  obtain ⟨G₁, hG₁⟩ := jHomLift e d h g₁ hg₁
  obtain ⟨G₂, hG₂⟩ := jHomLift e d h g₂ hg₂
  refine ⟨eRegularInclusion.comp G₁ + jRegularInclusion.comp G₂, ?_⟩
  apply LinearMap.ext
  intro x
  change eRegularInclusion (G₁ (jMap d x)) + jRegularInclusion (G₂ (jMap d x)) = g x
  have h₁ : G₁ (jMap d x) = g₁ x := DFunLike.congr_fun hG₁ x
  have h₂ : G₂ (jMap d x) = g₂ x := DFunLike.congr_fun hG₂ x
  rw [h₁, h₂]
  exact regular_decomposition (k := k) (g x)

end ArExplicit.TriangularInduction

end OAI
