import OAI.Algebra.AuslanderReiten.Resolutions.CProjectiveResolution
import OAI.Algebra.AuslanderReiten.Ext.ExtBridge

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

private theorem F_coeff_zero (a : F q) (i : Letter)
    (hi : i = e ∨ i = x ∨ i = y ∨ i = z ∨ i = t ∨ i = j) : (a : C).coeff i = 0 := by
  have h := congrArg (fun b : C => b.coeff i) a.property
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [product] using h.symm

@[simp] theorem F_coeff_e (a : F q) : (a : C).coeff e = 0 := F_coeff_zero q a e (by simp)
@[simp] theorem F_coeff_x (a : F q) : (a : C).coeff x = 0 := F_coeff_zero q a x (by simp)
@[simp] theorem F_coeff_y (a : F q) : (a : C).coeff y = 0 := F_coeff_zero q a y (by simp)
@[simp] theorem F_coeff_z (a : F q) : (a : C).coeff z = 0 := F_coeff_zero q a z (by simp)
@[simp] theorem F_coeff_t (a : F q) : (a : C).coeff t = 0 := F_coeff_zero q a t (by simp)
@[simp] theorem F_coeff_j (a : F q) : (a : C).coeff j = 0 := F_coeff_zero q a j (by simp)

theorem F_expand (a : F q) : (a : C) =
    (a : C).coeff f • basisVector q f + (a : C).coeff u • basisVector q u +
    (a : C).coeff v • basisVector q v + (a : C).coeff n • basisVector q n := by
  ext i
  cases i <;> simp

def uPreimage (α β γ : k) : E q :=
  ⟨α • basisVector q e + β • basisVector q x + (γ / (1 + q)) • basisVector q t, by
    change (_ : C) * basisVector q e = _
    simp [add_mul, basis_mul, multiplicationTable]⟩

theorem uPreimage_spec (α β γ : k) (hq : 1 + q ≠ 0) :
    (uPreimage q α β γ : C) * basisVector q u =
      α • basisVector q u + β • basisVector q v + γ • basisVector q n := by
  rw [mul_u_formula]
  have hγ : (1 + q) * (γ / (1 + q)) = γ := by rw [mul_comm, div_mul_cancel₀ γ hq]
  simp [uPreimage, hγ]

theorem mem_range_dU_iff (hq : 1 + q ≠ 0) (a : F q) :
    a ∈ LinearMap.range (dU q) ↔ (a : C).coeff f = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp [product]
  · intro ha
    refine ⟨uPreimage q ((a : C).coeff u) ((a : C).coeff v) ((a : C).coeff n), ?_⟩
    apply Subtype.ext
    rw [coe_dU, uPreimage_spec q _ _ _ hq]
    simpa [ha] using (F_expand q a).symm

def fCoordinate : F q →ₗ[k] k where
  toFun a := (a : C).coeff f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def simpleCoordinate : Simple q →ₗ[k] k :=
  ((LinearMap.range (dU q)).restrictScalars k).liftQ (fCoordinate q) (by
    rintro a ⟨b, rfl⟩
    change (dU q b : C).coeff f = 0
    simp [product])

@[simp] theorem simpleCoordinate_mk (a : F q) :
    simpleCoordinate q (Submodule.Quotient.mk a) = (a : C).coeff f := rfl

theorem simpleCoordinate_eq_zero_iff (hq : 1 + q ≠ 0) (a : Simple q) :
    simpleCoordinate q a = 0 ↔ a = 0 := by
  refine Submodule.Quotient.induction_on _ a ?_
  intro b
  rw [simpleCoordinate_mk, Submodule.Quotient.mk_eq_zero]
  exact (mem_range_dU_iff q hq b).symm

theorem simpleCoordinate_injective (hq : 1 + q ≠ 0) : Function.Injective (simpleCoordinate q) := by
  intro a b hab
  apply sub_eq_zero.mp
  apply (simpleCoordinate_eq_zero_iff q hq (a - b)).mp
  simp [map_sub, hab]

def vertexF : F q := ⟨basisVector q f, by
  change basisVector q f * basisVector q f = basisVector q f
  simpa [multiplicationTable] using basis_mul q f f⟩

theorem simpleCoordinate_surjective : Function.Surjective (simpleCoordinate q) := by
  intro r
  refine ⟨Submodule.Quotient.mk (r • vertexF q), ?_⟩
  simp [vertexF]

def simpleCoordinateEquiv (hq : 1 + q ≠ 0) : Simple q ≃ₗ[k] k :=
  LinearEquiv.ofBijective (simpleCoordinate q)
    ⟨simpleCoordinate_injective q hq, simpleCoordinate_surjective q⟩

theorem simple_finrank (hq : 1 + q ≠ 0) : Module.finrank k (Simple q) = 1 := by
  rw [(simpleCoordinateEquiv q hq).finrank_eq]
  exact Module.finrank_self k

theorem simpleCoordinate_smul (c : C) (a : Simple q) :
    simpleCoordinate q (c • a) = c.coeff f * simpleCoordinate q a := by
  refine Submodule.Quotient.induction_on _ a ?_
  intro b
  rfl

theorem e_smul_simple (hq : 1 + q ≠ 0) (a : Simple q) : basisVector q e • a = 0 := by
  apply simpleCoordinate_injective q hq
  rw [simpleCoordinate_smul, map_zero]
  simp

theorem f_smul_simple (hq : 1 + q ≠ 0) (a : Simple q) : basisVector q f • a = a := by
  apply simpleCoordinate_injective q hq
  rw [simpleCoordinate_smul]
  simp

def vertexE : E q := ⟨basisVector q e, by
  change basisVector q e * basisVector q e = basisVector q e
  simpa [multiplicationTable] using basis_mul q e e⟩

theorem e_smul_vertexE : basisVector q e • vertexE q = vertexE q := by
  apply Subtype.ext
  exact (vertexE q).property

theorem smul_vertexE (a : E q) : (a : C) • vertexE q = a := by
  apply Subtype.ext
  exact a.property

theorem hom_E_simple_eq_zero (hq : 1 + q ≠ 0) (g : E q →ₗ[C] Simple q) : g = 0 := by
  have hz : g (vertexE q) = 0 := by
    calc
      g (vertexE q) = g (basisVector q e • vertexE q) := congrArg g (e_smul_vertexE q).symm
      _ = basisVector q e • g (vertexE q) := g.map_smul _ _
      _ = 0 := e_smul_simple q hq _
  ext a
  calc
    g a = g ((a : C) • vertexE q) := congrArg g (smul_vertexE q a).symm
    _ = (a : C) • g (vertexE q) := g.map_smul _ _
    _ = 0 := by rw [hz, smul_zero]

variable [CharP k 2]

theorem simple_positiveExt (h : NoPositivePowerOne q) :
    PositiveExtVanish C (Simple q) (Simple q) := by
  apply (positiveExtVanish_iff_resolution C (Simple q) (Simple q) (projectiveResolution q h)).mpr
  intro n g _
  have hg : g = 0 := by
    apply ModuleCat.hom_ext
    exact hom_E_simple_eq_zero q (by simpa using h 1 (by decide)) g.hom
  refine ⟨0, ?_⟩
  simp [hg]

end ArExplicit.Resolution

end

end OAI
