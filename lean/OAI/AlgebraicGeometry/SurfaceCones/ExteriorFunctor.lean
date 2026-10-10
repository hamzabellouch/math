import OAI.AlgebraicGeometry.SurfaceCones.KummerCanonical
import OAI.AlgebraicGeometry.SurfaceCones.KummerSymmetry

namespace OAI

/-! Functoriality of Kähler exterior algebras and coordinate-change formulas. -/
noncomputable section
open Module KaehlerDifferential
namespace CanonicalCoordinates
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

def exteriorFunctor (f : A →ₐ[k] B) :
    ExteriorAlgebra A Ω[A⁄k] →ₐ[k] ExteriorAlgebra B Ω[B⁄k] := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap f).symm
  exact (exteriorMap k A B).restrictScalars k

lemma exteriorFunctor_D (f : A →ₐ[k] B) (a : A) :
    exteriorFunctor f (ExteriorAlgebra.ι A (D k A a)) =
      ExteriorAlgebra.ι B (D k B (f a)) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap f).symm
  exact exteriorMap_D k A B a

lemma exteriorFunctor_smul (f : A →ₐ[k] B) (a : A)
    (v : ExteriorAlgebra A Ω[A⁄k]) :
    exteriorFunctor f (a • v) = f a • exteriorFunctor f v := by
  let : Algebra A B := f.toRingHom.toAlgebra
  let : IsScalarTower k A B :=
    IsScalarTower.of_algebraMap_eq' (AlgHom.comp_algebraMap f).symm
  change exteriorMap k A B (a • v) =
    algebraMap A B a • exteriorMap k A B v
  rw [map_smul, IsScalarTower.algebraMap_smul]

lemma volume_swap {F M : Type*} [CommRing F] [AddCommGroup M] [Module F M]
    (u v : M) :
    ExteriorAlgebra.ι F v * ExteriorAlgebra.ι F u =
      -(ExteriorAlgebra.ι F u * ExteriorAlgebra.ι F v) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap v u)

lemma volume_reflect {F M : Type*} [CommRing F] [Algebra k F]
    [AddCommGroup M] [Module F M] [Module k M]
    (d : Derivation k F M) (x y : F) :
    ExteriorAlgebra.ι F (d (1-x)) * ExteriorAlgebra.ι F (d (1-y)) =
      ExteriorAlgebra.ι F (d x) * ExteriorAlgebra.ι F (d y) := by
  simp only [map_sub, Derivation.map_one_eq_zero, zero_sub, map_neg, neg_mul_neg]

lemma volume_invert {F M : Type*} [Field F] [Algebra k F]
    [AddCommGroup M] [Module F M] [Module k M]
    (d : Derivation k F M) (x y : F) :
    ExteriorAlgebra.ι F (d x⁻¹) * ExteriorAlgebra.ι F (d (y/x)) =
      (- (x^3)⁻¹) • (ExteriorAlgebra.ι F (d x) * ExteriorAlgebra.ι F (d y)) := by
  simp only [Derivation.leibniz_inv, Derivation.leibniz_div,
    map_smul, map_sub, mul_sub, smul_mul_assoc, mul_smul_comm, smul_smul,
    ExteriorAlgebra.ι_sq_zero, smul_zero, sub_zero]
  by_cases hx : x = 0
  · simp [hx]
  · congr 1
    field_simp

end CanonicalCoordinates

end

/-! Jacobian formulas under the projective symmetries of the Kummer field. -/
noncomputable section
open Module KaehlerDifferential
namespace SourceSymmetry
open ExplicitCone CanonicalCoordinates
local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : SMul L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorSMul _ _
local instance : MulAction L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorMulAction _ _

lemma rootEquiv_base (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) (x : K) :
    rootEquiv σ π a hσ (algebraMap K L x) = algebraMap K L (σ x) := by
  apply Subtype.ext
  exact closureLift_base σ x

abbrev fieldCoord (i : Fin 2) : L := algebraMap R L (MvPolynomial.X i)
lemma fieldCoord_eq (i : Fin 2) :
    fieldCoord i = algebraMap K L (coord i) :=
  IsScalarTower.algebraMap_apply R K L (MvPolynomial.X i)

def rootProduct : L := ∏ i : Fin 6, z i
lemma rootProduct_ne_zero : rootProduct ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _ => z_ne_zero i)
lemma rootProduct_eq : rootProduct = ∏ i : Fin 5, KummerTriple.root 7 i := by
  rw [rootProduct, Fin.prod_univ_succ]
  change (1 : L) * (∏ i : Fin 5, KummerTriple.root 7 i) = _
  exact one_mul _

lemma rootEquiv_product (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) :
    ∃ c : ℂ, c ≠ 0 ∧ rootEquiv σ π a hσ rootProduct =
      algebraMap ℂ L c * (rootProduct / z (π 0)^6) := by
  choose c hc he using (fun i => rootMap_z σ π a hσ i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr (fun i _ => hc i), ?_⟩
  change rootMap σ π a hσ (∏ i, z i) = _
  rw [map_prod]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_div_distrib]
  have hp : (∏ i : Fin 6, z (π i)) = rootProduct := Equiv.prod_comp π z
  rw [hp]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma rootSwap_coord (i : Fin 2) : rootSwap (fieldCoord i) = fieldCoord (1-i) := by
  rw [fieldCoord_eq, rootSwap, rootEquiv_base, swapBase_coord, ← fieldCoord_eq]
lemma rootReflect_coord (i : Fin 2) : rootReflect (fieldCoord i) = 1-fieldCoord i := by
  rw [fieldCoord_eq, rootReflect, rootEquiv_base, reflectBase_coord, map_sub, map_one,
    ← fieldCoord_eq]
lemma rootInvert_x : rootInvert (fieldCoord 0) = (fieldCoord 0)⁻¹ := by
  rw [fieldCoord_eq, rootInvert, rootEquiv_base, invertBase_x, map_inv₀, ← fieldCoord_eq]
lemma rootInvert_y : rootInvert (fieldCoord 1) = fieldCoord 1 / fieldCoord 0 := by
  rw [fieldCoord_eq, rootInvert, rootEquiv_base, invertBase_y, map_div₀,
    ← fieldCoord_eq, ← fieldCoord_eq]

def volumeForm : ExteriorAlgebra L Ω[L⁄ℂ] :=
  ExteriorAlgebra.ι L (D ℂ L (fieldCoord 0)) *
    ExteriorAlgebra.ι L (D ℂ L (fieldCoord 1))

lemma canonicalForm_eq_product : KummerTriple.canonicalForm =
    (rootProduct^6)⁻¹ • volumeForm := by
  rw [rootProduct_eq]
  rfl

lemma rootSwap_volume : exteriorFunctor rootSwap.toAlgHom volumeForm = -volumeForm := by
  rw [volumeForm, map_mul, exteriorFunctor_D, exteriorFunctor_D,
    AlgEquiv.coe_toAlgHom, rootSwap_coord, rootSwap_coord]
  exact volume_swap _ _

lemma rootReflect_volume : exteriorFunctor rootReflect.toAlgHom volumeForm = volumeForm := by
  rw [volumeForm, map_mul, exteriorFunctor_D, exteriorFunctor_D,
    AlgEquiv.coe_toAlgHom, rootReflect_coord, rootReflect_coord]
  exact volume_reflect (D ℂ L) _ _

lemma rootInvert_volume : exteriorFunctor rootInvert.toAlgHom volumeForm =
    (-(fieldCoord 0 ^ 3)⁻¹) • volumeForm := by
  rw [volumeForm, map_mul, exteriorFunctor_D, exteriorFunctor_D,
    AlgEquiv.coe_toAlgHom, rootInvert_x, rootInvert_y]
  exact volume_invert (D ℂ L) _ _

end SourceSymmetry

end

/-! The canonical density transforms with weight five under the three chart symmetries. -/
noncomputable section
open Module KaehlerDifferential
namespace SourceSymmetry
open ExplicitCone CanonicalCoordinates
@[instance_reducible] def canonicalExteriorModule (F M : Type*) [CommRing F]
    [AddCommGroup M] [Module F M] : Module F (ExteriorAlgebra F M) := inferInstance

local instance : Module L Ω[L⁄ℂ] := kaehlerModule ℂ L
local instance : Module L (ExteriorAlgebra L Ω[L⁄ℂ]) := canonicalExteriorModule _ _
local instance : SMul L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorSMul _ _
local instance : MulAction L (ExteriorAlgebra L Ω[L⁄ℂ]) := exteriorMulAction _ _

private lemma density_coefficient {F : Type*} [Field F]
    (c r z d : F) (hc : c ≠ 0) (hr : r ≠ 0) (hz : z ≠ 0) :
    ((c * (r / z^6))^6)⁻¹ * (d / z^21) =
      (d / c^6 * z^15) * (r^6)⁻¹ := by
  field_simp

lemma rootEquiv_canonical (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0)))
    (δ : ℂ) (hδ : δ ≠ 0)
    (hv : exteriorFunctor (rootEquiv σ π a hσ).toAlgHom volumeForm =
      (algebraMap ℂ L δ / z (π 0)^21) • volumeForm) :
    ∃ b : ℂ, b ≠ 0 ∧
      exteriorFunctor (rootEquiv σ π a hσ).toAlgHom KummerTriple.canonicalForm =
        (algebraMap ℂ L b * z (π 0)^15) • KummerTriple.canonicalForm := by
  obtain ⟨c, hc, hp⟩ := rootEquiv_product σ π a hσ
  refine ⟨δ / c^6, div_ne_zero hδ (pow_ne_zero 6 hc), ?_⟩
  have hc' : algebraMap ℂ L c ≠ 0 := by simpa only [map_zero] using (algebraMap ℂ L).injective.ne hc
  rw [canonicalForm_eq_product, exteriorFunctor_smul, map_inv₀, map_pow,
    AlgEquiv.coe_toAlgHom, hp, hv, smul_smul, smul_smul,
    map_div₀, map_pow]
  exact congrArg (fun s : L => s • volumeForm)
    (density_coefficient _ _ _ _ hc' rootProduct_ne_zero (z_ne_zero _))

lemma rootSwap_canonical : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootSwap.toAlgHom KummerTriple.canonicalForm =
      algebraMap ℂ L b • KummerTriple.canonicalForm := by
  have hv : exteriorFunctor rootSwap.toAlgHom volumeForm =
      (algebraMap ℂ L (-1) / z (swapLines 0)^21) • volumeForm := by
    rw [rootSwap_volume]
    change -volumeForm = (algebraMap ℂ L (-1) / (1 : L)^21) • volumeForm
    simp only [map_neg, map_one, one_pow, div_one, neg_one_smul]
  obtain ⟨b,hb,he⟩ := rootEquiv_canonical swapBase swapLines swapScalars
    swapBase_lines (-1) (by norm_num) hv
  exact ⟨b,hb,by
    change exteriorFunctor rootSwap.toAlgHom _ =
      (algebraMap ℂ L b * (1 : L)^15) • _ at he
    simpa only [one_pow, mul_one] using he⟩

lemma rootReflect_canonical : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootReflect.toAlgHom KummerTriple.canonicalForm =
      algebraMap ℂ L b • KummerTriple.canonicalForm := by
  have hv : exteriorFunctor rootReflect.toAlgHom volumeForm =
      (algebraMap ℂ L (1) / z (reflectLines 0)^21) • volumeForm := by
    rw [rootReflect_volume]
    change volumeForm = (algebraMap ℂ L 1 / (1 : L)^21) • volumeForm
    simp only [map_one, one_pow, div_one, one_smul]
  obtain ⟨b,hb,he⟩ := rootEquiv_canonical reflectBase reflectLines reflectScalars
    reflectBase_lines (1) (by norm_num) hv
  exact ⟨b,hb,by
    change exteriorFunctor rootReflect.toAlgHom _ =
      (algebraMap ℂ L b * (1 : L)^15) • _ at he
    simpa only [one_pow, mul_one] using he⟩

lemma x_eq_root : fieldCoord 0 = z 1 ^ 7 := by
  rw [fieldCoord_eq, z_pow, lineValue_eq]
  rfl

lemma rootInvert_canonical : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootInvert.toAlgHom KummerTriple.canonicalForm =
      (algebraMap ℂ L b * z 1 ^ 15) • KummerTriple.canonicalForm := by
  have hv : exteriorFunctor rootInvert.toAlgHom volumeForm =
      (algebraMap ℂ L (-1) / z (invertLines 0)^21) • volumeForm := by
    rw [rootInvert_volume, x_eq_root, ← pow_mul]
    change (-(z 1 ^ (7*3))⁻¹) • volumeForm =
      (algebraMap ℂ L (-1) / z 1 ^21) • volumeForm
    simp only [map_neg, map_one, div_eq_mul_inv, neg_one_mul]
  obtain ⟨b,hb,he⟩ := rootEquiv_canonical invertBase invertLines invertScalars
    invertBase_lines (-1) (by norm_num) hv
  exact ⟨b,hb,he⟩

/-- The exact rational density of a frame of K on the chart indexed by t.
Its inverse fifth section factor is the same rational form on every chart. -/
def canonicalDensity (t : SectionIndex) : ExteriorAlgebra L Ω[L⁄ℂ] :=
  sectionCoefficient t ^ 5 • KummerTriple.canonicalForm

private lemma weight_cancellation {F : Type*} [Field F]
    (b c a z : F) (hz : z ≠ 0) :
    (b * (c / z^3))^5 * (a * z^15) = (b^5*a) * c^5 := by
  field_simp

lemma rootEquiv_density (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (ρ : Equiv.Perm (Fin 3)) (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0)))
    (hp : ∀ j, z (π (pairs j).1) * z (π (pairs j).2) =
      z (pairs (ρ j)).1 * z (pairs (ρ j)).2)
    (hc : ∃ b : ℂ, b ≠ 0 ∧
      exteriorFunctor (rootEquiv σ π a hσ).toAlgHom KummerTriple.canonicalForm =
        (algebraMap ℂ L b * z (π 0)^15) • KummerTriple.canonicalForm)
    (t : SectionIndex) :
    ∃ b : ℂ, b ≠ 0 ∧
      exteriorFunctor (rootEquiv σ π a hσ).toAlgHom (canonicalDensity t) =
        algebraMap ℂ L b • canonicalDensity (sectionPerm π ρ t) := by
  obtain ⟨d,hd,he⟩ := hc
  obtain ⟨b,hb,ht⟩ := transformed_sections σ π ρ a hσ hp t
  refine ⟨b^5*d, mul_ne_zero (pow_ne_zero 5 hb) hd, ?_⟩
  rw [canonicalDensity, canonicalDensity, exteriorFunctor_smul, map_pow,
    AlgEquiv.coe_toAlgHom, ht, he, smul_smul, smul_smul, map_mul, map_pow]
  exact congrArg (fun s : L => s • KummerTriple.canonicalForm)
    (weight_cancellation _ _ _ _ (z_ne_zero _))

lemma rootSwap_density (t : SectionIndex) : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootSwap.toAlgHom (canonicalDensity t) =
      algebraMap ℂ L b • canonicalDensity (swapSections t) := by
  apply rootEquiv_density swapBase swapLines swapPairs swapScalars
    swapBase_lines swap_pair_products
  change ∃ b : ℂ, b ≠ 0 ∧ exteriorFunctor rootSwap.toAlgHom _ =
    (algebraMap ℂ L b * (1 : L)^15) • _
  simpa only [one_pow, mul_one] using rootSwap_canonical

lemma rootReflect_density (t : SectionIndex) : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootReflect.toAlgHom (canonicalDensity t) =
      algebraMap ℂ L b • canonicalDensity (reflectSections t) := by
  apply rootEquiv_density reflectBase reflectLines swapPairs reflectScalars
    reflectBase_lines reflect_pair_products
  change ∃ b : ℂ, b ≠ 0 ∧ exteriorFunctor rootReflect.toAlgHom _ =
    (algebraMap ℂ L b * (1 : L)^15) • _
  simpa only [one_pow, mul_one] using rootReflect_canonical

lemma rootInvert_density (t : SectionIndex) : ∃ b : ℂ, b ≠ 0 ∧
    exteriorFunctor rootInvert.toAlgHom (canonicalDensity t) =
      algebraMap ℂ L b • canonicalDensity (invertSections t) := by
  apply rootEquiv_density invertBase invertLines invertPairs invertScalars
    invertBase_lines invert_pair_products
  exact rootInvert_canonical

end SourceSymmetry

end

end OAI
