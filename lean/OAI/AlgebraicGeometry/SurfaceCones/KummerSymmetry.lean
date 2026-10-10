import OAI.AlgebraicGeometry.SurfaceCones.KummerTripleOpen

namespace OAI

/-! Projective symmetries of the complete quadrangle lift to its Kummer extension. -/
noncomputable section
namespace SourceSymmetry
open ExplicitCone
abbrev A := AlgebraicClosure K

/-- Lift a complex-linear automorphism of the rational function field to its algebraic closure. -/
def closureLift (σ : K ≃ₐ[ℂ] K) : A ≃ₐ[ℂ] A :=
  { IsAlgClosure.equivOfEquiv A A σ.toRingEquiv with
    commutes' := fun c => by
      change IsAlgClosure.equivOfEquiv A A σ.toRingEquiv
        (algebraMap ℂ A c) = algebraMap ℂ A c
      rw [IsScalarTower.algebraMap_apply ℂ K A,
        IsAlgClosure.equivOfEquiv_algebraMap]
      exact congrArg (algebraMap K A) (σ.commutes c) }

@[simp] lemma closureLift_base (σ : K ≃ₐ[ℂ] K) (x : K) :
    closureLift σ (algebraMap K A x) = algebraMap K A (σ x) :=
  IsAlgClosure.equivOfEquiv_algebraMap A A σ.toRingEquiv x

/-- Over the algebraically closed ground field every element with a scalar
positive power is itself a scalar. -/
lemma scalar_of_power {E : Type*} [Field E] [Algebra ℂ E]
    {n : ℕ} (hn : 0 < n) {x : E} {a : ℂ}
    (hx : x ^ n = algebraMap ℂ E a) : ∃ c : ℂ, algebraMap ℂ E c = x := by
  have hi : IsIntegral ℂ x :=
    (hx.symm ▸ isIntegral_algebraMap (R := ℂ) (A := E) (x := a)).of_pow hn
  exact hi.mem_range_algebraMap_of_minpoly_splits
    (K := ℂ) (IsAlgClosed.splits _)

/-- Six homogeneous forms in the affine rational trivialization. -/
def lineValue : Fin 6 → K := Fin.cases 1 KummerLines.radicand

lemma z_pow (i : Fin 6) : z i ^ 7 = algebraMap K L (lineValue i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [z, lineValue]
  · exact KummerCover.fieldRoot_pow KummerLines.radicand j

lemma ambient_z_pow (i : Fin 6) : (z i : A) ^ 7 = algebraMap K A (lineValue i) := by
  exact congrArg Subtype.val (z_pow i)

lemma ambient_z_ne_zero (i : Fin 6) : (z i : A) ≠ 0 := by
  exact (L.val.injective).ne (z_ne_zero i)

/-- Projectively permuting the six line forms in the base field really
permutes the six Kummer roots up to nonzero complex scalar and the same
projective denominator in the chosen algebraic closure. -/
lemma transformed_roots (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) :
    ∀ i, ∃ c : ℂ, c ≠ 0 ∧ closureLift σ (z i : A) =
      algebraMap ℂ A c * ((z (π i) : A) / (z (π 0) : A)) := by
  intro i
  let t : A := (z (π i) : A) / (z (π 0) : A)
  have ht : t ≠ 0 := div_ne_zero (ambient_z_ne_zero _) (ambient_z_ne_zero _)
  have hp : (closureLift σ (z i : A) / t) ^ 7 = algebraMap ℂ A (a i) := by
    rw [div_pow, ← map_pow, ambient_z_pow, closureLift_base, hσ]
    simp only [map_mul, map_div₀, ← IsScalarTower.algebraMap_apply]
    have ht7 : t ^ 7 = algebraMap K A (lineValue (π i)) /
        algebraMap K A (lineValue (π 0)) := by
      simp only [t, div_pow, ambient_z_pow]
    rw [← ht7, mul_div_cancel_right₀ _ (pow_ne_zero 7 ht)]
  obtain ⟨c, hc⟩ := scalar_of_power (by decide : 0 < 7) hp
  have he : closureLift σ (z i : A) = algebraMap ℂ A c * t := by
    exact (div_eq_iff ht).mp hc.symm
  refine ⟨c, ?_, he⟩
  intro hc0
  rw [hc0, map_zero, zero_mul] at he
  exact ambient_z_ne_zero i ((closureLift σ).injective (by simpa using he))

/-- The lifted automorphism maps the five-root subfield to itself. -/
lemma closureLift_mem (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0)))
    (x : L) : closureLift σ (x : A) ∈ L := by
  have hroots (i : Fin 5) : closureLift σ (y i : A) ∈ L := by
    obtain ⟨c, _, hc⟩ := transformed_roots σ π a hσ i.succ
    change closureLift σ (z i.succ : A) ∈ L
    rw [hc]
    exact L.mul_mem ((L.restrictScalars ℂ).algebraMap_mem c)
      (L.div_mem (z (π i.succ)).property (z (π 0)).property)
  have hx : x ∈ Algebra.adjoin K (Set.range y) := by
    rw [KummerCover.fieldRoot_generates]; trivial
  induction hx using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hroots i
  | algebraMap t =>
    change closureLift σ (algebraMap K A t) ∈ L
    rw [closureLift_base]
    exact L.algebraMap_mem (σ t)
  | add x y hx hy ex ey =>
    change closureLift σ ((x : A) + (y : A)) ∈ L
    simpa only [map_add] using L.add_mem ex ey
  | mul x y hx hy ex ey =>
    change closureLift σ ((x : A) * (y : A)) ∈ L
    simpa only [map_mul] using L.mul_mem ex ey

/-- Restriction of a lifted projective line-arrangement symmetry to the
Kummer field. -/
def rootMap (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) : L →ₐ[ℂ] L :=
  { toFun := fun x => ⟨closureLift σ (x : A), closureLift_mem σ π a hσ x⟩
    map_zero' := by apply Subtype.ext; exact map_zero _
    map_one' := by apply Subtype.ext; exact map_one _
    map_add' := fun x y => by apply Subtype.ext; exact map_add _ _ _
    map_mul' := fun x y => by apply Subtype.ext; exact map_mul _ _ _
    commutes' := fun c => by apply Subtype.ext; exact (closureLift σ).commutes c }

lemma rootMap_z (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ) (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) (i : Fin 6) :
    ∃ c : ℂ, c ≠ 0 ∧ rootMap σ π a hσ (z i) =
      algebraMap ℂ L c * (z (π i) / z (π 0)) := by
  obtain ⟨c, hc, he⟩ := transformed_roots σ π a hσ i
  exact ⟨c, hc, Subtype.ext he⟩


lemma rootMap_surjective (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ) (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) :
    Function.Surjective (rootMap σ π a hσ) := by
  let f := rootMap σ π a hσ
  have hz (i : Fin 6) : z i ∈ f.fieldRange := by
    obtain ⟨c, hc, he⟩ := rootMap_z σ π a hσ (π.symm i)
    obtain ⟨d, hd, he0⟩ := rootMap_z σ π a hσ (π.symm 0)
    simp only [Equiv.apply_symm_apply] at he he0
    refine ⟨algebraMap ℂ L (d / c) * (z (π.symm i) / z (π.symm 0)), ?_⟩
    change f _ = z i
    simp only [map_mul, map_div₀, AlgHom.commutes]
    change (algebraMap ℂ L d / algebraMap ℂ L c) * (rootMap σ π a hσ (z (π.symm i)) /
      rootMap σ π a hσ (z (π.symm 0))) = z i
    rw [he, he0, show z 0 = 1 from rfl]
    have hc' : algebraMap ℂ L c ≠ 0 := by simpa only [map_zero] using (algebraMap ℂ L).injective.ne hc
    have hd' : algebraMap ℂ L d ≠ 0 := by simpa only [map_zero] using (algebraMap ℂ L).injective.ne hd
    field_simp [hc', hd', z_ne_zero (π 0)]
  have hgen : IntermediateField.adjoin ℂ (Set.range y) ≤ f.fieldRange := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i.succ
  rw [roots_generate_over_complex] at hgen
  intro x
  exact hgen (show x ∈ (⊤ : IntermediateField ℂ L) from trivial)

/-- The Kummer field carries every projective symmetry of the six
line arrangement that is supplied by an rational-function automorphism. -/
def rootEquiv (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (a : Fin 6 → ℂ) (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0))) : L ≃ₐ[ℂ] L :=
  AlgEquiv.ofBijective (rootMap σ π a hσ)
    ⟨(rootMap σ π a hσ).injective, rootMap_surjective σ π a hσ⟩

end SourceSymmetry


namespace SourceSymmetry
open ExplicitCone MvPolynomial
open scoped nonZeroDivisors

/-- The affine coordinate x in the exact source rational function field. -/
abbrev coord (i : Fin 2) : K := algebraMap R K (X i)

lemma coord_ne_zero (i : Fin 2) : coord i ≠ 0 := by
  simpa only [map_zero] using (IsFractionRing.injective R K).ne (X_ne_zero i)

lemma xPowers_le : Submonoid.powers (X (0 : Fin 2) : R) ≤ R⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n (X_ne_zero 0))

def xOpen : Subalgebra R K :=
  Localization.subalgebra K (Submonoid.powers (X (0 : Fin 2) : R)) xPowers_le

instance : IsLocalization.Away (X (0 : Fin 2) : R) xOpen :=
  inferInstanceAs (IsLocalization.Away (X (0 : Fin 2) : R)
    (Localization.subalgebra K _ xPowers_le))
instance : IsFractionRing xOpen K :=
  inferInstanceAs (IsFractionRing (Localization.subalgebra K _ xPowers_le) K)

abbrev ax (i : Fin 2) : xOpen := algebraMap R xOpen (X i)

def ix : xOpen := IsLocalization.Away.invSelf (X (0 : Fin 2) : R)

lemma ax_ix : ax 0 * ix = 1 := IsLocalization.Away.mul_invSelf _
lemma ix_unit : IsUnit ix := isUnit_iff_exists_inv.mpr ⟨ax 0, by simpa [mul_comm] using ax_ix⟩

def invertEval : R →ₐ[ℂ] xOpen := aeval ![ix, ax 1 * ix]

lemma invertEval_x : invertEval (X (0 : Fin 2)) = ix := by simp [invertEval]
lemma invertEval_y : invertEval (X (1 : Fin 2)) = ax 1 * ix := by simp [invertEval]

/-- The projective involution (x,y) ↦ (1/x,y/x), constructed on its principal open before extending to the function field. -/
def invertHom : xOpen →ₐ[ℂ] xOpen :=
  IsLocalization.Away.liftAlgHom (X (0 : Fin 2) : R)
    (f := invertEval) (by rw [invertEval_x]; exact ix_unit)

lemma invertHom_base (p : R) : invertHom (algebraMap R xOpen p) = invertEval p := by
  unfold invertHom
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl
lemma invertHom_x : invertHom (ax 0) = ix := by rw [invertHom_base, invertEval_x]
lemma invertHom_y : invertHom (ax 1) = ax 1 * ix := by rw [invertHom_base, invertEval_y]

lemma invertHom_ix : invertHom ix = ax 0 := by
  apply ix_unit.mul_left_inj.mp
  have hh := congrArg invertHom ax_ix
  rw [map_mul, map_one, invertHom_x] at hh
  calc
    invertHom ix * ix = 1 := by simpa [mul_comm] using hh
    _ = ax 0 * ix := ax_ix.symm

lemma invertHom_involutive : invertHom.comp invertHom = AlgHom.id ℂ xOpen := by
  apply IsLocalization.algHom_ext (Submonoid.powers (X (0 : Fin 2) : R))
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change invertHom (invertHom (ax 0)) = ax 0
    rw [invertHom_x, invertHom_ix]
  · change invertHom (invertHom (ax 1)) = ax 1
    rw [invertHom_y, map_mul, invertHom_y, invertHom_ix]
    calc
      ax 1 * ix * ax 0 = ax 1 * (ax 0 * ix) := by ring
      _ = ax 1 := by rw [ax_ix, mul_one]

def invertOpenEquiv : xOpen ≃ₐ[ℂ] xOpen :=
  AlgEquiv.ofAlgHom invertHom invertHom invertHom_involutive invertHom_involutive

def invertBase : K ≃ₐ[ℂ] K :=
  IsFractionRing.algEquivOfAlgEquiv invertOpenEquiv

lemma ix_coe : (ix : K) = (coord 0)⁻¹ := by
  have h := congrArg (fun x : xOpen => (x : K)) ax_ix
  change coord 0 * (ix : K) = 1 at h
  apply mul_left_cancel₀ (coord_ne_zero 0)
  rw [mul_inv_cancel₀ (coord_ne_zero 0)]
  exact h

lemma invertBase_x : invertBase (coord 0) = (coord 0)⁻¹ := by
  change invertBase (algebraMap xOpen K (ax 0)) = _
  rw [invertBase, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change (invertHom (ax 0) : K) = _
  rw [invertHom_x, ix_coe]

lemma invertBase_y : invertBase (coord 1) = coord 1 / coord 0 := by
  change invertBase (algebraMap xOpen K (ax 1)) = _
  rw [invertBase, IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change (invertHom (ax 1) : K) = _
  rw [invertHom_y]
  change coord 1 * (ix : K) = _
  rw [ix_coe, div_eq_mul_inv]


def swapPolynomial : R ≃ₐ[ℂ] R :=
  let f : R →ₐ[ℂ] R := aeval ![X 1, X 0]
  AlgEquiv.ofAlgHom f f (by ext i; fin_cases i <;> simp [f])
    (by ext i; fin_cases i <;> simp [f])

def reflectPolynomial : R ≃ₐ[ℂ] R :=
  let f : R →ₐ[ℂ] R := aeval ![1 - X 0, 1 - X 1]
  AlgEquiv.ofAlgHom f f (by ext i; fin_cases i <;> simp [f])
    (by ext i; fin_cases i <;> simp [f])

def swapBase : K ≃ₐ[ℂ] K := IsFractionRing.algEquivOfAlgEquiv swapPolynomial

def reflectBase : K ≃ₐ[ℂ] K := IsFractionRing.algEquivOfAlgEquiv reflectPolynomial

lemma swapBase_coord (i : Fin 2) : swapBase (coord i) = coord (1 - i) := by
  fin_cases i <;>
    simp [swapBase, coord, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
      swapPolynomial]

lemma reflectBase_coord (i : Fin 2) : reflectBase (coord i) = 1 - coord i := by
  fin_cases i <;>
    simp [reflectBase, coord, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
      reflectPolynomial]

def swapLines : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide
  right_inv := by decide

def reflectLines : Equiv.Perm (Fin 6) where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by decide
  right_inv := by decide

def invertLines : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 5, 4]
  invFun := ![1, 0, 2, 3, 5, 4]
  left_inv := by decide
  right_inv := by decide

lemma lineValue_eq : lineValue =
    ![1, coord 0, coord 1, coord 0 - 1, coord 1 - 1, coord 0 - coord 1] := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [lineValue]
  · change KummerLines.radicand j = _
    fin_cases j <;> simp [KummerLines.radicand, KummerLines.lineForm, coord]

def swapScalars : Fin 6 → ℂ := ![1, 1, 1, 1, 1, -1]
def reflectScalars : Fin 6 → ℂ := ![1, -1, -1, -1, -1, -1]
def invertScalars : Fin 6 → ℂ := ![1, 1, 1, -1, -1, -1]

lemma swapBase_lines (i : Fin 6) : swapBase (lineValue i) =
    algebraMap ℂ K (swapScalars i) *
      (lineValue (swapLines i) / lineValue (swapLines 0)) := by
  fin_cases i <;> simp [lineValue_eq, swapScalars, swapLines, swapBase_coord]

lemma reflectBase_lines (i : Fin 6) : reflectBase (lineValue i) =
    algebraMap ℂ K (reflectScalars i) *
      (lineValue (reflectLines i) / lineValue (reflectLines 0)) := by
  fin_cases i <;> simp [lineValue_eq, reflectScalars, reflectLines, reflectBase_coord]

lemma invertBase_lines (i : Fin 6) : invertBase (lineValue i) =
    algebraMap ℂ K (invertScalars i) *
      (lineValue (invertLines i) / lineValue (invertLines 0)) := by
  fin_cases i <;>
    simp [lineValue_eq, invertScalars, invertLines, invertBase_x, invertBase_y] <;>
    field_simp <;> ring

/-- Three symmetries, generating the projective S₄ of the quadrangle. -/
def rootSwap : L ≃ₐ[ℂ] L := rootEquiv swapBase swapLines swapScalars swapBase_lines
def rootReflect : L ≃ₐ[ℂ] L :=
  rootEquiv reflectBase reflectLines reflectScalars reflectBase_lines
def rootInvert : L ≃ₐ[ℂ] L := rootEquiv invertBase invertLines invertScalars invertBase_lines

end SourceSymmetry

end

/-! Transport of ratio charts under projective symmetries. -/
noncomputable section
namespace SourceSymmetry
variable {k F ι : Type*} [Field k] [Field F] [Algebra k F]

def ratioChart (v : ι → F) (t : ι) : Subalgebra k F :=
  Algebra.adjoin k (Set.range fun i => v i / v t)

lemma ratioChart_generator (v : ι → F) (t i : ι) :
    v i / v t ∈ ratioChart (k := k) v t :=
  Algebra.subset_adjoin (Set.mem_range_self i)

lemma ratioChart_map_eq (v : ι → F) (hv : ∀ i, v i ≠ 0)
    (e : F ≃ₐ[k] F) (π : Equiv.Perm ι) (d : F) (hd : d ≠ 0)
    (a : ι → k) (ha : ∀ i, a i ≠ 0)
    (he : ∀ i, e (v i) = algebraMap k F (a i) * (v (π i) / d)) (t : ι) :
    (ratioChart (k := k) v t).map e.toAlgHom = ratioChart v (π t) := by
  have ha' (i : ι) : algebraMap k F (a i) ≠ 0 :=
    by simpa only [map_zero] using (algebraMap k F).injective.ne (ha i)
  have hratio (i : ι) : e (v i / v t) =
      algebraMap k F (a i / a t) * (v (π i) / v (π t)) := by
    rw [map_div₀, he, he, map_div₀]
    field_simp [hd, hv, ha']
  apply le_antisymm
  · rw [ratioChart, AlgHom.map_adjoin]
    apply Algebra.adjoin_le
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change e (v i / v t) ∈ ratioChart (k := k) v (π t)
    rw [hratio]
    exact (ratioChart v (π t)).mul_mem ((ratioChart v (π t)).algebraMap_mem _)
      (ratioChart_generator v (π t) (π i))
  · apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    have hg : e (v (π.symm i) / v t) ∈ (ratioChart (k := k) v t).map e.toAlgHom :=
      ⟨_, ratioChart_generator v t (π.symm i), rfl⟩
    have hm := ((ratioChart (k := k) v t).map e.toAlgHom).mul_mem
      (((ratioChart (k := k) v t).map e.toAlgHom).algebraMap_mem
        (a t / a (π.symm i))) hg
    have heq : algebraMap k F (a t / a (π.symm i)) *
        e (v (π.symm i) / v t) = v i / v (π t) := by
      rw [hratio, map_div₀, map_div₀, Equiv.apply_symm_apply]
      field_simp [ha']
    rw [heq] at hm
    exact hm

def ratioChartEquiv (v : ι → F) (hv : ∀ i, v i ≠ 0)
    (e : F ≃ₐ[k] F) (π : Equiv.Perm ι) (d : F) (hd : d ≠ 0)
    (a : ι → k) (ha : ∀ i, a i ≠ 0)
    (he : ∀ i, e (v i) = algebraMap k F (a i) * (v (π i) / d)) (t : ι) :
    ratioChart (k := k) v t ≃ₐ[k] ratioChart (k := k) v (π t) :=
  (e.subalgebraMap (ratioChart (k := k) v t)).trans
    (Subalgebra.equivOfEq _ _ (ratioChart_map_eq v hv e π d hd a ha he t))

end SourceSymmetry


/-! Symmetries of the eighteen sections of H = 3J − E. -/
namespace SourceSymmetry
open ExplicitCone

abbrev SectionIndex := Fin 6 × Fin 3

def coefficientChart (t : SectionIndex) : Subalgebra ℂ L :=
  ratioChart sectionCoefficient t

lemma coefficient_ne_zero (t : SectionIndex) : sectionCoefficient t ≠ 0 :=
  mul_ne_zero (mul_ne_zero (z_ne_zero _) (z_ne_zero _)) (z_ne_zero _)

lemma coefficientChart_base : coefficientChart (0,0) = sectionChart := rfl

def sectionPerm (π : Equiv.Perm (Fin 6)) (ρ : Equiv.Perm (Fin 3)) :
    Equiv.Perm SectionIndex := Equiv.prodCongr π ρ

def swapPairs : Equiv.Perm (Fin 3) where
  toFun := ![1,0,2]
  invFun := ![1,0,2]
  left_inv := by decide
  right_inv := by decide
def invertPairs : Equiv.Perm (Fin 3) where
  toFun := ![2,1,0]
  invFun := ![2,1,0]
  left_inv := by decide
  right_inv := by decide

lemma swap_pair_products (j : Fin 3) :
    z (swapLines (pairs j).1) * z (swapLines (pairs j).2) =
      z (pairs (swapPairs j)).1 * z (pairs (swapPairs j)).2 := by
  fin_cases j <;> simp [pairs, swapPairs, swapLines]

lemma reflect_pair_products (j : Fin 3) :
    z (reflectLines (pairs j).1) * z (reflectLines (pairs j).2) =
      z (pairs (swapPairs j)).1 * z (pairs (swapPairs j)).2 := by
  fin_cases j <;> simp [pairs, swapPairs, reflectLines, mul_comm]

lemma invert_pair_products (j : Fin 3) :
    z (invertLines (pairs j).1) * z (invertLines (pairs j).2) =
      z (pairs (invertPairs j)).1 * z (pairs (invertPairs j)).2 := by
  fin_cases j <;> simp [pairs, invertPairs, invertLines, mul_comm]

lemma transformed_sections (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (ρ : Equiv.Perm (Fin 3)) (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0)))
    (hp : ∀ j, z (π (pairs j).1) * z (π (pairs j).2) =
      z (pairs (ρ j)).1 * z (pairs (ρ j)).2) :
    ∀ i, ∃ c : ℂ, c ≠ 0 ∧ rootEquiv σ π a hσ (sectionCoefficient i) =
      algebraMap ℂ L c * (sectionCoefficient (sectionPerm π ρ i) / z (π 0) ^ 3) := by
  intro i
  obtain ⟨c, hc, he⟩ := rootMap_z σ π a hσ i.1
  obtain ⟨d, hd, he'⟩ := rootMap_z σ π a hσ (pairs i.2).1
  obtain ⟨f, hf, he''⟩ := rootMap_z σ π a hσ (pairs i.2).2
  refine ⟨c*d*f, mul_ne_zero (mul_ne_zero hc hd) hf, ?_⟩
  change rootMap σ π a hσ (z i.1 * z (pairs i.2).1 * z (pairs i.2).2) = _
  rw [map_mul, map_mul, he, he', he'', map_mul, map_mul]
  have hp' : sectionCoefficient (sectionPerm π ρ i) =
      z (π i.1) * (z (π (pairs i.2).1) * z (π (pairs i.2).2)) := by
    rw [hp]
    simp only [sectionCoefficient, sectionPerm, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, mul_assoc]
  rw [hp']
  field_simp

def sectionChartEquiv (σ : K ≃ₐ[ℂ] K) (π : Equiv.Perm (Fin 6))
    (ρ : Equiv.Perm (Fin 3)) (a : Fin 6 → ℂ)
    (hσ : ∀ i, σ (lineValue i) =
      algebraMap ℂ K (a i) * (lineValue (π i) / lineValue (π 0)))
    (hp : ∀ j, z (π (pairs j).1) * z (π (pairs j).2) =
      z (pairs (ρ j)).1 * z (pairs (ρ j)).2) (t : SectionIndex) :
    coefficientChart t ≃ₐ[ℂ] coefficientChart (sectionPerm π ρ t) := by
  let b := fun i => Classical.choose (transformed_sections σ π ρ a hσ hp i)
  have hb (i) : b i ≠ 0 ∧ rootEquiv σ π a hσ (sectionCoefficient i) =
      algebraMap ℂ L (b i) *
        (sectionCoefficient (sectionPerm π ρ i) / z (π 0) ^ 3) :=
    Classical.choose_spec (transformed_sections σ π ρ a hσ hp i)
  exact ratioChartEquiv sectionCoefficient coefficient_ne_zero (rootEquiv σ π a hσ)
    (sectionPerm π ρ) (z (π 0)^3) (pow_ne_zero 3 (z_ne_zero _))
    b (fun i => (hb i).1) (fun i => (hb i).2) t

def swapSections : Equiv.Perm SectionIndex := sectionPerm swapLines swapPairs
def reflectSections : Equiv.Perm SectionIndex := sectionPerm reflectLines swapPairs
def invertSections : Equiv.Perm SectionIndex := sectionPerm invertLines invertPairs

def swapChart (t : SectionIndex) :
    coefficientChart t ≃ₐ[ℂ] coefficientChart (swapSections t) :=
  sectionChartEquiv swapBase swapLines swapPairs swapScalars swapBase_lines swap_pair_products t

def reflectChart (t : SectionIndex) :
    coefficientChart t ≃ₐ[ℂ] coefficientChart (reflectSections t) :=
  sectionChartEquiv reflectBase reflectLines swapPairs reflectScalars reflectBase_lines
    reflect_pair_products t

def invertChart (t : SectionIndex) :
    coefficientChart t ≃ₐ[ℂ] coefficientChart (invertSections t) :=
  sectionChartEquiv invertBase invertLines invertPairs invertScalars invertBase_lines
    invert_pair_products t

end SourceSymmetry


namespace SourceSymmetry
open ExplicitCone

def stepPermutation : Fin 3 → Equiv.Perm SectionIndex :=
 ![swapSections, reflectSections, invertSections]

def stepChart (m : Fin 3) (t : SectionIndex) :
    coefficientChart t ≃ₐ[ℂ] coefficientChart (stepPermutation m t) := by
  refine Fin.cases (swapChart t) (fun j => ?_) m
  refine Fin.cases (reflectChart t) (fun k => ?_) j
  refine Fin.cases (invertChart t) (fun v => Fin.elim0 v) k

def applyWord : List (Fin 3) → SectionIndex → SectionIndex
  | [], t => t
  | m :: ms, t => applyWord ms (stepPermutation m t)

def wordChart : (ms : List (Fin 3)) → (t : SectionIndex) →
    coefficientChart t ≃ₐ[ℂ] coefficientChart (applyWord ms t)
  | [], _ => AlgEquiv.refl
  | m :: ms, t => (stepChart m t).trans (wordChart ms (stepPermutation m t))

def Good (t : SectionIndex) : Prop :=
  t.1 ≠ (pairs t.2).1 ∧ t.1 ≠ (pairs t.2).2

def wordFor (t : SectionIndex) : List (Fin 3) :=
  ![![[], [0], []],
    ![[], [0, 2], [2]],
    ![[0, 2, 0], [], [2, 0]],
    ![[0, 2, 1], [], [2, 1]],
    ![[], [0, 2, 0, 1], [2, 0, 1]],
    ![[2, 0, 1, 2], [0, 2, 0, 1, 2], []]] t.1 t.2

lemma wordFor_image (t : SectionIndex) (ht : Good t) :
    applyWord (wordFor t) (0,0) = t := by
  rcases t with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;> simp [Good, pairs] at ht
  all_goals decide

def goodChartEquiv (t : SectionIndex) (ht : Good t) :
    sectionChart ≃ₐ[ℂ] coefficientChart t :=
  (Subalgebra.equivOfEq _ _ coefficientChart_base.symm).trans
    ((wordChart (wordFor t) (0,0)).trans
      (Subalgebra.equivOfEq _ _ (congrArg coefficientChart (wordFor_image t ht))))

end SourceSymmetry


namespace SourceSymmetry
open ExplicitCone

lemma coefficientChart_field (t : SectionIndex) :
    IntermediateField.adjoin ℂ (coefficientChart t : Set L) = ⊤ := by
  let S := IntermediateField.adjoin ℂ (coefficientChart t : Set L)
  have hs (i : SectionIndex) : sectionCoefficient i / sectionCoefficient t ∈ S :=
    IntermediateField.subset_adjoin ℂ _ (ratioChart_generator sectionCoefficient t i)
  have hz (i : Fin 6) : z i ∈ S := by
    have hh := S.div_mem (hs (i,0)) (hs (0,0))
    have he : (sectionCoefficient (i,0) / sectionCoefficient t) /
        (sectionCoefficient (0,0) / sectionCoefficient t) = z i := by
      rw [div_div_div_cancel_right₀ (coefficient_ne_zero t)]
      change (z i * z 1 * z 4) / (1 * z 1 * z 4) = z i
      rw [one_mul, mul_assoc, mul_div_cancel_right₀ _ (mul_ne_zero (z_ne_zero _) (z_ne_zero _))]
    exact he ▸ hh
  have hroot : IntermediateField.adjoin ℂ (Set.range y) ≤ S := by
    apply IntermediateField.adjoin_le_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact hz i.succ
  rw [roots_generate_over_complex] at hroot
  exact top_unique hroot

instance coefficientChart_fractionRing (t : SectionIndex) :
    IsFractionRing (coefficientChart t) L :=
  IsFractionRing.of_field (coefficientChart t) L fun f => by
    have hf : f ∈ IntermediateField.adjoin ℂ (coefficientChart t : Set L) := by
      rw [coefficientChart_field]; trivial
    obtain ⟨p,hp,q,hq,h⟩ := IntermediateField.mem_adjoin_iff_div.mp hf
    rw [Algebra.adjoin_eq] at hp hq
    exact ⟨⟨p,hp⟩,⟨q,hq⟩,h⟩

lemma section_pow_10 : sectionCoefficient (1,0) ^ 7 =
    sectionCoefficient (3,0) ^ 7 + sectionCoefficient (0,0) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_add]
  congr 1
  simp [pairs, lineValue_eq]
  ring
lemma section_pow_40 : sectionCoefficient (4,0) ^ 7 =
    sectionCoefficient (2,0) ^ 7 - sectionCoefficient (0,0) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_sub]
  congr 1
  simp [pairs, lineValue_eq]
  ring
lemma section_pow_21 : sectionCoefficient (2,1) ^ 7 =
    sectionCoefficient (4,1) ^ 7 + sectionCoefficient (0,1) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_add]
  congr 1
  simp [pairs, lineValue_eq]
  ring
lemma section_pow_31 : sectionCoefficient (3,1) ^ 7 =
    sectionCoefficient (1,1) ^ 7 - sectionCoefficient (0,1) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_sub]
  congr 1
  simp [pairs, lineValue_eq]
  ring
lemma section_pow_52 : sectionCoefficient (5,2) ^ 7 =
    sectionCoefficient (1,2) ^ 7 - sectionCoefficient (2,2) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_sub]
  congr 1
  simp [pairs, lineValue_eq]
  ring
lemma section_pow_02 : sectionCoefficient (0,2) ^ 7 =
    sectionCoefficient (1,2) ^ 7 - sectionCoefficient (3,2) ^ 7 := by
  simp only [sectionCoefficient, mul_pow, z_pow, ← map_mul, ← map_sub]
  congr 1
  simp [pairs, lineValue_eq]
  ring

end SourceSymmetry

end

end OAI
