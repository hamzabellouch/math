import OAI.Analysis.NuclearUltrapower.IntegralCertificate
import OAI.Analysis.NuclearUltrapower.DyadicGroup
import OAI.Analysis.NuclearUltrapower.HilbertSchmidt
import OAI.Analysis.NuclearUltrapower.FiniteRepresentations

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOS.ElementarySpectral
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vectorStabilizer (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) : Subgroup E where
  carrier := {g | ρ g x = x}
  one_mem' := by simp
  mul_mem' ha hb := by
    change ρ _ x = x at ha hb ⊢
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hb] using ha
  inv_mem' {g} hg := by
    change ρ g⁻¹ x = x
    apply (ρ g).injective
    change (ρ g * ρ g⁻¹) x = ρ g x
    rw [← map_mul, mul_inv_cancel, map_one]
    exact hg.symm

theorem deltaOp_ker_fixed (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) (hx : x ∈ (deltaOp ρ).ker) :
    ∀ g : E, ρ g x = x := by
  have he := delta_energy ρ x
  change (inner ℂ x (deltaOp ρ x)).re = SOSEnergy.energy eGenSet ρ x / 2 at he
  have hx0 : deltaOp ρ x = 0 := hx
  rw [hx0, inner_zero_right, Complex.zero_re] at he
  have hs : SOSEnergy.energy eGenSet ρ x = 0 := by linarith
  have hf : (eGenSet : Set E) ⊆ vectorStabilizer ρ x := by
    intro g hg
    have hle : ‖ρ g x-x‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x :=
      Finset.single_le_sum (fun s _ => sq_nonneg ‖ρ s x-x‖) hg
    rw [hs] at hle
    have hz : ‖ρ g x-x‖ = 0 := by nlinarith [norm_nonneg (ρ g x-x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hz)
  have hfull := (Subgroup.closure_le (vectorStabilizer ρ x)).mpr hf
  rw [eSet_generates] at hfull
  exact fun g => hfull (Subgroup.mem_top g)

/-- The constructive quantitative projection consequence actually used in the
semidirect-product proof. It does not assume a Kazhdan pair. -/
theorem exists_fixed_nearby (ρ : E →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    ∃ y : H, (∀ g : E, ρ g y = y) ∧
      (1/10 : ℝ) * ‖x-y‖ ^ 2 ≤ SOSEnergy.energy eGenSet ρ x := by
  let K := (deltaOp ρ).ker
  let y := K.starProjection x
  have hy : y ∈ K := K.starProjection_apply_mem x
  have hfix := deltaOp_ker_fixed ρ y hy
  refine ⟨y,hfix,?_⟩
  have hp := deltaOp_gap ρ (x-y) (K.sub_starProjection_mem_orthogonal x)
  have he : SOSEnergy.energy eGenSet ρ (x-y) = SOSEnergy.energy eGenSet ρ x := by
    unfold SOSEnergy.energy
    apply Finset.sum_congr rfl
    intro s _
    rw [map_sub, hfix s]
    congr 2
    abel
  exact he ▸ hp

end NuclearUltrapower.SOS.ElementarySpectral
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

def integralAction : SOS.E →* MulAut (Multiplicative IntegralVector3) where
  toFun M := AddEquiv.toMultiplicative (Matrix.SpecialLinearGroup.toLin' M).toAddEquiv
  map_one' := by ext v i; simp
  map_mul' M N := by ext v i; simp [map_mul]

abbrev IntegralGroup := SemidirectProduct (Multiplicative IntegralVector3) SOS.E integralAction

def integralTranslation (v : IntegralVector3) : IntegralGroup :=
  SemidirectProduct.inl (Multiplicative.ofAdd v)

def integralTheta : Monoid.End IntegralGroup where
  toFun g := ⟨Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd), g.right⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd ((2 : ℤ) • (g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right h.left.toAdd)) =
        Multiplicative.ofAdd ((2 : ℤ) • g.left.toAdd +
        Matrix.SpecialLinearGroup.toLin' g.right ((2 : ℤ) • h.left.toAdd))
      simp only [smul_add, map_smul]
    · rfl

@[simp] theorem integralTheta_left (g : IntegralGroup) :
    (integralTheta g).left.toAdd = (2 : ℤ) • g.left.toAdd := rfl

@[simp] theorem integralTheta_right (g : IntegralGroup) :
    (integralTheta g).right = g.right := rfl

theorem integralTheta_injective : Function.Injective integralTheta := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : IntegralGroup => x.left.toAdd i) he
    change 2 * g.left.toAdd i = 2 * h.left.toAdd i at hi
    omega
  · simpa only [integralTheta_right] using congrArg (fun x : IntegralGroup => x.right) he

@[simp] theorem integralTheta_translation (v : IntegralVector3) :
    integralTheta (integralTranslation v) = integralTranslation ((2 : ℤ) • v) := rfl

@[simp] theorem integralTheta_pow_translation (n : ℕ) (v : IntegralVector3) :
    (integralTheta ^ n) (integralTranslation v) = integralTranslation ((2 : ℤ) ^ n • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Monoid.End.coe_mul, Function.comp_apply, ih, integralTheta_translation]
      congr 1
      simp only [pow_succ', mul_smul]

/-- The inclusion is literally integer coordinate inclusion into Z[1/2]. -/
def integralInclusion : IntegralGroup →* G where
  toFun g := ⟨Multiplicative.ofAdd (fun i => (g.left.toAdd i : Dyadic)), (g.right, 1)⟩
  map_one' := by ext <;> simp
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change ((g.left.toAdd i + (Matrix.SpecialLinearGroup.toLin' g.right) h.left.toAdd i : ℤ) : Dyadic) =
        (g.left.toAdd i : Dyadic) + (dilationAction (g.right, 1)) (fun j => (h.left.toAdd j : Dyadic)) i
      simp [dilationAction, matrixAction, Matrix.SpecialLinearGroup.toLin'_apply,
        Matrix.mulVec, dotProduct, LinearEquiv.smulOfUnit]
    · rfl

/-- The stable letter t=(0,I,1). -/
def stableLetter : G :=
  SemidirectProduct.inr (1, Multiplicative.ofAdd (1 : ℤ))

/-- The source group law implements exactly multiplication of translations by two. -/
theorem stableLetter_conjugation (g : IntegralGroup) :
    stableLetter * integralInclusion g * stableLetter⁻¹ = integralInclusion (integralTheta g) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    change 0 + ((dilationAction (1, Multiplicative.ofAdd (1 : ℤ)))
      (fun j => (g.left.toAdd j : Dyadic))) i =
      ((2 * g.left.toAdd i : ℤ) : Dyadic) +
      (dilationAction (g.right, 1) (0 : Vector3)) i
    simp [dilationAction, matrixAction, LinearEquiv.smulOfUnit, Units.smul_def]
  · change (1, Multiplicative.ofAdd (1 : ℤ)) * ((g.right : SL3Z), 1) =
      ((g.right : SL3Z), 1) * (1, Multiplicative.ofAdd (1 : ℤ))
    simp

/-- The integral copy is genuinely a subgroup, not merely a homomorphic image. -/
theorem integralInclusion_injective : Function.Injective integralInclusion := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : G => x.left.toAdd i) he
    change (g.left.toAdd i : Dyadic) = (h.left.toAdd i : Dyadic) at hi
    apply IsLocalization.injective (S := Dyadic)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (by norm_num : (2 : ℤ) ≠ 0)))
    simpa only [eq_intCast] using hi
  · exact Subtype.ext (congrArg (fun x : G => x.right.1) he)

abbrev Residue3 := Fin 3 → ZMod 2

def residue (g : IntegralGroup) : Residue3 := fun i => (g.left.toAdd i : ZMod 2)

def residueMatrix (M : SOS.E) : Residue3 ≃ₗ[ZMod 2] Residue3 :=
  Matrix.SpecialLinearGroup.toLin' (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod 2)) M)

theorem residue_mul (g h : IntegralGroup) :
    residue (g * h) = residue g + residueMatrix g.right (residue h) := by
  funext i
  simp [residue, integralAction, residueMatrix, Matrix.SpecialLinearGroup.toLin'_apply,
    Matrix.mulVec, dotProduct]

@[simp] theorem residue_one : residue 1 = 0 := by ext; simp [residue]

@[simp] theorem residue_theta (g : IntegralGroup) : residue (integralTheta g) = 0 := by
  ext i
  change ((2 * g.left.toAdd i : ℤ) : ZMod 2) = 0
  have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  simp [htwo]

theorem mem_theta_range_iff (g : IntegralGroup) :
    g ∈ integralTheta.range ↔ residue g = 0 := by
  constructor
  · rintro ⟨h, rfl⟩
    exact residue_theta h
  · intro hg
    have hd (i : Fin 3) : (2 : ℤ) ∣ g.left.toAdd i := by
      have hi := congrFun hg i
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
    refine ⟨⟨Multiplicative.ofAdd (fun i => g.left.toAdd i / 2), g.right⟩, ?_⟩
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      change 2 * (g.left.toAdd i / 2) = g.left.toAdd i
      exact Int.mul_ediv_cancel' (hd i)
    · rfl

theorem leftRel_theta_iff (g h : IntegralGroup) :
    QuotientGroup.leftRel integralTheta.range g h ↔ residue g = residue h := by
  rw [QuotientGroup.leftRel_apply, mem_theta_range_iff]
  have he : residue (g⁻¹) + residueMatrix (g⁻¹).right (residue g) = 0 := by
    rw [← residue_mul, inv_mul_cancel, residue_one]
  rw [residue_mul]
  constructor
  · intro hz
    have hi := add_left_cancel (hz.trans he.symm)
    exact (residueMatrix (g⁻¹).right).injective hi |>.symm
  · intro hgh
    rwa [← hgh]

/-- The eight left cosets are precisely the three translation residues. -/
def thetaCosetEquiv : (IntegralGroup ⧸ integralTheta.range) ≃ Residue3 where
  toFun := Quotient.lift residue (fun g h hgh => (leftRel_theta_iff g h).mp hgh)
  invFun a := Quotient.mk'' (integralTranslation (fun i => (a i).val))
  left_inv q := by
    induction q using Quotient.inductionOn with | h g =>
      apply Quotient.sound
      apply (leftRel_theta_iff _ _).mpr
      ext i
      simp [residue, integralTranslation]
  right_inv a := by
    ext i
    simp [residue, integralTranslation]

theorem integralTheta_index : integralTheta.range.index = 8 := by
  rw [Subgroup.index_eq_card, Nat.card_congr thetaCosetEquiv]
  simp [Residue3, Nat.card_eq_fintype_card]

instance : integralTheta.range.FiniteIndex := ⟨by rw [integralTheta_index]; norm_num⟩

/-- Reduction modulo two, acting by affine permutations on its eight points. -/
def residuePermutation : IntegralGroup →* Equiv.Perm Residue3 where
  toFun g := (residueMatrix g.right).toEquiv.trans (Equiv.addLeft (residue g))
  map_one' := by
    ext x i
    simp [residueMatrix]
  map_mul' g h := by
    ext x i
    change (residue (g * h) + residueMatrix (g * h).right x) i =
      (residue g + residueMatrix g.right (residue h + residueMatrix h.right x)) i
    rw [residue_mul, map_add]
    simp [residueMatrix, map_mul, add_assoc]

@[simp] theorem residuePermutation_apply (g : IntegralGroup) (x : Residue3) :
    residuePermutation g x = residue g + residueMatrix g.right x := rfl

abbrev ResidueHilbert := EuclideanSpace ℂ Residue3

def residueUnitary : IntegralGroup →* (ResidueHilbert ≃ₗᵢ[ℂ] ResidueHilbert) where
  toFun g := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (residuePermutation g)
  map_one' := by
    ext f x
    change f ((residuePermutation 1).symm x) = f x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext f x
    change f ((residuePermutation (g * h)).symm x) =
      f ((residuePermutation h).symm ((residuePermutation g).symm x))
    rw [map_mul]
    rfl

@[simp] theorem residueUnitary_apply (g : IntegralGroup) (f : ResidueHilbert) (x : Residue3) :
    residueUnitary g f x = f ((residuePermutation g).symm x) := rfl

def augmentation : Submodule ℂ ResidueHilbert := LinearMap.ker ({
  toFun f := ∑ x, f x
  map_add' f h := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum] } : ResidueHilbert →ₗ[ℂ] ℂ)

@[simp] theorem mem_augmentation (f : ResidueHilbert) :
    f ∈ augmentation ↔ ∑ x, f x = 0 := Iff.rfl

theorem augmentation_invariant (g : IntegralGroup) (f : ResidueHilbert)
    (hf : f ∈ augmentation) : residueUnitary g f ∈ augmentation := by
  rw [mem_augmentation] at *
  simpa only [residueUnitary_apply, Equiv.sum_comp] using hf

def augmentationVector : ResidueHilbert :=
  PiLp.single 2 (0 : Residue3) 1 - PiLp.single 2 (1 : Residue3) 1

theorem augmentationVector_mem : augmentationVector ∈ augmentation := by
  simp [augmentationVector, PiLp.sub_apply, PiLp.single_apply, Finset.sum_sub_distrib]

theorem augmentationVector_ne_zero : augmentationVector ≠ 0 := by
  intro h
  have he := congrArg (fun f : ResidueHilbert => f 0) h
  have hz : (0 : Residue3) ≠ 1 := by
    intro hz
    have h0 := congrFun hz 0
    exact zero_ne_one h0
  simp [augmentationVector, hz] at he

instance augmentation_nontrivial : Nontrivial augmentation := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro h
  have hmem := augmentationVector_mem
  rw [h] at hmem
  exact augmentationVector_ne_zero hmem

def augmentationRep : FiniteUnitaryRep IntegralGroup :=
  (FiniteUnitaryRep.mk ResidueHilbert residueUnitary).restrict augmentation augmentation_invariant

/-- A translation-fixed vector in the augmentation representation is zero. -/
theorem augmentation_no_translation_invariants (f : augmentationRep)
    (hf : ∀ v : IntegralVector3, augmentationRep.action (integralTranslation v) f = f) :
    f = 0 := by
  have ht (v : IntegralVector3) (x : Residue3) :
      f.val (residuePermutation (integralTranslation v) x) = f.val x := by
    have he := congrArg (fun z : augmentationRep => z.val (residuePermutation (integralTranslation v) x)) (hf v)
    change f.val ((residuePermutation (integralTranslation v)).symm
      (residuePermutation (integralTranslation v) x)) = _ at he
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hc (x : Residue3) : f.val x = f.val 0 := by
    have he : residuePermutation (integralTranslation (fun i => (x i).val)) 0 = x := by
      ext i
      simp [residue, integralTranslation, residueMatrix]
    simpa only [he] using ht (fun i => (x i).val) 0
  have hz : f.val 0 = 0 := by
    have hs := f.property
    rw [mem_augmentation] at hs
    simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hn : (Fintype.card Residue3 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_eq_zero.mp hs).resolve_left hn
  apply Subtype.ext
  ext x
  exact (hc x).trans hz

/-- All positive dilation pullbacks kill the translation subgroup. -/
theorem augmentation_pull_translation (j : ℕ) (hj : 0 < j) (v : IntegralVector3) :
    augmentationRep.action ((integralTheta ^ j) (integralTranslation v)) = 1 := by
  have hr : residuePermutation ((integralTheta ^ j) (integralTranslation v)) = 1 := by
    rw [integralTheta_pow_translation]
    ext x i
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    simp [residue, integralTranslation, residueMatrix, htwo, Nat.ne_of_gt hj]
  ext f
  apply Subtype.ext
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residuePermutation ((integralTheta ^ j) (integralTranslation v))) f.val = f.val
  rw [hr]
  rfl

/-- The required irreducible mod-two representation is a constituent of the
augmentation representation, hence has no translation-fixed vectors. -/
theorem exists_aperiodic_integral_rep :
    ∃ π : FiniteUnitaryRep.{0,0} IntegralGroup, π.Irreducible ∧
      (∀ j : ℕ, 0 < j → ¬ π.Equivalent (π.pull (integralTheta ^ j))) := by
  obtain ⟨π, hπ, T, hT⟩ := FiniteUnitaryRep.exists_irreducible augmentationRep
  refine ⟨π, hπ, fun j hj he => ?_⟩
  obtain ⟨U, hU⟩ := he
  have hkill (v : IntegralVector3) (x : π) :
      π.action ((integralTheta ^ j) (integralTranslation v)) x = x := by
    apply T.injective
    rw [hT, augmentation_pull_translation j hj]
    rfl
  have hfix (x : π) (v : IntegralVector3) : π.action (integralTranslation v) x = x := by
    apply U.injective
    rw [hU]
    change π.action ((integralTheta ^ j) (integralTranslation v)) (U x) = U x
    exact hkill v (U x)
  have hall (x : π) : x = 0 := by
    apply T.injective
    rw [map_zero]
    apply augmentation_no_translation_invariants
    intro v
    rw [← hT, hfix]
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  exact hx (hall x)

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Elementary
open SOS

theorem transvection_one_mem : ∀ (i j : Fin 3) (h : i ≠ j),
    Matrix.SpecialLinearGroup.transvection h (1 : ℤ) ∈ SOS.genSet := by
  decide +kernel

def transvectionHom {i j : Fin 3} (h : i ≠ j) : Multiplicative ℤ →* SL3Z where
  toFun z := Matrix.SpecialLinearGroup.transvection h z.toAdd
  map_one' := by simp
  map_mul' a b := Matrix.SpecialLinearGroup.transvection_add h a.toAdd b.toAdd

theorem transvection_mem {i j : Fin 3} (h : i ≠ j) (k : ℤ) :
    Matrix.SpecialLinearGroup.transvection h k ∈ SOS.elementary := by
  have he : Matrix.SpecialLinearGroup.transvection h k =
      (Matrix.SpecialLinearGroup.transvection h (1:ℤ)) ^ k := by
    have hz := (transvectionHom h).map_zpow (Multiplicative.ofAdd (1:ℤ)) k
    simpa only [transvectionHom, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul,
      mul_one, Int.cast_id] using hz
  rw [he]
  exact SOS.elementary.zpow_mem (Subgroup.subset_closure (transvection_one_mem i j h)) k

def elementaryTransvection {i j : Fin 3} (h : i ≠ j) (k : ℤ) : SOS.E :=
  ⟨Matrix.SpecialLinearGroup.transvection h k, transvection_mem h k⟩

def basisVector (i : Fin 3) : IntegralVector3 := Pi.single i 1

theorem transvection_basis {i j : Fin 3} (h : i ≠ j) (k : ℤ) :
    Matrix.SpecialLinearGroup.toLin' (elementaryTransvection h k) (basisVector j) =
      basisVector j + k • basisVector i := by
  exact Matrix.SpecialLinearGroup.transvection_smul_single_snd h k

def linearInclusion : SOS.E →* IntegralGroup := SemidirectProduct.inr

theorem conjugate_translation (M : SOS.E) (v : IntegralVector3) :
    linearInclusion M * integralTranslation v * (linearInclusion M)⁻¹ =
      integralTranslation (Matrix.SpecialLinearGroup.toLin' (M : SL3Z) v) := by
  change SemidirectProduct.inr M * SemidirectProduct.inl (Multiplicative.ofAdd v) *
    (SemidirectProduct.inr M)⁻¹ = SemidirectProduct.inl
      ((integralAction M) (Multiplicative.ofAdd v))
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut M (Multiplicative.ofAdd v)).symm

theorem translation_add (v w : IntegralVector3) :
    integralTranslation (v+w) = integralTranslation v * integralTranslation w := by
  exact map_mul SemidirectProduct.inl (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem translation_neg (v : IntegralVector3) :
    integralTranslation (-v) = (integralTranslation v)⁻¹ := by
  exact map_inv SemidirectProduct.inl (Multiplicative.ofAdd v)

theorem translation_sub (v w : IntegralVector3) :
    integralTranslation (v-w) = integralTranslation v * (integralTranslation w)⁻¹ := by
  rw [sub_eq_add_neg, translation_add, translation_neg]

theorem vector_decomp (v : IntegralVector3) : v = ∑ i : Fin 3, v i • basisVector i := by
  ext j
  simp [basisVector, Pi.single_apply, Finset.sum_apply]

theorem translation_zsmul (v : IntegralVector3) (k : ℤ) :
    integralTranslation (k • v) = integralTranslation v ^ k := by
  exact map_zpow SemidirectProduct.inl (Multiplicative.ofAdd v) k

theorem translation_three (v : IntegralVector3) :
    integralTranslation v = integralTranslation (v 0 • basisVector 0) *
      integralTranslation (v 1 • basisVector 1) * integralTranslation (v 2 • basisVector 2) := by
  have hv : v = v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2 := by
    ext j
    fin_cases j <;> simp [basisVector]
  calc
    _ = integralTranslation (v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2) := congrArg _ hv
    _ = _ := by rw [translation_add, translation_add]

theorem normal_form (g : IntegralGroup) :
    g = integralTranslation g.left.toAdd * linearInclusion g.right := by
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Displacement
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))

def dist (g : Γ) (x : H) : ℝ := ‖ρ g x - x‖

theorem mul_le (g h : Γ) (x : H) :
    dist ρ (g*h) x ≤ dist ρ g x + dist ρ h x := by
  have he : ρ (g*h) x - x = (ρ g x-x) + ρ g (ρ h x-x) := by
    rw [map_mul]
    change ρ g (ρ h x)-x = _
    rw [map_sub]
    abel
  unfold dist
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [(ρ g).norm_map])

@[simp] theorem inv (g : Γ) (x : H) : dist ρ g⁻¹ x = dist ρ g x := by
  unfold dist
  rw [← (ρ g).norm_map (ρ g⁻¹ x-x), map_sub]
  have he : ρ g (ρ g⁻¹ x) = x := by
    change (ρ g * ρ g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [he, norm_sub_rev]

theorem prod_le (w : List Γ) (x : H) :
    dist ρ w.prod x ≤ (w.map (fun g => dist ρ g x)).sum := by
  induction w with
  | nil => simp [dist]
  | cons g w ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons] using
      (mul_le ρ g w.prod x).trans (add_le_add le_rfl ih)

theorem conjugate (g h : Γ) (x : H) (hg : ρ g x = x) :
    dist ρ (g*h*g⁻¹) x = dist ρ h x := by
  have hi : ρ g⁻¹ x = x := by
    apply (ρ g).injective
    change (ρ g * ρ g⁻¹) x = ρ g x
    rw [← map_mul, mul_inv_cancel, map_one]
    exact hg.symm
  unfold dist
  simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hi]
  calc
    _ = ‖ρ g (ρ h x-x)‖ := by rw [map_sub, hg]
    _ = _ := (ρ g).norm_map _

theorem change_vector (g : Γ) (x y : H) :
    dist ρ g y ≤ 2 * ‖x-y‖ + dist ρ g x := by
  have he : ρ g y-y = -ρ g (x-y) + (ρ g x-x) + (x-y) := by
    rw [map_sub]
    abel
  unfold dist
  rw [he]
  calc
    _ ≤ ‖-ρ g (x-y)‖ + ‖ρ g x-x‖ + ‖x-y‖ := norm_add₃_le
    _ = _ := by rw [norm_neg, (ρ g).norm_map]; ring

end NuclearUltrapower.Displacement
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closest point to zero in a closed convex unitary orbit hull is fixed.
This supplies the bounded-orbit implication without using property T as an axiom. -/
theorem unitary_orbit_norm_le (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (hno : ∀ y : H, (∀ g, ρ g y = y) → y = 0)
    (x : H) (r : ℝ) (hbound : ∀ g, ‖ρ g x - x‖ ≤ r) : ‖x‖ ≤ r := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let K : Set H := closure (convexHull ℝ (Set.range (fun g => ρ g x)))
  have hclosed : IsClosed K := isClosed_closure
  have hconvex : Convex ℝ K := (convex_convexHull ℝ _).closure
  have horbit (g : Γ) : ρ g x ∈ K := subset_closure (subset_convexHull ℝ _ (Set.mem_range_self g))
  have hnonempty : K.Nonempty := ⟨ρ 1 x, horbit 1⟩
  have hinvariant (g : Γ) : ∀ y ∈ K, ρ g y ∈ K := by
    have hpre : Convex ℝ ((ρ g) ⁻¹' K) :=
      hconvex.linear_preimage ((ρ g).toLinearMap.restrictScalars ℝ)
    apply closure_minimal (convexHull_min ?_ hpre) (hclosed.preimage (ρ g).continuous)
    rintro _ ⟨h, rfl⟩
    change ρ g (ρ h x) ∈ K
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply] using horbit (g*h)
  obtain ⟨z, hz, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hnonempty
    hclosed.isComplete hconvex (0 : H)
  have hfix (g : Γ) : ρ g z = z := by
    have hi := (norm_eq_iInf_iff_real_inner_le_zero hconvex hz).mp hmin
      (ρ g z) (hinvariant g z hz)
    have hn := norm_sub_sq (𝕜 := ℝ) (ρ g z) z
    rw [(ρ g).norm_map, real_inner_comm] at hn
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    simp only [RCLike.re_to_real] at hn
    have hm : ‖ρ g z - z‖ = 0 := by nlinarith [norm_nonneg (ρ g z-z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hm)
  have hz0 := hno z hfix
  have hb : K ⊆ Metric.closedBall x r := by
    apply closure_minimal (convexHull_min ?_ (convex_closedBall x r)) Metric.isClosed_closedBall
    rintro _ ⟨g, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hbound g
  have := hb hz
  simpa [hz0, Metric.mem_closedBall, dist_eq_norm] using this
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary
open SOS SOSEnergy
open Displacement (dist)

/-- An explicit finite set in the honest integral elementary subgroup. -/
def kazhdanSet : Finset IntegralGroup :=
  eGenSet.image linearInclusion ∪ Finset.univ.image (fun i => integralTranslation (basisVector i))

theorem kazhdanSet_nonempty : kazhdanSet.Nonempty := by
  classical
  refine ⟨integralTranslation (basisVector 0), ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)

theorem kazhdanSet_generates : Subgroup.closure (kazhdanSet : Set IntegralGroup) = ⊤ := by
  classical
  let K := Subgroup.closure (kazhdanSet : Set IntegralGroup)
  have hlin : ∀ M : E, linearInclusion M ∈ K := by
    have he : (eGenSet : Set E) ⊆ K.comap linearInclusion := by
      intro M hM
      exact Subgroup.subset_closure (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨M,hM,rfl⟩))
    have hc := (Subgroup.closure_le (K.comap linearInclusion)).mpr he
    rw [eSet_generates] at hc
    exact fun M => hc (Subgroup.mem_top M)
  have hb (i : Fin 3) : integralTranslation (basisVector i) ∈ K :=
    Subgroup.subset_closure (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have ht : ∀ v, integralTranslation v ∈ K := by
    intro v
    rw [translation_three]
    exact K.mul_mem (K.mul_mem (by rw [translation_zsmul]; exact K.zpow_mem (hb 0) _)
      (by rw [translation_zsmul]; exact K.zpow_mem (hb 1) _))
      (by rw [translation_zsmul]; exact K.zpow_mem (hb 2) _)
  apply top_unique
  intro g _
  rw [normal_form g]
  exact K.mul_mem (ht _) (hlin _)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem translation_line_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (i : Fin 3) (k : ℤ) : dist ρ (integralTranslation (k • basisVector i)) y ≤ 2*C := by
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, i ≠ j := by
    by_cases hi : i = 0
    · exact ⟨1,by simp [hi]⟩
    · exact ⟨0,hi⟩
  let M := elementaryTransvection hj k
  have hv : k • basisVector i =
      Matrix.SpecialLinearGroup.toLin' (M : SL3Z) (basisVector j) - basisVector j := by
    rw [transvection_basis]
    abel
  rw [hv, translation_sub, ← conjugate_translation]
  have hm : ρ (linearInclusion M) y = y := hfix M
  exact (Displacement.mul_le ρ _ _ y).trans (by
    rw [Displacement.conjugate ρ _ _ _ hm, Displacement.inv]
    linarith [hs j])

omit [CompleteSpace H] in
theorem translation_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (v : IntegralVector3) : dist ρ (integralTranslation v) y ≤ 6*C := by
  have h0 := translation_line_displacement ρ y C hfix hs 0 (v 0)
  have h1 := translation_line_displacement ρ y C hfix hs 1 (v 1)
  have h2 := translation_line_displacement ρ y C hfix hs 2 (v 2)
  let a := integralTranslation (v 0 • basisVector 0)
  let b := integralTranslation (v 1 • basisVector 1)
  let c := integralTranslation (v 2 • basisVector 2)
  have ht := Displacement.mul_le ρ (a*b) c y
  have ht' := Displacement.mul_le ρ a b y
  rw [translation_three]
  change dist ρ ((a*b)*c) y ≤ _
  linarith

omit [CompleteSpace H] in
theorem integral_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (g : IntegralGroup) : dist ρ g y ≤ 6*C := by
  conv_lhs => rw [normal_form g]
  have hm : dist ρ (linearInclusion g.right) y = 0 := by
    simp only [Displacement.dist, hfix g.right, sub_self, norm_zero]
  exact (Displacement.mul_le ρ _ _ y).trans (by
    rw [hm,add_zero]
    exact translation_displacement ρ y C hfix hs g.left.toAdd)

/-- This is the needed absolute gap, proved from the certified elementary gap
and the elementary conjugacy identities on integral translations. -/
theorem kazhdan_energy (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (hno : ∀ y : H, (∀ g, ρ g y = y) → y = 0) (x : H) :
    (1/4000 : ℝ) * ‖x‖ ^ 2 ≤ energy kazhdanSet ρ x := by
  classical
  let T := energy kazhdanSet ρ x
  let r := Real.sqrt T
  have hT : 0 ≤ T := energy_nonneg _ _ _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = T := Real.sq_sqrt hT
  have he : energy eGenSet (ρ.comp linearInclusion) x ≤ T := by
    change (∑ s ∈ eGenSet, ‖ρ (linearInclusion s) x-x‖^2) ≤
      ∑ s ∈ kazhdanSet, ‖ρ s x-x‖^2
    have hh : (∑ s ∈ eGenSet.image linearInclusion, ‖ρ s x-x‖^2) =
        ∑ s ∈ eGenSet, ‖ρ (linearInclusion s) x-x‖^2 := by
      apply Finset.sum_image
      intro a _ b _ hab
      exact congrArg SemidirectProduct.right hab
    rw [← hh]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      (fun _ _ _ => sq_nonneg _)
  obtain ⟨y,hfix,hy⟩ := SOS.ElementarySpectral.exists_fixed_nearby (ρ.comp linearInclusion) x
  have hxy : ‖x-y‖ ≤ 4*r := by
    nlinarith [hy.trans he, norm_nonneg (x-y)]
  have hs (i : Fin 3) : dist ρ (integralTranslation (basisVector i)) x ≤ r := by
    apply (Real.le_sqrt (norm_nonneg _) hT).mpr
    change ‖ρ (integralTranslation (basisVector i)) x-x‖^2 ≤
      ∑ s ∈ kazhdanSet, ‖ρ s x-x‖^2
    exact Finset.single_le_sum (f := fun s : IntegralGroup => ‖ρ s x-x‖^2) (fun _ _ => sq_nonneg _)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have hsy (i : Fin 3) : dist ρ (integralTranslation (basisVector i)) y ≤ 9*r := by
    have h := Displacement.change_vector ρ (integralTranslation (basisVector i)) x y
    linarith [hs i]
  have hall : ∀ g : IntegralGroup, dist ρ g y ≤ 54*r := by
    intro g
    convert integral_displacement ρ y (9*r) hfix hsy g using 1
    ring
  have hyn : ‖y‖ ≤ 54*r := unitary_orbit_norm_le ρ hno y (54*r) hall
  have hxn : ‖x‖ ≤ 58*r := by
    have h := norm_add_le (x-y) y
    rw [sub_add_cancel] at h
    linarith
  change (1/4000 : ℝ) * ‖x‖^2 ≤ T
  nlinarith [sq_nonneg (58*r-‖x‖), norm_nonneg x]

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Elementary
universe v

theorem hasKazhdanGap : HasKazhdanGap.{0,v} kazhdanSet (1/4000) := by
  intro H _ _ _ ρ hρ x
  exact kazhdan_energy ρ hρ x

end NuclearUltrapower.Elementary
end
end

end OAI
