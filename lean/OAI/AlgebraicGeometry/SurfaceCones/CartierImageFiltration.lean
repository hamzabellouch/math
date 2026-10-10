import OAI.AlgebraicGeometry.SurfaceCones.SwappedBaseChange

namespace OAI

/-!
# Powers and image filtrations of Cartier ideal actions

This development accompanies *A Complete Local Domain without a Small
Cohen–Macaulay Module* (OpenAI, 2026).
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D]
  (T : C ⥤ C) (a : T ⟶ 𝟭 C)

/-- The ideal multiple, defined as the image of the ideal action. -/
def multiple (M : C) : C := Abelian.image (a.app M)

/-- Repeated images of the ideal action. -/
def iterated : ℕ → C → C
  | 0, M => M
  | n + 1, M => iterated n (multiple T a M)

/-- Canonical image/cokernel sequence of the ideal action. -/
def layerSequence (M : C) : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι (a.app M)) (cokernel.π (a.app M))
    (kernel.condition (cokernel.π (a.app M)))

lemma layerSequence_shortExact (M : C) : (layerSequence T a M).ShortExact := by
  change (ShortComplex.mk (kernel.ι (cokernel.π (a.app M))) (cokernel.π (a.app M)) _).ShortExact
  exact { exact := ShortComplex.exact_kernel (cokernel.π (a.app M)) }

variable (J : D ⥤ C) (Q : C → D) (e : ∀ M, J.obj (Q M) ≅ cokernel (a.app M))

/-- The same sequence, identified with its supported quotient. -/
def supportedSequence (M : C) : ShortComplex C :=
  ShortComplex.mk (Abelian.image.ι (a.app M)) (cokernel.π (a.app M) ≫ (e M).inv)
    (by rw [← Category.assoc, kernel.condition, zero_comp])

lemma supportedSequence_shortExact (M : C) :
    (supportedSequence T a J Q e M).ShortExact := by
  let eS : layerSequence T a M ≅ supportedSequence T a J Q e M :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (e M).symm
      (by simp [layerSequence, supportedSequence])
      (by simp [layerSequence, supportedSequence])
  exact ShortComplex.shortExact_of_iso eS (layerSequence_shortExact T a M)

/-- Successive quotients selected by images of the ideal action. -/
def layers : ℕ → C → List D
  | 0, _ => []
  | n + 1, M => Q M :: layers n (multiple T a M)

include e in
/-- A nilpotent iterated image gives a finite filtration by supported layers. -/
lemma filteredBy_iterated_zero (n : ℕ) (M : C) (h : IsZero (iterated T a n M)) :
    CoherentK0.FilteredBy M ((layers T a Q n M).map J.obj) := by
  induction n generalizing M with
  | zero => exact .zero M h
  | succ n ih =>
    exact .step (supportedSequence_shortExact T a J Q e M)
      (ih (multiple T a M) h)
end CartierImageFiltration

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]
  (T : C ⥤ C) (a : T ⟶ 𝟭 C)

/-- Iterated tensor functors. -/
def power : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => T ⋙ power n

instance power_preservesEpis [T.PreservesEpimorphisms] (n : ℕ) :
    (power T n).PreservesEpimorphisms := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 C).PreservesEpimorphisms)
  | succ n ih => exact inferInstanceAs ((T ⋙ power T n).PreservesEpimorphisms)

/-- The n-fold ideal action, as a natural transformation. -/
def powerAction : (n : ℕ) → power T n ⟶ 𝟭 C
  | 0 => 𝟙 _
  | n + 1 => Functor.whiskerLeft T (powerAction n) ≫ a

/-- The canonical inclusion of the iterated ideal image in the original object. -/
def iteratedInclusion : (n : ℕ) → (M : C) → iterated T a n M ⟶ M
  | 0, M => 𝟙 M
  | n + 1, M => iteratedInclusion n (multiple T a M) ≫ Abelian.image.ι (a.app M)

/-- Powers surject onto the corresponding iterated image. -/
def powerToImage : (n : ℕ) → (M : C) → (power T n).obj M ⟶ iterated T a n M
  | 0, M => 𝟙 M
  | n + 1, M => (power T n).map (Abelian.factorThruImage (a.app M)) ≫
      powerToImage n (multiple T a M)

instance powerToImage_epi [T.PreservesEpimorphisms] (n : ℕ) (M : C) :
    Epi (powerToImage T a n M) := by
  induction n generalizing M with
  | zero => exact inferInstanceAs (Epi (𝟙 M))
  | succ n ih =>
    change Epi ((power T n).map (Abelian.factorThruImage (a.app M)) ≫
      powerToImage T a n (multiple T a M))
    exact epi_comp' (inferInstanceAs (Epi ((power T n).map
      (Abelian.factorThruImage (a.app M))))) (ih (multiple T a M))

instance iteratedInclusion_mono (n : ℕ) (M : C) :
    Mono (iteratedInclusion T a n M) := by
  induction n generalizing M with
  | zero => exact inferInstanceAs (Mono (𝟙 M))
  | succ n ih =>
    change Mono (iteratedInclusion T a n (multiple T a M) ≫ Abelian.image.ι (a.app M))
    exact mono_comp' (ih (multiple T a M))
      (inferInstanceAs (Mono (kernel.ι (cokernel.π (a.app M)))))

lemma powerToImage_fac (n : ℕ) (M : C) :
    powerToImage T a n M ≫ iteratedInclusion T a n M = (powerAction T a n).app M := by
  induction n generalizing M with
  | zero =>
    change 𝟙 M ≫ 𝟙 M = 𝟙 M
    exact Category.id_comp (𝟙 M)
  | succ n ih =>
    let f : (power T n).obj (T.obj M) ⟶ (power T n).obj (multiple T a M) :=
      (power T n).map (Abelian.factorThruImage (a.app M))
    let g : (power T n).obj (multiple T a M) ⟶ iterated T a n (multiple T a M) :=
      powerToImage T a n (multiple T a M)
    let h : iterated T a n (multiple T a M) ⟶ multiple T a M :=
      iteratedInclusion T a n (multiple T a M)
    let i : multiple T a M ⟶ M := Abelian.image.ι (a.app M)
    change (f ≫ g) ≫ (h ≫ i) = (powerAction T a n).app (T.obj M) ≫ a.app M
    calc
      (f ≫ g) ≫ (h ≫ i) = f ≫ (g ≫ h) ≫ i := by simp only [Category.assoc]
      _ = f ≫ (powerAction T a n).app (multiple T a M) ≫ i := by rw [show g ≫ h = _ from ih _]
      _ = (powerAction T a n).app (T.obj M) ≫ a.app M := by
        let p : T.obj M ⟶ multiple T a M := Abelian.factorThruImage (a.app M)
        have hn : f ≫ (powerAction T a n).app (multiple T a M) =
            (powerAction T a n).app (T.obj M) ≫ p :=
          (powerAction T a n).naturality p
        calc
          f ≫ (powerAction T a n).app (multiple T a M) ≫ i =
              (f ≫ (powerAction T a n).app (multiple T a M)) ≫ i :=
            (Category.assoc _ _ _).symm
          _ = ((powerAction T a n).app (T.obj M) ≫ p) ≫ i :=
            congrArg (fun k => k ≫ i) hn
          _ = (powerAction T a n).app (T.obj M) ≫ (p ≫ i) := Category.assoc _ _ _
          _ = (powerAction T a n).app (T.obj M) ≫ a.app M :=
            congrArg (fun k => (powerAction T a n).app (T.obj M) ≫ k) (Abelian.image.fac (a.app M))

/-- Vanishing of the n-fold ideal action forces the iterated image to vanish. -/
lemma iterated_isZero_of_powerAction_zero [T.PreservesEpimorphisms]
    (n : ℕ) (M : C) (h : (powerAction T a n).app M = 0) :
    IsZero (iterated T a n M) := by
  have hi : iteratedInclusion T a n M = 0 := by
    apply (cancel_epi (powerToImage T a n M)).mp
    rw [powerToImage_fac, h, comp_zero]
  exact (IsZero.of_mono_eq_zero _ hi)

/-- If an ideal power on L factors through a subobject, its quotient is
annihilated by that power. This is the categorical lattice sandwich. -/
lemma powerAction_quotient_zero [T.PreservesEpimorphisms]
    {S : ShortComplex C} (hS : S.ShortExact) (n : ℕ)
    (b : (power T n).obj S.X₂ ⟶ S.X₁)
    (hb : b ≫ S.f = (powerAction T a n).app S.X₂) :
    (powerAction T a n).app S.X₃ = 0 := by
  have : Epi S.g := hS.epi_g
  apply (cancel_epi ((power T n).map S.g)).mp
  rw [comp_zero, (powerAction T a n).naturality, Functor.id_map, ← hb,
    Category.assoc, S.zero, comp_zero]
end CartierImageFiltration

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (T : C ⥤ C) (S : D ⥤ D) (F : C ⥤ D) (e : T ⋙ F ≅ F ⋙ S)

/-- Iterated tensor actions commute with restriction through the restriction comparison. -/
def powerComparison : (n : ℕ) → (M : C) →
    F.obj ((power T n).obj M) ≅ (power S n).obj (F.obj M)
  | 0, _ => Iso.refl _
  | n + 1, M => powerComparison n (T.obj M) ≪≫ (power S n).mapIso (e.app M)

variable (a : T ⟶ 𝟭 C) (b : S ⟶ 𝟭 D)
    (he : ∀ M, (e.app M).hom ≫ b.app (F.obj M) = F.map (a.app M))

include he

/-- The same restriction comparison intertwines every Cartier
power. This lifts the local principal-equation calculation to the iterated tensor functor used in the coherent filtration. -/
lemma powerComparison_action (n : ℕ) (M : C) :
    (powerComparison T S F e n M).hom ≫ (powerAction S b n).app (F.obj M) =
      F.map ((powerAction T a n).app M) := by
  induction n generalizing M with
  | zero => simp [powerComparison, powerAction, power]
  | succ n ih =>
    change ((powerComparison T S F e n (T.obj M)).hom ≫
      (power S n).map (e.app M).hom) ≫
      ((powerAction S b n).app (S.obj (F.obj M)) ≫ b.app (F.obj M)) =
      F.map ((powerAction T a n).app (T.obj M) ≫ a.app M)
    have hn := (powerAction S b n).naturality (e.app M).hom
    dsimp only [Functor.comp_obj, Functor.id_map, Functor.id_obj] at hn
    rw [Category.assoc, ← Category.assoc ((power S n).map _), hn,
      Category.assoc, he, ← Category.assoc, ih, ← F.map_comp]

variable [HasZeroMorphisms D]
/-- Vanishing of a local power implies vanishing of the restricted global action. -/
lemma map_powerAction_zero_of_comparison (n : ℕ) (M : C)
    (h : (powerAction S b n).app (F.obj M) = 0) :
    F.map ((powerAction T a n).app M) = 0 := by
  rw [← powerComparison_action T S F e a b he, h, comp_zero]
end CartierImageFiltration

end

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CartierImageFiltration
universe u v
variable {C : Type u} [Category.{v} C]

/-- The recursively iterated identity functor is canonically the identity. -/
def identityPowerIso : (n : ℕ) → (M : C) → (power (𝟭 C) n).obj M ≅ M
  | 0, M => Iso.refl M
  | n + 1, M => identityPowerIso n M

/-- For the identity tensor functor, an iterated action is the power
of its endomorphism component, with its canonical source identification. -/
lemma powerAction_id (b : 𝟭 C ⟶ 𝟭 C) (n : ℕ) (M : C) :
    (powerAction (𝟭 C) b n).app M =
      (identityPowerIso n M).hom ≫ (End.of (b.app M) ^ n).asHom := by
  induction n with
  | zero =>
    change 𝟙 M = 𝟙 M ≫ 𝟙 M
    simp
  | succ n ih =>
    change (powerAction (𝟭 C) b n).app M ≫ b.app M =
      (identityPowerIso n M).hom ≫ (End.of (b.app M) ^ (n + 1)).asHom
    rw [ih, pow_succ', End.mul_def, Category.assoc]

variable [HasZeroMorphisms C]
/-- A trivialization turns nilpotence of the normalized scalar
endomorphism into nilpotence of the tensor-power action. -/
lemma powerAction_zero_of_trivialization (T : C ⥤ C) (a : T ⟶ 𝟭 C)
    (e : T ≅ 𝟭 C) (n : ℕ) (M : C)
    (h : (End.of ((e.inv ≫ a).app M) ^ n).asHom = 0) :
    (powerAction T a n).app M = 0 := by
  let cmp : T ⋙ 𝟭 C ≅ 𝟭 C ⋙ 𝟭 C :=
    Functor.rightUnitor T ≪≫ e ≪≫ (Functor.leftUnitor (𝟭 C)).symm
  have hh (N : C) : (cmp.app N).hom ≫ (e.inv ≫ a).app ((𝟭 C).obj N) =
      (𝟭 C).map (a.app N) := by simp [cmp]
  exact map_powerAction_zero_of_comparison T (𝟭 C) (𝟭 C) cmp a (e.inv ≫ a) hh n M
    (by
      simp only [Functor.id_obj, powerAction_id]
      exact (congrArg ((identityPowerIso n M).hom ≫ ·) h).trans (comp_zero))
end CartierImageFiltration

end

noncomputable section
open scoped BigOperators
namespace CartierAffineLattice
variable {R M L : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup L] [Module R L]

/-- Finite generation makes the elementwise power killing condition uniform.
This is the local Noetherian support step in the divisor lattice filtration. -/
lemma exists_uniform_power [Module.Finite R M] (t : R)
    (h : ∀ m : M, ∃ k : ℕ, t ^ k • m = 0) :
    ∃ k : ℕ, ∀ m : M, t ^ k • m = 0 := by
  classical
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  choose k hk using fun i : Fin n => h (v i)
  let K : ℕ := ∑ i, k i
  have hgen (i : Fin n) : t ^ K • v i = 0 := by
    have hki : k i ≤ K := Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [show K = (K - k i) + k i by omega, pow_add, mul_smul, hk i, smul_zero]
  let a : M →ₗ[R] M := t ^ K • LinearMap.id
  have ha : LinearMap.ker a = ⊤ := by
    apply top_unique
    rw [← hv]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hgen i
  refine ⟨K, fun m => ?_⟩
  have hm : m ∈ LinearMap.ker a := by rw [ha]; trivial
  exact hm

/-- Vanishing of principal localization gives a uniform nilpotence exponent. -/
lemma exists_annihilator_power_of_localization_zero [Module.Finite R M]
    (t : R) (f : M →ₗ[R] L) [IsLocalizedModule.Away t f] [Subsingleton L] :
    ∃ k : ℕ, ∀ m : M, t ^ k • m = 0 := by
  apply exists_uniform_power t
  intro m
  obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq t
    (Subsingleton.elim (f m) (f 0))
  exact ⟨k, by simpa only [smul_zero] using hk⟩
end CartierAffineLattice

namespace CartierAffineLattice
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules
/-- The local support assertion: a coherent associated sheaf that
vanishes on the complement of the principal divisor is killed by one power
of its equation. This uses restriction, evaluation and localization. -/
lemma exists_annihilator_power_of_puncture_zero {R : CommRingCat.{0}}
    (M : ModuleCat R) [Module.Finite R M] (t : R)
    (h : IsZero ((tilde M).over (PrimeSpectrum.basicOpen t))) :
    ∃ k : ℕ, ∀ m : M, t ^ k • m = 0 := by
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen t
  let E := SheafOfModules.evaluation.{0} ((Spec R).ringCatSheaf.over U)
    (op (Over.mk (𝟙 U)))
  have : E.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  have hz := E.map_isZero h
  have hs := ModuleCat.subsingleton_of_isZero hz
  let : Subsingleton ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op U)) := hs
  exact exists_annihilator_power_of_localization_zero t (tilde.toOpen M U).hom
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry
open Scheme.Modules ActualSheafTensor CartierImageFiltration
namespace AffineCartierNilpotence
variable {R : CommRingCat.{0}} (L : (Spec R).Modules)
  (e : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
  (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf)

/-- Principal equation obtained from the trivialized ideal inclusion
by the fully faithful associated-sheaf functor. -/
def equation : R :=
  let q : tilde (ModuleCat.of R R) ⟶ tilde (ModuleCat.of R R) := e.inv ≫ i
  ((tilde.functor R).preimage q) 1

lemma normalized_scalar :
    AffineNaturalScalar.scalar R
      ((trivialTensorIso (Spec R).sheaf e).inv ≫ idealAction (Spec R).sheaf i) =
        equation L e i := by
  dsimp only [AffineNaturalScalar.scalar, equation]
  congr 2
  congr 1
  exact trivial_action_unit (Spec R).sheaf e i

/-- Support on the Cartier divisor implies tensor-ideal nilpotence
on an affine trivializing chart. The equation comes from the ideal inclusion. -/
lemma powerAction_zero_of_puncture_zero (M : ModuleCat R) [Module.Finite R M]
    (h : IsZero ((tilde M).over (PrimeSpectrum.basicOpen (equation L e i)))) :
    ∃ n : ℕ, (powerAction (tensorLeft (Spec R).sheaf L)
      (idealAction (Spec R).sheaf i) n).app (tilde M) = 0 := by
  obtain ⟨n, hn⟩ := CartierAffineLattice.exists_annihilator_power_of_puncture_zero
    M (equation L e i) h
  refine ⟨n, powerAction_zero_of_trivialization _ _
    (trivialTensorIso (Spec R).sheaf e) n (tilde M) ?_⟩
  apply AffineNaturalScalar.power_zero R _ M n
  erw [normalized_scalar L e i]
  exact hn

/-- Coherent affine sheaves satisfy uniform ideal nilpotence.
The finite module of global sections is transferred through the affine counit. -/
lemma coherent_powerAction_zero_of_puncture_zero (M : (Spec R).Modules)
    [M.IsFinitePresentation]
    (h : IsZero (M.over (PrimeSpectrum.basicOpen (equation L e i)))) :
    ∃ n : ℕ, (powerAction (tensorLeft (Spec R).sheaf L)
      (idealAction (Spec R).sheaf i) n).app M = 0 := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  let N := moduleSpecΓFunctor.obj M
  have : Module.Finite R N := CoherentGlobal.finiteGamma_of_coherent M
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  let b : tilde N ≅ M := @asIso _ _ _ _ (fromTildeΓ M) (isIso_fromTildeΓ_of_isQuasicoherent M)
  let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf
    (PrimeSpectrum.basicOpen (equation L e i))
  have hN : IsZero ((tilde N).over (PrimeSpectrum.basicOpen (equation L e i))) :=
    h.of_iso (F.mapIso b)
  obtain ⟨n, hn⟩ := powerAction_zero_of_puncture_zero L e i N hN
  refine ⟨n, ?_⟩
  let a := powerAction (tensorLeft (Spec R).sheaf L) (idealAction (Spec R).sheaf i) n
  have he := a.naturality b.hom
  have : Epi ((power (tensorLeft (Spec R).sheaf L) n).map b.hom) :=
    @IsIso.epi_of_iso _ _ _ _ _
      (((power (tensorLeft (Spec R).sheaf L) n).mapIso b).isIso_hom)
  apply (cancel_epi ((power (tensorLeft (Spec R).sheaf L) n).map b.hom)).mp
  simpa only [a, hn, zero_comp, comp_zero] using he

end AffineCartierNilpotence


end

noncomputable section
open TensorProduct
namespace CartierTorsion
variable {R L M : Type*} [CommRing R] [AddCommGroup L] [Module R L]
  [AddCommGroup M] [Module R M]
  (e : L ≃ₗ[R] R) (i : L →ₗ[R] R)

lemma line_map_formula (l : L) : i l = e l * i (e.symm 1) := by
  have h := i.map_smul (e l) (e.symm 1)
  simpa only [← e.symm.map_smul, smul_eq_mul, mul_one, e.symm_apply_apply] using h

lemma line_map_regular (hi : Function.Injective i) : IsRegular (i (e.symm 1)) := by
  apply (Commute.isRegular_iff (fun b => Commute.all _ b)).mpr
  intro a b hab
  apply e.symm.injective
  apply hi
  rw [line_map_formula e i (e.symm a), line_map_formula e i (e.symm b)]
  simpa only [e.apply_symm_apply, mul_comm] using hab

include e in
/-- Tensoring an invertible ideal with a torsion-free module is injective. -/
lemma tensor_action_injective [Module.IsTorsionFree R M] (hi : Function.Injective i) :
    Function.Injective
      ((TensorProduct.lid R M).toLinearMap.comp (TensorProduct.map i LinearMap.id)) := by
  let b : L ⊗[R] M ≃ₗ[R] M := (e.rTensor M).trans (TensorProduct.lid R M)
  have h (x : L ⊗[R] M) :
      ((TensorProduct.lid R M).toLinearMap.comp (TensorProduct.map i LinearMap.id)) x =
        i (e.symm 1) • b x := by
    induction x using TensorProduct.inductionOn with
    | tmul l m =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
        LinearEquiv.coe_coe, TensorProduct.lid_tmul]
      change i l • m = i (e.symm 1) • (e l • m)
      rw [line_map_formula e i, mul_comm, mul_smul]
    | add x y hx hy => simp_all
  intro x y hxy
  apply b.injective
  apply (line_map_regular e i hi).isSMulRegular (M := M)
  simpa only [h] using hxy
end CartierTorsion

end

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace ActualSheafTensor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
local instance : MonoidalCategory (PresheafOfModules.{u} (ringSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat)))

private local instance tensorSectionModule (M : SheafOfModules.{u} (ringSheaf R))
    (U : Cᵒᵖ) : Module (R.obj.obj U) (M.val.obj U) := (M.val.obj U).isModule
private local instance tensorSectionCommRing (U : Cᵒᵖ) : CommRing ((ringSheaf R).obj.obj U) :=
  inferInstanceAs (CommRing (R.obj.obj U))

lemma idealAction_mono_of_unitIso {L : SheafOfModules.{u} (ringSheaf R)}
    (i : L ⟶ SheafOfModules.unit _) [Mono i]
    (e : L ≅ SheafOfModules.unit _) (M : SheafOfModules.{u} (ringSheaf R))
    (hM : ∀ U, Module.IsTorsionFree (R.obj.obj U) (M.val.obj U)) :
    Mono ((idealAction R i).app M) := by
  have : PreservesFiniteLimits (SheafOfModules.forget.{u} (ringSheaf R)) :=
    SheafOfModules.Finite.forgetPreservesFiniteLimits (ringSheaf R)
  have : (SheafOfModules.forget.{u} (ringSheaf R)).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape _
  have : Mono i.val := inferInstanceAs (Mono ((SheafOfModules.forget _).map i))
  let g := (i.val ▷ M.val) ≫ (λ_ M.val).hom
  have : Mono g := by
    apply PresheafOfModules.mono_of_injective
    intro U
    let _ := hM U
    let eU : L.val.obj U ≃ₗ[R.obj.obj U] R.obj.obj U :=
      CategoryTheory.Iso.toLinearEquiv ((SheafOfModules.evaluation (ringSheaf R) U).mapIso e)
    exact CartierTorsion.tensor_action_injective eU (i.val.app U).hom
      (PresheafOfModules.injective_of_mono i.val U)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)
  have hh : (idealAction R i).app M = (adj.homEquiv _ _).symm g := by
    apply (adj.homEquiv _ _).injective
    exact (idealAction_adjoint R i M).trans ((adj.homEquiv _ _).apply_symm_apply g).symm
  rw [hh]
  change Mono ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map g ≫
    adj.counit.app M)
  exact mono_comp' ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map_mono g)
    (inferInstanceAs (Mono (adj.counit.app M)))

variable [∀ U, HasSheafify (J.over U) AddCommGrpCat.{u}]
  [∀ U, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- An invertible ideal acts injectively on sectionwise torsion-free
module sheaves. In particular its first Cartier Tor vanishes. -/
lemma idealAction_mono_of_line {L : SheafOfModules.{u} (ringSheaf R)}
    (d : LineTrivialization R L) (i : L ⟶ SheafOfModules.unit _) [Mono i]
    (M : SheafOfModules.{u} (ringSheaf R))
    (hM : ∀ U, Module.IsTorsionFree (R.obj.obj U) (M.val.obj U)) :
    Mono ((idealAction R i).app M) := by
  apply SheafLocality.module_mono_of_coversTop (ringSheaf R) d.cover
  intro a
  let V := d.obj a
  let F := SheafOfModules.overFunctor (ringSheaf R) V
  have hiOver : Mono (F.map i) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro U
    have : PreservesFiniteLimits (SheafOfModules.forget.{u} (ringSheaf R)) :=
      SheafOfModules.Finite.forgetPreservesFiniteLimits (ringSheaf R)
    have : (SheafOfModules.forget.{u} (ringSheaf R)).PreservesMonomorphisms :=
      preservesMonomorphisms_of_preservesLimitsOfShape _
    have : Mono i.val := inferInstanceAs (Mono ((SheafOfModules.forget _).map i))
    exact PresheafOfModules.injective_of_mono i.val (op U.unop.left)
  have hmOver := @idealAction_mono_of_unitIso _ _ _ (R.over V) _ _ _ (F.map i) hiOver
    (d.iso a) (M.over V) (fun U => hM (op U.unop.left))
  have h := idealAction_over_inv R V i M
  have hcOver : Mono ((tensorOverIso R V L M).inv ≫ F.map ((idealAction R i).app M)) := by
    erw [h]
    exact hmOver
  have he : F.map ((idealAction R i).app M) =
      (tensorOverIso R V L M).hom ≫
        ((tensorOverIso R V L M).inv ≫ F.map ((idealAction R i).app M)) := by
    exact ((tensorOverIso R V L M).hom_inv_id_assoc _).symm
  rw [he]
  exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ (tensorOverIso R V L M).isIso_hom) hcOver
end ActualSheafTensor

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules ActualSheafTensor
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

private local instance affineSectionAlgebra
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Algebra R Γ(Spec R, U) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).obj.obj (op U)))
private local instance affineSectionModule (M : (Spec R).Modules)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Module R Γ(M, U) :=
  inferInstanceAs (Module R ((modulesSpecToSheaf.obj M).obj.obj (op U)))
private local instance affineSectionScalarModule (M : (Spec R).Modules)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) : Module Γ(Spec R, U) Γ(M, U) :=
  (M.val.obj (op U)).isModule
private local instance affineSheafSectionModule (M : (Spec R).Modules)
    (U : (Spec R).Opensᵒᵖ) : Module ((Spec R).sheaf.obj.obj U) (M.val.obj U) :=
  (M.val.obj U).isModule

private local instance affineFiniteQuasicoherent (M : (Spec R).Modules)
    [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
private local instance affineSectionTower (M : (Spec R).Modules)
    (U : TopologicalSpace.Opens (PrimeSpectrum R)) : IsScalarTower R Γ(Spec R, U) Γ(M, U) :=
  IsScalarTower.of_compHom R Γ(Spec R, U) Γ(M, U)

/-- Global sections detect maps from quasi-coherent affine sheaves. -/
lemma hom_ext_affine {M N : (Spec R).Modules} [M.IsQuasicoherent]
    (a b : M ⟶ N) (h : moduleSpecΓFunctor.map a = moduleSpecΓFunctor.map b) : a = b := by
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  apply (cancel_epi (fromTildeΓ M)).mp
  have ha := fromTildeΓNatTrans.naturality a
  have hb := fromTildeΓNatTrans.naturality b
  change (tilde.functor R).map (moduleSpecΓFunctor.map a) ≫ fromTildeΓ N =
    fromTildeΓ M ≫ a at ha
  change (tilde.functor R).map (moduleSpecΓFunctor.map b) ≫ fromTildeΓ N =
    fromTildeΓ M ≫ b at hb
  exact ha.symm.trans ((congrArg (fun f => (tilde.functor R).map f ≫ fromTildeΓ N) h).trans hb)

/-- Injectivity of a natural affine sheaf endomorphism is equivalent
to injectivity of its scalar action on the module of global sections. -/
lemma scalar_regular_on_Gamma (b : 𝟭 (Spec R).Modules ⟶ 𝟭 (Spec R).Modules)
    (M : (Spec R).Modules) [M.IsQuasicoherent] [Mono (b.app M)] :
    IsSMulRegular (moduleSpecΓFunctor.obj M) (AffineNaturalScalar.scalar R b) := by
  let P := moduleSpecΓFunctor.obj M
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  let c : tilde P ≅ M := @asIso _ _ _ _ (fromTildeΓ M) (isIso_fromTildeΓ_of_isQuasicoherent M)
  have he : b.app (tilde P) = c.hom ≫ b.app M ≫ c.inv := by
    have h := b.naturality c.hom
    dsimp only [CategoryTheory.Functor.id_map] at h
    rw [← Category.assoc, h, Category.assoc, c.hom_inv_id]
    exact (Category.comp_id _).symm
  have : Mono (b.app (tilde P)) := by rw [he]; infer_instance
  have : Mono ((tilde.functor R).preimage (b.app (tilde P))) :=
    (tilde.functor R).mono_of_mono_map (by
      erw [(tilde.functor R).map_preimage]
      exact inferInstanceAs (Mono (b.app (tilde P))))
  have hi := (ModuleCat.mono_iff_injective ((tilde.functor R).preimage (b.app (tilde P)))).mp
    inferInstance
  intro x y hxy
  apply hi
  simpa only [AffineNaturalScalar.preimage_apply] using hxy

/-- The canonical affine quasi-coherent counit isomorphism. -/
def affineCounitIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde (moduleSpecΓFunctor.obj M) ≅ M := by
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  exact @asIso _ _ _ _ (fromTildeΓ M) (isIso_fromTildeΓ_of_isQuasicoherent M)

/-- The precise puncture identification on the associated section modules. -/
def affinePunctureSectionsIso (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] (U : (Spec R).Opens)
    (e : M.over U ≅ N.over U) :
    Γ(tilde (moduleSpecΓFunctor.obj M), U) ≃ₗ[R]
      Γ(tilde (moduleSpecΓFunctor.obj N), U) :=
  let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf U
  punctureSectionsIso U (F.mapIso (affineCounitIso M) ≪≫ e ≪≫
    (F.mapIso (affineCounitIso N)).symm)

variable [IsNoetherianRing R]
  (L : (Spec R).Modules) (eL : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
  (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf) [Mono i]

/-- For coherent sheaves on an affine Cartier chart, clearing
both directions of a prescribed puncture isomorphism gives injective maps
between their section modules, with a shared constructed exponent.
The regularity of the equation is proved from the ideal action. -/
lemma coherent_compatible_sandwich (M N : (Spec R).Modules)
    [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)) ≅
      N.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i))) :
    let P := moduleSpecΓFunctor.obj M
    let Q := moduleSpecΓFunctor.obj N
    let t := AffineCartierNilpotence.equation L eL i
    ∃ (n : ℕ) (a : P →ₗ[R] Q) (b : Q →ₗ[R] P),
      Function.Injective a ∧ Function.Injective b ∧
      (∀ x, (tilde.toOpen Q (PrimeSpectrum.basicOpen t)).hom (a x) =
        t ^ n • affinePunctureSectionsIso M N (PrimeSpectrum.basicOpen t) e
          ((tilde.toOpen P (PrimeSpectrum.basicOpen t)).hom x)) ∧
      (∀ y, (tilde.toOpen P (PrimeSpectrum.basicOpen t)).hom (b y) =
        t ^ n • (affinePunctureSectionsIso M N (PrimeSpectrum.basicOpen t) e).symm
          ((tilde.toOpen Q (PrimeSpectrum.basicOpen t)).hom y)) ∧
      a.comp b = t ^ (2 * n) • (LinearMap.id : Q →ₗ[R] Q) ∧
      b.comp a = t ^ (2 * n) • (LinearMap.id : P →ₗ[R] P) := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  let P := moduleSpecΓFunctor.obj M
  let Q := moduleSpecΓFunctor.obj N
  have : Module.Finite R P := CoherentGlobal.finiteGamma_of_coherent M
  have : Module.Finite R Q := CoherentGlobal.finiteGamma_of_coherent N
  have : Module.FinitePresentation R P := Module.finitePresentation_of_finite R P
  have : Module.FinitePresentation R Q := Module.finitePresentation_of_finite R Q
  have : IsIso (fromTildeΓ M) := isIso_fromTildeΓ_of_isQuasicoherent M
  have : IsIso (fromTildeΓ N) := isIso_fromTildeΓ_of_isQuasicoherent N
  let cM : tilde P ≅ M := @asIso _ _ _ _ (fromTildeΓ M) (isIso_fromTildeΓ_of_isQuasicoherent M)
  let cN : tilde Q ≅ N := @asIso _ _ _ _ (fromTildeΓ N) (isIso_fromTildeΓ_of_isQuasicoherent N)
  let b := (trivialTensorIso (Spec R).sheaf eL).inv ≫ idealAction (Spec R).sheaf i
  have hmonoM : Mono ((idealAction (Spec R).sheaf i).app M) :=
    @idealAction_mono_of_unitIso _ _ _ (Spec R).sheaf _ _ L i ‹Mono i› eL M hM
  have hmonoN : Mono ((idealAction (Spec R).sheaf i).app N) :=
    @idealAction_mono_of_unitIso _ _ _ (Spec R).sheaf _ _ L i ‹Mono i› eL N hN
  have hbM : Mono (b.app M) := by
    change Mono (((trivialTensorIso (Spec R).sheaf eL).inv.app M) ≫ (idealAction (Spec R).sheaf i).app M)
    exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ ((trivialTensorIso (Spec R).sheaf eL).app M).isIso_inv) hmonoM
  have hbN : Mono (b.app N) := by
    change Mono (((trivialTensorIso (Spec R).sheaf eL).inv.app N) ≫ (idealAction (Spec R).sheaf i).app N)
    exact mono_comp' (@IsIso.mono_of_iso _ _ _ _ _ ((trivialTensorIso (Spec R).sheaf eL).app N).isIso_inv) hmonoN
  have htP : IsSMulRegular P (AffineCartierNilpotence.equation L eL i) := by
    rw [← AffineCartierNilpotence.normalized_scalar L eL i]
    exact @scalar_regular_on_Gamma R b M inferInstance hbM
  have htQ : IsSMulRegular Q (AffineCartierNilpotence.equation L eL i) := by
    rw [← AffineCartierNilpotence.normalized_scalar L eL i]
    exact @scalar_regular_on_Gamma R b N inferInstance hbN
  let U := PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)
  let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf U
  let e' := F.mapIso cM ≪≫ e ≪≫ (F.mapIso cN).symm
  obtain ⟨n, a, b, ha, hb, haf, hbf, hab, hba⟩ := exists_compatible_sandwich
    (AffineCartierNilpotence.equation L eL i) htP htQ
    (tilde.toOpen P U).hom (tilde.toOpen Q U).hom (punctureSectionsIso U e')
  exact ⟨n, a, b, ha, hb, haf, hbf, hab, hba⟩
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

attribute [local instance] affineSectionModule affineSectionScalarModule affineSheafSectionModule
  affineFiniteQuasicoherent affineSectionAlgebra affineSectionTower

/-- A morphism from an associated affine sheaf, even over an arbitrary
open, is determined by the images of the original module's sections.
This is proved by localization on basic opens and sheaf separation. -/
lemma hom_ext_tilde_over (P : ModuleCat R) (N : (Spec R).Modules)
    (U : (Spec R).Opens) (a b : (tilde P).over U ⟶ N.over U)
    (h : ∀ x : P,
      (a.val.app (op (Over.mk (𝟙 U)))) ((tilde.toOpen P U).hom x) =
        (b.val.app (op (Over.mk (𝟙 U)))) ((tilde.toOpen P U).hom x)) : a = b := by
  have basic (r : R) (hr : PrimeSpectrum.basicOpen r ≤ U) :
      a.val.app (op (Over.mk (homOfLE hr))) =
        b.val.app (op (Over.mk (homOfLE hr))) := by
    let V := PrimeSpectrum.basicOpen r
    let W : Over U := Over.mk (homOfLE hr)
    let q : W ⟶ Over.mk (𝟙 U) := Over.homMk (homOfLE hr) (by dsimp [W]; rfl)
    let aa : Γ(tilde P, V) →ₗ[R] Γ(N, V) := (show Γ(tilde P, V) →ₗ[Γ(Spec R, V)] Γ(N, V) from
      (a.val.app (op W)).hom).restrictScalars R
    let bb : Γ(tilde P, V) →ₗ[R] Γ(N, V) := (show Γ(tilde P, V) →ₗ[Γ(Spec R, V)] Γ(N, V) from
      (b.val.app (op W)).hom).restrictScalars R
    have he : aa = bb := by
      apply IsLocalizedModule.ext (.powers r) (tilde.toOpen P V).hom
      · intro s
        obtain ⟨s, n, rfl⟩ := s
        rw [map_pow]
        exact (N.isUnit_algebraMap_end_of_le_basicOpen r le_rfl).pow n
      · ext x
        have ha := ConcreteCategory.congr_hom (a.val.naturality q.op) ((tilde.toOpen P U).hom x)
        have hb := ConcreteCategory.congr_hom (b.val.naturality q.op) ((tilde.toOpen P U).hom x)
        have ht := ConcreteCategory.congr_hom (tilde.toOpen_res P U V (homOfLE hr)) x
        change (tilde P).val.map (homOfLE hr).op ((tilde.toOpen P U).hom x) =
          (tilde.toOpen P V).hom x at ht
        change aa ((tilde P).val.map (homOfLE hr).op ((tilde.toOpen P U).hom x)) =
          N.val.map (homOfLE hr).op
            ((a.val.app (op (Over.mk (𝟙 U)))) ((tilde.toOpen P U).hom x)) at ha
        change bb ((tilde P).val.map (homOfLE hr).op ((tilde.toOpen P U).hom x)) =
          N.val.map (homOfLE hr).op
            ((b.val.app (op (Over.mk (𝟙 U)))) ((tilde.toOpen P U).hom x)) at hb
        rw [ht] at ha hb
        exact ha.trans ((congrArg (N.val.map (homOfLE hr).op) (h x)).trans hb.symm)
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => LinearMap.congr_fun he x)
  ext V x
  apply TopCat.Presheaf.IsSheaf.section_ext (modulesSpecToSheaf.obj N).2
  intro p hp
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hrV : PrimeSpectrum.basicOpen _ ≤ _⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp V.unop.left.2
  refine ⟨_, hrV, hpr, ?_⟩
  let W : Over U := Over.mk (homOfLE (hrV.trans V.unop.hom.le))
  let q : W ⟶ V.unop := Over.homMk (homOfLE hrV) (by subsingleton)
  have ha := ConcreteCategory.congr_hom (a.val.naturality q.op) x
  have hb := ConcreteCategory.congr_hom (b.val.naturality q.op) x
  change (a.val.app (op W)) ((tilde P).val.map (homOfLE hrV).op x) =
    N.val.map (homOfLE hrV).op ((a.val.app V) x) at ha
  change (b.val.app (op W)) ((tilde P).val.map (homOfLE hrV).op x) =
    N.val.map (homOfLE hrV).op ((b.val.app V) x) at hb
  exact ha.symm.trans ((congrArg (fun f => f ((tilde P).val.map (homOfLE hrV).op x))
    (basic r (hrV.trans V.unop.hom.le))).trans hb)
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

attribute [local instance] affineSectionModule affineSectionScalarModule affineSheafSectionModule
  affineFiniteQuasicoherent affineSectionAlgebra affineSectionTower

/-- Denominator-cleared sheaf maps retain the prescribed puncture morphism. -/
lemma tilde_cleared_map_over (P Q : ModuleCat R) (t : R) (n : ℕ)
    (e : (tilde P).over (PrimeSpectrum.basicOpen t) ≅
      (tilde Q).over (PrimeSpectrum.basicOpen t)) (a : P →ₗ[R] Q)
    (ha : ∀ x, (tilde.toOpen Q (PrimeSpectrum.basicOpen t)).hom (a x) =
      t ^ n • punctureSectionsIso (PrimeSpectrum.basicOpen t) e
        ((tilde.toOpen P (PrimeSpectrum.basicOpen t)).hom x)) :
    ((tilde.functor R).map (ModuleCat.ofHom a)).over (PrimeSpectrum.basicOpen t) =
      ((tilde.functor R).map
        (ModuleCat.ofHom (t ^ n • (LinearMap.id : P →ₗ[R] P)))).over
          (PrimeSpectrum.basicOpen t) ≫ e.hom := by
  let U := PrimeSpectrum.basicOpen t
  apply hom_ext_tilde_over P (tilde Q) U
  intro x
  have ham := ConcreteCategory.congr_hom (tilde.toOpen_map_app (ModuleCat.ofHom a) U) x
  have hsm := ConcreteCategory.congr_hom (tilde.toOpen_map_app
    (ModuleCat.ofHom (t ^ n • (LinearMap.id : P →ₗ[R] P))) U) x
  change (tilde.map (ModuleCat.ofHom a)).val.app (op U) ((tilde.toOpen P U).hom x) =
    (tilde.toOpen Q U).hom (a x) at ham
  change (tilde.map (ModuleCat.ofHom (t ^ n • (LinearMap.id : P →ₗ[R] P)))).val.app (op U)
    ((tilde.toOpen P U).hom x) = (tilde.toOpen P U).hom (t ^ n • x) at hsm
  change (tilde.map (ModuleCat.ofHom a)).val.app (op U) ((tilde.toOpen P U).hom x) =
    punctureSectionsIso U e
      ((tilde.map (ModuleCat.ofHom (t ^ n • (LinearMap.id : P →ₗ[R] P)))).val.app (op U)
        ((tilde.toOpen P U).hom x))
  rw [ham, hsm, LinearMap.map_smul]
  erw [LinearEquiv.map_smul]
  exact ha x

/-- On every affine chart, a puncture isomorphism provides a pair of coherent-sheaf monomorphisms with one common denominator and exact
compatibility on the whole puncture. -/
lemma exists_tilde_compatible_sandwich
    (P Q : ModuleCat R) [Module.FinitePresentation R P] [Module.FinitePresentation R Q]
    (t : R) (htP : IsSMulRegular P t) (htQ : IsSMulRegular Q t)
    (e : (tilde P).over (PrimeSpectrum.basicOpen t) ≅
      (tilde Q).over (PrimeSpectrum.basicOpen t)) :
    ∃ (n : ℕ) (a : tilde P ⟶ tilde Q) (b : tilde Q ⟶ tilde P),
      Mono a ∧ Mono b ∧
      a.over (PrimeSpectrum.basicOpen t) =
        ((tilde.functor R).map
          (ModuleCat.ofHom (t ^ n • (LinearMap.id : P →ₗ[R] P)))).over
            (PrimeSpectrum.basicOpen t) ≫ e.hom ∧
      b.over (PrimeSpectrum.basicOpen t) =
        ((tilde.functor R).map
          (ModuleCat.ofHom (t ^ n • (LinearMap.id : Q →ₗ[R] Q)))).over
            (PrimeSpectrum.basicOpen t) ≫ e.inv ∧
      a ≫ b = (tilde.functor R).map
        (ModuleCat.ofHom (t ^ (2 * n) • (LinearMap.id : P →ₗ[R] P))) ∧
      b ≫ a = (tilde.functor R).map
        (ModuleCat.ofHom (t ^ (2 * n) • (LinearMap.id : Q →ₗ[R] Q))) := by
  let U := PrimeSpectrum.basicOpen t
  obtain ⟨n, a, b, ha, hb, haf, hbf, hab, hba⟩ := exists_compatible_sandwich t htP htQ
    (tilde.toOpen P U).hom (tilde.toOpen Q U).hom (punctureSectionsIso U e)
  let aa := (tilde.functor R).map (ModuleCat.ofHom a)
  let bb := (tilde.functor R).map (ModuleCat.ofHom b)
  have : Mono (ModuleCat.ofHom a) := (ModuleCat.mono_iff_injective _).mpr ha
  have : Mono (ModuleCat.ofHom b) := (ModuleCat.mono_iff_injective _).mpr hb
  have haa : Mono aa := (CoherentExactAffine.preservesMonomorphisms (R := R)).preserves _
  have hbb : Mono bb := (CoherentExactAffine.preservesMonomorphisms (R := R)).preserves _
  refine ⟨n, aa, bb, haa, hbb,
    tilde_cleared_map_over P Q t n e a haf,
    tilde_cleared_map_over Q P t n e.symm b hbf, ?_, ?_⟩
  · change (tilde.functor R).map _ ≫ (tilde.functor R).map _ = _
    rw [← Functor.map_comp]
    congr 1
    apply ModuleCat.hom_ext
    exact hba
  · change (tilde.functor R).map _ ≫ (tilde.functor R).map _ = _
    rw [← Functor.map_comp]
    congr 1
    apply ModuleCat.hom_ext
    exact hab
end CartierAffineLattice

end

noncomputable section
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.OAI.AlgebraicGeometry Opposite
open Scheme.Modules ActualSheafTensor
namespace CartierAffineLattice
variable {R : CommRingCat.{0}}

attribute [local instance] affineSectionModule affineSectionScalarModule affineSheafSectionModule
  affineFiniteQuasicoherent affineSectionAlgebra affineSectionTower

/-- Scalar map on an associated sheaf. -/
def tildeScalar (r : R) (P : ModuleCat R) : tilde P ⟶ tilde P :=
  (tilde.functor R).map (ModuleCat.ofHom (r • (LinearMap.id : P →ₗ[R] P)))

/-- Scalar action on a quasi-coherent affine sheaf via its canonical
section-module presentation, rather than an unspecified endomorphism. -/
def affineScalar (r : R) (M : (Spec R).Modules) [M.IsQuasicoherent] : M ⟶ M :=
  (affineCounitIso M).inv ≫ tildeScalar r (moduleSpecΓFunctor.obj M) ≫
    (affineCounitIso M).hom

private lemma conjugate_compat {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {M M' N N' : C} (i : M ≅ M') (j : N ≅ N')
    (e : F.obj M' ≅ F.obj N') (a : M ⟶ N) (t : M ⟶ M)
    (ha : F.map a = F.map t ≫ (F.mapIso i ≪≫ e ≪≫ (F.mapIso j).symm).hom) :
    F.map (i.inv ≫ a ≫ j.hom) = F.map (i.inv ≫ t ≫ i.hom) ≫ e.hom := by
  simp only [Functor.map_comp, ha, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [← F.map_comp, j.inv_hom_id, F.map_id, Category.comp_id]

private lemma transport_all {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {P Q M N : C} (cM : P ≅ M) (cN : Q ≅ N)
    (e : F.obj M ≅ F.obj N) (aa : P ⟶ Q) (bb : Q ⟶ P)
    [Mono aa] [Mono bb] (sP vP : P ⟶ P) (sQ vQ : Q ⟶ Q)
    (ha : F.map aa = F.map sP ≫ (F.mapIso cM ≪≫ e ≪≫ (F.mapIso cN).symm).hom)
    (hb : F.map bb = F.map sQ ≫ (F.mapIso cM ≪≫ e ≪≫ (F.mapIso cN).symm).inv)
    (hab : aa ≫ bb = vP) (hba : bb ≫ aa = vQ) :
    ∃ (a : M ⟶ N) (b : N ⟶ M), Mono a ∧ Mono b ∧
      F.map a = F.map (cM.inv ≫ sP ≫ cM.hom) ≫ e.hom ∧
      F.map b = F.map (cN.inv ≫ sQ ≫ cN.hom) ≫ e.inv ∧
      a ≫ b = cM.inv ≫ vP ≫ cM.hom ∧ b ≫ a = cN.inv ≫ vQ ≫ cN.hom := by
  refine ⟨cM.inv ≫ aa ≫ cN.hom, cN.inv ≫ bb ≫ cM.hom,
    inferInstance, inferInstance, conjugate_compat F cM cN e aa sP ha, ?_, ?_, ?_⟩
  · apply conjugate_compat F cN cM e.symm bb sQ
    simpa only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc] using hb
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc aa bb,
      hab]
  · simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc bb aa,
      hba]

private lemma sheaf_sandwich_of_linear (P Q : ModuleCat R)
    (M N : (Spec R).Modules) (cM : tilde P ≅ M) (cN : tilde Q ≅ N)
    (t : R) (e : M.over (PrimeSpectrum.basicOpen t) ≅ N.over (PrimeSpectrum.basicOpen t))
    (hdata :
      let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf (PrimeSpectrum.basicOpen t)
      let e' := F.mapIso cM ≪≫ e ≪≫ (F.mapIso cN).symm
      ∃ (n : ℕ) (a : P →ₗ[R] Q) (b : Q →ₗ[R] P),
        Function.Injective a ∧ Function.Injective b ∧
        (∀ x, (tilde.toOpen Q (PrimeSpectrum.basicOpen t)).hom (a x) =
          t ^ n • punctureSectionsIso (PrimeSpectrum.basicOpen t) e'
            ((tilde.toOpen P (PrimeSpectrum.basicOpen t)).hom x)) ∧
        (∀ y, (tilde.toOpen P (PrimeSpectrum.basicOpen t)).hom (b y) =
          t ^ n • (punctureSectionsIso (PrimeSpectrum.basicOpen t) e').symm
            ((tilde.toOpen Q (PrimeSpectrum.basicOpen t)).hom y)) ∧
        a.comp b = t ^ (2 * n) • (LinearMap.id : Q →ₗ[R] Q) ∧
        b.comp a = t ^ (2 * n) • (LinearMap.id : P →ₗ[R] P)) :
    let U := PrimeSpectrum.basicOpen t
    ∃ (n : ℕ) (a : M ⟶ N) (b : N ⟶ M), Mono a ∧ Mono b ∧
      a.over U = (cM.inv ≫ tildeScalar (t ^ n) P ≫ cM.hom).over U ≫ e.hom ∧
      b.over U = (cN.inv ≫ tildeScalar (t ^ n) Q ≫ cN.hom).over U ≫ e.inv ∧
      a ≫ b = cM.inv ≫ tildeScalar (t ^ (2 * n)) P ≫ cM.hom ∧
      b ≫ a = cN.inv ≫ tildeScalar (t ^ (2 * n)) Q ≫ cN.hom := by
  let U := PrimeSpectrum.basicOpen t
  let F := SheafOfModules.overFunctor (Spec R).ringCatSheaf U
  let e' := F.mapIso cM ≪≫ e ≪≫ (F.mapIso cN).symm
  obtain ⟨n, a, b, ha, hb, haf, hbf, hab, hba⟩ := hdata
  let aa := (tilde.functor R).map (ModuleCat.ofHom a)
  let bb := (tilde.functor R).map (ModuleCat.ofHom b)
  have : Mono (ModuleCat.ofHom a) := (ModuleCat.mono_iff_injective _).mpr ha
  have : Mono (ModuleCat.ofHom b) := (ModuleCat.mono_iff_injective _).mpr hb
  have haa : Mono aa := (CoherentExactAffine.preservesMonomorphisms (R := R)).preserves _
  have hbb : Mono bb := (CoherentExactAffine.preservesMonomorphisms (R := R)).preserves _
  have h₁ := tilde_cleared_map_over P Q t n e' a haf
  have h₂ := tilde_cleared_map_over Q P t n e'.symm b hbf
  have h₃ : aa ≫ bb = tildeScalar (t ^ (2 * n)) P := by
    change aa ≫ bb = (tilde.functor R).map _
    rw [show aa ≫ bb = (tilde.functor R).map
      (ModuleCat.ofHom (b.comp a)) from (Functor.map_comp _ _ _).symm, hba]
  have h₄ : bb ≫ aa = tildeScalar (t ^ (2 * n)) Q := by
    change bb ≫ aa = (tilde.functor R).map _
    rw [show bb ≫ aa = (tilde.functor R).map
      (ModuleCat.ofHom (a.comp b)) from (Functor.map_comp _ _ _).symm, hab]
  exact ⟨n, @transport_all _ _ _ _ F _ _ _ _ cM cN e aa bb haa hbb _ _ _ _ h₁ h₂ h₃ h₄⟩

/-- The affine coherent-sheaf sandwich on a trivializing Cartier
chart. The equation and its regularity come from the ideal inclusion;
the puncture compatibility is an equality of sheaf morphisms on all opens. -/
lemma exists_coherent_sheaf_sandwich [IsNoetherianRing R]
    (L : (Spec R).Modules) (eL : L ≅ SheafOfModules.unit (Spec R).ringCatSheaf)
    (i : L ⟶ SheafOfModules.unit (Spec R).ringCatSheaf) [Mono i]
    (M N : (Spec R).Modules) [M.IsFinitePresentation] [N.IsFinitePresentation]
    (hM : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (M.val.obj U))
    (hN : ∀ U, Module.IsTorsionFree ((Spec R).sheaf.obj.obj U) (N.val.obj U))
    (e : M.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i)) ≅
      N.over (PrimeSpectrum.basicOpen (AffineCartierNilpotence.equation L eL i))) :
    let t := AffineCartierNilpotence.equation L eL i
    let U := PrimeSpectrum.basicOpen t
    ∃ (n : ℕ) (a : M ⟶ N) (b : N ⟶ M), Mono a ∧ Mono b ∧
      a.over U = (affineScalar (t ^ n) M).over U ≫ e.hom ∧
      b.over U = (affineScalar (t ^ n) N).over U ≫ e.inv ∧
      a ≫ b = affineScalar (t ^ (2 * n)) M ∧
      b ≫ a = affineScalar (t ^ (2 * n)) N := by
  have : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  have : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  exact sheaf_sandwich_of_linear _ _ M N (affineCounitIso M) (affineCounitIso N) _ e
    (coherent_compatible_sandwich L eL i M N hM hN e)
end CartierAffineLattice

end

end OAI
