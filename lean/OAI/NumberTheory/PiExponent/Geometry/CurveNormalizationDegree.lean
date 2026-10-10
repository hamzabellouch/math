import OAI.NumberTheory.PiExponent.Approximation.ProjectionFormula
import OAI.NumberTheory.PiExponent.Cohomology.EulerExact
import OAI.NumberTheory.PiExponent.Geometry.FiniteCurveZeros
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteSupportLocalIso

namespace OAI

noncomputable section
namespace PiExponent.CurveNormalizationDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

lemma cokernel_stalk_subsingleton {M N : X.Modules} (s : M ⟶ N) (x : X)
    (hx : x ∈ isoOpen s) :
    Subsingleton ((cokernel s).presheaf.stalk x) := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf ⋙
    TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  let : F.PreservesZeroMorphisms := by
    constructor
    intro M N
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (0 : M ⟶ N)).hom = 0
    rw [Functor.map_zero]
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map 0 = 0
    exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map_zero _ _
  let : PreservesColimitsOfSize.{0,0} F := by
    refine @comp_preservesColimits _ _ _ _ _ _ _ _ ?_ ?_
    · exact PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits X.ringCatSheaf
    · exact inferInstanceAs (PreservesColimitsOfSize.{0,0}
        (TopCat.Sheaf.forget AddCommGrpCat.{0} (X : TopCat) ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x))
  obtain ⟨U,hx,hU⟩ := (mem_isoOpen_iff s x).mp hx
  let := hU
  let : IsIso (F.map s) := stalk_isIso_of_restrict s U.ι ⟨x,hx⟩
  have hz : IsZero (F.obj (cokernel s)) :=
    (isZero_cokernel_of_epi (F.map s)).of_iso (PreservesCokernel.iso F s)
  exact AddCommGrpCat.subsingleton_of_isZero hz

theorem finite_closed_complement [IsIntegral X] [IsNoetherian X]
    (hd : topologicalKrullDim X ≤ 1) (U : X.Opens) (hU : U ≠ ⊥) :
    ((U : Set X)ᶜ).Finite ∧ ∀ x ∉ U, IsClosed ({x} : Set X) := by
  have hproper : (U : Set X)ᶜ ≠ Set.univ := by
    intro he
    apply hU
    apply SetLike.coe_injective
    simpa using he
  refine ⟨proper_closed_finite_of_dimension_one hd U.isOpen.isClosed_compl hproper, ?_⟩
  intro x hx
  have hc : closure ({x} : Set X) ⊆ (U : Set X)ᶜ :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) U.isOpen.isClosed_compl
  have hsub : (closure ({x} : Set X)).Subsingleton :=
    proper_irreducible_closed_subsingleton hd isClosed_closure
      isIrreducible_singleton.closure (fun he => hproper (Set.eq_univ_of_univ_subset (he ▸ hc)))
  have he : closure ({x} : Set X) = {x} := by
    apply Set.Subset.antisymm
    · intro y hy
      exact hsub hy (subset_closure (Set.mem_singleton x))
    · exact subset_closure
  exact he ▸ isClosed_closure

theorem stalk_subsingleton_of_localIso (M N : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (e : M.restrict U.ι ≅ N.restrict U.ι)
    [Subsingleton (N.presheaf.stalk x)] : Subsingleton (M.presheaf.stalk x) := by
  let a := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app M
  let b := (Scheme.Modules.restrictStalkNatIso U.ι ⟨x,hx⟩).app N
  let d := (Scheme.Modules.toPresheaf U.toScheme ⋙
    TopCat.Presheaf.stalkFunctor Ab (⟨x,hx⟩ : U.toScheme)).mapIso e
  let c := a.symm ≪≫ d ≪≫ b
  constructor
  intro s t
  apply (ConcreteCategory.bijective_of_isIso c.hom).injective
  exact Subsingleton.elim (α := N.presheaf.stalk x) _ _

theorem tensor_stalk_subsingleton (M : X.Modules) (L : LineBundle X) (x : X)
    [Subsingleton (M.presheaf.stalk x)] :
    Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
  exact stalk_subsingleton_of_localIso _ M x U hx
    ((moduleTensorRestrictFrame U L.sheaf e).app M)

theorem finite_support_euler (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (d : ℕ) :
    eulerCharacteristic p d M =
      letI := Module.compHom Γ(M,⊤) (baseScalars p)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) :=
    PiExponentSeshadri.FiniteSupport.finite_closed_support_flasque _ S hfin hclosed hsupp
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    let : Subsingleton (cohomology M (j+1)) := ⟨fun x y =>
      (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf j M x).trans
        (PiExponentSeshadri.FlasqueCohomology.flasque_ext_zero X.ringCatSheaf j M y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

theorem finite_support_tensor_euler (p : X ⟶ Spec (.of ℂ)) (M : X.Modules)
    (L : LineBundle X) (S : Set X) (hfin : S.Finite)
    (hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))
    (hsupp : ∀ x ∉ S, Subsingleton (M.presheaf.stalk x)) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X M L.sheaf) = eulerCharacteristic p d M := by
  have ht (x : X) (hx : x ∉ S) :
      Subsingleton ((moduleTensor X M L.sheaf).presheaf.stalk x) := by
    let := hsupp x hx
    exact tensor_stalk_subsingleton M L x
  let e := finiteSupportLocallyIsoGlobal (moduleTensor X M L.sheaf) M S hfin hclosed ht hsupp
    (fun x _ => by
      obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne x
      exact ⟨U,hx,⟨(moduleTensorRestrictFrame U L.sheaf e).app M⟩⟩)
  let := Module.compHom Γ(moduleTensor X M L.sheaf,⊤) (baseScalars p)
  let := Module.compHom Γ(M,⊤) (baseScalars p)
  let ec : Γ(moduleTensor X M L.sheaf,⊤) ≃ₗ[ℂ] Γ(M,⊤) :=
    { e.toAddEquiv with
      map_smul' := fun r x => e.map_smul (baseScalars p r) x }
  rw [finite_support_euler p _ S hfin hclosed ht,
    finite_support_euler p M S hfin hclosed hsupp]
  exact_mod_cast ec.finrank_eq

theorem cokernel_tensor_euler [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    {M N : X.Modules} (u : M ⟶ N) (hu : isoOpen u ≠ ⊥) (L : LineBundle X) (d : ℕ) :
    eulerCharacteristic p d (moduleTensor X (cokernel u) L.sheaf) =
      eulerCharacteristic p d (cokernel u) := by
  obtain ⟨hfin,hclosed⟩ := finite_closed_complement hd (isoOpen u) hu
  exact finite_support_tensor_euler p _ L (isoOpen u : Set X)ᶜ hfin hclosed
    (fun x hx => cokernel_stalk_subsingleton u x (not_not.mp hx)) d

end PiExponent.CurveNormalizationDegree

end

end OAI
