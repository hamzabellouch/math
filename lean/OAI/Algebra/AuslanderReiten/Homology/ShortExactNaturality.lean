import OAI.Algebra.AuslanderReiten.Cones.MappingConeNaturality

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit
open CompleteComparison

universe u
variable {R : Type u} [Ring R]

namespace CompleteComparison
variable {K L M : CochainComplex (ModuleCat.{u} R) ℤ}

theorem cochainHomotopyRawEquiv_comp
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hM : ExactProjectiveCochain M)
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M) :
    cochainHomotopyRawEquiv hK.to_chain hM.to_chain (f ≫ g) =
      StableHom.comp (cochainHomotopyRawEquiv hL.to_chain hM.to_chain g)
        (cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex f) := by
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective f
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).map_surjective g
  rw [← Functor.map_comp, cochainHomotopyRawEquiv_map, cochainHomotopyRawEquiv_map,
    cochainHomotopyRawEquiv_map, cochainCokernelMap_comp, StableHom.comp_classOf]

theorem cochainHomotopyRawEquiv_comp_class
    (hK : TotallyAcyclicCochain K) (hL : TotallyAcyclicCochain L)
    (hM : ExactProjectiveCochain M)
    (f : (HomotopyCategory.quotient _ _).obj K ⟶ (HomotopyCategory.quotient _ _).obj L)
    (g : (HomotopyCategory.quotient _ _).obj L ⟶ (HomotopyCategory.quotient _ _).obj M)
    (p : CochainCokernel K →ₗ[R] CochainCokernel L)
    (q : CochainCokernel L →ₗ[R] CochainCokernel M)
    (hf : cochainHomotopyRawEquiv hK.to_chain hL.to_chain.toExactProjectiveComplex f =
      StableHom.classOf R _ _ p)
    (hg : cochainHomotopyRawEquiv hL.to_chain hM.to_chain g = StableHom.classOf R _ _ q) :
    cochainHomotopyRawEquiv hK.to_chain hM.to_chain (f ≫ g) =
      StableHom.classOf R _ _ (q.comp p) := by
  rw [cochainHomotopyRawEquiv_comp hK hL hM, hg, hf, StableHom.comp_classOf]

end CompleteComparison

variable [Module.Injective R R]
variable {F G K : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ : F ⟶ G) (p : CochainCokernel G →ₗ[R] CochainCokernel K)
variable (hex : Function.Exact (cochainCokernelMap φ) p)
variable (hF : TotallyAcyclicCochain F) (hG : TotallyAcyclicCochain G)
variable (hK : TotallyAcyclicCochain K)
variable (hi : Function.Injective (cochainCokernelMap φ)) (hp : Function.Surjective p)

theorem shortExactConeIso_raw_hom :
    cochainHomotopyRawEquiv (mappingCone_totallyAcyclic φ hF hG).to_chain
      hK.to_chain.toExactProjectiveComplex (shortExactConeIso φ p hex hF hG hK hi hp).hom =
    StableHom.classOf R _ _ (rawConeQuotient φ p hex) := by
  simp only [cochainHomotopyRawEquiv, AddEquiv.trans_apply, shortExactConeIso_hom,
    StableIsomorphism.sourceAddEquiv, StableIsomorphism.targetAddEquiv,
    StableIsomorphism.ofLinearEquiv, AddEquiv.coe_mk, Equiv.coe_fn_mk,
    StableHom.comp_classOf]
  apply congrArg (StableHom.classOf R _ _)
  apply LinearMap.ext
  intro x
  simp [completeConeQuotient]

variable {F₁ G₁ K₁ F₂ G₂ K₂ : CochainComplex (ModuleCat.{u} R) ℤ}
variable (φ₁ : F₁ ⟶ G₁) (φ₂ : F₂ ⟶ G₂)
variable (p₁ : CochainCokernel G₁ →ₗ[R] CochainCokernel K₁)
  (p₂ : CochainCokernel G₂ →ₗ[R] CochainCokernel K₂)
variable (hex₁ : Function.Exact (cochainCokernelMap φ₁) p₁)
  (hex₂ : Function.Exact (cochainCokernelMap φ₂) p₂)
variable (hF₁ : TotallyAcyclicCochain F₁) (hG₁ : TotallyAcyclicCochain G₁)
  (hK₁ : TotallyAcyclicCochain K₁)
variable (hF₂ : TotallyAcyclicCochain F₂) (hG₂ : TotallyAcyclicCochain G₂)
  (hK₂ : TotallyAcyclicCochain K₂)
variable (hi₁ : Function.Injective (cochainCokernelMap φ₁)) (hp₁ : Function.Surjective p₁)
  (hi₂ : Function.Injective (cochainCokernelMap φ₂)) (hp₂ : Function.Surjective p₂)
variable (a : F₁ ⟶ F₂) (b : G₁ ⟶ G₂) (c : K₁ ⟶ K₂)
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (hH : H.hom 1 0 = 0)
variable (hc : p₂.comp (cochainCokernelMap b) = (cochainCokernelMap c).comp p₁)

include hH hc in

theorem shortExactConeIso_natural :
    (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) ≫
        (shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).hom =
      (shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).hom ≫
        (HomotopyCategory.quotient _ _).map c := by
  apply (cochainHomotopyRawEquiv (mappingCone_totallyAcyclic φ₁ hF₁ hG₁).to_chain
    hK₂.to_chain.toExactProjectiveComplex).injective
  have hl := cochainHomotopyRawEquiv_comp_class
    (mappingCone_totallyAcyclic φ₁ hF₁ hG₁) (mappingCone_totallyAcyclic φ₂ hF₂ hG₂)
    hK₂.toExactProjectiveCochain
    ((HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H))
    (shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).hom
    (cochainCokernelMap (mappingCone.mapOfHomotopy H)) (rawConeQuotient φ₂ p₂ hex₂)
    (cochainHomotopyRawEquiv_map _ _ _) (shortExactConeIso_raw_hom φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂)
  have hr := cochainHomotopyRawEquiv_comp_class
    (mappingCone_totallyAcyclic φ₁ hF₁ hG₁) hK₁ hK₂.toExactProjectiveCochain
    (shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).hom
    ((HomotopyCategory.quotient _ _).map c)
    (rawConeQuotient φ₁ p₁ hex₁) (cochainCokernelMap c)
    (shortExactConeIso_raw_hom φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁) (cochainHomotopyRawEquiv_map _ _ _)
  exact hl.trans ((congrArg (StableHom.classOf R _ _)
    (rawConeQuotient_natural H hH p₁ p₂ hex₁ hex₂ (cochainCokernelMap c) hc)).trans hr.symm)

include hc in

theorem shortExactTriangle_connecting_natural
    (hab : cochainCokernelMap (φ₁ ≫ b) = cochainCokernelMap (a ≫ φ₂)) :
    (HomotopyCategory.quotient _ _).map c ≫
        (shortExactTriangle φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂).mor₃ =
      (shortExactTriangle φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁).mor₃ ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
          ((HomotopyCategory.quotient _ _).map a) := by
  obtain ⟨H, hH⟩ := cochain_homotopy_of_cokernel_eq hF₁ hG₂.toExactProjectiveCochain
    (φ₁ ≫ b) (a ≫ φ₂) hab
  let E₁ := shortExactConeIso φ₁ p₁ hex₁ hF₁ hG₁ hK₁ hi₁ hp₁
  let E₂ := shortExactConeIso φ₂ p₂ hex₂ hF₂ hG₂ hK₂ hi₂ hp₂
  have hn : (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) ≫ E₂.hom =
      E₁.hom ≫ (HomotopyCategory.quotient _ _).map c :=
    shortExactConeIso_natural φ₁ φ₂ p₁ p₂ hex₁ hex₂ hF₁ hG₁ hK₁ hF₂ hG₂ hK₂
      hi₁ hp₁ hi₂ hp₂ a b c H hH hc
  have hi : (HomotopyCategory.quotient _ _).map c ≫ E₂.inv =
      E₁.inv ≫ (HomotopyCategory.quotient _ _).map (mappingCone.mapOfHomotopy H) := by
    apply (cancel_mono E₂.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn]
    simp
  change (HomotopyCategory.quotient _ _).map c ≫
      (E₂.inv ≫ (mappingCone.triangleh φ₂).mor₃) =
    (E₁.inv ≫ (mappingCone.triangleh φ₁).mor₃) ≫ _
  erw [← Category.assoc, hi, Category.assoc,
    ← (mappingCone.trianglehMapOfHomotopy H).comm₃]
  exact (Category.assoc E₁.inv (mappingCone.triangleh φ₁).mor₃
    ((CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ)) 1).map
      ((HomotopyCategory.quotient _ _).map a))).symm

end ArExplicit

end

end OAI
