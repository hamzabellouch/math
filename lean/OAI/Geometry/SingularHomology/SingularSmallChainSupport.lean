import OAI.Geometry.SingularHomology.SingularChainsFinsupp
import OAI.Geometry.SingularHomology.SingularSmallChains

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial Opposite

namespace Problem340

theorem simplicialChainMap_finsupp {S T : SSet} (f : S ⟶ T) (n : ℕ)
    (z : S _⦋n⦌ →₀ ℝ) :
    ((SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)).f n).hom
      (simplicialChainsFinsuppEquiv S n z) =
    simplicialChainsFinsuppEquiv T n
      (Finsupp.lmapDomain ℝ ℝ (f.app (op ⦋n⦌)) z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single σ r =>
    simp only [simplicialChainsFinsuppEquiv_single, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]
    exact congrArg (fun k : ModuleCat.of ℝ ℝ ⟶
      (T.chainComplex (ModuleCat.of ℝ ℝ)).X n => k.hom r)
      (SSet.ι_chainComplexMap_f S T f (ModuleCat.of ℝ ℝ) σ)

theorem finsupp_range_lmapDomain_eq_supported {α β : Type*} (f : α → β) :
    LinearMap.range (Finsupp.lmapDomain ℝ ℝ f) =
      Finsupp.supported ℝ ℝ (Set.range f) := by
  simpa only [Finsupp.supported_univ, Submodule.map_top, Set.image_univ] using
    (Finsupp.lmapDomain_supported ℝ ℝ f (Set.univ : Set α))

theorem mem_range_simplicialChainMap_iff {S T : SSet} (f : S ⟶ T) (n : ℕ)
    (z : (T.chainComplex (ModuleCat.of ℝ ℝ)).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap f (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (simplicialChainsFinsuppEquiv T n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.range (f.app (op ⦋n⦌))) := by
  rw [← finsupp_range_lmapDomain_eq_supported]
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨v, rfl⟩ := (simplicialChainsFinsuppEquiv S n).surjective w
    refine ⟨v, ?_⟩
    rw [simplicialChainMap_finsupp, LinearEquiv.symm_apply_apply]
  · rintro ⟨v, hv⟩
    refine ⟨simplicialChainsFinsuppEquiv S n v, ?_⟩
    rw [simplicialChainMap_finsupp, hv, LinearEquiv.apply_symm_apply]

theorem mem_range_subcomplex_chainMap_iff (S : SSet) (K : S.Subcomplex) (n : ℕ)
    (z : (S.chainComplex (ModuleCat.of ℝ ℝ)).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap K.ι (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (simplicialChainsFinsuppEquiv S n).symm z ∈
        Finsupp.supported ℝ ℝ (K.obj (op ⦋n⦌)) := by
  rw [mem_range_simplicialChainMap_iff]
  change _ ∈ Finsupp.supported ℝ ℝ (Set.range (Subtype.val : K.obj (op ⦋n⦌) → S _⦋n⦌)) ↔ _
  rw [Subtype.range_val]

theorem finsupp_domLCongr_mem_supported_iff {α β : Type*} (e : α ≃ β)
    (z : α →₀ ℝ) (t : Set β) :
    (Finsupp.domLCongr e : (α →₀ ℝ) ≃ₗ[ℝ] (β →₀ ℝ)) z ∈
      Finsupp.supported ℝ ℝ t ↔
    z ∈ Finsupp.supported ℝ ℝ (e ⁻¹' t) := by
  rw [Finsupp.mem_supported', Finsupp.mem_supported']
  constructor
  · intro h a ha
    have hh := h (e a) ha
    simpa using hh
  · intro h b hb
    have hh := h (e.symm b) (by simpa using hb)
    simpa using hh

theorem mem_range_singularSubcomplex_iff {X : Type} [TopologicalSpace X]
    (K : (TopCat.toSSet.obj (TopCat.of X)).Subcomplex) (n : ℕ)
    (z : (realSingularChainComplex X).X n) :
    z ∈ LinearMap.range ((SSet.chainComplexMap K.ι (ModuleCat.of ℝ ℝ)).f n).hom ↔
      (singularChainsFinsuppEquiv X n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.ofPred (fun σ : RealSingularSimplex X n =>
          (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)).symm σ ∈ K.obj (op ⦋n⦌))) := by
  refine (mem_range_subcomplex_chainMap_iff _ K n z).trans ?_
  change _ ↔ Finsupp.domLCongr (R := ℝ) (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌))
    ((simplicialChainsFinsuppEquiv (TopCat.toSSet.obj (TopCat.of X)) n).symm z) ∈ _
  rw [finsupp_domLCongr_mem_supported_iff]
  simp only [Set.preimage_ofPred_eq, Equiv.symm_apply_apply]
  rfl

namespace SingularSmallChains

theorem mem_range_inclusion_iff_supported {X : Type} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (n : ℕ)
    (z : (realSingularChainComplex X).X n) :
    z ∈ LinearMap.range ((inclusion U).f n).hom ↔
      (singularChainsFinsuppEquiv X n).symm z ∈
        Finsupp.supported ℝ ℝ (Set.ofPred (fun σ : RealSingularSimplex X n =>
          ∃ i, Set.range σ ⊆ U i)) := by
  refine (mem_range_singularSubcomplex_iff (small U) n z).trans ?_
  simp only [mem_small, Equiv.apply_symm_apply]

theorem mem_range_inclusion_iff_support {X : Type} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (n : ℕ)
    (z : (realSingularChainComplex X).X n) :
    z ∈ LinearMap.range ((inclusion U).f n).hom ↔
      ∀ σ ∈ ((singularChainsFinsuppEquiv X n).symm z).support,
        ∃ i, Set.range σ ⊆ U i := by
  rw [mem_range_inclusion_iff_supported, Finsupp.mem_supported]
  rfl

theorem exists_chain_of_finsupp_support {X : Type} [TopologicalSpace X]
    {ι : Type*} (U : ι → Set X) (n : ℕ) (z : RealSingularChains X n)
    (hz : ∀ σ ∈ z.support, ∃ i, Set.range σ ⊆ U i) :
    ∃ w : (chains U).X n,
      ((inclusion U).f n).hom w = singularChainsFinsuppEquiv X n z := by
  apply (mem_range_inclusion_iff_support U n _).mpr
  simpa only [LinearEquiv.symm_apply_apply] using hz

abbrev supportedChains {X : Type} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (n : ℕ) :=
      Finsupp.supported ℝ ℝ (Set.ofPred (fun σ : RealSingularSimplex X n =>
    ∃ i, Set.range σ ⊆ U i))

def toSupportedChains {X : Type} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (n : ℕ) : (chains U).X n →ₗ[ℝ] supportedChains U n :=
  LinearMap.codRestrict (supportedChains U n)
    ((singularChainsFinsuppEquiv X n).symm.toLinearMap.comp ((inclusion U).f n).hom)
    (fun w => (mem_range_inclusion_iff_supported U n _).mp ⟨w, rfl⟩)

def chainsEquivSupported {X : Type} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (n : ℕ) : (chains U).X n ≃ₗ[ℝ] supportedChains U n :=
  LinearEquiv.ofBijective (toSupportedChains U n) (by
    constructor
    · intro x y h
      apply inclusion_f_injective U n
      apply (singularChainsFinsuppEquiv X n).symm.injective
      exact congrArg Subtype.val h
    · intro z
      have hz : singularChainsFinsuppEquiv X n z.val ∈
          LinearMap.range ((inclusion U).f n).hom := by
        apply (mem_range_inclusion_iff_supported U n _).mpr
        simpa only [LinearEquiv.symm_apply_apply] using z.property
      obtain ⟨w, hw⟩ := hz
      refine ⟨w, Subtype.ext ?_⟩
      change (singularChainsFinsuppEquiv X n).symm (((inclusion U).f n).hom w) = z.val
      rw [hw, LinearEquiv.symm_apply_apply])

@[simp]
theorem chainsEquivSupported_apply_val {X : Type} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (n : ℕ) (w : (chains U).X n) :
    (chainsEquivSupported U n w).val =
      (singularChainsFinsuppEquiv X n).symm (((inclusion U).f n).hom w) := rfl

@[simp]
theorem inclusion_chainsEquivSupported_symm {X : Type} [TopologicalSpace X] {ι : Type*}
    (U : ι → Set X) (n : ℕ) (z : supportedChains U n) :
    ((inclusion U).f n).hom ((chainsEquivSupported U n).symm z) =
      singularChainsFinsuppEquiv X n z.val := by
  apply (singularChainsFinsuppEquiv X n).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  exact congrArg Subtype.val ((chainsEquivSupported U n).apply_symm_apply z)

end SingularSmallChains

end Problem340

end

end OAI
