import Mathlib
import OAI.Algebra.FinitisticAsymmetry.Rickard.InjectiveSums

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace LittleFinitistic.Rickard
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

abbrev productTerm (j : ℤ) := ∀ i, (K i).X j
abbrev sumTerm (j : ℤ) := Π₀ i, (K i).X j
abbrev reducedTerm (j : ℤ) := productTerm K j × sumTerm K (j+1)

def productD (j : ℤ) : productTerm K j →ₗ[R] productTerm K (j+1) :=
  LinearMap.pi (fun i => ((K i).d j (j+1)).hom.comp (LinearMap.proj i))

def sumD (j : ℤ) : sumTerm K j →ₗ[R] sumTerm K (j+1) :=
  DFinsupp.mapRange.linearMap (fun i => ((K i).d j (j+1)).hom)

@[simp] lemma productD_apply (j : ℤ) (p : productTerm K j) (i : ℕ) :
    productD K j p i = (K i).d j (j+1) (p i) := rfl
@[simp] lemma sumD_apply (j : ℤ) (s : sumTerm K j) (i : ℕ) :
    sumD K j s i = (K i).d j (j+1) (s i) := rfl

def sumInclusion (j : ℤ) : sumTerm K j →ₗ[R] productTerm K j :=
  LinearMap.pi (fun i => DFinsupp.lapply i)

@[simp] lemma sumInclusion_apply (j : ℤ) (s : sumTerm K j) (i : ℕ) :
    sumInclusion K j s i = s i := rfl

lemma d_d_apply (i : ℕ) (j : ℤ) (p : (K i).X j) :
    (K i).d (j+1) (j+1+1) ((K i).d j (j+1) p) = 0 := by
  exact ConcreteCategory.congr_hom ((K i).d_comp_d j (j+1) (j+1+1)) p

def reducedD (j : ℤ) : reducedTerm K j →ₗ[R] reducedTerm K (j+1) :=
  ((productD K j).comp (LinearMap.fst R _ _) +
    (sumInclusion K (j+1)).comp (LinearMap.snd R _ _)).prod
      (-(sumD K (j+1)).comp (LinearMap.snd R _ _))

@[simp] lemma reducedD_fst (j : ℤ) (x : reducedTerm K j) (i : ℕ) :
    (reducedD K j x).1 i = (K i).d j (j+1) (x.1 i) + x.2 i := rfl
@[simp] lemma reducedD_snd (j : ℤ) (x : reducedTerm K j) (i : ℕ) :
    (reducedD K j x).2 i = -(K i).d (j+1) (j+1+1) (x.2 i) := rfl

lemma reducedD_sq (j : ℤ) :
    (reducedD K (j+1)).comp (reducedD K j) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · ext i
    simp only [LinearMap.comp_apply, reducedD_fst, reducedD_snd, map_add,
      d_d_apply, zero_add, add_neg_cancel, LinearMap.zero_apply, Prod.fst_zero, Pi.zero_apply]
  · apply DFinsupp.ext
    intro i
    simp only [LinearMap.comp_apply, reducedD_snd, map_neg, d_d_apply, neg_zero,
      LinearMap.zero_apply, Prod.snd_zero, DFinsupp.zero_apply]

def reducedComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.of (fun j => ModuleCat.of R (reducedTerm K j))
    (fun j => ModuleCat.ofHom (reducedD K j)) (fun j => by
      apply ModuleCat.hom_ext
      exact reducedD_sq K j)

@[simp] lemma reducedComplex_d (j : ℤ) :
    (reducedComplex K).d j (j+1) = ModuleCat.ofHom (reducedD K j) := by
  simp [reducedComplex, CochainComplex.of]

lemma reducedComplex_injective [IsNoetherianRing R]
    (hK : ∀ i j, Injective ((K i).X j)) (j : ℤ) :
    Injective ((reducedComplex K).X j) := by
  let (i : ℕ) : Module.Injective R ((K i).X j) :=
    (Module.injective_iff_injective_object R _).mpr (hK i j)
  let (i : ℕ) : Module.Injective R ((K i).X (j+1)) :=
    (Module.injective_iff_injective_object R _).mpr (hK i (j+1))
  let := dfinsupp_injective (R := R) (fun i => (K i).X (j+1))
  let := prod_injective (R := R) (productTerm K j) (sumTerm K (j+1))
  apply Module.injective_object_of_injective_module

lemma reduced_hom_exact (D : ModuleCat.{u} R) [Module.Finite R D]
    (j : ℤ) (hex : ∃ s : Finset ℕ, ∀ i ∉ s, ∀ f : D ⟶ (K i).X (j+1),
      f ≫ (K i).d (j+1) (j+1+1) = 0 → ∃ g : D ⟶ (K i).X j,
      g ≫ (K i).d j (j+1) = f)
    (f : D ⟶ (reducedComplex K).X (j+1))
    (hf : f ≫ (reducedComplex K).d (j+1) (j+1+1) = 0) :
    ∃ g : D ⟶ (reducedComplex K).X j,
      g ≫ (reducedComplex K).d j (j+1) = f := by
  classical
  let a : ∀ i, D →ₗ[R] (K i).X (j+1) := fun i =>
    (LinearMap.proj i).comp ((LinearMap.fst R _ _).comp f.hom)
  let b : D →ₗ[R] sumTerm K (j+1+1) := (LinearMap.snd R _ _).comp f.hom
  obtain ⟨s, hs⟩ := finite_support_map (R := R) _ D b
  obtain ⟨t, ht⟩ := hex
  have hcycle (i : ℕ) (x : D) :
      (K i).d (j+1) (j+1+1) (a i x) + b x i = 0 := by
    have h := congrArg (fun z : reducedTerm K (j+1+1) => z.1 i)
      (ConcreteCategory.congr_hom hf x)
    rw [reducedComplex_d] at h
    change (reducedD K (j+1) (f x)).1 i = 0 at h
    exact h
  have he (i : ℕ) : ∃ c : D →ₗ[R] (K i).X j,
      i ∉ s ∪ t → ((K i).d j (j+1)).hom.comp c = a i := by
    by_cases hi : i ∈ s ∪ t
    · exact ⟨0, fun h => (h hi).elim⟩
    · have his : i ∉ s := fun h => hi (Finset.mem_union_left _ h)
      have hit : i ∉ t := fun h => hi (Finset.mem_union_right _ h)
      obtain ⟨c, hc⟩ := ht i hit (ModuleCat.ofHom (a i)) (by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
          ModuleCat.hom_zero, LinearMap.zero_apply, hs x i his, add_zero] using hcycle i x)
      exact ⟨c.hom, fun _ => congrArg ModuleCat.Hom.hom hc⟩
  choose c hc using he
  let q : D →ₗ[R] productTerm K j := LinearMap.pi c
  let v : ∀ i, D →ₗ[R] (K i).X (j+1) := fun i => a i - ((K i).d j (j+1)).hom.comp (c i)
  let w : D →ₗ[R] sumTerm K (j+1) := ∑ i ∈ s ∪ t, (DFinsupp.lsingle i).comp (v i)
  have hw (x : D) (i : ℕ) : w x i = a i x - (K i).d j (j+1) (c i x) := by
    by_cases hi : i ∈ s ∪ t
    · simp [w, LinearMap.sum_apply, DFinsupp.single_apply, hi, v]
    · have hci : (K i).d j (j+1) (c i x) = a i x := LinearMap.congr_fun (hc i hi) x
      simp [w, LinearMap.sum_apply, DFinsupp.single_apply, hi, hci, v]
  let g : D →ₗ[R] reducedTerm K j := q.prod w
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · ext i
    rw [reducedComplex_d]
    change (reducedD K j (g x)).1 i = a i x
    rw [reducedD_fst]
    change (K i).d j (j+1) (c i x) + w x i = a i x
    rw [hw]
    abel
  · apply DFinsupp.ext
    intro i
    rw [reducedComplex_d]
    change (reducedD K j (g x)).2 i = b x i
    rw [reducedD_snd]
    change -(K i).d (j+1) (j+1+1) (w x i) = b x i
    rw [hw, map_sub, d_d_apply, sub_zero]
    exact neg_eq_of_add_eq_zero_right (hcycle i x)

lemma reduced_isStrictlyGE
    (hK : ∀ i j, j < 0 → IsZero ((K i).X j)) :
    (reducedComplex K).IsStrictlyGE (-1) := by
  apply (CochainComplex.isStrictlyGE_iff _ _).mpr
  intro j hj
  apply ModuleCat.isZero_iff_subsingleton.mpr
  let (i : ℕ) : Subsingleton ((K i).X j) :=
    ModuleCat.isZero_iff_subsingleton.mp (hK i j (by omega))
  let (i : ℕ) : Subsingleton ((K i).X (j+1)) :=
    ModuleCat.isZero_iff_subsingleton.mp (hK i (j+1) (by omega))
  change Subsingleton (reducedTerm K j)
  infer_instance

lemma reduced_not_exact_zero
    (hK : ∀ i j, j < 0 → IsZero ((K i).X j))
    (hnon : ∀ i, ∃ x : (K i).X 0, x ≠ 0 ∧ (K i).d 0 1 x = 0) :
    ¬ (reducedComplex K).ExactAt 0 := by
  classical
  choose x hxne hxd using hnon
  let p : reducedTerm K 0 := (x, 0)
  have hp : (reducedComplex K).d 0 1 p = 0 := by
    rw [show (1 : ℤ)=0+1 from rfl, reducedComplex_d]
    apply Prod.ext
    · ext i
      change (K i).d 0 1 (x i) + 0 = 0
      simpa only [add_zero] using hxd i
    · apply DFinsupp.ext
      intro i
      change -(K i).d 1 2 0 = 0
      rw [map_zero, neg_zero]
  intro hex
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff ((reducedComplex K).sc' (-1) 0 1)).mp
    ((HomologicalComplex.exactAt_iff' _ _ _ _ (by simp) (by simp)).mp hex) p hp
  change (reducedComplex K).d (-1) 0 y = p at hy
  have hd : (reducedComplex K).d (-1) 0 = ModuleCat.ofHom (reducedD K (-1)) :=
    reducedComplex_d K (-1)
  rw [hd] at hy
  change reducedTerm K (-1) at y
  obtain ⟨i, hi⟩ := Infinite.exists_notMem_finset y.2.support
  have hy0 : y.2 i = 0 := DFinsupp.notMem_support_iff.mp hi
  have hy1 : y.1 i = 0 :=
    (ModuleCat.isZero_iff_subsingleton.mp (hK i (-1) (by omega))).elim _ _
  have h := congrArg (fun z : reducedTerm K 0 => z.1 i) hy
  change (reducedD K (-1) y).1 i = x i at h
  rw [reducedD_fst, hy0, hy1, map_zero, zero_add] at h
  exact hxne i h.symm

local instance reducedProductsHasDerivedCategory : HasDerivedCategory (ModuleCat.{u} R) :=
  HasDerivedCategory.standard _

lemma not_isZero_Q_of_not_exact_zero (L : CochainComplex (ModuleCat.{u} R) ℤ)
    (h : ¬ L.ExactAt 0) : ¬ IsZero (DerivedCategory.Q.obj L) := by
  intro hz
  apply h
  apply (HomologicalComplex.exactAt_iff_isZero_homology L 0).mpr
  exact ((DerivedCategory.homologyFunctor (ModuleCat R) 0).map_isZero hz).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) 0).app L).symm

end LittleFinitistic.Rickard

end
end

end OAI
