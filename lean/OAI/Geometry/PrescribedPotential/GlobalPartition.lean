import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev
import OAI.Geometry.PrescribedPotential.ParametrixAtlas

namespace OAI

/-! Global Partition. -/

section

noncomputable section
open Set Filter Topology MeasureTheory Manifold IsManifold
open scoped ContDiff SchwartzMap Classical

namespace GlobalElliptic
open Anticanonical EllipticKernel SobolevChart SourceSmooth
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

 
def Smooth.ofReal (f : SmoothRealFunction A) : Smooth A :=
  ⟨fun x => (f.value x : ℂ), fun i => by
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    exact (f.smooth i).comp (coordinateEquiv d).contDiff.contDiffOn
      (fun y hy => by simpa using hy)⟩

@[simp] lemma Smooth.ofReal_apply (f : SmoothRealFunction A) (x : X) :
    Smooth.ofReal f x = (f.value x : ℂ) := rfl

lemma Smooth.ofReal_tsupport (f : SmoothRealFunction A) :
    tsupport (Smooth.ofReal f : X → ℂ) = tsupport f.value := by
  apply congrArg closure
  ext x
  simp [Function.mem_support]

 

structure Localizers (A : ComplexAtlas d X) (ι : Type*) [Fintype ι] where
  index : ι → Fin A.count
  weight : ι → Smooth A
  support_sub : ∀ i, tsupport (weight i : X → ℂ) ⊆ (A.euclideanChart (index i)).source
  sum_one : ∀ x, ∑ i, weight i x = 1

namespace Localizers
variable {ι : Type*} [Fintype ι] (D : Localizers A ι)

 
def coordinates [T2Space X] [CompactSpace X] (s : ℝ) :
    Smooth A →ₗ[ℝ] (ι → L2 (EC d)) where
  toFun f i := schwartzCoord s (localize A (D.index i) (D.weight i) (D.support_sub i) f)
  map_add' f h := by
    funext i
    change schwartzCoord s (localizeLinear A (D.index i) (D.weight i) (D.support_sub i) (f + h)) = _
    rw [map_add, schwartzCoord_add]
    rfl
  map_smul' c f := by
    funext i
    apply realize_injective s
    change realize s (schwartzCoord s (localizeLinear A (D.index i) (D.weight i) (D.support_sub i) (c • f))) =
      realize s (c • schwartzCoord s (localizeLinear A (D.index i) (D.weight i) (D.support_sub i) f))
    rw [map_smul, realize_schwartzCoord]
    change SchwartzMap.toTemperedDistributionCLM _ _ volume (c • localizeLinear A (D.index i) (D.weight i) (D.support_sub i) f) = _
    rw [ContinuousLinearMap.map_smul_of_tower, ContinuousLinearMap.map_smul_of_tower, realize_schwartzCoord]

lemma coordinates_injective [T2Space X] [CompactSpace X] (s : ℝ) :
    Function.Injective (D.coordinates s) := by
  intro f h heq
  apply Smooth.ext
  intro x
  have hi (i : ι) : D.weight i x * f x = D.weight i x * h x := by
    have ht := congrArg (fun v : ι → L2 (EC d) => realize s (v i)) heq
    dsimp only [coordinates, LinearMap.coe_mk, AddHom.coe_mk] at ht
    rw [realize_schwartzCoord, realize_schwartzCoord] at ht
    have he := schwartz_distribution_injective ht
    by_cases hx : x ∈ (A.euclideanChart (D.index i)).source
    · have htx := (A.euclideanChart (D.index i)).mapsTo hx
      have hh := congrArg (fun u : 𝓢(EC d, ℂ) => u (A.euclideanChart (D.index i) x)) he
      simpa only [localize_apply, localizeFun_apply A _ _ htx,
        (A.euclideanChart (D.index i)).left_inv hx] using hh
    · have hz : D.weight i x = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hx (D.support_sub i ht))
      simp [hz]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hi i)
  simpa only [← Finset.sum_mul, D.sum_one, one_mul] using hsum

 

def closedSpace [T2Space X] [CompactSpace X] (s : ℝ) :
    Submodule ℝ (ι → L2 (EC d)) := (LinearMap.range (D.coordinates s)).topologicalClosure

abbrev Sobolev [T2Space X] [CompactSpace X] (s : ℝ) := ↥(D.closedSpace s)

instance [T2Space X] [CompactSpace X] (s : ℝ) : CompleteSpace (D.Sobolev s) :=
  (LinearMap.range (D.coordinates s)).isClosed_topologicalClosure.completeSpace_coe

 
def embed [T2Space X] [CompactSpace X] (s : ℝ) : Smooth A →ₗ[ℝ] D.Sobolev s :=
  (D.coordinates s).codRestrict (D.closedSpace s)
    (fun f => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ f))

lemma embed_injective [T2Space X] [CompactSpace X] (s : ℝ) :
    Function.Injective (D.embed s) := by
  intro f h hh
  exact D.coordinates_injective s (congrArg Subtype.val hh)

lemma embed_dense [T2Space X] [CompactSpace X] (s : ℝ) : DenseRange (D.embed s) := by
  change Dense (Set.range (D.embed s))
  rw [Subtype.dense_iff, ← Set.range_comp]
  change closure (Set.range (D.coordinates s)) ⊆ closure (Set.range (D.coordinates s))
  exact subset_rfl

end Localizers

 

theorem exists_patch_localizers [T2Space X] [CompactSpace X] (g : KaehlerMetric A) :
    ∃ (S : Finset (ParametrixPatch g)) (D : Localizers A S),
      (∀ p : S, D.index p = p.val.index) ∧
      (∀ p : S, tsupport (D.weight p : X → ℂ) ⊆ p.val.source) := by
  obtain ⟨S, hS⟩ := ParametrixPatch.finite_cover g
  let := A.chartedSpace
  let := A.isManifold
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, Coordinates d) (s := (Set.univ : Set X)) isClosed_univ
    (fun p : S => p.val.source) (fun p => p.val.isOpen_source) (by
      intro x _
      obtain ⟨p, hp, hx⟩ := hS x
      exact mem_iUnion.mpr ⟨⟨p, hp⟩, hx⟩)
  let f (p : S) : SmoothRealFunction A :=
    ⟨ρ p, (A.contMDiff_iff (ρ p)).mp (ρ p).contMDiff⟩
  let D : Localizers A S :=
    { index := fun p => p.val.index
      weight := fun p => Smooth.ofReal (f p)
      support_sub := by
        intro p
        rw [Smooth.ofReal_tsupport]
        exact (hρ p).trans (fun x hx => hx.1)
      sum_one := by
        intro x
        change (∑ p : S, ((ρ p x : ℝ) : ℂ)) = 1
        rw [← Complex.ofReal_sum]
        exact_mod_cast (show ∑ p : S, ρ p x = 1 by
          simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ x)) }
  refine ⟨S, D, fun _ => rfl, ?_⟩
  intro p
  change tsupport (Smooth.ofReal (f p) : X → ℂ) ⊆ _
  rw [Smooth.ofReal_tsupport]
  exact hρ p

end GlobalElliptic

end
end

end OAI
