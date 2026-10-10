import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CubeTaylor02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open scoped BigOperators Topology commutatorElement
end
end
 

 
section

 

noncomputable section
open scoped Pointwise commutatorElement
namespace CompactGroupProducts
variable {G K : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
omit [IsTopologicalGroup G] [IsTopologicalGroup K] in
lemma HasCompactReps.map_into {H Γ : Subgroup G} (h : HasCompactReps H Γ)
    (f : G →* K) (hf : Continuous f) (Λ : Subgroup K) (hΓ : Γ ≤ Λ.comap f) :
    HasCompactReps (H.map f) Λ := by
  rcases h with ⟨C, hC, hCH, hrep⟩
  refine ⟨f '' C, hC.image hf, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, hCH hc, rfl⟩
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨c, hc, hcΓ⟩ := hrep g hg
    refine ⟨f c, ⟨c, hc, rfl⟩, ?_⟩
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hΓ hcΓ

 
lemma HasCompactReps.sup {H J Γ : Subgroup G}
    (hH : HasCompactReps H Γ) (hJ : HasCompactReps J Γ)
    (hnormal : H ≤ Subgroup.normalizer J) : HasCompactReps (H ⊔ J) Γ := by
  rcases hH with ⟨C, hC, hCH, hrepH⟩
  rcases hJ with ⟨D, hD, hDJ, hrepJ⟩
  refine ⟨C * D, hC.mul hD, ?_, ?_⟩
  · rintro _ ⟨c, hc, d, hd, rfl⟩
    exact (H ⊔ J).mul_mem (Subgroup.mem_sup_left (hCH hc))
      (Subgroup.mem_sup_right (hDJ hd))
  · intro g hg
    change g ∈ (↑(H ⊔ J) : Set G) at hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnormal] at hg
    rcases hg with ⟨h, hh, j, hj, rfl⟩
    obtain ⟨c, hc, hcΓ⟩ := hrepH h hh
    let δ := c⁻¹ * h
    have hδH : δ ∈ H := H.mul_mem (H.inv_mem (hCH hc)) hh
    have hδΓ : δ ∈ Γ := hcΓ
    have hvJ : δ * j * δ⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (hnormal hδH) j).mp hj
    obtain ⟨d, hd, hdΓ⟩ := hrepJ _ hvJ
    refine ⟨c * d, ⟨c, hc, d, hd, rfl⟩, ?_⟩
    have heq : (c * d)⁻¹ * (h * j) = (d⁻¹ * (δ * j * δ⁻¹)) * δ := by
      dsimp [δ]
      group
    rw [heq]
    exact Γ.mul_mem hdΓ hδΓ

end CompactGroupProducts
namespace CompactGroupProducts
open Topology
variable {G : Type*} [Group G] [TopologicalSpace G]

 

lemma HasCompactReps.compactSpace {H Γ : Subgroup G} (h : HasCompactReps H Γ) :
    CompactSpace (H ⧸ Γ.comap H.subtype) := by
  obtain ⟨C,hC,hCH,hr⟩ := h
  let D : Set H := Subtype.val ⁻¹' C
  have hD : IsCompact D := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' D = C := by
      ext x
      exact ⟨fun ⟨y,hy,he⟩ => he ▸ hy,fun hx => ⟨⟨x,hCH hx⟩,hx,rfl⟩⟩
    rwa [he]
  have he : QuotientGroup.mk (s := Γ.comap H.subtype) '' D = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    induction x using Quotient.inductionOn with | h x =>
      obtain ⟨c,hc,hcx⟩ := hr x x.property
      exact ⟨⟨c,hCH hc⟩,hc,QuotientGroup.eq.mpr hcx⟩
  exact ⟨he ▸ hD.image QuotientGroup.continuous_mk⟩

end CompactGroupProducts
namespace CubeFaces
variable {G ι : Type*} [Group G] [DecidableEq ι]
lemma cube_empty (H : Filtration G) (k : ℕ) :
    cube H (∅ : Finset ι) k = (H.level k).map (face ∅) := by
  apply le_antisymm
  · refine iSup_le fun D => iSup_le fun hD => ?_
    have he : D = ∅ := Finset.subset_empty.mp hD
    subst D
    simp only [Finset.card_empty, zero_add]
    exact le_rfl
  · intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact face_mem_cube H (Finset.empty_subset _) (by simpa using hg)

lemma map_upper_cube_le (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ) :
    (cube H I (k + 1)).map (upper a) ≤ cube H (insert a I) k := by
  rw [map_upper_cube]
  refine iSup_le fun E => iSup_le fun hE => ?_
  rintro f ⟨g, hg, rfl⟩
  apply face_mem_cube H (Finset.insert_subset_insert a hE)
  apply H.antitone _ hg
  have := Finset.card_insert_le a E
  omega

lemma cube_insert_eq (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ) :
    cube H (insert a I) k = cube H I k ⊔ (cube H I (k + 1)).map (upper a) := by
  apply le_antisymm (cube_insert_le H a I k)
  exact sup_le (cube_mono H (Finset.subset_insert a I) k) (map_upper_cube_le H a I k)

 
def latticeArrays (Γ : Subgroup G) : Subgroup (Finset ι → G) where
  carrier := {f | ∀ v, f v ∈ Γ}
  one_mem' := fun _ => Γ.one_mem
  mul_mem' hf hg := fun v => Γ.mul_mem (hf v) (hg v)
  inv_mem' hf := fun v => Γ.inv_mem (hf v)

section CompactCubes
variable [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
lemma continuous_face (D : Finset ι) : Continuous (face D : G → (Finset ι → G)) := by
  apply continuous_pi
  intro v
  by_cases hD : D ⊆ v
  · simp only [face_apply, hD, ite_true]
    exact continuous_id
  · simpa only [face_apply, hD, ite_false] using
      (continuous_const : Continuous (fun _ : G => (1 : G)))

omit [IsTopologicalGroup G] in
lemma continuous_upper (a : ι) : Continuous (upper a : (Finset ι → G) → (Finset ι → G)) := by
  apply continuous_pi
  intro v
  by_cases ha : a ∈ v
  · simpa only [upper, MonoidHom.coe_mk, OneHom.coe_mk, ha, ite_true] using
      (continuous_apply v : Continuous (fun f : Finset ι → G => f v))
  · simpa only [upper, MonoidHom.coe_mk, OneHom.coe_mk, ha, ite_false] using
      (continuous_const : Continuous (fun _ : Finset ι → G => (1 : G)))

 

theorem cube_hasCompactReps (H : Filtration G) (Γ : Subgroup G)
    (hrep : ∀ k, CompactGroupProducts.HasCompactReps (H.level k) Γ)
    (I : Finset ι) (k : ℕ) :
    CompactGroupProducts.HasCompactReps (cube H I k) (latticeArrays Γ) := by
  induction I using Finset.induction_on generalizing k with
  | empty =>
    rw [cube_empty]
    apply (hrep k).map_into (face ∅) (continuous_face ∅) (latticeArrays Γ)
    intro g hg v
    simpa only [face_apply, Finset.empty_subset, ite_true] using hg
  | @insert a I ha ih =>
    rw [cube_insert_eq]
    apply (ih k).sup _ (cube_le_normalizer_upper H a I k)
    apply (ih (k + 1)).map_into (upper a) (continuous_upper a) (latticeArrays Γ)
    intro f hf v
    change (if a ∈ v then f v else 1) ∈ Γ
    split_ifs
    · exact hf v
    · exact Γ.one_mem

end CompactCubes

end CubeFaces

namespace CompactGroupProducts
open Topology
variable {G : Type*} [Group G] [TopologicalSpace G]

 

lemma HasCompactReps.comap_subtype {A K Γ : Subgroup G}
    (h : HasCompactReps A Γ) (hAK : A ≤ K) :
    HasCompactReps (A.comap K.subtype) (Γ.comap K.subtype) := by
  obtain ⟨C,hC,hCA,hr⟩ := h
  let D : Set K := Subtype.val ⁻¹' C
  have hD : IsCompact D := by
    apply IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' D = C := by
      ext x
      exact ⟨fun ⟨y,hy,he⟩ => he ▸ hy,fun hx => ⟨⟨x,hAK (hCA hx)⟩,hx,rfl⟩⟩
    rwa [he]
  refine ⟨D,hD,fun x hx => hCA hx,?_⟩
  intro x hx
  obtain ⟨c,hc,hcx⟩ := hr x hx
  exact ⟨⟨c,hAK (hCA hc)⟩,hc,hcx⟩

lemma HasCompactReps.top_comap_subtype {K Γ : Subgroup G}
    (h : HasCompactReps K Γ) : HasCompactReps ⊤ (Γ.comap K.subtype) := by
  have he : K.comap K.subtype = ⊤ := by ext x; simp
  simpa only [he] using h.comap_subtype (le_refl K)

end CompactGroupProducts
end
end
 

 
section

noncomputable section
open scoped Topology commutatorElement
namespace CubeMaxFiltration
open CubeFaces CompactGroupProducts
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

 

def clamp (H : Filtration G) (k : ℕ) : Filtration G where
  level j := H.level (max k j)
  antitone := fun i j hij => H.antitone (max_le_max_left k hij)
  commutator_le i j := (H.commutator_le _ _).trans (H.antitone (by omega))

omit [TopologicalSpace G] [IsTopologicalGroup G] [Fintype ι] in
lemma level_eq_clamp_cube [TopologicalSpace G] [IsTopologicalGroup G] [Fintype ι]
    (H : Filtration G) (I : Finset ι) (k : ℕ) :
    level H I k=cube (clamp H k) I 0 := by
  simp only [level,cube,clamp,Nat.add_zero]

 

theorem hasCompactReps_level (H : Filtration G) (Γ : Subgroup G)
    (hr : ∀ j,HasCompactReps (H.level j) Γ) (k : ℕ) :
    HasCompactReps ((filtration H (Finset.univ : Finset ι)).level k)
      (CubeLocalHaar.cubeLattice H Γ) := by
  have hh := cube_hasCompactReps (clamp H k) Γ (fun j => hr (max k j))
    (Finset.univ : Finset ι) 0
  rw [←level_eq_clamp_cube] at hh
  exact hh.comap_subtype (by
    rw [←level_zero]
    exact antitone H Finset.univ (Nat.zero_le k))

end CubeMaxFiltration

namespace CubeLocalHaar
open CubeFaces CompactGroupProducts MeasureTheory
variable {G ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Fintype ι] [DecidableEq ι]

omit [IsTopologicalGroup G] in
lemma cubeLattice_discrete [IsTopologicalGroup G] (H : Filtration G) (Γ : Subgroup G)
    (hΓ : IsDiscrete (Γ:Set G)) :
    IsDiscrete (cubeLattice (ι := ι) H Γ : Set (cube H (Finset.univ : Finset ι) 0)) := by
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  let φ : cubeLattice H Γ→(Finset ι→Γ) := fun x w => ⟨(x.val:Finset ι→G) w,x.property w⟩
  have hc : Continuous φ := by
    apply continuous_pi
    intro w
    exact ((continuous_apply w).comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  have hi : Function.Injective φ := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    funext w
    exact congrArg Subtype.val (congrFun he w)
  let : DiscreteTopology (cubeLattice H Γ) := DiscreteTopology.of_continuous_injective hc hi
  exact isDiscrete_iff_discreteTopology.mpr inferInstance

variable [T2Space G] [SecondCountableTopology G]

 

theorem existsUnique_cubeHaar (H : Filtration G) (h01 : H.level 0=H.level 1)
    (s : ℕ) (hs : H.level (s+1)=⊥) (Γ : Subgroup G)
    (hr : ∀ j,HasCompactReps (H.level j) Γ) (hΓ : IsDiscrete (Γ:Set G))
    [MeasurableSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)]
    [BorelSpace ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)] :
    ∃! μ : ProbabilityMeasure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ),
      SMulInvariantMeasure (cube H (Finset.univ : Finset ι) 0)
        ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)
        (μ : Measure ((cube H (Finset.univ : Finset ι) 0)⧸cubeLattice H Γ)) := by
  let : SecondCountableTopology (cube H (Finset.univ : Finset ι) 0) :=
    Topology.IsInducing.subtypeVal.secondCountableTopology
  let K := CubeMaxFiltration.filtration H (Finset.univ : Finset ι)
  apply RationalNilmanifoldMeasure.existsUnique_invariant (s+1) (cubeLattice H Γ) K.level
    (CubeMaxFiltration.filtration_zero H Finset.univ)
    (CubeMaxFiltration.filtration_bot H Finset.univ hs)
  · intro i g x hx
    have hg : g∈K.level 1 := by rw [CubeMaxFiltration.filtration_one H Finset.univ h01]; trivial
    simpa only [Nat.add_comm] using K.commutator_le 1 i (Subgroup.commutator_mem_commutator hg hx)
  · exact fun i => CubeMaxFiltration.hasCompactReps_level H Γ hr i
  · exact cubeLattice_discrete H Γ hΓ

end CubeLocalHaar

end
end
end
end
end

end OAI
