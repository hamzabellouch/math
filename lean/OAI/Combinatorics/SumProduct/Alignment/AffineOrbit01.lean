import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice25
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open MeasureTheory Filter Topology
end
 
end

section
 

noncomputable section
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan
variable {n : ℕ} (s r : ℕ) (hs : 1 ≤ s) (D : Pivot n) (F : Finset (Scale n))

 

def pivotOptions : Finset (Path D) := (uniform_pivot_haar s r hs D F).choose

lemma pivotOptions_nonempty : (pivotOptions s r hs D F).Nonempty :=
  (uniform_pivot_haar s r hs D F).choose_spec.1

lemma pivotOptions_paths : ∀ p∈pivotOptions s r hs D F,
    p.length=D.targets ∧ ∀ o∈p,0<o.1 :=
  (uniform_pivot_haar s r hs D F).choose_spec.2.1

def pivotModulus (B : Finset (Scale n)) : ℕ :=
  ((uniform_pivot_haar s r hs D F).choose_spec.2.2 B).choose

lemma pivotModulus_pos (B : Finset (Scale n)) : 0<pivotModulus s r hs D F B :=
  ((uniform_pivot_haar s r hs D F).choose_spec.2.2 B).choose_spec.1

 
lemma pivotOptions_mass (B : Finset (Scale n)) (q₀ : ℕ)
    (hq₀ : pivotModulus s r hs D F B∣q₀) (b : Scale n) (hb : b∈B) (τ : ℝ) :
    ChartedMassAssertion D F (pivotOptions s r hs D F) s r q₀ b τ :=
  ((uniform_pivot_haar s r hs D F).choose_spec.2.2 B).choose_spec.2 q₀ hq₀ b hb τ

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

 

namespace ClosedOrbitLift
open Topology
open scoped unitInterval

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

 
def quotientInclusion (J Λ : Subgroup G) : (J ⧸ Λ.comap J.subtype) → G ⧸ Λ :=
  Quotient.map' (fun x : J => (x:G)) (by
    intro x y h
    have hh : x⁻¹ * y ∈ Λ.comap J.subtype := QuotientGroup.leftRel_apply.mp h
    apply QuotientGroup.leftRel_apply.mpr
    exact hh)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma quotientInclusion_mk (J Λ : Subgroup G) (x : J) :
    quotientInclusion J Λ (QuotientGroup.mk x) = QuotientGroup.mk (x:G) := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma quotientInclusion_injective (J Λ : Subgroup G) :
    Function.Injective (quotientInclusion J Λ) := by
  intro x y
  induction x using Quotient.inductionOn with | h x =>
    induction y using Quotient.inductionOn with | h y =>
      intro he
      apply Quotient.sound
      change (QuotientGroup.mk (x:G) : G ⧸ Λ) = QuotientGroup.mk (y:G) at he
      have hh : (x:G)⁻¹ * (y:G) ∈ Λ := QuotientGroup.eq.mp he
      apply QuotientGroup.leftRel_apply.mpr
      exact hh

omit [IsTopologicalGroup G] in
lemma continuous_quotientInclusion (J Λ : Subgroup G) :
    Continuous (quotientInclusion J Λ) := by
  rw [(QuotientGroup.isQuotientMap_mk (Λ.comap J.subtype)).continuous_iff]
  exact QuotientGroup.continuous_mk.comp continuous_subtype_val

omit [IsTopologicalGroup G] in
lemma quotientInclusion_embedding (J Λ : Subgroup G)
    [CompactSpace (J ⧸ Λ.comap J.subtype)] [T2Space (G ⧸ Λ)] :
    IsEmbedding (quotientInclusion J Λ) :=
  ((continuous_quotientInclusion J Λ).isClosedEmbedding
    (quotientInclusion_injective J Λ)).isEmbedding

 

theorem path_stays_in_subgroup (J Λ : Subgroup G)
    [CompactSpace (J ⧸ Λ.comap J.subtype)] [T2Space (G ⧸ Λ)]
    (hΛ : IsDiscrete (Λ : Set G)) (γ : C(unitInterval,G))
    (hγ0 : γ 0 ∈ J)
    (hγ : ∀ t, ∃ x : J, QuotientGroup.mk (x:G) = (QuotientGroup.mk (γ t) : G ⧸ Λ)) :
    ∀ t, γ t ∈ J := by
  classical
  let Δ := Λ.comap J.subtype
  have hΔ : IsDiscrete (Δ : Set J) :=
    hΛ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  let π := quotientInclusion J Λ
  have hπ : IsEmbedding π := quotientInclusion_embedding J Λ
  have hex : ∀ t, ∃ x : J ⧸ Δ, π x = (QuotientGroup.mk (γ t) : G ⧸ Λ) := by
    intro t
    obtain ⟨x,hx⟩ := hγ t
    exact ⟨QuotientGroup.mk x,hx⟩
  choose q hq using hex
  have hqc : Continuous q := hπ.continuous_iff.mpr (by
    have he : π ∘ q = fun t => (QuotientGroup.mk (γ t) : G ⧸ Λ) := funext hq
    rw [he]
    exact QuotientGroup.continuous_mk.comp γ.continuous)
  have hq0 : q 0 = QuotientGroup.mk (⟨γ 0,hγ0⟩ : J) := by
    apply hπ.injective
    exact hq 0
  obtain ⟨δ,hδ,hδ0⟩ := (Δ.isQuotientCoveringMap hΔ).isCoveringMap.exists_path_lifts
    ⟨q,hqc⟩ ⟨γ 0,hγ0⟩ hq0
  have hδγ : (fun t => ((δ t : J) : G)) = γ := by
    apply (Λ.isQuotientCoveringMap hΛ).isCoveringMap.eq_of_comp_eq
      (continuous_subtype_val.comp δ.continuous) γ.continuous ?_ 0 ?_
    · funext t
      have hd := congrArg π (congrFun hδ t)
      exact hd.trans (hq t)
    · exact congrArg Subtype.val hδ0
  intro t
  rw [← congrFun hδγ t]
  exact (δ t).property

 

theorem map_mem_of_projected_orbit (J Λ : Subgroup G)
    [PathConnectedSpace J] [CompactSpace (J ⧸ Λ.comap J.subtype)]
    [T2Space (G ⧸ Λ)] (hΛ : IsDiscrete (Λ : Set G))
    (ψ : G → G) (hψ : Continuous ψ) (hψ1 : ψ 1 = 1)
    (c : J)
    (hpres : ∀ y : J, ∃ z : J,
      (QuotientGroup.mk (z:G) : G ⧸ Λ) = QuotientGroup.mk (ψ (y:G) * (c:G))) :
    ∀ y : J, ψ (y:G) ∈ J := by
  intro y
  let p := PathConnectedSpace.somePath (1:J) y
  let γ : C(unitInterval,G) := ⟨fun t => ψ (p t : G) * (c:G),
    (hψ.comp (continuous_subtype_val.comp p.continuous)).mul continuous_const⟩
  have hγ0 : γ 0 ∈ J := by
    simpa only [γ, ContinuousMap.coe_mk, Path.source, OneMemClass.coe_one, hψ1, one_mul]
      using c.property
  have ht := path_stays_in_subgroup J Λ hΛ γ hγ0 (fun t => hpres (p t)) 1
  have hyc : ψ (y:G) * (c:G) ∈ J := by simpa [γ] using ht
  simpa using J.mul_mem hyc (J.inv_mem c.property)

end ClosedOrbitLift
 
end

section
 

 

noncomputable section
namespace AffineOrbitRestriction
open CubeLocalHaar Topology
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Λ J : Subgroup G) (h σ : G)

lemma coset_eq_iff (x y : G) :
    (QuotientGroup.mk (h*x*σ) : G⧸Λ)=QuotientGroup.mk (h*y*σ) ↔
      (QuotientGroup.mk x : G⧸conjugateLattice Λ σ)=QuotientGroup.mk y := by
  simp only [QuotientGroup.eq,mem_conjugateLattice,mul_inv_rev,mul_assoc]
  simp

variable [PathConnectedSpace J]
variable [CompactSpace (J⧸(conjugateLattice Λ σ).comap J.subtype)]
variable [T2Space (G⧸conjugateLattice Λ σ)]
variable (hΛ : IsDiscrete (conjugateLattice Λ σ : Set G))
variable (S : G →* G) (hS : Continuous S)
variable (hpres : ∀ y : J,∃ z : J,
  (QuotientGroup.mk (S (h*(y:G)*σ)) : G⧸Λ)=QuotientGroup.mk (h*(z:G)*σ))

 
def basedHom : G →* G :=
  (MulAut.conj (h⁻¹*S h)).toMonoidHom.comp S

omit [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp] lemma basedHom_apply (y : G) :
    basedHom h S y=h⁻¹*S h*S y*(S h)⁻¹*h := by
  simp [basedHom,MulAut.conj_apply,mul_assoc]

include hS in
lemma basedHom_continuous : Continuous (basedHom h S) := by
  have he : (basedHom h S : G → G)=(fun y=>h⁻¹*S h*S y*(S h)⁻¹*h) :=
    funext (basedHom_apply h S)
  rw [he]
  exact ((continuous_const.mul hS).mul continuous_const).mul continuous_const

 
omit [TopologicalSpace G] [IsTopologicalGroup G] [PathConnectedSpace J]
  [CompactSpace (J⧸(conjugateLattice Λ σ).comap J.subtype)]
  [T2Space (G⧸conjugateLattice Λ σ)] in
lemma physical_based (a : J)
    (ha : (QuotientGroup.mk (S (h*σ)) : G⧸Λ)=QuotientGroup.mk (h*(a:G)*σ))
    (y : G) :
    (QuotientGroup.mk (S (h*y*σ)) : G⧸Λ)=
      QuotientGroup.mk (h*(basedHom h S y*(a:G))*σ) := by
  have hh:=congrArg (fun x : G⧸Λ=>(S h*S y*(S h)⁻¹) • x) ha
  change (QuotientGroup.mk ((S h*S y*(S h)⁻¹)*S (h*σ)) : G⧸Λ)=
    QuotientGroup.mk ((S h*S y*(S h)⁻¹)*(h*(a:G)*σ)) at hh
  convert hh using 1
  · congr 1
    simp [map_mul,mul_assoc]
  · congr 1
    simp [basedHom_apply,mul_assoc]

include hΛ hS hpres in
 

theorem exists_affine_restriction :
    ∃ a : J,∃ φ : J →* J,Continuous φ ∧
      ∀ y : J,(QuotientGroup.mk (S (h*(y:G)*σ)) : G⧸Λ)=
        QuotientGroup.mk (h*((a*φ y : J):G)*σ) := by
  obtain ⟨a,ha⟩:=hpres 1
  simp only [OneMemClass.coe_one,mul_one] at ha
  have hψ : ∀ y : J,basedHom h S (y:G)∈J := by
    apply ClosedOrbitLift.map_mem_of_projected_orbit J (conjugateLattice Λ σ) hΛ
      (basedHom h S) (basedHom_continuous h S hS) (map_one _) a
    intro y
    obtain ⟨z,hz⟩:=hpres y
    refine ⟨z,?_⟩
    apply (coset_eq_iff Λ h σ (z:G) (basedHom h S (y:G)*(a:G))).mp
    exact hz.symm.trans (physical_based Λ J h σ S a ha (y:G))
  let φ : J →* J :=
    { toFun:=fun y=>⟨(a:G)⁻¹*basedHom h S (y:G)*(a:G),
        J.mul_mem (J.mul_mem (J.inv_mem a.property) (hψ y)) a.property⟩
      map_one':=by apply Subtype.ext; simp
      map_mul':=by intro x y; apply Subtype.ext; simp [map_mul,mul_assoc] }
  refine ⟨a,φ,?_,?_⟩
  · exact ((continuous_const.mul ((basedHom_continuous h S hS).comp
      continuous_subtype_val)).mul continuous_const).subtype_mk _
  · intro y
    convert physical_based Λ J h σ S a ha (y:G) using 1
    congr 1
    simp [φ,mul_assoc]

end AffineOrbitRestriction
end
 
end

section
 

 

noncomputable section
namespace AffineOrbitRestriction
open CubeLocalHaar CubeFaces RationalLattice Topology
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (Λ J : Subgroup G) (h σ : G) (H : Filtration J) (S : G →* G) (s : ℕ)

 

def PreservesPhysicalFaces : Prop :=
  ∀ k ≤ s,∀ f∈cube (ι:=Fin (k+1)) H Finset.univ 0,
    ∃ g∈cube (ι:=Fin (k+1)) H Finset.univ 0,∀ w,
      (QuotientGroup.mk (if Fin.last k∈w then S (h*(f w:G)*σ) else h*(f w:G)*σ) : G⧸Λ)=
        QuotientGroup.mk (h*(g w:G)*σ)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
lemma point_preservation_of_faces (hH0 : H.level 0=⊤)
    (hpres : PreservesPhysicalFaces Λ J h σ H S s) (y : J) :
    ∃ z : J,(QuotientGroup.mk (S (h*(y:G)*σ)) : G⧸Λ)=
      QuotientGroup.mk (h*(z:G)*σ) := by
  have hy : y∈H.level (0+0) := by simp [hH0]
  have hf:=face_mem_cube (ι:=Fin 1) H
    (Finset.empty_subset (Finset.univ : Finset (Fin 1))) (by simpa using hy)
  obtain ⟨g,hg,he⟩:=hpres 0 (Nat.zero_le s) (face ∅ y) hf
  refine ⟨g Finset.univ,?_⟩
  simpa [face_apply] using he Finset.univ

lemma affine_faces_of_physical (a : J) (φ : J →* J)
    (hphys : ∀ y : J,(QuotientGroup.mk (S (h*(y:G)*σ)) : G⧸Λ)=
      QuotientGroup.mk (h*((a*φ y:J):G)*σ))
    (hpres : PreservesPhysicalFaces Λ J h σ H S s) :
    PreservesFaces H ((conjugateLattice Λ σ).comap J.subtype) a φ s := by
  intro k hk f hf
  obtain ⟨g,hg,he⟩:=hpres k hk f hf
  refine ⟨g,hg,?_⟩
  apply QuotientGroup.eq.mpr
  intro w
  change ((g w:G)⁻¹*(affineUpper (Fin.last k) a φ f w:J):G)∈conjugateLattice Λ σ
  apply QuotientGroup.eq.mp
  apply (coset_eq_iff Λ h σ (g w:G) (affineUpper (Fin.last k) a φ f w:J)).mp
  have hh:=he w
  by_cases hw : Fin.last k∈w
  · simp only [hw,ite_true] at hh
    simpa only [affineUpper,hw,ite_true] using hh.symm.trans (hphys (f w))
  · simpa only [affineUpper,hw,ite_false] using hh.symm

variable [PathConnectedSpace J]
variable [CompactSpace (J⧸(conjugateLattice Λ σ).comap J.subtype)]
variable [T2Space (G⧸conjugateLattice Λ σ)]

 

theorem exists_affine_face_restriction (hH0 : H.level 0=⊤)
    (hΛ : IsDiscrete (conjugateLattice Λ σ : Set G)) (hS : Continuous S)
    (hpres : PreservesPhysicalFaces Λ J h σ H S s) :
    ∃ a : J,∃ φ : J →* J,Continuous φ ∧
      (∀ y : J,(QuotientGroup.mk (S (h*(y:G)*σ)) : G⧸Λ)=
        QuotientGroup.mk (h*((a*φ y:J):G)*σ)) ∧
      PreservesFaces H ((conjugateLattice Λ σ).comap J.subtype) a φ s := by
  obtain ⟨a,φ,hφ,hphys⟩:=exists_affine_restriction Λ J h σ hΛ S hS
    (point_preservation_of_faces Λ J h σ H S s hH0 hpres)
  exact ⟨a,φ,hφ,hphys,affine_faces_of_physical Λ J h σ H S s a φ hphys hpres⟩

end AffineOrbitRestriction

end
end
end

end OAI
