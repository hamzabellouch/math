import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.CoveringSubspace01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open Topology
open scoped unitInterval
namespace CoveringSubspace
open CompactGroupProducts
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

 

theorem subgroup_orbit_covering (H Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (hrep : HasCompactReps H Γ) :
    IsCoveringMap (imageRestrict (QuotientGroup.mk (s := Γ)) (H : Set G)) := by
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  have hquot : Topology.IsQuotientMap
      (imageRestrict (QuotientGroup.mk (s := Γ)) (H : Set G)) := by
    obtain ⟨C, hC, hCH, hr⟩ := hrep
    apply isQuotientMap_imageRestrict QuotientGroup.continuous_mk hC hCH
    intro g hg
    obtain ⟨c, hc, hcΓ⟩ := hr g hg
    exact ⟨c, hc, QuotientGroup.eq.mpr hcΓ⟩
  have hdisc : IsDiscrete ((Γ.comap H.subtype : Subgroup H) : Set H) :=
    hΓ.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  apply (hquot.isQuotientCoveringMap_of_subgroupOp (E := H) (Γ.comap H.subtype) hdisc ?_).isCoveringMap
  intro x y
  constructor
  · intro hxy
    exact (QuotientGroup.eq (s := Γ) (a := x.val) (b := y.val)).mp
      (congrArg Subtype.val hxy)
  · intro hxy
    exact Subtype.ext ((QuotientGroup.eq (s := Γ) (a := x.val) (b := y.val)).mpr hxy)

 

theorem subgroup_path_mem (H Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (hrep : HasCompactReps H Γ) (f : C(I, G)) (hstart : f 0 ∈ H)
    (himage : ∀ t, (f t : G ⧸ Γ) ∈ QuotientGroup.mk '' (H : Set G)) :
    ∀ t, f t ∈ H :=
  path_mem_subspace (Γ.isQuotientCoveringMap hΓ).isCoveringMap (H : Set G)
    (subgroup_orbit_covering H Γ hΓ hrep) f hstart himage

end CoveringSubspace

namespace CubeFaces
open CompactGroupProducts
variable {G ι : Type} [Group G] [DecidableEq ι] [Fintype ι]
  [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

omit [DecidableEq ι] [IsTopologicalGroup G] [T2Space G] in
 
lemma latticeArrays_isDiscrete (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G)) :
    IsDiscrete (↑(latticeArrays (ι := ι) Γ) : Set (Finset ι → G)) := by
  let : DiscreteTopology Γ := isDiscrete_iff_discreteTopology.mp hΓ
  have h : IsDiscrete (Set.range (fun f : Finset ι → Γ => fun v => (f v).val)) :=
    (Topology.IsInducing.piMap
    (fun _ : Finset ι => (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : Γ → G)))).isDiscrete_range
  have heq : Set.range (fun f : Finset ι → Γ => fun v => (f v).val) =
      (↑(latticeArrays (ι := ι) Γ) : Set (Finset ι → G)) := by
    ext f
    constructor
    · rintro ⟨g, rfl⟩
      exact fun v => (g v).property
    · intro hf
      exact ⟨fun v => ⟨f v, hf v⟩, rfl⟩
  rwa [heq] at h

 

theorem quotient_affine_face_displacement
    (H : Filtration G) (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (hrep : ∀ j, HasCompactReps (H.level j) Γ)
    (D : Finset ι) (a : ι) (ha : a ∉ D)
    [PathConnectedSpace (H.level D.card)]
    (c g : G) (φ : G →* G) (hφ : Continuous φ)
    (hc : c ∈ H.level 1) (hg : g ∈ H.level D.card)
    (hpres : ∀ f ∈ cube H (insert a D) 0,
      (affineUpper a c φ f : (Finset ι → G) ⧸ latticeArrays Γ) ∈
        QuotientGroup.mk '' (cube H (insert a D) 0 : Set (Finset ι → G))) :
    g⁻¹ * φ g ∈ H.level (D.card + 1) := by
  let p : Path (1 : H.level D.card) ⟨g, hg⟩ := PathConnectedSpace.somePath _ _
  let q : C(I, Finset ι → G) :=
    ⟨fun t => affineUpper a c φ (face D (p t).val), by
      apply continuous_pi
      intro v
      dsimp [affineUpper, face_apply]
      by_cases hav : a ∈ v <;> by_cases hDv : D ⊆ v <;> simp only [hav, hDv, ite_true, ite_false]
      · exact continuous_const.mul (hφ.comp (continuous_subtype_val.comp p.continuous))
      · exact continuous_const
      · exact continuous_subtype_val.comp p.continuous
      · exact continuous_const⟩
  have hstart : q 0 ∈ cube H (insert a D) 0 := by
    have heq : q 0 = face {a} c := by
      funext v
      simp [q, affineUpper, p.source, face_apply]
    rw [heq]
    exact face_mem_cube H (by simp) (by simpa using hc)
  have himage : ∀ t, (q t : (Finset ι → G) ⧸ latticeArrays Γ) ∈
      QuotientGroup.mk '' (cube H (insert a D) 0 : Set (Finset ι → G)) := by
    intro t
    apply hpres
    exact face_mem_cube H (Finset.subset_insert _ _) (p t).property
  have hmem := CoveringSubspace.subgroup_path_mem (cube H (insert a D) 0)
    (latticeArrays Γ) (latticeArrays_isDiscrete Γ hΓ)
    (cube_hasCompactReps H Γ hrep (insert a D) 0) q hstart himage 1
  apply affine_face_displacement H D a ha c g φ hc hg
  simpa [q, p.target] using hmem

end CubeFaces

end
 
end

section
 

noncomputable section
open Topology
namespace RationalLattice
open WeightedLinear MalcevCharacters CompactGroupProducts CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (H : Filtration G) (w : Fin n → ℕ) (hmono : Monotone w)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

include hmono hH in
omit [IsTopologicalGroup G] [T2Space G] in
lemma chart_level_pathConnected (k : ℕ) : PathConnectedSpace (H.level k) := by
  let e : H.level k ≃ₜ (WeightedLinear.level w k) :=
    (logHomeomorph c).subtype (fun g=>by
      change g∈H.level k ↔ ∀ i,w i < k → logHomeomorph c g i=0
      rw [logHomeomorph_apply]
      exact mem_level_iff_log c H w hmono hH k g)
  exact e.symm.surjective.pathConnectedSpace e.symm.continuous

 
def PreservesFaces (Γ : Subgroup G) (a : G) (F : G →* G) (s : ℕ) : Prop :=
  ∀ k ≤ s,∀ f∈cube (ι:=Fin (k+1)) H Finset.univ 0,
    (affineUpper (Fin.last k) a F f : (Finset (Fin (k+1)) → G) ⧸ latticeArrays Γ)∈
      QuotientGroup.mk '' (↑(cube (ι:=Fin (k+1)) H Finset.univ 0) : Set (Finset (Fin (k+1)) → G))

include hmono hH in
 

theorem face_displacement_all_levels (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (hrep : ∀ j,HasCompactReps (H.level j) Γ)
    (a : G) (ha : a∈H.level 1) (F : G →* G) (hF : Continuous F)
    (s : ℕ) (hs : H.level (s+1)=⊥) (hpres : PreservesFaces H Γ a F s)
    (k : ℕ) (_hk : 0 < k) (g : G) (hg : g∈H.level k) :
    g⁻¹*F g∈H.level (k+1) := by
  by_cases hks : k ≤ s
  · let D : Finset (Fin (k+1)):=Finset.univ.erase (Fin.last k)
    have hD : D.card=k := by simp [D]
    have hfull : insert (Fin.last k) D=Finset.univ := by simp [D]
    let : PathConnectedSpace (H.level D.card) := chart_level_pathConnected c H w hmono hH _
    have hh:=quotient_affine_face_displacement H Γ hΓ hrep D (Fin.last k)
      (by simp [D]) a g F hF ha (by simpa [hD] using hg) (by
        rw [hfull]
        exact hpres k hks)
    simpa [hD] using hh
  · have hone : g=1 := by
      have hh:=H.antitone (show s+1 ≤ k by omega) hg
      simpa [hs] using hh
    simp [hone]

include hmono hH in
 

theorem face_affine_displacement_weighted (hsk : SecondKind c) (hw : ∀ i,0 < w i)
    (Γ : Subgroup G) (hΓ : IsDiscrete (Γ : Set G))
    (hrep : ∀ j,HasCompactReps (H.level j) Γ)
    (a : G) (ha : a∈H.level 1) (F : G →* G) (hF : Continuous F)
    (s : ℕ) (hs : H.level (s+1)=⊥) (hpres : PreservesFaces H Γ a F s) (i : Fin n) :
    WeightedPolynomial.IsWeighted w (w i-1)
      (fun y=>canonicalLog c (a*F (canonicalExp c y)) i-y i) :=
  affine_log_displacement_weighted c hsk H w hw hmono hH F hF
    (fun k hk g hg=>face_displacement_all_levels c H w hmono hH Γ hΓ hrep
      a ha F hF s hs hpres k hk g hg) a i

end RationalLattice
end
 
end

section
 

noncomputable section
namespace RationalLattice
open MalcevCharacters WeightedLinear
variable {G J : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates J m)
    (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (K : CubeFaces.Filtration J)
    (w : Fin n → ℕ) (v : Fin m → ℕ) (hmono : Monotone w) (hvmono : Monotone v)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
    (hK : ∀ k (g : J),g∈K.level k ↔ ∀ i : Fin m,v i < k → d.coord g i=0)
    (p : G →* J) (hp : Continuous p)
    (honto : ∀ k,(H.level k).map p=K.level k)

include hsk hmono hvmono hH hK hp honto in
 

theorem logHomLinear_level_map (k : ℕ) :
    Submodule.map (logHomLinear d c p).toLinearMap (level w k)=level v k := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hg : canonicalExp c x∈H.level k :=
      (canonicalExp_mem_level_iff c H w hmono hH _ _).mpr hx
    have hpg : p (canonicalExp c x)∈K.level k := by
      rw [← honto]
      exact Subgroup.mem_map.mpr ⟨_,hg,rfl⟩
    have hlog := (mem_level_iff_log d K v hvmono hK _ _).mp hpg
    change ∀ i,v i < k → logHomLinear d c p x i=0
    rw [logHomLinear_apply d c hsk p hp]
    exact hlog
  · intro hy
    have hgy : canonicalExp d y∈K.level k :=
      (canonicalExp_mem_level_iff d K v hvmono hK _ _).mpr hy
    rw [← honto] at hgy
    obtain ⟨g,hg,he⟩:=Subgroup.mem_map.mp hgy
    refine Submodule.mem_map.mpr ⟨canonicalLog c g,
      (mem_level_iff_log c H w hmono hH _ _).mp hg,?_⟩
    rw [ContinuousLinearMap.coe_coe,logHomLinear_apply d c hsk p hp]
    change canonicalLog d (p (canonicalExp c (canonicalLog c g)))=y
    rw [canonicalExp_log,he,canonicalLog_exp]

include hsk hmono hvmono hH hK hp honto in
theorem logHomLinear_preserves : Preserves w v (logHomLinear d c p).toLinearMap := by
  intro k x hx
  rw [← logHomLinear_level_map c d hsk H K w v hmono hvmono hH hK p hp honto k]
  exact Submodule.mem_map.mpr ⟨x,hx,rfl⟩

end RationalLattice
end
 
end

section
 

noncomputable section
namespace RationalLattice
open MalcevCharacters WeightedLinear CompactGroupProducts CubeFaces
open FilteredShears.PolynomialShears PolynomialShearPoint
variable {G J : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group J] [TopologicalSpace J] [IsTopologicalGroup J] [T2Space J]
variable {n m : ℕ} (c : RealCoordinates G n) (d : RealCoordinates J m)
    (hsk : SecondKind c) (hdsk : SecondKind d)
variable (H : Filtration G) (K : Filtration J)
    (w : Fin n → ℕ) (v : Fin m → ℕ) (hw : ∀ i,0 < w i) (hv : ∀ j,0 < v j)
    (hmono : Monotone w) (hvmono : Monotone v)
    (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
    (hK : ∀ k (g : J),g∈K.level k ↔ ∀ i : Fin m,v i < k → d.coord g i=0)
    (p : G →* J) (hp : Continuous p)
    (honto : ∀ k,(H.level k).map p=K.level k)

include hsk hdsk hw hv hmono hvmono hH hK hp honto in
 

theorem exists_face_lift (Γ : Subgroup J) (hΓ : IsDiscrete (Γ : Set J))
    (hrep : ∀ j,HasCompactReps (K.level j) Γ)
    (a : J) (ha : a∈K.level 1) (F : J →* J) (hF : Continuous F)
    (s : ℕ) (hs : K.level (s+1)=⊥) (hpres : PreservesFaces K Γ a F s) :
    ∃ A : shears (R:=ℝ) w,
      (∀ x,p (canonicalExp c (pointMap A.val.toAlgHom x))=
        a*F (p (canonicalExp c x))) ∧
      Function.Bijective (pointMap A.val.toAlgHom) := by
  let P:=(logHomLinear d c p).toLinearMap
  have hon : ∀ k,Submodule.map P (level w k)=level v k :=
    logHomLinear_level_map c d hsk H K w v hmono hvmono hH hK p hp honto
  have hP : Preserves w v P :=
    logHomLinear_preserves c d hsk H K w v hmono hvmono hH hK p hp honto
  obtain ⟨R,hPR,hR⟩:=exists_rightInverse w v P hon
  let D (y : Fin m → ℝ):=canonicalLog d (a*F (canonicalExp d y))-y
  have hD (j : Fin m) : WeightedPolynomial.IsWeighted v (v j-1) (fun y=>D y j) :=
    face_affine_displacement_weighted d K v hvmono hK hdsk hv Γ hΓ hrep
      a ha F hF s hs hpres j
  have hDR (i : Fin n) : WeightedPolynomial.IsWeighted w (w i-1)
      (fun x=>R (D (P x)) i) := lifted_displacement_weighted hP hR D hD i
  obtain ⟨A,hA,hbij⟩:=exists_shear w hw (fun x=>R (D (P x))) hDR
  refine ⟨A,?_,?_⟩
  · intro x
    rw [hA,map_canonicalExp d c hsk p hp]
    change canonicalExp d (P (x+R (D (P x))))=_
    rw [map_add,hPR]
    have he : P x+D (P x)=canonicalLog d (a*F (canonicalExp d (P x))) := by
      dsimp [D]
      abel
    rw [he,canonicalExp_log]
    change a*F (canonicalExp d (logHomLinear d c p x))=_
    rw [← map_canonicalExp d c hsk p hp]
  · have he : pointMap A.val.toAlgHom=(fun x=>x+R (D (P x))) := funext hA
    rwa [he]

end RationalLattice

end
end
end

end OAI
