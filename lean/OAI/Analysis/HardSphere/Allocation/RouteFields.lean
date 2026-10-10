import Mathlib
import OAI.Analysis.HardSphere.Allocation.PhysicalPairedRoute
import OAI.Analysis.HardSphere.Paths.SimpleRouteGeometry
import OAI.Analysis.HardSphere.Allocation.PhysicalLabelLaw

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

def RouteFieldValid (p : SimplePath x y) (z : DiscreteTorus K→Option J) : Prop :=
  ∃ f : Fin p.val.length↪J, ∀i,z (pathVertexEmbedding p i.castSucc)=some (f i)
def fieldLabels (p : SimplePath x y) (z : DiscreteTorus K→Option J) (h : RouteFieldValid p z) : Fin p.val.length↪J := h.choose
omit [NeZero K] [Fintype J] [DecidableEq J] in
lemma fieldLabels_spec (p : SimplePath x y) (z : DiscreteTorus K→Option J) (h : RouteFieldValid p z) :
    ∀i,z (pathVertexEmbedding p i.castSucc)=some (fieldLabels p z h i) := h.choose_spec

omit [DecidableEq J] in
lemma branchAccessible_home {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (v : DiscreteTorus K) (d : PhysicalDatum N K M G L) (j : J)
    (hj : j∈branchAccessible hL g m t r R C S u particle v d) :
    datumHome hL d (particle j)=siteIndex v ∧ datumAccessible hL g m t r R C S u (particle j) d := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).2).2

lemma routeFieldValid_of_supported {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) :
    RouteFieldValid p z := by
  have he : ∀i : Fin p.val.length,∃j : J,
      j∈branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d ∧
      z (pathVertexEmbedding p i.castSucc)=some j := by
    intro i
    have hh := hz (pathVertexEmbedding p i.castSucc)
    rw [paddedLabels,ite_eq_left (ha i)] at hh
    obtain ⟨j,hj,he⟩ := Finset.mem_image.mp hh
    exact ⟨j,hj,he.symm⟩
  choose f hf hfe using he
  have hhome : ∀i,gridSite (datumHome hL d (particle (f i)))=pathVertexEmbedding p i.castSucc := by
    intro i
    rw [(branchAccessible_home hL g m t r R C S u particle _ d _ (hf i)).1]
    exact indexSite_siteIndex _
  exact ⟨departureEmbedding p (fun j ↦ gridSite (datumHome hL d (particle j))) f hhome,hfe⟩

lemma fieldLabels_physical {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (h : RouteFieldValid p z) :
    ∀i,datumHome hL d (particle (fieldLabels p z h i))=siteIndex (pathVertexEmbedding p i.castSucc) ∧
      datumAccessible hL g m t r R C S u (particle (fieldLabels p z h i)) d := by
  intro i
  apply branchAccessible_home hL g m t r R C S u particle _ d _
  have hh := hz (pathVertexEmbedding p i.castSucc)
  rw [paddedLabels,ite_eq_left (ha i),fieldLabels_spec p z h] at hh
  simpa using hh

omit [NeZero K] in
lemma simpleRouteLength_eq (hxy : x≠y) (p : SimplePath x y) : p.val.length-1+1=p.val.length := by
  have hp : p.val.length≠0 := fun h ↦ hxy (SimpleGraph.Walk.eq_of_length_eq_zero h)
  omega

def fieldRouteLabels (hxy : x≠y) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (h : RouteFieldValid p z) : Fin (p.val.length-1+1)↪J :=
  (finCongr (simpleRouteLength_eq hxy p)).toEmbedding.trans (fieldLabels p z h)

lemma fieldRouteLabels_physical {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J→Fin N)
    (d : PhysicalDatum N K M G L) (hxy : x≠y) (p : SimplePath x y) (z : DiscreteTorus K→Option J)
    (hz : ∀v,z v∈paddedLabels (branchAccessible hL g m t r R C S u particle v d))
    (ha : ∀i : Fin p.val.length,(branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty)
    (h : RouteFieldValid p z) :
    ∀i,datumHome hL d (particle (fieldRouteLabels hxy p z h i))=
      simpleRouteVertices p (p.val.length-1) i.castSucc ∧
      datumAccessible hL g m t r R C S u (particle (fieldRouteLabels hxy p z h i)) d := by
  intro i
  exact fieldLabels_physical hL g m t r R C S u particle d p z hz ha h (Fin.cast (simpleRouteLength_eq hxy p) i)

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J]

abbrev PhysicalRouteCode (x y : DiscreteTorus K) (J : Type*) :=
  SimplePath x y × (DiscreteTorus K→Option J)

def physicalCodedRoute {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) :
    Kernel (PhysicalDatum N K M G L) ((Option J→C(Time,Point))×(Option J→C(Time,Point))) :=
  if h : RouteFieldValid c.1 c.2 then
    physicalPairedRoute hL g m t r R C S u particle (fieldRouteLabels hxy c.1 c.2 h)
      (simpleRouteVertices c.1 (c.1.val.length-1))
      (simpleRouteSteps hL c.1 (c.1.val.length-1) (simpleRouteLength_eq hxy c.1))
  else 0

lemma physicalCodedRoute_mass_le_one {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) (d : PhysicalDatum N K M G L) :
    physicalCodedRoute hL g m t r R C S u particle hxy c d univ≤1 := by
  unfold physicalCodedRoute
  split
  · exact physicalPairedRoute_mass_le_one ..
  · change (0 : ℝ≥0∞)≤1
    exact bot_le
instance physicalCodedRoute_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (c : PhysicalRouteCode x y J) :
    IsFiniteKernel (physicalCodedRoute (M:=M) hL g m t r R C S u particle hxy c) :=
  ⟨1,by simp,physicalCodedRoute_mass_le_one hL g m t r R C S u particle hxy c⟩

def physicalRouteFamily {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) :
    Kernel (PhysicalDatum N K M G L × PhysicalRouteCode x y J)
      ((Option J→C(Time,Point))×(Option J→C(Time,Point))) where
  toFun z := physicalCodedRoute hL g m t r R C S u particle hxy z.2 z.1
  measurable' := measurable_from_prod_countable_left fun c ↦
    (physicalCodedRoute hL g m t r R C S u particle hxy c).measurable
instance physicalRouteFamily_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) : IsFiniteKernel (physicalRouteFamily (M:=M) hL g m t r R C S u particle hxy) :=
  ⟨1,by simp,fun z ↦ physicalCodedRoute_mass_le_one hL g m t r R C S u particle hxy z.2 z.1⟩

def physicalMixedRoutes {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν] :
    Kernel (PhysicalDatum N K M G L)
      (PhysicalRouteCode x y J × ((Option J→C(Time,Point))×(Option J→C(Time,Point)))) :=
  (ν.prod (physicalLabels hL g m t r R C S u particle)) ⊗ₖ
    physicalRouteFamily hL g m t r R C S u particle hxy
instance physicalMixedRoutes_finite {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν] :
    IsFiniteKernel (physicalMixedRoutes hL g m t r R C S u particle hxy ν) := by
  unfold physicalMixedRoutes; infer_instance

lemma physicalMixedRoutes_mass_le_one {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time) (particle : J↪Fin N)
    (hxy : x≠y) (ν : Kernel (PhysicalDatum N K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (d : PhysicalDatum N K M G L) :
    physicalMixedRoutes hL g m t r R C S u particle hxy ν d univ≤1 := by
  rw [physicalMixedRoutes,Kernel.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  calc
    _ ≤ ∫⁻_c,1 ∂(ν.prod (physicalLabels hL g m t r R C S u particle)) d :=
      lintegral_mono fun c ↦ physicalCodedRoute_mass_le_one hL g m t r R C S u particle hxy c d
    _ = 1 := by simp

end HardSphere.Groups
end
end

end OAI
