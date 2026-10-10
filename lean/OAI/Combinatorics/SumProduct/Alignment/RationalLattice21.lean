import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice19
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
noncomputable section
end

 

section
 

 

noncomputable section
namespace RationalLattice
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G)

structure CoveredLattice where
  small : Subgroup G
  integer : ∀ g,g∈small ↔ ∀ i,∃ z : ℤ,c.coord g i=z
  le : small≤Γ
  discrete : DiscreteTopology Γ

namespace CoveredLattice
variable (B : CoveredLattice c Γ)
omit [IsTopologicalGroup G] in
lemma conjugate_le [IsTopologicalGroup G] (σ : G) :
    CubeLocalHaar.conjugateLattice B.small σ≤CubeLocalHaar.conjugateLattice Γ σ:=
  fun _ h=>B.le h
include B in
lemma conjugate_discrete (σ : G) : DiscreteTopology (CubeLocalHaar.conjugateLattice Γ σ) := by
  let : DiscreteTopology Γ:=B.discrete
  exact DiscreteTopology.preimage_of_continuous_injective (Γ:Set G)
    (show Continuous (MulAut.conj σ⁻¹).toMonoidHom from
      (continuous_const.mul continuous_id).mul continuous_const) (MulAut.conj σ⁻¹).injective
include B in
lemma conjugate_quotient_t2 (σ : G) : T2Space (G⧸CubeLocalHaar.conjugateLattice Γ σ) := by
  let : T2Space G:=c.coord.symm.t2Space
  let : DiscreteTopology (CubeLocalHaar.conjugateLattice Γ σ):=B.conjugate_discrete c Γ σ
  let : IsClosed (CubeLocalHaar.conjugateLattice Γ σ : Set G):=
    (CubeLocalHaar.conjugateLattice Γ σ).isClosed_of_discreteTopology
  infer_instance

variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
variable (F : K →* G) (hF : Continuous F) (hinj : Function.Injective F)
include B hF hinj in
omit [IsTopologicalGroup K] in
lemma conjugate_induced_discrete [IsTopologicalGroup K] (σ : G) :
    DiscreteTopology ((CubeLocalHaar.conjugateLattice Γ σ).comap F) := by
  let : DiscreteTopology (CubeLocalHaar.conjugateLattice Γ σ):=B.conjugate_discrete c Γ σ
  exact DiscreteTopology.preimage_of_continuous_injective
    (CubeLocalHaar.conjugateLattice Γ σ : Set G) hF hinj
end CoveredLattice

end RationalLattice
end
 
end

section
 

 

noncomputable section
namespace RationalLattice.PolynomialArrays
open MalcevCharacters MalcevWeightedCoordinates
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n q : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (A : CubeFaces.Filtration G) (w : Fin n → ℕ)
variable (hA : ∀ k (g : G),g∈A.level k ↔ ∀ i : Fin n,w i<k → c.coord g i=0)
variable (hw : ∀ i,0<w i) (hmono : Monotone w)
variable (Γ : Subgroup G) (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)

include hw hmono hΓ in
lemma covered_geometry : ∃ e : RealCoordinates (group (q:=q) c hsk A w hA)
    (Fintype.card (Index w q)),
    SecondKind e ∧ Nonempty (CoveredLattice e (lattice c hsk A w hA Γ)) ∧
    (∀ k f,f∈(filtration c hsk A w hA).level k ↔ ∀ i,orderedWeight (q:=q) w i<k → e.coord f i=0) ∧
    (∀ f,IsRational e f ↔ IsRational (chart c hsk A w hA hw) f) := by
  obtain ⟨Λ,e,he,hΛ,hle,_,ha,hr⟩:=second_integer_cover c hsk A w hA hw hmono Γ hΓ (q:=q)
  let : DiscreteTopology Γ:=integerCoordinates_discrete c Γ hΓ
  exact ⟨e,he,⟨⟨Λ,hΛ,hle,lattice_discrete c hsk A w hA Γ⟩⟩,ha,hr⟩

lemma filtration_top (k : ℕ) (hk : A.level k=⊤) :
    (filtration (q:=q) c hsk A w hA).level k=⊤ := by
  apply top_unique
  intro f _ u
  rw [hk]
  trivial

lemma filtration_terminal (s : ℕ) (hs : A.level (s+1)=⊥) :
    (filtration (q:=q) c hsk A w hA).level (s+1)=⊥ := by
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  funext u
  exact Subgroup.mem_bot.mp (hs ▸ hf u)

end RationalLattice.PolynomialArrays
end
 
end

section
 

 

noncomputable section
namespace RationalLattice
open MalcevCharacters MalcevWeightedCoordinates
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (Γ : Subgroup G) [DiscreteTopology Γ]

lemma grid_integer_cover (D : ℕ) (hD : 0<D)
    (hgrid : ∀ g : G,(∀ i,∃ z : ℤ,c.coord g i=(D:ℝ)*z) → g∈Γ) :
    ∃ Λ : Subgroup G,∃ e : RealCoordinates G n,
      (∀ g,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z) ∧
      Λ≤Γ ∧ (Λ.subgroupOf Γ).FiniteIndex ∧
      (∀ g i,e.coord g i=0 ↔ c.coord g i=0) ∧
      (∀ g,IsRational e g ↔ IsRational c g) := by
  obtain ⟨w,hw,hDw,hlat⟩:=exists_lattice_weights c D hD
  let Λ:=weightedLattice c w hlat
  let e:=scaledCoordinates c w hw
  have hΛ : ∀ g,g∈Λ ↔ ∀ i,∃ z : ℤ,e.coord g i=z:=weightedLattice_iff c w hlat hw
  have hle : Λ≤Γ:=by
    intro g hg
    apply hgrid g
    intro i
    obtain ⟨a,ha⟩:=hg i
    obtain ⟨b,hb⟩:=hDw i
    refine ⟨(b:ℤ)*a,?_⟩
    rw [ha,hb]
    push_cast
    ring
  let : T2Space G:=c.coord.symm.t2Space
  obtain ⟨C,hC,hrep⟩:=compact_reps_of_integerCoordinates e Λ hΛ
  refine ⟨Λ,e,hΛ,hle,TriangularDenominators.finiteIndex_of_compact_reps Λ Γ hle C hC hrep,
    ?_,scaledCoordinates_rational c w hw⟩
  intro g i
  change c.coord g i/(w i:ℝ)=0 ↔ c.coord g i=0
  have hn : (w i:ℝ)≠0:=by exact_mod_cast (hw i).ne'
  simp only [div_eq_zero_iff,hn,or_false]

lemma grid_adapted_cover (A : CubeFaces.Filtration G) (w : Fin n → ℕ) (hmono : Monotone w)
    (hA : ∀ k g,g∈A.level k ↔ ∀ i,w i<k → c.coord g i=0)
    (D : ℕ) (hD : 0<D) (hgrid : ∀ g : G,(∀ i,∃ z : ℤ,c.coord g i=(D:ℝ)*z) → g∈Γ) :
    ∃ e : RealCoordinates G n,SecondKind e ∧ Nonempty (CoveredLattice e Γ) ∧
      (∀ k g,g∈A.level k ↔ ∀ i,w i<k → e.coord g i=0) ∧
      (∀ g,IsRational e g ↔ IsRational c g) := by
  obtain ⟨Λ,d,hΛ,hle,_,hz,hr⟩:=grid_integer_cover c Γ D hD hgrid
  refine ⟨secondCoordinates d,secondCoordinates_secondKind d,
    ⟨⟨Λ,expCoordinates_lattice d Λ hΛ,hle,inferInstance⟩⟩,?_,
    fun g=>(secondCoordinates_rational d g).trans (hr g)⟩
  intro k g
  obtain ⟨r,_,he⟩:=exists_weight_cutoff w hmono k
  have hd : ∀ g : G,g∈A.level k ↔ ∀ i : Fin n,i.val<r → d.coord g i=0 := by
    intro g
    rw [hA]
    simp only [← he,hz]
  simpa only [← he] using secondCoordinates_adapted d (A.level k) r hd g

end RationalLattice
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalLattice.FiniteProducts
open MalcevCharacters MalcevWeightedCoordinates
variable {ι : Type} [Fintype ι] (G : ι → Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι → ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i) → ℕ) (hw : ∀ i j,0<w i j) (hmono : ∀ i,Monotone (w i))
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (Γ : ∀ i,Subgroup (G i)) (B : ∀ i,CoveredLattice (c i) (Γ i))

def lattice : Subgroup (∀ i,G i) where
  carrier:=fun g=>∀ i,g i∈Γ i
  one_mem':=fun i=>(Γ i).one_mem
  mul_mem':=fun hg hh i=>(Γ i).mul_mem (hg i) (hh i)
  inv_mem':=fun hg i=>(Γ i).inv_mem (hg i)

def projection (i : ι) : (∀ i,G i) →* G i where
  toFun g:=g i
  map_one':=rfl
  map_mul' _ _:=rfl
omit [Fintype ι] [∀ index,IsTopologicalGroup (G index)] in
lemma projection_continuous [Fintype ι] [∀ index,IsTopologicalGroup (G index)]
    (i : ι) : Continuous (projection G i):=continuous_apply i

include B in
omit [∀ index,IsTopologicalGroup (G index)] in
lemma lattice_discrete [∀ index,IsTopologicalGroup (G index)] :
    DiscreteTopology (lattice G Γ) := by
  let (i : ι) : DiscreteTopology (Γ i):=(B i).discrete
  let F : lattice G Γ → ∀ i,Γ i:=fun g i=>⟨g.val i,g.property i⟩
  have hF : Continuous F:=continuous_pi (fun i=>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _)
  apply DiscreteTopology.of_continuous_injective hF
  intro g h he
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun he i)

include B in
lemma grid_lattice : ∃ D : ℕ,0<D ∧ ∀ g : ∀ i,G i,
    (∀ j,∃ z : ℤ,(chart G n c hsk A w hw hA).coord g j=(D:ℝ)*z) → g∈lattice G Γ := by
  classical
  let d:=chart G n c hsk A w hw hA
  have hi (i : ι):=rationalHom_origin_grid (c i) d (projection G i)
    (chart_projection_polynomial G n c hsk A w hw hA i)
  choose D hD hgrid using hi
  refine ⟨∏ i,D i,Finset.prod_pos (fun i _=>hD i),?_⟩
  intro g hg i
  apply (B i).le
  apply ((B i).integer _).mpr
  have hd : ∀ j,∃ z : ℤ,d.coord g j=(D i:ℝ)*z:=by
    intro j
    obtain ⟨a,ha⟩:=hg j
    obtain ⟨b,hb⟩:=Finset.dvd_prod_of_mem D (Finset.mem_univ i)
    refine ⟨(b:ℤ)*a,?_⟩
    rw [ha,hb]
    push_cast
    ring
  have hh:=hgrid i (d.coord g) hd
  simp only [Homeomorph.symm_apply_apply] at hh
  exact hh

include B hmono in
lemma covered_geometry : ∃ e : RealCoordinates (∀ i,G i) (Fintype.card (Index n)),
    SecondKind e ∧ Nonempty (CoveredLattice e (lattice G Γ)) ∧
    (∀ k g,g∈(filtration G A).level k ↔ ∀ j,orderedWeight n w j<k → e.coord g j=0) ∧
    (∀ g,IsRational e g ↔ IsRational (chart G n c hsk A w hw hA) g) := by
  let : DiscreteTopology (lattice G Γ):=lattice_discrete G n c Γ B
  obtain ⟨D,hD,hgrid⟩:=grid_lattice G n c hsk A w hw hA Γ B
  exact grid_adapted_cover (chart G n c hsk A w hw hA) (lattice G Γ) (filtration G A)
    (orderedWeight n w) (orderedWeight_monotone n w) (chart_adapted G n c hsk A w hw hmono hA)
    D hD hgrid

include B hmono hsk hw hA in
lemma lattice_compactSpace : CompactSpace ((∀ i,G i)⧸lattice G Γ) := by
  obtain ⟨e,_,⟨C⟩,_,_⟩:=covered_geometry G n c hsk A w hw hmono hA Γ B
  obtain ⟨S,hS,hrep⟩:=compact_reps_of_integerCoordinates e C.small C.integer
  apply CompactGroupProducts.HasCompactReps.quotient_compactSpace
  refine ⟨S,hS,fun _ _=>Subgroup.mem_top _,?_⟩
  intro g _
  obtain ⟨a,ha,hag⟩:=hrep g
  exact ⟨a,ha,C.le hag⟩

omit [Fintype ι] [∀ index,IsTopologicalGroup (G index)] in
lemma filtration_top [Fintype ι] [∀ index,IsTopologicalGroup (G index)]
    (k : ℕ) (hk : ∀ i,(A i).level k=⊤) : (filtration G A).level k=⊤ := by
  apply top_unique
  intro g _ i
  rw [hk i]
  trivial
omit [Fintype ι] [∀ index,IsTopologicalGroup (G index)] in
lemma filtration_terminal [Fintype ι] [∀ index,IsTopologicalGroup (G index)]
    (s : ℕ) (hs : ∀ i,(A i).level (s+1)=⊥) :
    (filtration G A).level (s+1)=⊥ := by
  apply bot_unique
  intro g hg
  apply Subgroup.mem_bot.mpr
  funext i
  exact Subgroup.mem_bot.mp (hs i ▸ hg i)

end RationalLattice.FiniteProducts

end
end

end OAI
