import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WordPlan02
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan PolynomialShearPoint
open FilteredShears.PolynomialShears RationalLattice MalcevCharacters
variable {n k r : ℕ} (D : Pivot n)
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (c : RealCoordinates G k) (hsk : SecondKind c) (H : _root_.OAI.CubeFaces.Filtration G)
variable (w : Fin k → ℕ) (hw : ∀ i,0<w i)
variable (hH : ∀ j (g : G),g∈H.level j ↔ ∀ i : Fin k,w i<j → c.coord g i=0)
variable (Γ : Subgroup G) [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable [HasOuterApproxClosed X]
variable {Y : Fin D.targets → Type*} [∀ j,TopologicalSpace (Y j)]
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → X → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)

include hsk hw hH in
 

theorem pivot_haar_mass
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))]
    (q : C(G⧸Γ,X)) (A : Fin D.pairs → shears (R:=ℝ) w)
    (hπ : ∀ j,Continuous (π j))
    (hRead : ∀ j a t,Continuous (fun y=>Read j a y t))
    (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
    (hown : ∀ j e,D.owner e=j → ∀ z,
      π j (q (expQuotient c Γ (A e • z)))=
        unitShift D e • π j (q (expQuotient c Γ z)))
    (F : Finset (Scale n)) (P : Finset (Path D)) (τ : ℝ) (q₀ : ℕ) (b : Scale n)
    (hp : ∀ x : CoverState (σ:=Fin k) (Fin D.pairs), ∃ p∈P,∀ d∈F,
      Good D (palette D Y π Read τ (fun z=>q (expQuotient c Γ z)))
        (generators D w A) q₀ (scaleRun D 0 p b*d)
        (exactRun D.index D.tail D.owner D.added (generators D w A) q₀ 0 p b x).2) :
    ((P.card : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
      (μ.map q : Measure X)
        (⋃ p∈P,closedOption D π Read F τ q₀ b p) := by
  classical
  have hPN : P.Nonempty := by
    obtain ⟨p,hp,_⟩:=hp (0,0)
    exact ⟨p,hp⟩
  let : Nonempty {p // p∈P}:=hPN.to_subtype
  let AS (p : {p // p∈P}) : shears (R:=ℝ) w:=
    (jump D (generators D w A) q₀ 0 p.val b).1⁻¹
  have hc : ∀ z,∃ p : {p // p∈P},shearedPoint c Γ q (AS p) z∈
      closedOption D π Read F τ q₀ b p.val := by
    intro z
    obtain ⟨p,hpP,hp⟩:=closed_cover D π Read w A
      (fun z=>q (expQuotient c Γ z)) hown F P τ q₀ b hp z
    exact ⟨⟨p,hpP⟩,hp⟩
  have hm:=weightedCover_finite_closed_mass c Γ hsk H w hw hH hΓ μ q AS
    (fun p=>closedOption D π Read F τ q₀ b p.val)
    (fun p=>closedOption_isClosed D π Read hπ hRead hS F τ q₀ b p.val) hc
  simpa only [Fintype.card_coe,Set.iUnion_subtype] using hm

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan PolynomialShearPoint
open FilteredShears.PolynomialShears RationalLattice MalcevCharacters
variable {n : ℕ}

 

def ChartedMassAssertion (D : Pivot n) (F : Finset (Scale n))
    (P : Finset (Path D)) (s r q₀ : ℕ) (b : Scale n) (τ : ℝ) : Prop :=
  ∀ (k : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : RealCoordinates G k), SecondKind c →
  ∀ (H : _root_.OAI.CubeFaces.Filtration G) (w : Fin k → ℕ),
    (∀ i,0<w i) → (∀ i,w i ≤ s) →
    (∀ j (g : G),g∈H.level j ↔ ∀ i : Fin k,w i<j → c.coord g i=0) →
  ∀ (Γ : Subgroup G) [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
    (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [HasOuterApproxClosed X]
    (Y : Fin D.targets → Type) [∀ j,TopologicalSpace (Y j)]
    [∀ j,MulAction (Shifts D) (Y j)]
    (π : (j : Fin D.targets) → X → Y j)
    (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ),
    (∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z) →
  ∀ (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))]
    (q : C(G⧸Γ,X)) (A : Fin D.pairs → shears (R:=ℝ) w),
    (∀ j,Continuous (π j)) →
    (∀ j a t,Continuous (fun y=>Read j a y t)) →
    (∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y)) →
    (∀ j e,D.owner e=j → ∀ z,
      π j (q (expQuotient c Γ (A e • z)))=
        unitShift D e • π j (q (expQuotient c Γ z))) →
    ((P.card : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
      (μ.map q : Measure X)
        (⋃ p∈P,closedOption D π Read F τ q₀ b p)

 

theorem uniform_pivot_haar (s r : ℕ) (hs : 1 ≤ s) (D : Pivot n)
    (F : Finset (Scale n)) :
    ∃ P : Finset (Path D),P.Nonempty ∧
      (∀ p∈P,p.length=D.targets ∧ ∀ o∈p,0<o.1) ∧
      ∀ B : Finset (Scale n), ∃ Q : ℕ,0<Q ∧
        ∀ q₀ : ℕ,Q∣q₀ → ∀ b∈B,∀ τ : ℝ,ChartedMassAssertion D F P s r q₀ b τ := by
  classical
  obtain ⟨P,hPlen,hPlan⟩:=pivot_future_plan (κ:=Fin r → Bool) s D F
  have hPN : P.Nonempty := by
    obtain ⟨Q,_,hQ⟩:=hPlan {1}
    have hnil : (⊤ : Subgroup PUnit).lowerCentralSeries s=⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact Subgroup.mem_bot.mpr (Subsingleton.elim _ _)
    obtain ⟨p,hp,_⟩:=hQ Q (dvd_refl _) PUnit hnil PUnit
      (fun _ _ _ (_ : Fin r)=>false) (fun _=>PUnit.unit) 1 (by simp) PUnit.unit
    exact ⟨p,hp⟩
  refine ⟨P,hPN,hPlen,?_⟩
  intro B
  obtain ⟨Q,hQ,hPlanB⟩:=hPlan B
  refine ⟨Q,hQ,?_⟩
  intro q₀ hq₀ b hb τ k G ig tg itg c hsk H w hw hws hH Γ mg bg X tx mx bx hx Y ty ay π Read hΓ μ hμ q A hπ
    hRead hS hown
  apply pivot_haar_mass D c hsk H w hw hH Γ π Read hΓ μ q A hπ hRead hS hown F P τ q₀ b
  intro x
  exact hPlanB q₀ hq₀ (CoverGroup w (Fin D.pairs))
    (cover_lowerCentralSeries w hs hws) (CoverState (σ:=Fin k) (Fin D.pairs))
    (palette D Y π Read τ (fun z=>q (expQuotient c Γ z))) (generators D w A) b hb x

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

noncomputable section
open Topology
namespace CubeFaces
variable {G ι : Type} [Group G] [DecidableEq ι]
theorem cube_top_support (H : Filtration G) (I : Finset ι) (k : ℕ)
    {f : Finset ι → G} (hf : f∈cube H I k)
    (hv : ∀ v,v ⊂ I → f v=1) : f I∈H.level (I.card+k) :=
  CubeRationalCharts.cube_corner_mem H I k hf _
    (fun v h=>by rw [hv v h]; exact (H.level _).one_mem) le_rfl
end CubeFaces

namespace CubeFaces
variable {G ι : Type} [Group G] [DecidableEq ι]

 
def affineUpper (a : ι) (c : G) (φ : G →* G) (f : Finset ι → G) : Finset ι → G :=
  fun v => if a ∈ v then c * φ (f v) else f v

 

theorem affine_face_displacement (H : Filtration G) (D : Finset ι) (a : ι)
    (ha : a ∉ D) (c g : G) (φ : G →* G)
    (hc : c ∈ H.level 1) (hg : g ∈ H.level D.card)
    (hpres : affineUpper a c φ (face D g) ∈ cube H (insert a D) 0) :
    g⁻¹ * φ g ∈ H.level (D.card + 1) := by
  have hD : D ⊆ insert a D := Finset.subset_insert _ _
  have hz : face D g ∈ cube H (insert a D) 0 :=
    face_mem_cube H hD (by simpa using hg)
  have hcf : face {a} c ∈ cube H (insert a D) 0 :=
    face_mem_cube H (by simp) (by simpa using hc)
  let f := (face D g)⁻¹ * ((face {a} c)⁻¹ * affineUpper a c φ (face D g))
  have hf : f ∈ cube H (insert a D) 0 :=
    (cube H _ _).mul_mem ((cube H _ _).inv_mem hz)
      ((cube H _ _).mul_mem ((cube H _ _).inv_mem hcf) hpres)
  have hv (v : Finset ι) (hvi : v ⊂ insert a D) : f v = 1 := by
    have hn : ¬ (a ∈ v ∧ D ⊆ v) := by
      rintro ⟨hav, hDv⟩
      exact hvi.not_superset (Finset.insert_subset hav hDv)
    dsimp [f, affineUpper]
    simp only [Finset.singleton_subset_iff]
    by_cases hav : a ∈ v <;> by_cases hDv : D ⊆ v <;> simp_all
  have htop := cube_top_support H (insert a D) 0 hf hv
  simpa [f, affineUpper, face_apply, hD, Finset.card_insert_of_notMem ha] using htop

end CubeFaces

open scoped unitInterval
namespace CoveringSubspace

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

 
def imageRestrict (p : E → X) (S : Set E) : S → p '' S :=
  fun e => ⟨p e, ⟨e, e.property, rfl⟩⟩

lemma continuous_imageRestrict {p : E → X} (hp : Continuous p) (S : Set E) :
    Continuous (imageRestrict p S) :=
  (hp.comp continuous_subtype_val).subtype_mk _

 

theorem path_mem_subspace {p : E → X} (hp : IsCoveringMap p) (S : Set E)
    (hS : IsCoveringMap (imageRestrict p S)) (f : C(I, E))
    (hstart : f 0 ∈ S) (himage : ∀ t, p (f t) ∈ p '' S) :
    ∀ t, f t ∈ S := by
  let γ : C(I, p '' S) :=
    ⟨fun t => ⟨p (f t), himage t⟩, (hp.continuous.comp f.continuous).subtype_mk _⟩
  obtain ⟨Γ, hΓ, hΓ0⟩ := hS.exists_path_lifts γ ⟨f 0, hstart⟩ rfl
  have heq : (fun t => (Γ t).val) = f := by
    refine hp.eq_of_comp_eq (continuous_subtype_val.comp Γ.continuous) f.continuous ?_ 0 ?_
    · exact congrArg (fun g => fun t => (g t).val) hΓ
    · exact congrArg Subtype.val hΓ0
  intro t
  rw [← congrFun heq t]
  exact (Γ t).property

 
theorem isQuotientMap_imageRestrict [T2Space X] {p : E → X} (hp : Continuous p)
    {S C : Set E} (hC : IsCompact C) (hCS : C ⊆ S)
    (hrep : ∀ s ∈ S, ∃ c ∈ C, p c = p s) :
    Topology.IsQuotientMap (imageRestrict p S) := by
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let incl : C → S := fun c => ⟨c, hCS c.property⟩
  have hinc : Continuous incl := continuous_subtype_val.subtype_mk _
  have hq : Continuous (imageRestrict p S) := continuous_imageRestrict hp S
  have hsurj : Function.Surjective (imageRestrict p S ∘ incl) := by
    rintro ⟨x, s, hs, rfl⟩
    obtain ⟨c, hc, heq⟩ := hrep s hs
    exact ⟨⟨c, hc⟩, Subtype.ext heq⟩
  exact Topology.IsQuotientMap.of_comp hinc hq
    ((hq.comp hinc).isClosedMap.isQuotientMap (hq.comp hinc) hsurj)

end CoveringSubspace

end
end
end

end OAI
