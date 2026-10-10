import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AlignmentMass01
import OAI.Combinatorics.SumProduct.Alignment.RationalLattice24
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
end

section
 

noncomputable section
open Filter Topology MeasureTheory
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan PolynomialShearPoint
open FilteredShears.PolynomialShears
variable {n k r : ℕ} (D : Pivot n)
abbrev Slots := Fin D.pairs → ℤ
abbrev Shifts := Multiplicative (Slots D)

def unitShift (e : Fin D.pairs) : Shifts D := Multiplicative.ofAdd (Pi.single e 1)

def generators (w : Fin k → ℕ) (A : Fin D.pairs → shears (R:=ℝ) w) :
    Fin D.pairs → CoverGroup w (Fin D.pairs) := fun e=>(A e,unitShift D e)

def terminalShift (q₀ : ℕ) (b : Scale n) (U : Finset (Fin D.pairs)) : Shifts D :=
  FreeGroup.lift (letter D.index D.tail D.owner D.added (unitShift D) q₀ b) (baseWord D U)

def jumpSlot (q₀ : ℕ) (p : Path D) (b : Scale n) : Slots D :=
  (jump D (unitShift D) q₀ 0 p b).toAdd

lemma lift_map {G H E : Type*} [Group G] [Group H] (f : G →* H) (a : E → G)
    (u : FreeGroup E) : f (FreeGroup.lift a u)=FreeGroup.lift (fun e=>f (a e)) u := by
  have he : f.comp (FreeGroup.lift a)=FreeGroup.lift (fun e=>f (a e)) := by
    apply FreeGroup.ext_hom
    intro e
    simp
  exact DFunLike.congr_fun he u

lemma jump_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (L : Fin D.pairs → G) (q₀ j : ℕ) (p : Path D) (b : Scale n) :
    f (jump D L q₀ j p b)=jump D (fun e=>f (L e)) q₀ j p b := by
  induction p generalizing j b with
  | nil => simp [jump]
  | cons o p ih =>
    simp only [jump,map_mul,ih,lift_map]
    have he : (fun e=>f (letter D.index D.tail D.owner D.added L q₀ b e))=
        letter D.index D.tail D.owner D.added (fun e=>f (L e)) q₀ b := by
      funext e
      simp [letter]
    rw [he]

lemma jump_slot (w : Fin k → ℕ) (A : Fin D.pairs → shears (R:=ℝ) w)
    (q₀ : ℕ) (p : Path D) (b : Scale n) :
    (jump D (generators D w A) q₀ 0 p b).2.toAdd=jumpSlot D q₀ p b := by
  exact congrArg Multiplicative.toAdd
    (jump_map D (MonoidHom.snd (shears (R:=ℝ) w) (Shifts D)) (generators D w A) q₀ 0 p b)

abbrev OwnSubset (j : Fin D.targets) :=
  {U : Finset (Fin D.pairs) // ∀ e∈U,D.owner e=j}
abbrev Comparison (F : Finset (Scale n)) (r : ℕ) :=
  {d : Scale n // d∈F} × (Σ j : Fin D.targets, OwnSubset D j) × Fin r

variable {X : Type*} (Y : Fin D.targets → Type*)
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → X → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)

 
def palette (τ : ℝ) (Θ : (Fin k → ℝ) → X) :
    Fin D.targets → ℚ → CoverState (σ:=Fin k) (Fin D.pairs) → (Fin r → Bool) :=
  fun j a x c=>decide (3*τ/2 < Read j a (π j (Θ x.1),x.2) c)

def centerReading (F : Finset (Scale n)) (q₀ : ℕ) (b : Scale n) (p : Path D)
    (i : Comparison D F r) (x : X) : ℝ :=
  Read i.2.1.1 (blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail i.2.1.1))
    (π i.2.1.1 x,jumpSlot D q₀ p b) i.2.2

def translatedReading (F : Finset (Scale n)) (q₀ : ℕ) (b : Scale n) (p : Path D)
    (i : Comparison D F r) (x : X) : ℝ :=
  Read i.2.1.1 (blockProduct (scaleRun D 0 p b*i.1.val) (block D.index D.tail i.2.1.1))
    (terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val •
      (π i.2.1.1 x,jumpSlot D q₀ p b)) i.2.2

 

lemma own_state_reading (w : Fin k → ℕ) (A : Fin D.pairs → shears (R:=ℝ) w)
    (Θ : (Fin k → ℝ) → X)
    (hown : ∀ j e,D.owner e=j → ∀ z,
      π j (Θ (A e • z))=unitShift D e • π j (Θ z))
    (j : Fin D.targets) (q₀ : ℕ) (b : Scale n) (U : OwnSubset D j)
    (x : CoverState (σ:=Fin k) (Fin D.pairs)) :
    let u:=FreeGroup.lift (letter D.index D.tail D.owner D.added (generators D w A) q₀ b)
      (baseWord D U.val)
    (π j (Θ (u • x).1),(u • x).2)=terminalShift D q₀ b U.val • (π j (Θ x.1),x.2) := by
  apply OwnTerminal.terminal_projection D (fun x=>(π j (Θ x.1),x.2))
    (generators D w A) (unitShift D) j _ q₀ b U.val U.property x
  intro e he x
  ext
  · exact hown j e he x.1
  · rfl

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

noncomputable section
namespace ConstructedWordPlan.GlobalWordPlan
open AlignmentScales RationalPivotPlan PolynomialShearPoint
open FilteredShears.PolynomialShears
variable {n k r : ℕ} (D : Pivot n)
variable {X : Type*} {Y : Fin D.targets → Type*}
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → X → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)

 

def closedOption (F : Finset (Scale n)) (τ : ℝ) (q₀ : ℕ) (b : Scale n)
    (p : Path D) : Set X := AlignmentMass.ClosedGood τ
      (centerReading D Y π Read F q₀ b p) (translatedReading D Y π Read F q₀ b p)

 

lemma closed_cover (w : Fin k → ℕ) (A : Fin D.pairs → shears (R:=ℝ) w)
    (Θ : (Fin k → ℝ) → X)
    (hown : ∀ j e,D.owner e=j → ∀ z,
      π j (Θ (A e • z))=unitShift D e • π j (Θ z))
    (F : Finset (Scale n)) (P : Finset (Path D)) (τ : ℝ) (q₀ : ℕ) (b : Scale n)
    (hp : ∀ x : CoverState (σ:=Fin k) (Fin D.pairs), ∃ p∈P,∀ d∈F,
      Good D (palette D Y π Read τ Θ) (generators D w A) q₀ (scaleRun D 0 p b*d)
        (exactRun D.index D.tail D.owner D.added (generators D w A) q₀ 0 p b x).2)
    (z : Fin k → ℝ) :
    ∃ p∈P, Θ ((jump D (generators D w A) q₀ 0 p b).1 • z) ∈
      closedOption D π Read F τ q₀ b p := by
  classical
  obtain ⟨p,hpP,hgood⟩:=hp (z,0)
  refine ⟨p,hpP,?_⟩
  intro i
  let x : CoverState (σ:=Fin k) (Fin D.pairs):=
    (jump D (generators D w A) q₀ 0 p b) • (z,0)
  have hx : (exactRun D.index D.tail D.owner D.added (generators D w A) q₀ 0 p b (z,0)).2=x :=
    exactRun_snd D _ _ _ _ _ _
  have hv : x.2=jumpSlot D q₀ p b := by
    dsimp [x]
    simp only [add_zero,jump_slot]
  have he:=congrFun (hgood i.1.val i.1.property i.2.1.1 i.2.1.2.val i.2.1.2.property) i.2.2
  rw [hx] at he
  have hr:=own_state_reading D Y π w A Θ hown i.2.1.1 q₀
    (scaleRun D 0 p b*i.1.val) i.2.1.2 x
  dsimp only at hr
  dsimp only [palette] at he
  rw [hr] at he
  have he' : (3*τ/2 < centerReading D Y π Read F q₀ b p i (Θ x.1)) ↔
      (3*τ/2 < translatedReading D Y π Read F q₀ b p i (Θ x.1)) := by
    simpa only [centerReading,translatedReading,hv] using (decide_eq_decide.mp he)
  suffices centerReading D Y π Read F q₀ b p i (Θ x.1) ≤ 3*τ/2 ∨
      3*τ/2 ≤ translatedReading D Y π Read F q₀ b p i (Θ x.1) from this
  by_cases h : 3*τ/2 < centerReading D Y π Read F q₀ b p i (Θ x.1)
  · right
    exact le_of_lt (he'.mp h)
  · exact Or.inl (le_of_not_gt h)

open Topology
variable [TopologicalSpace X] [∀ j,TopologicalSpace (Y j)]

omit [∀ j,MulAction (Shifts D) (Y j)] in
lemma centerReading_continuous
    (hπ : ∀ j,Continuous (π j))
    (hRead : ∀ j a c,Continuous (fun y=>Read j a y c))
    (F : Finset (Scale n)) (q₀ : ℕ) (b : Scale n) (p : Path D)
    (i : Comparison D F r) : Continuous (centerReading D Y π Read F q₀ b p i) := by
  exact (hRead _ _ _).comp ((hπ _).prodMk continuous_const)

lemma translatedReading_continuous
    (hπ : ∀ j,Continuous (π j))
    (hRead : ∀ j a c,Continuous (fun y=>Read j a y c))
    (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
    (F : Finset (Scale n)) (q₀ : ℕ) (b : Scale n) (p : Path D)
    (i : Comparison D F r) : Continuous (translatedReading D Y π Read F q₀ b p i) := by
  let t:=terminalShift D q₀ (scaleRun D 0 p b*i.1.val) i.2.1.2.val
  exact (hRead _ _ _).comp (((hS _ t).comp (hπ _)).prodMk
    (show Continuous (fun _ : X=>t • jumpSlot D q₀ p b) from continuous_const))

lemma closedOption_isClosed
    (hπ : ∀ j,Continuous (π j))
    (hRead : ∀ j a c,Continuous (fun y=>Read j a y c))
    (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
    (F : Finset (Scale n)) (τ : ℝ) (q₀ : ℕ) (b : Scale n) (p : Path D) :
    IsClosed (closedOption D π Read F τ q₀ b p) :=
  AlignmentMass.isClosed_closedGood _ _ _
    (centerReading_continuous D π Read hπ hRead F q₀ b p)
    (translatedReading_continuous D π Read hπ hRead hS F q₀ b p)

end ConstructedWordPlan.GlobalWordPlan
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace RationalLattice
open MalcevCharacters PolynomialShearPoint FilteredShears.PolynomialShears WeightedBoxes
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n)
variable (Γ : Subgroup G) [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

 
def shearedPoint (q : C(G⧸Γ,X)) {w : Fin n → ℕ} (A : shears (R:=ℝ) w) : C((Fin n → ℝ),X) :=
  q.comp ((expQuotient c Γ).comp ⟨pointMap A.val.toAlgHom,pointMap_continuous _⟩)

omit [IsTopologicalGroup G] in
lemma weightedShear_imageLaw (q : C(G⧸Γ,X)) (w : Fin n → ℕ)
    (A : shears (R:=ℝ) w) (E : ℝ) :
    (weightedShearLaw c w Γ A E).map q=
      (boxLaw w E).map (shearedPoint c Γ q A) := by
  apply Subtype.ext
  change Measure.map q (Measure.map (expQuotient c Γ)
    (Measure.map (pointMap A.val.toAlgHom) (boxLaw w E : Measure (Fin n → ℝ))))=_
  rw [Measure.map_map q.continuous.measurable (expQuotient c Γ).continuous.measurable,
    Measure.map_map (q.continuous.comp (expQuotient c Γ).continuous).measurable
      (pointMap_continuous A.val.toAlgHom).measurable]
  rfl

variable (hsk : SecondKind c) (H : CubeFaces.Filtration G)
variable (w : Fin n → ℕ) (hw : ∀ i,0<w i)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)

include hsk hw hH in
 

theorem weightedCover_finite_closed_mass [HasOuterApproxClosed X]
    {O : Type*} [Fintype O] [Nonempty O]
    (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
    (μ : ProbabilityMeasure (G⧸Γ))
    [SMulInvariantMeasure G (G⧸Γ) (μ:Measure (G⧸Γ))]
    (q : C(G⧸Γ,X)) (A : O → shears (R:=ℝ) w) (F : O → Set X)
    (hF : ∀ o,IsClosed (F o))
    (hcover : ∀ z,∃ o,shearedPoint c Γ q (A o) z∈F o) :
    ((Fintype.card O : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
      (μ.map q : Measure X) (⋃ o,F o) := by
  let ν (o : O) (N : ℕ):=
    (boxLaw w (N:ℝ)).map (shearedPoint c Γ q (A o))
  apply AlignmentMass.finite_closed_mass _ ν F hF
  · intro o
    have he : ν o=fun N : ℕ=>
        (weightedShearLaw c w Γ (A o) (N:ℝ)).map q := by
      funext N
      exact (weightedShear_imageLaw c Γ q w (A o) N).symm
    rw [he]
    exact (weightedShear_pointImage_limit c hsk H w hw hH Γ hΓ μ (A o) q).comp
      tendsto_natCast_atTop_atTop
  · intro N
    exact AlignmentMass.cover_sum (boxLaw w (N:ℝ))
      (fun o=>shearedPoint c Γ q (A o))
      (fun o=>(shearedPoint c Γ q (A o)).continuous.measurable) F
      (fun o=>(hF o).measurableSet) hcover

end RationalLattice

end
end
end

end OAI
