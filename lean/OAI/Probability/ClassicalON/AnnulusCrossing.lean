import OAI.Probability.ClassicalON.PoleCrossing

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON.LatticeGraph

def innerSet (G : LatticeGraph) (k : ℕ) : Set G.vertices :=
  {x | |(scaledSite k x.val).1|≤1 ∧ |(scaledSite k x.val).2|≤1}

def outerSet (G : LatticeGraph) (k : ℕ) : Set G.vertices :=
  {x | 2≤|(scaledSite k x.val).1| ∨ 2≤|(scaledSite k x.val).2|}

theorem inner_outer_disjoint (G : LatticeGraph) (k : ℕ) : Disjoint (G.innerSet k) (G.outerSet k) := by
  apply Set.disjoint_left.mpr
  intro x hx ho
  rcases ho with h | h <;> linarith [hx.1,hx.2]

def positiveLayerPins (G : LatticeGraph) (I O : Set G.vertices) : G.vertices → Option (Spin 3) :=
  (poleSystem (fun e : G.edges => e.val.1) (fun e => e.val.2) (fun _ => 0) (I∪O) (fun _ => true)).pin

theorem positiveLayerPins_boundary (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices)
    (hI : I⊆G.innerSet k) (hO : O⊆G.outerSet k) :
    G.BoundaryPins k 3 (G.positiveLayerPins I O) := by
  intro x s hs
  by_cases h : x∈I∪O
  · rcases h with h | h
    · exact Or.inl (hI h)
    · exact Or.inr (hO h)
  · simp only [positiveLayerPins,poleSystem,h,↓reduceDIte] at hs
    cases hs

theorem rotate_positiveLayerPins_pi (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices)
    (hI : I⊆G.innerSet k) (hO : O⊆G.outerSet k) :
    G.rotatedBoundaryPins k (G.positiveLayerPins I O) Real.pi=
      (poleSystem (fun e : G.edges => e.val.1) (fun e => e.val.2) (fun _ => 0) (I∪O)
        (fun v => layerSigns I v)).pin := by
  funext x
  by_cases hx : x∈I∪O
  · have htheta : G.thetaPotential k x=if x∈I then 1 else 0 := by
      by_cases h : x∈I
      · simp only [h,ite_true,thetaPotential]
        exact squareTheta_one _ (hI h).1 (hI h).2
      · simp only [h,ite_false,thetaPotential]
        exact squareTheta_zero _ (hO (hx.resolve_left h))
    simp only [rotatedBoundaryPins,positiveLayerPins,poleSystem,hx,↓reduceDIte,Option.map_some]
    by_cases hi : x∈I
    · rw [show layerSigns I x=false by simp [layerSigns,hi]]
      congr 1
      exact rotate_pole _ _ (by simpa [hi] using htheta)
    · rw [show layerSigns I x=true by simp [layerSigns,hi]]
      congr 1
      exact rotation_zero_potential _ _ _ (by simpa [hi] using htheta) _
  · simp only [rotatedBoundaryPins,positiveLayerPins,poleSystem,hx,↓reduceDIte,Option.map_none]

theorem rotate_positiveLayerPins_zero (G : LatticeGraph) (k : ℕ) (I O : Set G.vertices) :
    G.rotatedBoundaryPins k (G.positiveLayerPins I O) 0=G.positiveLayerPins I O := by
  funext x
  simp only [rotatedBoundaryPins]
  cases hp : G.positiveLayerPins I O x with
  | none => rfl
  | some s =>
    simp only [Option.map_some]
    congr 1
    apply Subtype.ext
    change NormedSpace.exp ((0*G.thetaPotential k x) • axisC) s.val=s.val
    simp [zero_smul ℝ axisC]

theorem annulus_crossing_small (β : ℝ) (hβ : 0≤β) (ε : ℝ) (hε : 0<ε) :
    ∃ k : ℕ,4≤k ∧ ∀ (G : LatticeGraph),G.WithinDyadicBox k →
      ∀ (b : G.edges → ℝ),(∀ e,0≤b e ∧ b e≤β) →
      ∀ (I O : Set G.vertices),I⊆G.innerSet k → O⊆G.outerSet k →
      poleBondMean (fun e : G.edges => e.val.1) (fun e => e.val.2) b (I∪O) (fun _ => true)
        (crossingIndicator (fun e : G.edges => e.val.1) (fun e => e.val.2) I O)≤ε := by
  obtain ⟨k,hk,hr⟩ := annulus_partition_ratio β hβ ε hε
  refine ⟨k,hk,?_⟩
  intro G hG b hb I O hI hO
  have hd : Disjoint I O := (G.inner_outer_disjoint k).mono hI hO
  rw [pole_crossing_ratio _ _ _ (fun e => (hb e).1) _ _ hd]
  have h := hr G hG b hb (G.positiveLayerPins I O)
    (G.positiveLayerPins_boundary k I O hI hO) Real.pi 0
  rw [G.rotate_positiveLayerPins_pi k I O hI hO,G.rotate_positiveLayerPins_zero k I O] at h
  change 1-ε≤(poleSystem _ _ b (I∪O) (fun v => layerSigns I v)).Z (fun _ => 1)/
    (poleSystem _ _ b (I∪O) (fun _ => true)).Z (fun _ => 1) at h
  linarith

end ClassicalON.LatticeGraph

end

end OAI
