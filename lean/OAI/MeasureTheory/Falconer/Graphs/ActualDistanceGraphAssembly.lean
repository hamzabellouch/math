import OAI.MeasureTheory.Falconer.Graphs.ParentAbsoluteGraphAssembly
import OAI.MeasureTheory.Falconer.Graphs.GraphOriginalGraphRemoval

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

def sourceDistanceSlot (l : Fin 4) : Fin 2 := ![0,1,1,0] l

theorem sourceDistanceSlot_comp {α : Type*} (f : Fin 2 → α) :
    (fun l => f (sourceDistanceSlot l)) = ![f 0,f 1,f 1,f 0] := by
  funext l
  fin_cases l <;> rfl

theorem uniform_actual_retained_distance_graph
    {sig κ c₀ : ℝ} (hsig : 0 < sig) (hgap : 10*sig < κ)
    (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) (K : ℕ) (lam T : ℝ)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    (∀ l, (S l).card ≤ (N+1)^3+1) → (∀ l, (∑ t ∈ S l, k l t) ≤ K) →
    ∀ L : ℕ, (∀ l t, t ∈ S l → descriptorLength (d l t) ≤ L) →
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, 0 < (Q l).side) → (∀ l, (Q l).side ≤ 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (mass : Fin 2 → ℝ → ℝ) (B : ℕ) (δ : ℝ),
    (∀ l, RegularizedProfileData (Q l) (ρ l) N B δ lam (mass l)) →
    ∀ (J i : ℕ) (h : Fin 2 → Plane → ℂ), (∀ l, Measurable (h l)) → (∀ l x, ‖h l x‖ ≤ 1) →
    ∀ (a n : ℕ) (v : ℝ), a+n ≤ N → κ*N ≤ (n:ℝ) →
    0 ≤ v-(a+n) → (n:ℝ) ≤ v-(a+n)+2*sig*N → (L:ℝ) ≤ v-(a+n)+2*sig*N → v-a ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2
      (sourceParentAxis X Y) e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
    let M := fun l => ((2:ℝ)^N)^(-mass l (a+n))
    let F := fun e : GraphNonedgeIndex => graphOriginalTerm ![ρ 0,ρ 1,ρ 1,ρ 0]
      (fun l => (graphQuadCells ![Q 0,Q 1,Q 1,Q 0] e.1 l).carrier)
      ![M 0,M 1,M 1,M 0] ![β 0,β 1,β 1,β 0] true e.2.2 (sourceParentAxis X Y) θ v e.2.1.1 e.2.1.2 Ψ
    ‖(sourceRadialSquareEnergy a v Ψ (sourceParentRetainedF N sig t X Y (ρ 0) (ρ 1) n
        (((2:ℝ)^N)^(-mass 0 a)) (((2:ℝ)^N)^(-mass 1 a)) (β 0) (β 1)) : ℂ) -
      ((2:ℝ)^(2*(v-a))) • (graphProfileCoefficient N ![mass 0,mass 1,mass 1,mass 0] a (a+n) •
        (∑ e ∈ graphRetainedIndices I N sig (a+n) true ![Q 0,Q 1,Q 1,Q 0] rep, F e))‖ ≤ ((2:ℝ)^N)^(-T) := by
  classical
  obtain ⟨N₁,hrem⟩ := uniform_regularized_original_graph_removal hsig K lam T hΨ hs hc hcap
  obtain ⟨N₂,hcaps⟩ := graphAngularScale_cap_inactive hgap hc
  obtain ⟨W,hW,hw⟩ := continuous_supported_bump_bound hΨ.continuous hs
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k hcard hK L hL Q hQ hQs ρ mass B δ hd J i h hh hhb a n v
    hp hlow hu ht hLu hv A B' hA hB hsep
  let : ∀ l, IsProbabilityMeasure (ρ l) := fun l => (hd l).probability
  let X := (Q 0).descendant A
  let Y := (Q 1).descendant B'
  let t : ℝ := (a+n:ℕ)-a
  have htval : t = n := by dsimp [t]; push_cast; ring
  have hθ := hcaps N ((le_max_right _ _).trans hN) t (by simpa only [htval] using hlow)
  have hX : 0 < X.side := (Q 0).descendant_side_pos (hQ 0) A
  have hY : 0 < Y.side := (Q 1).descendant_side_pos (hQ 1) B'
  have hXs : X.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [X]; rw [DyadicSquare.descendant_side,hA,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 0) (by positivity : (0:ℝ) ≤ 2^a)
  have hYs : Y.side ≤ (2:ℝ)^(-(a:ℝ)) := by
    dsimp [Y]; rw [DyadicSquare.descendant_side,hB,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast]
    simpa only [one_div] using div_le_div_of_nonneg_right (hQs 1) (by positivity : (0:ℝ) ≤ 2^a)
  let I := sourceParentGraphIndices N sig t X Y (ρ 0) (ρ 1) n A B'
  have hI : I ⊆ graphNonedgeIndices (a+n) (angularBinCount (graphAngularScale N sig t c₀)) := by
    rw [hθ]
    exact sourceParentGraphIndices_subset hA hB
  have hr := hrem N ((le_max_left _ _).trans hN)
    (fun l => S (sourceDistanceSlot l)) (fun l => d (sourceDistanceSlot l)) (fun l => k (sourceDistanceSlot l))
    (fun l => hcard _) (fun l => hK _) L (fun l => hL _)
    (fun l => Q (sourceDistanceSlot l)) (fun l => hQ _) (fun l => hQs _)
    (fun l => ρ (sourceDistanceSlot l)) (fun l => mass (sourceDistanceSlot l)) B δ (fun l => hd _)
    J i (fun l => h (sourceDistanceSlot l)) (fun l => hh _) (fun l => hhb _)
    a (a+n) v (Nat.cast_nonneg a) (by exact_mod_cast Nat.le_add_right a n) hp
    (by simpa only [Nat.cast_add] using hu) (by simpa only [Nat.cast_add,add_sub_cancel_left] using ht)
    (by simpa only [Nat.cast_add] using hLu) hv true X Y hX hY hXs hYs (fun _ => hsep)
    (sourceParentAxis X Y) I hI (by
      intro e he l
      rw [sourceDistanceSlot_comp]
      exact sourceParentGraphIndices_parent (Q 0) (Q 1) (hQ 0) (hQ 1) A B' N n sig t (ρ 0) (ρ 1) he l)
  dsimp only at hr ⊢
  simp only [sourceDistanceSlot_comp] at hr
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l)
  have hm (l : Fin 2) : Measurable (fun z : Plane × UnitCircle => β l z.1 z.2) :=
    measurable_inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (mass l) N lam sig J i (h l) (hh l)
  have hb : ∀ (l : Fin 2) (x : Plane) (dir : UnitCircle), ‖β l x dir‖ ≤ symbolDerivativeConstant K^K := by
    intro l x dir
    exact inheritedCircleSymbol_norm_le (S l) (d l) (k l) (Q l) (hQ l) (ρ l) (mass l) N lam sig J i (h l)
      K (hK l) x (hhb l x) dir
  have he := sourceParentRetainedEnergy_absolute_graph_sum N sig t a v (Q 0) (Q 1) A B'
    (ρ 0) (ρ 1) n (Ma₁ := ((2:ℝ)^N)^(-mass 0 a)) (Ma₂ := ((2:ℝ)^N)^(-mass 1 a))
    (Mp₁ := ((2:ℝ)^N)^(-mass 0 (a+n))) (Mp₂ := ((2:ℝ)^N)^(-mass 1 (a+n)))
    (by positivity) (by positivity) (by positivity) (by positivity) (β 0) (β 1) (hm 0) (hm 1)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K)
    (pow_nonneg (zero_le_one.trans (symbolDerivativeConstant_one_le K)) K) (hb 0) (hb 1) hΨ.continuous.measurable hpos hs hW hw
  rw [← graphProfileCoefficient_distance] at he
  rw [← hθ] at he
  rw [he]
  have hM4 := sourceDistanceSlot_comp (fun l => ((2:ℝ)^N)^(-mass l (a+n:ℕ)))
  have hβ4 := sourceDistanceSlot_comp β
  rw [hM4,hβ4] at hr
  simpa only [Nat.cast_add,X,Y,I,t,β] using hr

end PlanarFalconer

end OAI
