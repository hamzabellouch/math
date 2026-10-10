import OAI.MeasureTheory.Falconer.Graphs.UniformDistancePairDegree
import OAI.MeasureTheory.Falconer.Estimates.DistanceMatrixData

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def activeDistanceMatrixNeighbors (I : Finset GraphNonedgeIndex)
    (p j b : ℕ) (θ axis : ℝ) (plus reverse : Bool) (row : CellPath × CellPath) :
    Finset (CellPath × CellPath) := by
  classical
  exact if (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty
    then distanceMatrixNeighbors I p j b plus reverse row else ∅

theorem uniform_actual_distance_degrees {sig κ c₀ : ℝ} (hsig : 0 < sig)
    (hgap : 10*sig < κ) (hc : 0 < c₀) (hcap : c₀ ≤ 2*Real.pi) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a n : ℕ, (∀ l, d l (e l) = .parallel a (a+n)) → a+n ≤ N → κ*N ≤ (n:ℝ) →
    ∀ A B : CellPath, A.length = a → B.length = a →
    dist ((Q 0).descendant A).center ((Q 1).descendant B).center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    let t : ℝ := (a+n:ℕ)-a
    let θ := graphAngularScale N sig t c₀
    let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
    let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
      (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
    ∀ (j b : ℕ) (plus reverse : Bool) (row : CellPath × CellPath),
    ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤
      144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a (a+n))
      (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a (a+n))+2000*(lam+sig)+60*sig) := by
  classical
  obtain ⟨N₁,hcount⟩ := uniform_inherited_distance_pair_degree hsig hJ
  obtain ⟨N₂,hscale⟩ := graphAngularScale_cap_inactive hgap hc
  refine ⟨max N₁ N₂,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a n hd hp hlow A B hA hB hsep
  dsimp only
  let t : ℝ := (a+n:ℕ)-a
  let θ := graphAngularScale N sig t c₀
  let axis := sourceParentAxis ((Q 0).descendant A) ((Q 1).descendant B)
  let rep := fun e : (ℕ × ℕ) × Bool => graphChosenRepresentative
    (graphAngularScale_pos N sig t hc) ((min_le_left _ _).trans hcap) true e.2 axis e.1.1 e.1.2
  let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
  let I := sourceRetainedDistanceIndices (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
  intro j b plus reverse row
  change ((activeDistanceMatrixNeighbors I (a+n) j b θ axis plus reverse row).card : ℝ) ≤ _
  by_cases hs : (tsupport (graphSourceWeight true plus axis (angularBinCount θ) j b)).Nonempty
  · rw [activeDistanceMatrixNeighbors,ite_eq_left hs]
    have hq : GraphSourceRepresentative true plus axis θ j b (rep ((j,b),plus)) := by
      rcases graphChosenRepresentative_spec (graphAngularScale_pos N sig t hc)
        ((min_le_left _ _).trans hcap) true plus axis j b with hq | hn
      · exact hq
      · exact (hn hs).elim
    have hbins := graphSourceWeight_support_bins true plus axis (angularBinCount θ) j b hq.1
    have hθ : θ = graphUncappedAngularScale N sig t := hscale N ((le_max_right _ _).trans hN) t
      (by simpa [t] using hlow)
    have hsc : graphAngularScale N sig (n:ℝ) c₀ = graphUncappedAngularScale N sig n := by
      simpa [θ,t] using hθ
    have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
    cases reverse
    · let C := distanceMatrixNeighbors I (a+n) j b plus false row
      have hdata (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceRetainedDistanceIndices_data (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
          (show distanceMatrixIndex row col j b plus ∈ I from (Finset.mem_filter.mp hc).2)
      have hocc (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_occupied (Q 0) (Q 1) (ρ 0) (ρ 1) A B N a n sig t hA hB (hdata col hc).1 l
      have hpar (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_parent (Q 0) (Q 1) (hQp 0) (hQp 1) A B N n sig t (ρ 0) (ρ 1) (hdata col hc).1 l
      have hact (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceParentGraphIndices_activity (Q 0) (Q 1) (ρ 0) (ρ 1) A B N n sig t (hdata col hc).1
      by_cases hn : C.Nonempty
      · obtain ⟨col₀,hcol₀⟩ := hn
        have hh := hcount N ((le_max_left _ _).trans hN) S d k Q hQ ρ m lam i hi h e he
          a (a+n) hd (Nat.le_add_right a n) hp A B hA hB hsep row C
          (Or.inl (show ((Q 0).descendant row.1).center ∈ ((Q 0).descendant A).carrier from
            hpar col₀ hcol₀ 0 (((Q 0).descendant row.1).center_mem ((Q 0).descendant_side_pos (hQp 0) row.1))))
          (Or.inr (show ((Q 1).descendant row.2).center ∈ ((Q 1).descendant B).carrier from
            hpar col₀ hcol₀ 2 (((Q 1).descendant row.2).center_mem ((Q 1).descendant_side_pos (hQp 1) row.2))))
          (fun col hc => hocc col hc 1) (fun col hc => hocc col hc 3)
          (fun col hc => hpar col hc 1) (fun col hc => hpar col hc 3)
          axis c₀ hc hcap j b false plus (rep ((j,b),plus)) hbins.1 hbins.2
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).1)
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).2)
          (fun col hc => (hdata col hc).2.2 1) (fun col hc => (hdata col hc).2.2 3)
          (fun col hc => by
            have hr := (hdata col hc).2.1
            rw [distanceMatrix_cells] at hr
            simpa only [Nat.cast_add,distanceMatrixIndex] using hr)
        exact hh
      · change (C.card : ℝ) ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
        positivity
    · let C := distanceMatrixNeighbors I (a+n) j b plus true row
      have hdata (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceRetainedDistanceIndices_data (Q 0) (Q 1) (ρ 0) (ρ 1) (β 0) (β 1) A B a n N sig t θ rep
          (show distanceMatrixIndex col row j b plus ∈ I from (Finset.mem_filter.mp hc).2)
      have hocc (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_occupied (Q 0) (Q 1) (ρ 0) (ρ 1) A B N a n sig t hA hB (hdata col hc).1 l
      have hpar (col : CellPath × CellPath) (hc : col ∈ C) (l : Fin 4) :=
        sourceParentGraphIndices_parent (Q 0) (Q 1) (hQp 0) (hQp 1) A B N n sig t (ρ 0) (ρ 1) (hdata col hc).1 l
      have hact (col : CellPath × CellPath) (hc : col ∈ C) :=
        sourceParentGraphIndices_activity (Q 0) (Q 1) (ρ 0) (ρ 1) A B N n sig t (hdata col hc).1
      by_cases hn : C.Nonempty
      · obtain ⟨col₀,hcol₀⟩ := hn
        have hh := hcount N ((le_max_left _ _).trans hN)
          (fun l : Fin 2 => S l.rev) (fun l : Fin 2 => d l.rev) (fun l : Fin 2 => k l.rev)
          (fun l : Fin 2 => Q l.rev) (fun l => hQ l.rev)
          (fun l : Fin 2 => ρ l.rev) (fun l : Fin 2 => m l.rev) lam i hi
          (fun l : Fin 2 => h l.rev) (fun l : Fin 2 => e l.rev) (fun l => he l.rev)
          a (a+n) (fun l => hd l.rev) (Nat.le_add_right a n) hp B A hB hA
          (by simpa only [show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl,dist_comm] using hsep) row C
          (Or.inl (show ((Q 1).descendant row.1).center ∈ ((Q 1).descendant B).carrier from
            hpar col₀ hcol₀ 1 (((Q 1).descendant row.1).center_mem ((Q 1).descendant_side_pos (hQp 1) row.1))))
          (Or.inr (show ((Q 0).descendant row.2).center ∈ ((Q 0).descendant A).carrier from
            hpar col₀ hcol₀ 3 (((Q 0).descendant row.2).center_mem ((Q 0).descendant_side_pos (hQp 0) row.2))))
          (fun col hc => hocc col hc 0) (fun col hc => hocc col hc 2)
          (fun col hc => hpar col hc 0) (fun col hc => hpar col hc 2)
          axis c₀ hc hcap j b true plus (rep ((j,b),plus)) hbins.1 hbins.2
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).1)
          (fun col hc => by simpa [hsc,sourceCenteredCellDirection,graphQuadCells,graphQuadPath,distanceMatrixIndex,θ,t,axis,Fin.rev] using (hact col hc).2)
          (fun col hc => (hdata col hc).2.2 0) (fun col hc => (hdata col hc).2.2 2)
          (fun col hc => by
            have hr := (hdata col hc).2.1
            have heq : graphQuadCells ![Q 0,Q 1,Q 1,Q 0] (distanceMatrixIndex col row j b plus).1 =
                ![distancePairCells (Q 1) (Q 0) row col 1,distancePairCells (Q 1) (Q 0) row col 0,
                  distancePairCells (Q 1) (Q 0) row col 3,distancePairCells (Q 1) (Q 0) row col 2] := by
              funext l
              fin_cases l <;> rfl
            rw [heq] at hr
            simpa only [Nat.cast_add,distanceMatrixIndex,show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl] using
              (graphRetainedDistance_reversal N sig (a+n) plus _ _).mp hr)
        simpa only [show (0:Fin 2).rev = 1 from rfl,show (1:Fin 2).rev = 0 from rfl,min_comm] using hh
      · change (C.card : ℝ) ≤ _
        rw [Finset.not_nonempty_iff_eq_empty.mp hn,Finset.card_empty,Nat.cast_zero]
        positivity
  · rw [activeDistanceMatrixNeighbors,ite_eq_right hs,Finset.card_empty,Nat.cast_zero]
    positivity

end PlanarFalconer

end OAI
