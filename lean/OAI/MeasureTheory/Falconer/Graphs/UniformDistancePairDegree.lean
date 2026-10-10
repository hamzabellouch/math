import OAI.MeasureTheory.Falconer.Estimates.DistanceCandidateWidth
import OAI.MeasureTheory.Falconer.Graphs.DistancePairDegree

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_inherited_distance_pair_degree {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ {ι : Fin 2 → Type} [∀ l, DecidableEq (ι l)],
    ∀ (S : ∀ l, Finset (ι l)) (d : ∀ l, ι l → PolicyDescriptor) (k : ∀ l, ι l → ℕ),
    ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) (m : Fin 2 → ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ (h : Fin 2 → Plane → ℂ) (e : ∀ l, ι l), (∀ l, e l ∈ S l) →
    ∀ a p : ℕ, (∀ l, d l (e l) = .parallel a p) → a ≤ p → p ≤ N →
    ∀ A B : CellPath, A.length = a → B.length = a →
    let X := (Q 0).descendant A
    let Y := (Q 1).descendant B
    dist X.center Y.center ≤ 2000*(2:ℝ)^(-(a:ℝ)) →
    ∀ (row : CellPath × CellPath) (C : Finset (CellPath × CellPath)),
    ((Q 0).descendant row.1).center ∈ X.carrier ∪ Y.carrier →
    ((Q 1).descendant row.2).center ∈ X.carrier ∪ Y.carrier →
    (∀ c ∈ C, c.1 ∈ occupiedAnchorPaths (Q 1) (ρ 1) p) →
    (∀ c ∈ C, c.2 ∈ occupiedAnchorPaths (Q 0) (ρ 0) p) →
    (∀ c ∈ C, ((Q 1).descendant c.1).carrier ⊆ Y.carrier) →
    (∀ c ∈ C, ((Q 0).descendant c.2).carrier ⊆ X.carrier) →
    ∀ axis c₀ : ℝ, 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    let β := fun l => inheritedCircleSymbol (S l) (d l) (k l) (Q l) (ρ l) (m l) N lam sig J i (h l)
    ∀ (j b : ℕ) (flip plus : Bool) (q : UnitCircle × UnitCircle),
    sourceCircleRotate (-axis) q.1 ∈ tsupport (circleAngularBin (angularBinCount θ) j) →
    sourceCircleRotate (-axis) q.2 ∈ tsupport (circleAngularBin (angularBinCount θ) b) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) j (sourceCircleRotate (-axis)
      (if flip then sourceRadialUnit ((Q 0).descendant row.1).center ((Q 1).descendant c.1).center
       else sourceRadialUnit ((Q 1).descendant c.1).center ((Q 0).descendant row.1).center)) (3*θ)) →
    (∀ c ∈ C, AngularBinActive (angularBinCount θ) b (sourceCircleRotate (-axis)
      (if !flip then sourceRadialUnit ((Q 1).descendant row.2).center ((Q 0).descendant c.2).center
       else sourceRadialUnit ((Q 0).descendant c.2).center ((Q 1).descendant row.2).center)) (3*θ)) →
    (∀ c ∈ C, RotatedAngularLabelEligible (ρ 1) ((Q 1).descendant c.1).carrier (β 1) (angularBinCount θ) j axis) →
    (∀ c ∈ C, RotatedAngularLabelEligible (ρ 0) ((Q 0).descendant c.2).carrier (β 0) (angularBinCount θ) b axis) →
    (∀ c ∈ C, GraphRetainedEdge N sig p true plus (distancePairCells (Q 0) (Q 1) row c) q) →
    (C.card : ℝ) ≤ 144*((2:ℝ)^N)^(min (height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a p)
      (height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a p)+2000*(lam+sig)+60*sig) := by
  classical
  obtain ⟨N₀,hcount⟩ := uniform_inherited_distance_candidates hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q hQ ρ m lam i hi h e he a p hd hap hp A B hA hB
  try dsimp only
  intro hsep row C hr₁ hr₂ ho₁ ho₂ hc₁ hc₂ axis c₀ hc hcap
  try dsimp only
  intro j b flip plus q hu hw ha₁ ha₂ hel₁ hel₂ hedge
  have hQp (l : Fin 2) : 0 < (Q l).side := by rw [hQ l]; norm_num
  have hside (l : Fin 2) (D : CellPath) (hD : D.length = a) :
      ((Q l).descendant D).side ≤ (2:ℝ)^(-(a:ℝ)) := by
    rw [DyadicSquare.descendant_side,hD,hQ l,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
  have h₁ := hcount N hN (S 1) (d 1) (k 1) (Q 1) (hQ 1) (ρ 1) (m 1) lam i hi (h 1) (e 1) (he 1)
    a p (hd 1) hap hp B hB (C.image Prod.fst)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ho₁ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hc₁ v hv)
    ((Q 0).descendant A) ((Q 1).descendant B)
    ((Q 0).descendant_side_pos (hQp 0) A) ((Q 1).descendant_side_pos (hQp 1) B)
    (hside 0 A hA) (hside 1 B hB) hsep (fun _ hx => Or.inr hx)
    ((Q 0).descendant row.1).center hr₁ q.1 axis c₀ hc hcap j flip hu
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ha₁ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel₁ v hv)
  have h₂ := hcount N hN (S 0) (d 0) (k 0) (Q 0) (hQ 0) (ρ 0) (m 0) lam i hi (h 0) (e 0) (he 0)
    a p (hd 0) hap hp A hA (C.image Prod.snd)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ho₂ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hc₂ v hv)
    ((Q 0).descendant A) ((Q 1).descendant B)
    ((Q 0).descendant_side_pos (hQp 0) A) ((Q 1).descendant_side_pos (hQp 1) B)
    (hside 0 A hA) (hside 1 B hB) hsep (fun _ hx => Or.inl hx)
    ((Q 1).descendant row.2).center hr₂ q.2 axis c₀ hc hcap b (!flip) hw
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact ha₂ v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel₂ v hv)
  let H₀ := height (fun t : ℕ => m 0 t-(t:ℝ)/(N:ℝ)) a p
  let H₁ := height (fun t : ℕ => m 1 t-(t:ℝ)/(N:ℝ)) a p
  have hn₁ := fun c hc => (Finset.mem_filter.mp (ho₁ c hc)).1
  have hn₂ := fun c hc => (Finset.mem_filter.mp (ho₂ c hc)).1
  rcases le_total H₀ H₁ with hmin | hmin
  · have hh := distance_pair_card_of_second_projection (Q 0) (Q 1) (hQ 1) N p hsig.le plus q row C hn₁ hedge _ h₂
    apply hh.trans_eq
    rw [min_eq_left hmin,mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  · have hh := distance_pair_card_of_projection (Q 0) (Q 1) (hQ 0) N p hsig.le plus q row C hn₂ hedge _ h₁
    apply hh.trans_eq
    rw [min_eq_right hmin,mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]

end PlanarFalconer

end OAI
