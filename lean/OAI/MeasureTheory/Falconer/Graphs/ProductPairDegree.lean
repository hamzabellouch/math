import OAI.MeasureTheory.Falconer.Recursion.ProductPrefixCount
import OAI.MeasureTheory.Falconer.Graphs.GraphFiberPacking

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

noncomputable def productPairCells (Q₁ Q₂ : DyadicSquare) (row col : CellPath × CellPath) :
    Fin 4 → DyadicSquare :=
  ![Q₁.descendant row.1,Q₁.descendant col.1,Q₂.descendant row.2,Q₂.descendant col.2]

theorem product_pair_fiber_card (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q)
    (P : CellPath) :
    ((C.filter (fun c => c.1 = P)).card : ℝ) ≤ 144*((2:ℝ)^N)^(60*sig) := by
  classical
  let F := C.filter (fun c => c.1 = P)
  by_cases hn : F.Nonempty
  · obtain ⟨c₀,hc₀⟩ := hn
    have hproj : (F.image Prod.snd).card = F.card := by
      apply Finset.card_image_iff.mpr
      intro c hc b hb he
      exact Prod.ext ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hb).2.symm) he
    change (F.card : ℝ) ≤ _
    rw [← hproj]
    apply graph_unit_center_fiber_card Q₂ hQ₂ N p hsig (F.image Prod.snd)
      (by
        intro b hb
        obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
        exact hlen c (Finset.mem_filter.mp hc).1)
      (Q₂.descendant c₀.2).center
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    have h0 := (hedge c₀ (Finset.mem_filter.mp hc₀).1).1
    have h1 := (hedge c (Finset.mem_filter.mp hc).1).1
    have he : c.1 = c₀.1 := (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hc₀).2.symm
    simp only [productPairCells,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] at h0 h1
    rw [he] at h1
    have hh := graphB_two_edges_close _ _ _ _ _ _ (graphSourceSign_cases false plus) h1 h0
    simpa only [dist_sub_left] using hh
  · have hz : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    change (F.card : ℝ) ≤ _
    rw [hz,Finset.card_empty,Nat.cast_zero]
    positivity

theorem product_pair_card_of_projection (Q₁ Q₂ : DyadicSquare) (hQ₂ : Q₂.side = 1)
    (N p : ℕ) {sig : ℝ} (hsig : 0 ≤ sig) (plus : Bool) (q : UnitCircle × UnitCircle)
    (row : CellPath × CellPath) (C : Finset (CellPath × CellPath))
    (hlen : ∀ c ∈ C, c.2 ∈ dyadicPaths p)
    (hedge : ∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q)
    (b : ℝ) (hproj : ((C.image Prod.fst).card : ℝ) ≤ b) :
    (C.card : ℝ) ≤ b*(144*((2:ℝ)^N)^(60*sig)) := by
  classical
  have he := Finset.card_eq_sum_card_image Prod.fst C
  calc
    _ = ∑ P ∈ C.image Prod.fst, ((C.filter (fun c => c.1 = P)).card : ℝ) := by exact_mod_cast he
    _ ≤ ∑ _P ∈ C.image Prod.fst, 144*((2:ℝ)^N)^(60*sig) :=
      Finset.sum_le_sum (fun P _ => product_pair_fiber_card Q₁ Q₂ hQ₂ N p hsig plus q row C hlen hedge P)
    _ = ((C.image Prod.fst).card : ℝ)*(144*((2:ℝ)^N)^(60*sig)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hproj (by positivity)

theorem uniform_inherited_product_pair_degree {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (d : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q₁ Q₂ : DyadicSquare, Q₁.side = 1 → Q₂.side = 1 →
    ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ), i < J →
    ∀ h : Plane → ℂ, ∀ e ∈ S, ∀ a g p : ℕ,
    d e = .parallel g p → a ≤ g → g ≤ p → p ≤ N → (g:ℝ)-a ≤ 2*sig*N →
    ∀ (A : CellPath) (row : CellPath × CellPath) (C : Finset (CellPath × CellPath)),
    (∀ c ∈ C, c.1 ∈ occupiedAnchorPaths Q₁ ρ p) →
    (∀ c ∈ C, c.1.take a = A) → (∀ c ∈ C, c.2 ∈ dyadicPaths p) →
    ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 2*Real.pi →
    let θ := graphAngularScale N sig ((p:ℝ)-a) c₀
    ∀ (j b : ℕ) (plus : Bool) (q : UnitCircle × UnitCircle),
    GraphSourceRepresentative false plus 0 θ j b q →
    (∀ c ∈ C, GraphRetainedEdge N sig p false plus (productPairCells Q₁ Q₂ row c) q) →
    (∀ c ∈ C, AngularLabelEligible ρ (Q₁.descendant c.1).carrier
      (inheritedCircleSymbol S d k Q₁ ρ m N lam sig J i h) (angularBinCount θ) j) →
    (C.card : ℝ) ≤ 144*((2:ℝ)^N)^(height (fun t : ℕ => m t-(t:ℝ)/(N:ℝ)) a p+2000*(lam+sig)+64*sig) := by
  obtain ⟨N₀,hcount⟩ := uniform_inherited_product_candidate_count hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S d k Q₁ Q₂ hQ₁ hQ₂ ρ m lam i hi h e he a g p hd hag hgp hp hgap A row C hC hparent hlen c₀ hc hcap
  dsimp only
  intro j b plus q hq hedge hel
  have hu := (graphSourceWeight_support_bins false plus 0 _ j b hq.1).1
  have hb := hcount N hN S d k Q₁ hQ₁ ρ m lam i hi h e he a g p hd hag hgp hp hgap
    A (C.image Prod.fst)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hC v hv)
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hparent v hv)
    (Q₁.descendant row.1).center q.1 c₀ hc hcap j hu
    (by
      intro c hc
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc
      exact hq.product_strip N sig p (productPairCells Q₁ Q₂ row v) (hedge v hv))
    (by intro c hc; obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hc; exact hel v hv)
  have hh := product_pair_card_of_projection Q₁ Q₂ hQ₂ N p hsig.le plus q row C hlen hedge _ hb
  refine hh.trans_eq ?_
  rw [mul_left_comm,← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^N)]
  congr 2
  ring

end PlanarFalconer

end OAI
