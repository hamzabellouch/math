import OAI.Combinatorics.CycleDecomposition.CostRegrouping

namespace OAI

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

structure Layers (P : AssignedPiece V) (Dstar : ℝ) where
  system : SplitSystem V
  count : ℕ
  positive : 0 < count
  cutoff : ∀ j < count, Dstar ≤ inductionScale P.vertices.card j
  last_lt : inductionScale P.vertices.card count < Dstar
  bounded : ∀ j < count, ∀ Q ∈ advance system 0 j [P],
    (system j Q).Bounded (inductionScale P.vertices.card j)
  degree : ∀ j ≤ count, ∀ Q ∈ advance system 0 j [P],
    2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j

theorem uniform_layers : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ Dstar ≥ D₀,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (P : AssignedPiece V),
    Dstar ≤ (P.vertices.card:ℝ) → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ P.vertices.card →
    Nonempty (Layers P Dstar) := by
  obtain ⟨Dsp,hsp⟩ := scale_splitter
  refine ⟨max Dsp 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro Dstar hD V _ _ P hn hdeg
  have hD1 : 1 < Dstar := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) ((le_max_right _ _).trans hD)
  have hn1 : 1 < (P.vertices.card:ℝ) := hD1.trans_le hn
  have hne : P.vertices.Nonempty := Finset.card_pos.mp (by exact_mod_cast (by linarith : (0:ℝ) < P.vertices.card))
  obtain ⟨split,hsplit⟩ := hsp V
  let s : SplitSystem V := fun j Q => split (inductionScale P.vertices.card j) Q
  have hs : ∀ j Q, Dstar ≤ inductionScale P.vertices.card j → Q.vertices.Nonempty →
      2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card j →
      (s j Q).Bounded (inductionScale P.vertices.card j) := by
    intro j Q hj hQ hd
    exact hsplit _ ((le_max_left _ _).trans (hD.trans hj)) Q hQ hd
  obtain ⟨m,hm,hlast,hcut⟩ := inductionScale_first_cutoff P.vertices.card Dstar hD1 hn
  have hL : ∀ Q ∈ [P], Q.vertices.Nonempty := by simpa using hne
  have hLd : ∀ Q ∈ [P], 2*(edgeCount Q.graph:ℝ)/Q.vertices.card ≤ inductionScale P.vertices.card 0 := by
    simpa only [List.mem_singleton,forall_eq,inductionScale_zero] using hdeg
  refine ⟨{ system := s, count := m, positive := hm, cutoff := hcut, last_lt := hlast, bounded := ?_, degree := ?_ }⟩
  · intro j hj
    simpa only [Nat.zero_add] using advance_bounded s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))
  · intro j hj
    simpa only [Nat.zero_add] using advance_valid s P.vertices.card Dstar (Nat.cast_nonneg _) hs
      0 j [P] hL hLd (fun l _ hl => hcut l (by omega))

variable {P : AssignedPiece V} {Dstar : ℝ}

abbrev Layers.frontier (H : Layers P Dstar) (j : ℕ) := advance H.system 0 j [P]
abbrev Layers.scale (_H : Layers P Dstar) (j : ℕ) := inductionScale (P.vertices.card:ℝ) j
abbrev Layers.mass (H : Layers P Dstar) (j : ℕ) := vertexMass (H.frontier j)
abbrev Layers.pieceMass (H : Layers P Dstar) (j : ℕ) := vertexMass (levelPieces H.system j (H.frontier j))

lemma Layers.mass_lower (H : Layers P Dstar) (j) : (P.vertices.card:ℝ) ≤ H.mass j :=
  advance_mass_lower H.system 0 j P

lemma Layers.mass_upper (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.mass (j+1) ≤ (1+80/logb 2 (H.scale j))*P.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn 0 (j+1) [P]
    (fun l hl => by simpa only [Nat.zero_add] using H.bounded l (by omega))
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) j (by norm_num; exact hlog j hj)
  simp only [Nat.zero_add,vertexMass_cons,vertexMass_nil,add_zero] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.mass,Layers.frontier,Layers.scale] at *
  nlinarith

lemma Layers.mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (k) (hk : k ≤ H.count) :
    H.mass k ≤ 2*P.vertices.card := by
  cases k with
  | zero => simp only [Layers.mass,Layers.frontier,advance_zero,vertexMass_cons,vertexMass_nil,add_zero]; nlinarith [(Nat.cast_nonneg P.vertices.card : (0:ℝ) ≤ _)]
  | succ j =>
    have hj : j < H.count := by omega
    have hh := H.mass_upper hn hlog j hj
    have hl := hlog j hj
    have hd : 80/logb 2 (H.scale j) ≤ 1 := (div_le_one (by linarith)).mpr hl
    have hc : (0:ℝ) ≤ P.vertices.card := Nat.cast_nonneg _
    nlinarith

lemma Layers.pieceMass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (j) (hj : j < H.count) :
    H.pieceMass j ≤ 2*P.vertices.card :=
  (levelPieces_mass H.system j (H.frontier j)).trans (by
    simpa only [Layers.mass,Layers.frontier,advance_succ,Nat.zero_add] using H.mass_two hn hlog (j+1) (by omega))

lemma Layers.cycles_bound (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hready : ∀ j < H.count, ErdosGallai.MainScaleReady 80 (H.scale j)) (j) (hj : j < H.count) :
    ((pastCycles H.system 0 (j+1) [P]).length:ℝ) ≤ 20*P.vertices.card/logb 2 (H.scale j) := by
  rw [pastCycles_length]
  apply (Finset.sum_le_sum (fun l hl => ?_)).trans
    (scale_prefix_cycle_cost P.vertices.card hn j (fun l => H.mass l)
      (fun l hl => H.mass_two hn (fun a ha => (hready a ha).log_large) l (by have := Finset.mem_range.mp hl; omega))
      (fun l hl => (hready l (by have := Finset.mem_range.mp hl; omega)).cycle_power))
  simpa only [Nat.zero_add] using levelCycles_length H.system l (H.frontier l) (H.scale l)
    (H.bounded l (by have := Finset.mem_range.mp hl; omega))

lemma Layers.subset (H : Layers P Dstar) (j) : ∀ Q ∈ H.frontier j, Q.vertices ⊆ P.vertices :=
  advance_subset H.system 0 j [P] P.vertices (by simp)

lemma Layers.box_subset (H : Layers P Dstar) (j) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier j) (hB : B ∈ (H.system j Q).boxes) : B.vertices ⊆ P.vertices :=
  ((H.system j Q).box_subset B hB).trans (H.subset j Q hQ)

lemma Layers.boundary_order (H : Layers P Dstar) (j) (hj : j < H.count)
    {Q : AssignedPiece V} (hQ : Q ∈ H.frontier (j+1)) :
    (Q.vertices.card:ℝ) ≤ (H.scale j)^(51/50:ℝ) := by
  simp only [Layers.frontier,advance_succ,Nat.zero_add] at hQ
  obtain ⟨T,hT,B,hB,hv,_⟩ := (nextLayer_mem H.system j _ Q).mp hQ
  rw [hv]
  exact (H.bounded j hj T hT).2.2.1 B hB

lemma Layers.local_mass (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤
      (1+80/logb 2 (H.scale (i+k)))*B.vertices.card := by
  have hh := advance_mass_global_product H.system P.vertices.card hn (i+1) k [(H.system i Q).rest B]
    (fun l hl R hR => by
      have hr := advance_local_mem H.system i l [P] hQ hB R hR
      have he : i+1+l = (i+l)+1 := by omega
      exact H.bounded (i+1+l) (by omega) R hr)
  have hx := scale_overlap_product P.vertices.card 2 hn (by norm_num) (i+k)
    (by norm_num; exact hlog (i+k) hik)
  simp only [vertexMass_cons,vertexMass_nil,add_zero,StageSplit.rest_vertices] at hh
  rw [show i+1+k=(i+k)+1 by omega] at hh
  have hx' := mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg B.vertices.card : (0:ℝ) ≤ _)
  norm_num only [show (40:ℝ)*2=80 by norm_num] at hx'
  dsimp only [Layers.scale] at *
  nlinarith

lemma Layers.local_mass_two (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ))
    (hlog : ∀ j < H.count, 80 ≤ logb 2 (H.scale j)) (i k)
    (hik : i+k < H.count) {Q B : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes) :
    vertexMass (advance H.system (i+1) k [(H.system i Q).rest B]) ≤ 2*B.vertices.card := by
  have hh := H.local_mass hn hlog i k hik hQ hB
  have hl := hlog (i+k) hik
  have hd : 80/logb 2 (H.scale (i+k)) ≤ 1 := (div_le_one (by linarith)).mpr hl
  have hc : (0:ℝ) ≤ B.vertices.card := Nat.cast_nonneg _
  nlinarith

lemma Layers.gap_order (H : Layers P Dstar) (hn : 1 < (P.vertices.card:ℝ)) (i)
    (hik : i+200 < H.count) {Q B R : AssignedPiece V}
    (hQ : Q ∈ H.frontier i) (hB : B ∈ (H.system i Q).boxes)
    (hR : R ∈ advance H.system (i+1) 200 [(H.system i Q).rest B]) :
    (R.vertices.card:ℝ) ≤ (H.scale i)^(1/1000:ℝ) ∧
      2*(edgeCount R.graph:ℝ)/R.vertices.card ≤ (H.scale i)^(1/1000:ℝ) := by
  have hr := advance_local_mem H.system i 200 [P] hQ hB R hR
  have hr' : R ∈ H.frontier ((i+200)+1) := by convert hr using 1
  have hd : 1 < H.scale i := inductionScale_gt_one P.vertices.card hn i
  constructor
  · have hh := H.boundary_order (i+200) hik hr'
    apply hh.trans
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity),← Real.rpow_mul (by linarith : 0 ≤ inductionScale P.vertices.card i)]
    apply Real.rpow_le_rpow_of_exponent_le hd.le
    nlinarith [inductionScale_window.1]
  · have hh := H.degree ((i+200)+1) (by omega) R hr'
    apply hh.trans
    rw [show i+200+1=i+201 by omega]
    dsimp only [Layers.scale]
    rw [inductionScale_add _ (by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hd.le inductionScale_window.2.le

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

lemma disjoint_subset_mass {V A : Type} [Fintype A] [DecidableEq V]
    (U : A → Finset V) (Y : Finset V) (hd : Pairwise fun r s => Disjoint (U r) (U s))
    (hu : ∀ r, U r ⊆ Y) : (∑ r, ((U r).card:ℝ)) ≤ Y.card := by
  have hc : (univ.biUnion U).card = ∑ r, (U r).card := Finset.card_biUnion (fun i _ j _ hij => hd hij)
  have hs : univ.biUnion U ⊆ Y := by
    intro v hv
    obtain ⟨r,_,hv⟩ := Finset.mem_biUnion.mp hv
    exact hu r hv
  have hh := Finset.card_le_card hs
  rw [hc] at hh
  exact_mod_cast hh

theorem uniform_box_cost : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, ∀ wmin : ℝ,
    MainScaleReady wmin D →
    ∀ (V A : Type) [Fintype V] [Fintype A],
    ∀ (G F : SimpleGraph V) (R : A → SimpleGraph V) (U : A → Finset V) (Y : Finset V),
    F ≤ G → (∀ r, R r ≤ G) →
    Pairwise (fun r s => Disjoint (R r).edgeSet (R s).edgeSet) →
    Pairwise (fun r s => Disjoint (U r) (U s)) →
    (∀ r, U r ⊆ Y) →
    (∀ r, ∀ ⦃x y⦄, (R r).Adj x y → x ∈ U r ∧ y ∈ U r) →
    (∀ r, Disjoint F.edgeSet (R r).edgeSet) →
    F.edgeSet ∪ (⋃ r, (R r).edgeSet) = G.edgeSet →
    (∀ r, Batch.CutExpansionOn (R r) (U r) (D^(9/10:ℝ))) →
    (∀ r, D^(9/10:ℝ) ≤ ((U r).card:ℝ) ∧ ((U r).card:ℝ) ≤ D^(51/50:ℝ)) →
    ((Y.card:ℝ) ≤ D^(51/50:ℝ)) →
    2*(F.edgeFinset.card:ℝ) ≤ 2*Y.card*D^(1/1000:ℝ) →
    ∀ T : ℝ, T ≤ 2*Y.card →
    ∀ _b : Indexing.GraphBatches F Y (D^(3/10:ℝ)) T,
    ∀ (n : ℕ) (C t : ℝ), 0 ≤ C → 0 ≤ t → Y.card ≤ n → D^(3/10:ℝ) < n →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (decompositionCost H:ℝ) ≤ C*Fintype.card Q) →
    (∀ (Q : Type) [Fintype Q] (H : SimpleGraph Q), Fintype.card Q < n →
      (Fintype.card Q:ℝ) ≤ D^(3/10:ℝ) → (Batch.decompositionCost H:ℝ) ≤ t*Fintype.card Q) →
    (Batch.decompositionCost G:ℝ) ≤
      t*(T-(∑ r, ((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D) +
      8*((∑ r, ((U r).card:ℝ))+T-Y.card) + (9+C*mainEta)*(∑ r, ((U r).card:ℝ)) := by
  obtain ⟨D₁,hD₁,hresolve⟩ := Batch.uniform_coupled_resolution_cost
  obtain ⟨D₂,hD₂,hpiece⟩ := uniform_piece_cost_on (1/4) mainEta (by norm_num) mainEta_pos
  refine ⟨max D₁ D₂,lt_of_lt_of_le hD₁ (le_max_left _ _),?_⟩
  intro D hD wmin hready V A _ _ G F R U Y hFG hRG hRR hUU hUY hRU hFR hcov hexp horder
    hY hF T hT b n C t hC ht hYn hsmall ih ihq
  have hD0 : 0 < D := by linarith [hready.gt_one]
  have ha : 1 ≤ D^(1/100:ℝ) := Real.one_le_rpow hready.gt_one.le (by norm_num)
  obtain ⟨a⟩ := Indexing.choose_active_family F Y b.vertices U (D^(1/100:ℝ)) (D^(3/100:ℝ))
    (Real.rpow_nonneg hD0.le _) b.subset hUY b.vertex_cover hUU
  let := a.finite
  have h8 (j) (i : a.Index j) : 8 ≤ (a.vertices j i).card := by
    have hh := hready.active_eight.trans (a.large j i)
    exact_mod_cast hh
  have hsquare (j) (i : a.Index j) : (D^(1/100:ℝ))^2 ≤ (a.vertices j i).card :=
    hready.active_square.trans (a.large j i)
  have hn (j) : (b.vertices j).card < n := by
    exact_mod_cast (b.order_le j).trans_lt hsmall
  obtain ⟨H,hHR,hHexp,hcost⟩ := hresolve D ((le_max_left _ _).trans hD) V A b.Index G F R U
    hFG hRG hRR hUU hRU hFR hcov hexp horder b.graph b.vertices b.graph_le b.disjoint b.edge_cover
    b.supported b.order_le a.Index a.vertices a.disjoint a.subset_batch a.router a.subset_router
    a.degree_le ha h8 hsquare n t ht hn ihq
  have hp (r : A) : (Batch.decompositionCost (H r):ℝ) ≤ (9+C*mainEta)*(U r).card := by
    have hh := hpiece D ((le_max_right _ _).trans hD) n C hC ih V (H r) (H r) (U r) le_rfl
      ((Finset.card_le_card (hUY r)).trans hYn) (fun x y h => hRU r (hHR r h)) (horder r).1 (horder r).2
      (by

        simpa only [CutExpansionOn,Batch.CutExpansionOn,show (1/4:ℝ)*D^(9/10:ℝ) = D^(9/10:ℝ)/4 by ring] using hHexp r)
    exact hh
  have hpsum : (∑ r, (Batch.decompositionCost (H r):ℝ)) ≤ (9+C*mainEta)*(∑ r, ((U r).card:ℝ)) := by
    simpa only [Finset.mul_sum] using Finset.sum_le_sum (s := univ) (fun r _ => hp r)
  have hbad : ((Y \ Indexing.goodVertices F Y (D^(1/100:ℝ))).card:ℝ) ≤ Y.card/logb 2 D :=
    hready.bad_count (Nat.cast_nonneg _) ((Indexing.bad_vertices_degree_bound F Y (D^(1/100:ℝ))).trans hF)
  have hrcount : D^(9/10:ℝ)*(Fintype.card A:ℝ) ≤ Y.card := by
    calc
      _ = ∑ _r : A, D^(9/10:ℝ) := by simp [mul_comm]
      _ ≤ ∑ r, ((U r).card:ℝ) := Finset.sum_le_sum (fun r _ => (horder r).1)
      _ ≤ _ := disjoint_subset_mass U Y hUU hUY
  have hskip := hready.skip_count (Nat.cast_nonneg Y.card) (Nat.cast_nonneg (Fintype.card b.Index))
    (Nat.cast_nonneg (Fintype.card A)) hY hT b.count_le hrcount
  have hlow : (∑ r, ((U r).card:ℝ))-2*Y.card/logb 2 D ≤ ∑ j, ∑ i, ((a.vertices j i).card:ℝ) := by
    have hh := a.lower
    simp only [div_eq_mul_inv] at hbad hskip hh ⊢
    linarith only [hh,hbad,hskip]
  have hhigh : (∑ j, ∑ i, ((a.vertices j i).card:ℝ)) ≤ (∑ r, ((U r).card:ℝ))+T-Y.card := by
    have hh := a.upper
    have hm := b.mass_le
    linarith
  have hhalf : (∑ j, ∑ i, ((a.vertices j i).card:ℝ))/3 ≤
      ∑ j, ∑ i, (((a.vertices j i).card / 2:ℕ):ℝ) := by
    simp only [Finset.sum_div]
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro i _
    exact Indexing.thirds_le_halves (h8 j i)
  have hq : (∑ j, ((b.vertices j).card:ℝ)) - ∑ j, ∑ i, (((a.vertices j i).card / 2:ℕ):ℝ) ≤
      T-(∑ r, ((U r).card:ℝ))/3+(2/3)*Y.card/logb 2 D := by
    have hm := b.mass_le
    simp only [div_eq_mul_inv] at hm hlow hhalf ⊢
    linarith only [hm,hlow,hhalf]
  have hqm := mul_le_mul_of_nonneg_left hq ht
  push_cast at hcost
  linarith

end
end ErdosGallai

end
end
end

end OAI
