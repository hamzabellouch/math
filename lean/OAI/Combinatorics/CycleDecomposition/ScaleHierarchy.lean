import OAI.Combinatorics.CycleDecomposition.ScaleExtraction

namespace OAI

universe u

universe cycleUniverse1 cycleUniverse2 cycleUniverse3 cycleUniverse4 cycleUniverse5 cycleUniverse6

section
open Filter Asymptotics Real
open scoped Topology
noncomputable section
open MeasureTheory ProbabilityTheory Finset
section
namespace ErdosGallai.Scale
open Finset SimpleGraph Classical Real
variable {V : Type cycleUniverse1} [Fintype V] [DecidableEq V]

lemma edgeOccurrences_refine {I : Type cycleUniverse2} (L : List I)
    (g : I → SimpleGraph V) (f : I → List (SimpleGraph V))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) (x y : V) :
    edgeOccurrences (L.flatMap f) x y = edgeOccurrences (L.map g) x y := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.flatMap_cons, edgeOccurrences_append, List.map_cons,
      edgeOccurrences_cons]
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma graphPartition_refine {I : Type cycleUniverse3} {G : SimpleGraph V}
    {C : List (SimpleGraph V)} {L : List I}
    {g : I → SimpleGraph V} {f : I → List (SimpleGraph V)}
    (hp : GraphPartition G (C ++ L.map g))
    (h : ∀ i ∈ L, GraphPartition (g i) (f i)) :
    GraphPartition G (C ++ L.flatMap f) := by
  intro x y
  simpa only [edgeOccurrences_append, edgeOccurrences_refine L g f h] using hp x y

theorem scale_split : ∃ Dsp : ℝ, ∀ D ≥ Dsp,
    ∀ (V : Type u) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) (A : Finset V), A.Nonempty → SupportedOn G A →
      2*(edgeCount G : ℝ)/A.card ≤ D →
    ∃ (C : List (SimpleGraph V)) (L : List (AssignedPiece V))
      (R : AssignedPiece V → List (AssignedPiece V))
      (H : AssignedPiece V → SimpleGraph V),
      (∀ K ∈ C, IsCycleGraph K ∧ D^(101/100:ℝ) ≤ (edgeCount K : ℝ)) ∧
      (C.length : ℝ) ≤ A.card/(2*D^(1/100:ℝ)) ∧
      (∀ P ∈ L, P.vertices ⊆ A ∧ P.vertices.Nonempty ∧
        (P.vertices.card : ℝ) ≤ D^(51/50:ℝ)) ∧
      (∀ x ∈ A, ∃ P ∈ L, x ∈ P.vertices) ∧
      (L.map (fun P => (P.vertices.card : ℝ))).sum ≤ (1+2/logb 2 D)*A.card ∧
      (∀ P ∈ L,
        (∀ Q ∈ R P, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        (R P).Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H P :: (R P).map AssignedPiece.graph) ∧
        SupportedOn (H P) P.vertices ∧
        2*(edgeCount (H P) : ℝ)/P.vertices.card ≤ D^(19/20:ℝ)) ∧
      GraphPartition G (C ++ L.flatMap (fun P => H P :: (R P).map AssignedPiece.graph)) := by
  classical
  obtain ⟨D₁,h₁⟩ := scale_boxes.{u}
  obtain ⟨D₂,h₂⟩ := scale_cut_extraction.{u}
  refine ⟨max D₁ D₂, ?_⟩
  intro D hD V _ _ G A hA hs hd
  obtain ⟨C,L,hC,hCN,hL,hcover,hp,hcost⟩ :=
    h₁ D ((le_max_left _ _).trans hD) V G A hA hs hd
  have hres : ∀ P : AssignedPiece V,
      ∃ (R : List (AssignedPiece V)) (H : SimpleGraph V), P ∈ L →
        (∀ Q ∈ R, Q.vertices ⊆ P.vertices ∧
          D^(9/10:ℝ) ≤ Q.vertices.card ∧
          (Q.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
          CutExpansionOn Q.graph Q.vertices (D^(9/10:ℝ))) ∧
        R.Pairwise (fun Q T => Disjoint Q.vertices T.vertices) ∧
        GraphPartition P.graph (H :: R.map AssignedPiece.graph) ∧
        SupportedOn H P.vertices ∧
        2*(edgeCount H : ℝ)/P.vertices.card ≤ D^(19/20:ℝ) := by
    intro P
    by_cases hP : P ∈ L
    · obtain ⟨R,H,hgood⟩ := h₂ D ((le_max_right _ _).trans hD) V
        P.graph P.vertices (hL P hP).2.1 P.supported (hL P hP).2.2
      exact ⟨R,H,fun _ => hgood⟩
    · exact ⟨[],⊥,fun hp => False.elim (hP hp)⟩
  choose R H hR using hres
  refine ⟨C,L,R,H,hC,hCN,hL,hcover,hcost,hR,?_⟩
  exact graphPartition_refine hp (fun P hP => (hR P hP).2.2.1)

end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Real Filter Finset
open scoped Topology

def scaleTheta : ℝ := 19/20
def inductionScale (n : ℝ) (j : ℕ) : ℝ := n ^ (scaleTheta ^ j)

lemma scaleTheta_pos : 0 < scaleTheta := by norm_num [scaleTheta]
lemma scaleTheta_lt_one : scaleTheta < 1 := by norm_num [scaleTheta]

lemma inductionScale_zero (n : ℝ) : inductionScale n 0 = n := by
  simp [inductionScale]

lemma inductionScale_pos (n : ℝ) (hn : 0 < n) (j : ℕ) :
    0 < inductionScale n j := Real.rpow_pos_of_pos hn _

lemma inductionScale_succ (n : ℝ) (hn : 0 ≤ n) (j : ℕ) :
    inductionScale n (j+1) = (inductionScale n j) ^ scaleTheta := by
  simp only [inductionScale, pow_succ, Real.rpow_mul hn]

lemma inductionScale_gt_one (n : ℝ) (hn : 1 < n) (j : ℕ) :
    1 < inductionScale n j := by
  simpa [inductionScale] using Real.rpow_lt_rpow_of_exponent_lt hn
    (pow_pos scaleTheta_pos j)

lemma inductionScale_le (n : ℝ) (hn : 1 ≤ n) (j : ℕ) :
    inductionScale n j ≤ n := by
  have hp : scaleTheta ^ j ≤ 1 := pow_le_one₀ scaleTheta_pos.le scaleTheta_lt_one.le
  simpa [inductionScale] using Real.rpow_le_rpow_of_exponent_le hn hp

lemma inductionScale_log (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n j) = scaleTheta ^ j * logb 2 n := by
  exact Real.logb_rpow_eq_mul_logb_of_pos hn

lemma inductionScale_log_pos (n : ℝ) (hn : 1 < n) (j : ℕ) :
    0 < logb 2 (inductionScale n j) := by
  exact Real.logb_pos (by norm_num) (inductionScale_gt_one n hn j)

lemma inductionScale_log_succ (n : ℝ) (hn : 0 < n) (j : ℕ) :
    logb 2 (inductionScale n (j+1)) = scaleTheta * logb 2 (inductionScale n j) := by
  rw [inductionScale_log n hn, inductionScale_log n hn, pow_succ]
  ring

lemma inductionScale_add (n : ℝ) (hn : 0 ≤ n) (i K : ℕ) :
    inductionScale n (i+K) = (inductionScale n i) ^ (scaleTheta ^ K) := by
  simp only [inductionScale, pow_add, Real.rpow_mul hn]

lemma inductionScale_window : (51/50 : ℝ) * scaleTheta ^ 200 < 1/1000 ∧
    scaleTheta ^ 201 < 1/1000 := by
  norm_num [scaleTheta]

lemma inductionScale_tendsto (n : ℝ) (hn : 0 < n) :
    Tendsto (inductionScale n) atTop (𝓝 1) := by
  have ht := (Real.continuous_const_rpow (ne_of_gt hn)).tendsto 0
  change Tendsto (fun j : ℕ => n ^ (scaleTheta ^ j)) atTop (𝓝 1)
  simpa only [Function.comp_def, Real.rpow_zero] using
    ht.comp (tendsto_pow_atTop_nhds_zero_of_lt_one scaleTheta_pos.le scaleTheta_lt_one)

theorem inductionScale_first_cutoff (n Dstar : ℝ) (hD : 1 < Dstar) (hn : Dstar ≤ n) :
    ∃ m : ℕ, 0 < m ∧ inductionScale n m < Dstar ∧
      ∀ j < m, Dstar ≤ inductionScale n j := by
  have hn0 : 0 < n := lt_trans (by norm_num) (hD.trans_le hn)
  have he : ∀ᶠ j in atTop, inductionScale n j < Dstar :=
    (inductionScale_tendsto n hn0).eventually (gt_mem_nhds hD)
  have hex : ∃ j, inductionScale n j < Dstar := he.exists
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · by_contra hm
    have hz : Nat.find hex = 0 := by omega
    have := Nat.find_spec hex
    rw [hz, inductionScale_zero] at this
    linarith
  · intro j hj
    exact le_of_not_gt (Nat.find_min hex hj)

theorem scale_reciprocal_log_sum (n : ℝ) (hn : 1 < n) (j : ℕ) :
    (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) ≤
      20 / logb 2 (inductionScale n j) := by
  induction j with
  | zero =>
    simp only [zero_add, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact div_le_div_of_nonneg_right (by norm_num) (inductionScale_log_pos n hn 0).le
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have hb : (∑ x ∈ range (j + 1), 1 / logb 2 (inductionScale n x)) +
        1 / logb 2 (inductionScale n (j+1)) ≤
        20 / logb 2 (inductionScale n j) + 1 / logb 2 (inductionScale n (j+1)) := by
      linarith [ih]
    apply hb.trans_eq
    rw [inductionScale_log_succ n (by linarith)]
    have hz : logb 2 (inductionScale n j) ≠ 0 := ne_of_gt (inductionScale_log_pos n hn j)
    dsimp [scaleTheta]
    field_simp
    ; ring

lemma exp_le_one_add_twice {x : ℝ} (hx : 0 ≤ x) (hxhalf : x ≤ 1/2) :
    exp x ≤ 1+2*x := by
  apply (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 1-x)).mpr
  nlinarith

theorem scale_overlap_product (n C₀ : ℝ) (hn : 1 < n) (hC : 0 ≤ C₀) (j : ℕ)
    (hcut : 40*C₀ ≤ logb 2 (inductionScale n j)) :
    (∏ l ∈ Finset.range (j+1), (1 + C₀ / logb 2 (inductionScale n l))) ≤
      1 + 40*C₀ / logb 2 (inductionScale n j) := by
  have hL := inductionScale_log_pos n hn j
  have hsum : (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) ≤
      20*C₀ / logb 2 (inductionScale n j) := by
    have hh := mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hC
    calc
      _ ≤ C₀ * (20 / logb 2 (inductionScale n j)) := by
        simpa only [Finset.mul_sum, mul_one_div] using hh
      _ = _ := by ring
  calc
    _ ≤ ∏ l ∈ Finset.range (j+1), exp (C₀ / logb 2 (inductionScale n l)) := by
      apply Finset.prod_le_prod₀
      · intro l hl
        have := div_nonneg hC (inductionScale_log_pos n hn l).le
        linarith
      · intro l hl
        simpa [add_comm] using Real.add_one_le_exp (C₀ / logb 2 (inductionScale n l))
    _ = exp (∑ l ∈ Finset.range (j+1), C₀ / logb 2 (inductionScale n l)) :=
      (Real.exp_sum _ _).symm
    _ ≤ exp (20*C₀ / logb 2 (inductionScale n j)) := Real.exp_le_exp.mpr hsum
    _ ≤ 1 + 2*(20*C₀ / logb 2 (inductionScale n j)) := by
      apply exp_le_one_add_twice (div_nonneg (by positivity) hL.le)
      apply (div_le_iff₀ hL).mpr
      linarith
    _ = _ := by ring

theorem scale_prefix_cycle_cost (n : ℝ) (hn : 1 < n) (j : ℕ) (A : ℕ → ℝ)
    (hA : ∀ l ∈ Finset.range (j+1), A l ≤ 2*n)
    (hscale : ∀ l ∈ Finset.range (j+1),
      1 / (inductionScale n l) ^ (1/100 : ℝ) ≤ 1 / logb 2 (inductionScale n l)) :
    (∑ l ∈ Finset.range (j+1), A l / (2*(inductionScale n l) ^ (1/100 : ℝ))) ≤
      20*n / logb 2 (inductionScale n j) := by
  have hn0 : 0 < n := by linarith
  calc
    _ ≤ ∑ l ∈ Finset.range (j+1), n * (1 / logb 2 (inductionScale n l)) := by
      apply Finset.sum_le_sum
      intro l hl
      have hp : 0 < (inductionScale n l) ^ (1/100 : ℝ) :=
        Real.rpow_pos_of_pos (inductionScale_pos n hn0 l) _
      calc
        _ ≤ 2*n / (2*(inductionScale n l) ^ (1/100 : ℝ)) :=
          div_le_div_of_nonneg_right (hA l hl) (by positivity)
        _ = n * (1 / (inductionScale n l) ^ (1/100 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hscale l hl) hn0.le
    _ = n * (∑ l ∈ Finset.range (j+1), 1 / logb 2 (inductionScale n l)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ n * (20 / logb 2 (inductionScale n j)) :=
      mul_le_mul_of_nonneg_left (scale_reciprocal_log_sum n hn j) hn0.le
    _ = _ := by ring

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

structure StageSplit (P : AssignedPiece V) where
  cycles : List (SimpleGraph V)
  boxes : List (AssignedPiece V)
  pieces : AssignedPiece V → List (AssignedPiece V)
  remainder : AssignedPiece V → SimpleGraph V
  cycles_good : ∀ K ∈ cycles, IsCycleGraph K
  box_subset : ∀ B ∈ boxes, B.vertices ⊆ P.vertices
  box_nonempty : P.vertices.Nonempty → ∀ B ∈ boxes, B.vertices.Nonempty
  box_cover : ∀ v ∈ P.vertices, ∃ B ∈ boxes, v ∈ B.vertices
  piece_subset : ∀ B ∈ boxes, ∀ R ∈ pieces B, R.vertices ⊆ B.vertices
  piece_disjoint : ∀ B ∈ boxes, (pieces B).Pairwise fun R S => Disjoint R.vertices S.vertices
  remainder_supported : ∀ B ∈ boxes, SupportedOn (remainder B) B.vertices
  box_partition : ∀ B ∈ boxes, GraphPartition B.graph (remainder B :: (pieces B).map AssignedPiece.graph)
  partition : GraphPartition P.graph (cycles ++ boxes.map AssignedPiece.graph)

def StageSplit.Bounded {P : AssignedPiece V} (s : StageSplit P) (D : ℝ) : Prop :=
  (s.cycles.length:ℝ) ≤ P.vertices.card / (2*D^(1/100:ℝ)) ∧
  (s.boxes.map (fun B => (B.vertices.card:ℝ))).sum ≤ (1+2/logb 2 D)*P.vertices.card ∧
  (∀ B ∈ s.boxes, (B.vertices.card:ℝ) ≤ D^(51/50:ℝ)) ∧
  (∀ B ∈ s.boxes, ∀ R ∈ s.pieces B,
    D^(9/10:ℝ) ≤ (R.vertices.card:ℝ) ∧ (R.vertices.card:ℝ) ≤ D^(51/50:ℝ) ∧
    CutExpansionOn R.graph R.vertices (D^(9/10:ℝ))) ∧
  (∀ B ∈ s.boxes, 2*(edgeCount (s.remainder B):ℝ)/B.vertices.card ≤ D^(19/20:ℝ))

def StageSplit.trivial (P : AssignedPiece V) : StageSplit P where
  cycles := []
  boxes := [P]
  pieces := fun _ => []
  remainder := AssignedPiece.graph
  cycles_good := by simp
  box_subset := by simp
  box_nonempty := by simp
  box_cover := by intro v hv; exact ⟨P,by simp,hv⟩
  piece_subset := by simp
  piece_disjoint := by simp
  remainder_supported := fun B _ => B.supported
  box_partition := by intro B _ x y; simp
  partition := by intro x y; simp

theorem scale_splitter : ∃ Dsp : ℝ, ∀ (V : Type) [Fintype V] [DecidableEq V],
    ∃ split : ∀ (_D : ℝ) (P : AssignedPiece V), StageSplit P,
      ∀ D ≥ Dsp, ∀ P, P.vertices.Nonempty →
        2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → (split D P).Bounded D := by
  obtain ⟨Dsp,hsp⟩ := scale_split
  refine ⟨Dsp,?_⟩
  intro V _ _
  have hex (D : ℝ) (P : AssignedPiece V) : ∃ s : StageSplit P,
      Dsp ≤ D → P.vertices.Nonempty → 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D → s.Bounded D := by
    by_cases h : Dsp ≤ D ∧ P.vertices.Nonempty ∧ 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ D
    · obtain ⟨C,L,R,H,hC,hCl,hL,hcover,horder,hR,hpart⟩ :=
        hsp D h.1 V P.graph P.vertices h.2.1 P.supported h.2.2
      have hpart' : GraphPartition P.graph (C ++ L.map AssignedPiece.graph) := by
        intro x y
        rw [edgeOccurrences_append, ← edgeOccurrences_refine L AssignedPiece.graph
          (fun B => H B :: (R B).map AssignedPiece.graph) (fun B hB => (hR B hB).2.2.1)]
        simpa only [edgeOccurrences_append] using hpart x y
      let s : StageSplit P := {
        cycles := C, boxes := L, pieces := R, remainder := H
        cycles_good := fun K hK => (hC K hK).1
        box_subset := fun B hB => (hL B hB).1
        box_nonempty := fun _ B hB => (hL B hB).2.1
        box_cover := hcover
        piece_subset := fun B hB Q hQ => (hR B hB).1 Q hQ |>.1
        piece_disjoint := fun B hB => (hR B hB).2.1
        remainder_supported := fun B hB => (hR B hB).2.2.2.1
        box_partition := fun B hB => (hR B hB).2.2.1
        partition := hpart' }
      refine ⟨s,fun _ _ _ => ⟨hCl,horder,fun B hB => (hL B hB).2.2,?_,?_⟩⟩
      · exact fun B hB Q hQ => (hR B hB).1 Q hQ |>.2
      · exact fun B hB => (hR B hB).2.2.2.2
    · exact ⟨StageSplit.trivial P,fun hD hP hdeg => False.elim (h ⟨hD,hP,hdeg⟩)⟩
  choose s hs using hex
  exact ⟨s,fun D hD P hP hdeg => hs D P hD hP hdeg⟩

def StageSplit.children {P : AssignedPiece V} (s : StageSplit P) : List (AssignedPiece V) :=
  s.boxes.pmap (fun B hB => ⟨B.vertices,s.remainder B,s.remainder_supported B hB⟩) (fun _ h => h)

lemma StageSplit.mem_children {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (Q : AssignedPiece V) :
    Q ∈ s.children ↔ ∃ B ∈ s.boxes, Q.vertices = B.vertices ∧ Q.graph = s.remainder B := by
  simp only [StageSplit.children, List.mem_pmap]
  constructor
  · rintro ⟨B,hB,rfl⟩; exact ⟨B,hB,rfl,rfl⟩
  · rintro ⟨B,hB,hv,hg⟩
    refine ⟨B,hB,?_⟩
    cases Q; cases B; simp_all

lemma StageSplit.children_map {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P)
    {α : Type cycleUniverse4} (f : Finset V → SimpleGraph V → α) :
    s.children.map (fun Q => f Q.vertices Q.graph) =
      s.boxes.map (fun B => f B.vertices (s.remainder B)) := by
  unfold StageSplit.children
  rw [List.map_pmap]
  change List.pmap (fun B (_ : B ∈ s.boxes) => f B.vertices (s.remainder B)) s.boxes _ = _
  exact List.pmap_eq_map (fun B (h : B ∈ s.boxes) => h)

lemma list_disjoint_card_le {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (Finset V)) (A : Finset V)
    (hd : L.Pairwise Disjoint) (hA : ∀ B ∈ L, B ⊆ A) :
    (L.map Finset.card).sum ≤ A.card := by
  induction L generalizing A with
  | nil => simp
  | cons B L ih =>
    obtain ⟨hBL,hd⟩ := List.pairwise_cons.mp hd
    have hBA := hA B (by simp)
    have hLA : ∀ C ∈ L, C ⊆ A \ B := by
      intro C hC v hv
      exact Finset.mem_sdiff.mpr ⟨hA C (by simp [hC]) hv,
        fun hb => Finset.disjoint_left.mp (hBL C hC) hb hv⟩
    have hh := ih (A \ B) hd hLA
    have hc := Finset.card_sdiff_of_subset hBA
    have hBAcard := Finset.card_le_card hBA
    simp only [List.map_cons,List.sum_cons]
    omega

def vertexMass (L : List (AssignedPiece V)) : ℝ :=
  (L.map (fun P => (P.vertices.card:ℝ))).sum

lemma vertexMass_nonneg {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) : 0 ≤ vertexMass L :=
  List.sum_nonneg (fun x hx => by obtain ⟨P,_,rfl⟩ := List.mem_map.mp hx; positivity)

@[simp] lemma vertexMass_nil {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] : vertexMass ([] : List (AssignedPiece V)) = 0 := rfl
@[simp] lemma vertexMass_cons {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (P : AssignedPiece V) (L) :
    vertexMass (P::L) = P.vertices.card + vertexMass L := rfl
@[simp] lemma vertexMass_append {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L M : List (AssignedPiece V)) :
    vertexMass (L++M) = vertexMass L + vertexMass M := by simp [vertexMass]
lemma vertexMass_flatMap {I : Type cycleUniverse5} (L : List I) (f : I → List (AssignedPiece V)) :
    vertexMass (L.flatMap f) = (L.map (fun i => vertexMass (f i))).sum := by
  induction L with
  | nil => simp
  | cons i L ih => simp [ih]

lemma StageSplit.children_mass {P : AssignedPiece V} (s : StageSplit P) :
    vertexMass s.children = vertexMass s.boxes := by
  unfold vertexMass
  rw [s.children_map (fun A _ => (A.card:ℝ))]

lemma StageSplit.pieces_mass {P : AssignedPiece V} (s : StageSplit P) {B : AssignedPiece V}
    (hB : B ∈ s.boxes) : vertexMass (s.pieces B) ≤ B.vertices.card := by
  have hh := list_disjoint_card_le ((s.pieces B).map AssignedPiece.vertices) B.vertices
    (List.pairwise_map.mpr (s.piece_disjoint B hB)) (by
      intro A hA; obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hA
      exact s.piece_subset B hB Q hQ)
  simpa [vertexMass,List.map_map,Function.comp_def] using (Nat.cast_le.mpr hh : (_:ℝ) ≤ _)

end
end ErdosGallai.Scale

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

abbrev SplitSystem (V : Type) [Fintype V] [DecidableEq V] :=
  ℕ → (P : AssignedPiece V) → StageSplit P

def nextLayer (s : SplitSystem V) (j : ℕ) (L : List (AssignedPiece V)) : List (AssignedPiece V) :=
  L.flatMap fun P => (s j P).children

def advance (s : SplitSystem V) (j : ℕ) : ℕ → List (AssignedPiece V) → List (AssignedPiece V)
  | 0,L => L
  | k+1,L => nextLayer s (j+k) (advance s j k L)

@[simp] lemma advance_zero (s : SplitSystem V) (j) (L) : advance s j 0 L = L := rfl
@[simp] lemma advance_succ (s : SplitSystem V) (j k) (L) :
    advance s j (k+1) L = nextLayer s (j+k) (advance s j k L) := rfl

lemma advance_add (s : SplitSystem V) (j k l) (L) :
    advance s j (k+l) L = advance s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp
  | succ l ih => simp only [Nat.add_succ,advance_succ,ih,Nat.add_assoc]

lemma advance_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse6}
    (L : List I) (f : I → List (AssignedPiece V)) :
    advance s j k (L.flatMap f) = L.flatMap (fun i => advance s j k (f i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [advance_succ,nextLayer,ih,List.flatMap_assoc]

lemma nextLayer_mem (s : SplitSystem V) (j) (L) (Q : AssignedPiece V) :
    Q ∈ nextLayer s j L ↔ ∃ P ∈ L, ∃ B ∈ (s j P).boxes,
      Q.vertices = B.vertices ∧ Q.graph = (s j P).remainder B := by
  simp only [nextLayer,List.mem_flatMap,StageSplit.mem_children]

lemma advance_subset (s : SplitSystem V) (j k) (L) (A : Finset V)
    (hA : ∀ P ∈ L, P.vertices ⊆ A) :
    ∀ Q ∈ advance s j k L, Q.vertices ⊆ A := by
  induction k with
  | zero => exact hA
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact ((s (j+k) P).box_subset B hB).trans (ih P hP)

lemma advance_nonempty (s : SplitSystem V) (j k) (L)
    (hL : ∀ P ∈ L, P.vertices.Nonempty) :
    ∀ Q ∈ advance s j k L, Q.vertices.Nonempty := by
  induction k with
  | zero => exact hL
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,_⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    rw [hv]
    exact (s (j+k) P).box_nonempty (ih P hP) B hB

lemma advance_cover (s : SplitSystem V) (j k) (L) (P : AssignedPiece V) (hP : P ∈ L)
    (v : V) (hv : v ∈ P.vertices) : ∃ Q ∈ advance s j k L, v ∈ Q.vertices := by
  induction k with
  | zero => exact ⟨P,hP,hv⟩
  | succ k ih =>
    obtain ⟨Q,hQ,hvQ⟩ := ih
    obtain ⟨B,hB,hvB⟩ := (s (j+k) Q).box_cover v hvQ
    let T : AssignedPiece V := ⟨B.vertices,(s (j+k) Q).remainder B,
      (s (j+k) Q).remainder_supported B hB⟩
    exact ⟨T,(nextLayer_mem s (j+k) _ T).mpr ⟨Q,hQ,B,hB,rfl,rfl⟩,hvB⟩

lemma list_union_mem {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) (v : V) :
    v ∈ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ ↔ ∃ P ∈ L, v ∈ P.vertices := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,Finset.mem_union,ih,List.mem_cons]
    aesop

lemma list_union_card {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] (L : List (AssignedPiece V)) :
    ((L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤ vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    simp only [List.foldr_cons,vertexMass_cons]
    have hc := Finset.card_union_le P.vertices (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅)
    have hc' : ((P.vertices ∪ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card:ℝ) ≤
        P.vertices.card + (L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅).card := by exact_mod_cast hc
    linarith

lemma list_cover_card_le (L : List (AssignedPiece V)) (A : Finset V)
    (hcover : ∀ v ∈ A, ∃ P ∈ L, v ∈ P.vertices) : (A.card:ℝ) ≤ vertexMass L := by
  have hsub : A ⊆ L.foldr (fun (P : AssignedPiece V) (U : Finset V) => P.vertices ∪ U) ∅ :=
    fun v hv => (list_union_mem L v).mpr (hcover v hv)
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (list_union_card L)

lemma advance_mass_lower (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (P.vertices.card:ℝ) ≤ vertexMass (advance s j k [P]) :=
  list_cover_card_le _ _ (fun v hv => advance_cover s j k [P] P (by simp) v hv)

lemma nextLayer_mass_bound (s : SplitSystem V) (j) (L : List (AssignedPiece V)) (D : ℝ)
    (hb : ∀ P ∈ L, (s j P).Bounded D) :
    vertexMass (nextLayer s j L) ≤ (1+2/logb 2 D)*vertexMass L := by
  induction L with
  | nil => simp [nextLayer]
  | cons P L ih =>
    have hP := (hb P (by simp)).2.1
    have hL := ih (fun Q hQ => hb Q (by simp [hQ]))
    simp only [nextLayer,List.flatMap_cons,vertexMass_append,StageSplit.children_mass,
      vertexMass_cons] at hL ⊢
    change vertexMass (s j P).boxes ≤ _ at hP
    nlinarith

lemma advance_valid (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l < j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L,
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n (j+k) := by
  induction k with
  | zero => simpa using hdeg
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    have hPdeg := ih (fun l hlj hl => hcut l hlj (by omega)) P hP
    have hb := hs (j+k) P (hcut (j+k) (by omega) (by omega))
      (advance_nonempty s j k L hL P hP) hPdeg
    rw [hv,hg,show j+(k+1) = (j+k)+1 by omega,inductionScale_succ n hn]
    exact hb.2.2.2.2 B hB

lemma advance_bounded (s : SplitSystem V) (n Dstar : ℝ) (hn : 0 ≤ n)
    (hs : ∀ l P, Dstar ≤ inductionScale n l → P.vertices.Nonempty →
      2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n l →
      (s l P).Bounded (inductionScale n l))
    (j k : ℕ) (L : List (AssignedPiece V))
    (hL : ∀ P ∈ L, P.vertices.Nonempty)
    (hdeg : ∀ P ∈ L, 2*(edgeCount P.graph:ℝ)/P.vertices.card ≤ inductionScale n j)
    (hcut : ∀ l, j ≤ l → l ≤ j+k → Dstar ≤ inductionScale n l) :
    ∀ P ∈ advance s j k L, (s (j+k) P).Bounded (inductionScale n (j+k)) := by
  intro P hP
  exact hs (j+k) P (hcut _ (by omega) (by omega)) (advance_nonempty s j k L hL P hP)
    (advance_valid s n Dstar hn hs j k L hL hdeg (fun l hlj hl => hcut l hlj (by omega)) P hP)

lemma advance_mass_global_product (s : SplitSystem V) (n : ℝ) (hn : 1 < n)
    (j k : ℕ) (L : List (AssignedPiece V))
    (hb : ∀ l < k, ∀ P ∈ advance s j l L, (s (j+l) P).Bounded (inductionScale n (j+l))) :
    vertexMass (advance s j k L) ≤ vertexMass L *
      ∏ l ∈ Finset.range (j+k), (1+2/logb 2 (inductionScale n l)) := by
  have hfac (l) : 1 ≤ 1+2/logb 2 (inductionScale n l) := by
    have := div_nonneg (by norm_num : (0:ℝ) ≤ 2) (inductionScale_log_pos n hn l).le
    linarith
  induction k with
  | zero =>
    simp only [advance_zero,Nat.add_zero]
    exact le_mul_of_one_le_right (vertexMass_nonneg L) (Finset.one_le_prod₀ (fun l _ => hfac l))
  | succ k ih =>
    have hm := nextLayer_mass_bound s (j+k) (advance s j k L) (inductionScale n (j+k))
      (hb k (by omega))
    have hi := mul_le_mul_of_nonneg_left (ih (fun l hl => hb l (by omega))) ((hfac (j+k)).trans' (by norm_num : (0:ℝ) ≤ 1))
    rw [advance_succ,show j+(k+1) = (j+k)+1 by omega,Finset.prod_range_succ]
    calc
      _ ≤ (1+2/logb 2 (inductionScale n (j+k))) * vertexMass (advance s j k L) := hm
      _ ≤ _ := by nlinarith only [hi]

end
end ErdosGallai.Scale
end
end
end

end OAI
