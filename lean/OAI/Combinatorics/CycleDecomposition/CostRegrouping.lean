import OAI.Combinatorics.CycleDecomposition.PrefixSelection

namespace OAI

universe cycleUniverse1 cycleUniverse2

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

def StageSplit.rest {P : AssignedPiece V} (s : StageSplit P) (B : AssignedPiece V) : AssignedPiece V :=
  if h : B ∈ s.boxes then ⟨B.vertices,s.remainder B,s.remainder_supported B h⟩ else B

@[simp] lemma StageSplit.rest_vertices {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) (B) :
    (s.rest B).vertices = B.vertices := by unfold StageSplit.rest; split_ifs <;> rfl
lemma StageSplit.rest_graph {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) {B} (hB : B ∈ s.boxes) :
    (s.rest B).graph = s.remainder B := by simp [StageSplit.rest,hB]
lemma StageSplit.children_eq_map_rest {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {P : AssignedPiece V} (s : StageSplit P) :
    s.children = s.boxes.map s.rest := by
  unfold StageSplit.children
  rw [← List.pmap_eq_map (f := s.rest) (fun B (hB : B ∈ s.boxes) => hB)]
  apply List.pmap_congr_left
  intro B hB
  simp [StageSplit.rest,hB]

lemma pastPieces_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse1}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastPieces s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastPieces s j k (f i))) := by
  induction k with
  | zero => simp [pastPieces]
  | succ k ih =>
    simp only [pastPieces,advance_flatMap,levelPieces,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _
lemma pastCycles_flatMap (s : SplitSystem V) (j k) {I : Type cycleUniverse2}
    (L : List I) (f : I → List (AssignedPiece V)) :
    (pastCycles s j k (L.flatMap f)).Perm (L.flatMap (fun i => pastCycles s j k (f i))) := by
  induction k with
  | zero => simp [pastCycles]
  | succ k ih =>
    simp only [pastCycles,advance_flatMap,levelCycles,List.flatMap_assoc]
    apply (ih.append_right _).trans
    exact List.flatMap_append_perm _ _ _

lemma pastPieces_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastPieces s j (k+l) L = pastPieces s j k L ++ pastPieces s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastPieces]
  | succ l ih => simp [pastPieces,ih,advance_add,Nat.add_assoc,List.append_assoc]
lemma pastCycles_add (s : SplitSystem V) (j k l) (L : List (AssignedPiece V)) :
    pastCycles s j (k+l) L = pastCycles s j k L ++ pastCycles s (j+k) l (advance s j k L) := by
  induction l with
  | zero => simp [pastCycles]
  | succ l ih => simp [pastCycles,ih,advance_add,Nat.add_assoc,List.append_assoc]

lemma advance_mem_mono (s : SplitSystem V) (j k) {L M : List (AssignedPiece V)}
    (h : ∀ P ∈ L, P ∈ M) : ∀ Q ∈ advance s j k L, Q ∈ advance s j k M := by
  induction k with
  | zero => exact h
  | succ k ih =>
    intro Q hQ
    obtain ⟨P,hP,B,hB,hv,hg⟩ := (nextLayer_mem s (j+k) _ Q).mp hQ
    exact (nextLayer_mem s (j+k) _ Q).mpr ⟨P,ih P hP,B,hB,hv,hg⟩

lemma advance_local_mem (s : SplitSystem V) (i k) (L : List (AssignedPiece V))
    {P B : AssignedPiece V} (hP : P ∈ advance s 0 i L) (hB : B ∈ (s i P).boxes) :
    ∀ Q ∈ advance s (i+1) k [(s i P).rest B], Q ∈ advance s 0 (i+1+k) L := by
  rw [advance_add, Nat.zero_add]
  apply advance_mem_mono
  intro Q hQ
  simp only [List.mem_singleton] at hQ
  subst Q
  simp only [advance_succ,Nat.zero_add]

  apply (nextLayer_mem s i _ _).mpr
  exact ⟨P,hP,B,hB,(s i P).rest_vertices B,(s i P).rest_graph hB⟩

lemma box_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) :
    GraphPartition B.graph
      (pastCycles s j k [R] ++ (pastPieces s j k [R]).map AssignedPiece.graph ++
        [graphUnion ((advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph)]) := by
  let L := (advance s j k [R]).map AssignedPiece.graph ++ A.map AssignedPiece.graph
  have hL : GraphPartition (graphUnion L) L := by
    apply graphPartition_of_le_one
    intro x y
    have hb := hBR x y
    have hr := past_partition s j k R x y
    simp only [edgeOccurrences_cons,edgeOccurrences_append] at hb hr ⊢
    dsimp only [L]
    rw [edgeOccurrences_append]
    split_ifs at hb hr <;> omega
  intro x y
  have hb := hBR x y
  have hr := past_partition s j k R x y
  have hl := hL x y
  simp only [edgeOccurrences_cons,edgeOccurrences_append,edgeOccurrences_nil,Nat.add_zero] at hb hr hl ⊢
  dsimp only [L] at hl
  rw [edgeOccurrences_append] at hl
  omega

lemma piece_list_cost (L : List (AssignedPiece V)) (c : ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card) :
    (L.map (fun P => (decompositionCost P.graph:ℝ))).sum ≤ c*vertexMass L := by
  induction L with
  | nil => simp
  | cons P L ih =>
    have hp := h P (by simp)
    have hl := ih (fun Q hQ => h Q (by simp [hQ]))
    simp only [List.map_cons,List.sum_cons,vertexMass_cons]
    nlinarith

lemma box_cost_regroup {B R : AssignedPiece V} (A : List (AssignedPiece V))
    (hBR : GraphPartition B.graph (R.graph :: A.map AssignedPiece.graph))
    (s : SplitSystem V) (j k : ℕ) (c q : ℝ)
    (hp : ∀ P ∈ pastPieces s j k [R], (decompositionCost P.graph:ℝ) ≤ c*P.vertices.card)
    (hq : (decompositionCost (graphUnion ((advance s j k [R]).map AssignedPiece.graph ++
      A.map AssignedPiece.graph)):ℝ) ≤ q) :
    (decompositionCost B.graph:ℝ) ≤ (pastCycles s j k [R]).length +
      c*vertexMass (pastPieces s j k [R]) + q := by
  have hh := decompositionCost_partition_real (box_regroup A hBR s j k)
  have hc := decompositionCost_cycles (pastCycles s j k [R]) (pastCycles_good s j k [R])
  have hm := piece_list_cost (pastPieces s j k [R]) c hp
  simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    add_zero,List.map_map,Function.comp_def] at hh
  linarith

end
end ErdosGallai.Scale

end

section

namespace ErdosGallai
noncomputable section
open Real Filter

def mainP : ℝ := 804
def mainEta : ℝ := 1/(100*mainP)
def mainH : ℝ := 80/(Scale.scaleTheta^200)
def mainA₁ : ℝ := mainH + 4/3
def mainA₂ : ℝ := max (9*mainP+8) (9*mainH)
lemma mainP_pos : 0 < mainP := by norm_num [mainP]
lemma mainEta_pos : 0 < mainEta := by norm_num [mainEta,mainP]
lemma mainH_pos : 0 < mainH := by unfold mainH; exact div_pos (by norm_num) (pow_pos Scale.scaleTheta_pos _)
lemma mainA₁_nonneg : 0 ≤ mainA₁ := by unfold mainA₁; linarith [mainH_pos]
lemma mainA₂_nonneg : 0 ≤ mainA₂ := by unfold mainA₂; exact (by norm_num [mainP] : (0:ℝ) ≤ 9*mainP+8).trans (le_max_left _ _)
lemma mainEta_mul_P : mainEta*mainP = 1/100 := by norm_num [mainEta,mainP]
lemma mainP_eq : mainP = 4*(200+1:ℝ) := by norm_num [mainP]

structure MainScaleReady (wmin D : ℝ) : Prop where
  gt_one : 1 < D
  log_large : wmin ≤ logb 2 D
  cycle_power : 1/(D^(1/100:ℝ)) ≤ 1/logb 2 D
  batch_power : D^(1/1000:ℝ) ≤ D^(3/10:ℝ)/2
  bad_power : 2*D^(-9/1000:ℝ) ≤ 1/logb 2 D
  skip_power : D^(-87/100:ℝ)+4*D^(-3/20:ℝ) ≤ 1/logb 2 D
  active_eight : 8 ≤ D^(3/100:ℝ)

lemma eventually_inverse_power_log (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ D : ℝ in atTop, C*D^(-ε) ≤ 1/logb 2 D := by
  filter_upwards [Batch.eventually_logb_le_power (ε/2) (by positivity),
    Batch.eventually_const_mul_power_le C (ε/2) ε (by linarith),
    eventually_gt_atTop (1:ℝ)] with D hl hc hD
  have hd : 0 < D := by linarith
  have hw : 0 < logb 2 D := Real.logb_pos (by norm_num) hD
  have hp : 0 < D^ε := Real.rpow_pos_of_pos hd _
  apply (le_div_iff₀ hw).mpr
  calc
    _ = (C*logb 2 D)/D^ε := by rw [Real.rpow_neg hd.le]; ring
    _ ≤ 1 := (div_le_one hp).mpr ((mul_le_mul_of_nonneg_left hl hC).trans hc)

lemma main_scale_ready_cutoff (wmin : ℝ) : ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D ≥ D₀, MainScaleReady wmin D := by
  have hev : ∀ᶠ D : ℝ in atTop, MainScaleReady wmin D := by
    filter_upwards [eventually_gt_atTop (1:ℝ),
      (Real.tendsto_logb_atTop (by norm_num : (1:ℝ) < 2)).eventually (eventually_ge_atTop wmin),
      eventually_inverse_power_log 1 (1/100) (by norm_num) (by norm_num),
      Batch.eventually_const_mul_power_le 2 (1/1000) (3/10) (by norm_num),
      eventually_inverse_power_log 2 (9/1000) (by norm_num) (by norm_num),
      eventually_inverse_power_log 2 (87/100) (by norm_num) (by norm_num),
      eventually_inverse_power_log 8 (3/20) (by norm_num) (by norm_num),
      Batch.eventually_constant_le_power 8 (3/100) (by norm_num)] with D hD hw hc hb hbad hs₁ hs₂ h8
    refine ⟨hD,hw,?_,by linarith,by simpa only [neg_div] using hbad,?_,h8⟩
    · simpa only [one_mul,Real.rpow_neg (by linarith : 0 ≤ D),one_div] using hc
    · simp only [neg_div]
      linarith
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  refine ⟨max A 2,lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_max_right _ _),?_⟩
  intro D hD
  exact hA D ((le_max_left _ _).trans hD)

lemma MainScaleReady.active_square {w D : ℝ} (h : MainScaleReady w D) :
    (D^(1/100:ℝ))^2 ≤ D^(3/100:ℝ) := by
  rw [← Real.rpow_mul_natCast (by linarith [h.gt_one] : 0 ≤ D)]
  apply Real.rpow_le_rpow_of_exponent_le h.gt_one.le
  norm_num

lemma MainScaleReady.bad_count {w D y b : ℝ} (h : MainScaleReady w D) (hy : 0 ≤ y)
    (hb : D^(1/100:ℝ)*b ≤ 2*y*D^(1/1000:ℝ)) : b ≤ y/logb 2 D := by
  have hd : 0 < D := by linarith [h.gt_one]
  have hp : 0 < D^(1/100:ℝ) := Real.rpow_pos_of_pos hd _
  calc
    b ≤ 2*y*D^(1/1000:ℝ)/D^(1/100:ℝ) := (le_div_iff₀ hp).mpr (by simpa [mul_comm] using hb)
    _ = y*(2*D^(-9/1000:ℝ)) := by
      have he : D^(1/1000:ℝ)/D^(1/100:ℝ) = D^(-9/1000:ℝ) := by
        rw [← Real.rpow_sub hd]; norm_num
      rw [show 2*y*D^(1/1000:ℝ)/D^(1/100:ℝ) = (2*y)*(D^(1/1000:ℝ)/D^(1/100:ℝ)) by ring,he]
      ring
    _ ≤ y*(1/logb 2 D) := mul_le_mul_of_nonneg_left h.bad_power hy
    _ = _ := by ring

lemma MainScaleReady.skip_count {w D y T b r : ℝ} (h : MainScaleReady w D)
    (hy : 0 ≤ y) (_hb : 0 ≤ b) (hr : 0 ≤ r)
    (hyD : y ≤ D^(51/50:ℝ)) (hT : T ≤ 2*y)
    (hbT : b ≤ 1+2*T/D^(3/10:ℝ)) (hrY : D^(9/10:ℝ)*r ≤ y) :
    D^(3/100:ℝ)*b*r ≤ y/logb 2 D := by
  have hd : 0 < D := by linarith [h.gt_one]
  have hB : 0 < D^(3/10:ℝ) := Real.rpow_pos_of_pos hd _
  have hS : 0 < D^(9/10:ℝ) := Real.rpow_pos_of_pos hd _
  have hL : 0 ≤ D^(3/100:ℝ) := Real.rpow_nonneg hd.le _
  have hb' : b ≤ 1+4*y/D^(3/10:ℝ) := by
    have ht := div_le_div_of_nonneg_right (by linarith : 2*T ≤ 4*y) hB.le
    linarith
  have hr' : r ≤ y/D^(9/10:ℝ) := (le_div_iff₀ hS).mpr (by simpa [mul_comm] using hrY)
  have he₁ : D^(3/100:ℝ)/D^(9/10:ℝ) = D^(-87/100:ℝ) := by
    rw [← Real.rpow_sub hd]; norm_num
  have he₂ : D^(51/50:ℝ)*D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)) = D^(-3/20:ℝ) := by
    rw [← Real.rpow_add hd,← Real.rpow_add hd,← Real.rpow_sub hd]; norm_num
  calc
    _ ≤ D^(3/100:ℝ)*(1+4*y/D^(3/10:ℝ))*(y/D^(9/10:ℝ)) := by gcongr
    _ = y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*y*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))) := by ring
    _ ≤ y*(D^(3/100:ℝ)/D^(9/10:ℝ)+4*D^(51/50:ℝ)*(D^(3/100:ℝ)/(D^(3/10:ℝ)*D^(9/10:ℝ)))) := by gcongr
    _ = y*(D^(-87/100:ℝ)+4*D^(-3/20:ℝ)) := by rw [he₁,← he₂]; ring
    _ ≤ y*(1/logb 2 D) := mul_le_mul_of_nonneg_left h.skip_power hy
    _ = _ := by ring

end
end ErdosGallai

end

section

namespace ErdosGallai.Scale
noncomputable section
open Finset SimpleGraph Real
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def costMass (L : List (AssignedPiece V)) : ℝ := (L.map (fun Q => (decompositionCost Q.graph:ℝ))).sum

lemma costMass_bound (L : List (AssignedPiece V)) (f : AssignedPiece V → ℝ)
    (h : ∀ P ∈ L, (decompositionCost P.graph:ℝ) ≤ f P) : costMass L ≤ (L.map f).sum :=
  List.sum_le_sum h

lemma past_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c : ℝ)
    (hp : ∀ Q ∈ pastPieces s j k [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j k [P]).length:ℝ) +
      c*vertexMass (pastPieces s j k [P]) + costMass (advance s j k [P]) := by
  have hh := decompositionCost_partition_real (past_partition s j k P)
  have hc := decompositionCost_cycles _ (pastCycles_good s j k [P])
  have hm := piece_list_cost _ c hp
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma stage_cost (s : SplitSystem V) (j) (P : AssignedPiece V) :
    (decompositionCost P.graph:ℝ) ≤ ((s j P).cycles.length:ℝ) + costMass (s j P).boxes := by
  have hh := decompositionCost_partition_real (s j P).partition
  have hc := decompositionCost_cycles _ (s j P).cycles_good
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at hh
  dsimp only [costMass]
  linarith

lemma vertexMass_perm {V : Type} [_contextInstance1 : Fintype V] [_contextInstance2 : DecidableEq V] {L M : List (AssignedPiece V)} (h : L.Perm M) : vertexMass L = vertexMass M :=
  (h.map _).sum_eq

lemma pastCycles_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => ((pastCycles s j k [P]).length:ℝ))).sum = ((pastCycles s j k L).length:ℝ) := by
  have h := (pastCycles_flatMap s j k L (fun P => [P])).length_eq
  simp only [List.flatMap_singleton'] at h
  rw [h,List.length_flatMap]
  simp [Function.comp_def]

lemma pastPieces_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (pastPieces s j k [P]))).sum = vertexMass (pastPieces s j k L) := by
  have h := vertexMass_perm (pastPieces_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma advance_sum (s : SplitSystem V) (j k) (L : List (AssignedPiece V)) :
    (L.map (fun P => vertexMass (advance s j k [P]))).sum = vertexMass (advance s j k L) := by
  have h := congrArg vertexMass (advance_flatMap s j k L (fun P => [P]))
  simpa only [List.flatMap_singleton',vertexMass_flatMap] using h.symm

lemma pastCycles_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastCycles s j (k+1) [P]).Perm ((s j P).cycles ++
      (s j P).boxes.flatMap (fun B => pastCycles s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastCycles_add]
  simp only [pastCycles,advance_zero,List.nil_append,levelCycles,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastCycles_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma pastPieces_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    (pastPieces s j (k+1) [P]).Perm ((s j P).boxes.flatMap (s j P).pieces ++
      (s j P).boxes.flatMap (fun B => pastPieces s (j+1) k [(s j P).rest B])) := by
  rw [show k+1=1+k by omega,pastPieces_add]
  simp only [pastPieces,advance_zero,List.nil_append,levelPieces,List.flatMap_singleton,
    Nat.add_zero,advance_succ,nextLayer,Nat.add_zero,List.flatMap_singleton,StageSplit.children_eq_map_rest]
  have hh := pastPieces_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])
  simp only [← List.map_eq_flatMap] at hh
  exact hh.append_left _

lemma advance_after_first (s : SplitSystem V) (j k) (P : AssignedPiece V) :
    advance s j (k+1) [P] = (s j P).boxes.flatMap (fun B => advance s (j+1) k [(s j P).rest B]) := by
  rw [show k+1=1+k by omega,advance_add]
  simp only [advance_succ,advance_zero,Nat.add_zero,nextLayer,List.flatMap_singleton,
    StageSplit.children_eq_map_rest]
  simpa only [← List.map_eq_flatMap] using advance_flatMap s (j+1) k (s j P).boxes (fun B => [(s j P).rest B])

lemma selected_input_cost (s : SplitSystem V) (j k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ B ∈ (s j P).boxes, ∀ Q ∈ pastPieces s (j+1) k [(s j P).rest B],
      (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ B ∈ (s j P).boxes,
      (decompositionCost (graphUnion ((advance s (j+1) k [(s j P).rest B]).map AssignedPiece.graph ++
        ((s j P).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s j P).pieces B) + α*vertexMass (advance s (j+1) k [(s j P).rest B]) +
      β*vertexMass ((s j P).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s j (k+1) [P]).length:ℝ) +
      c*vertexMass (pastPieces s j (k+1) [P]) + α*vertexMass (advance s j (k+1) [P]) +
      β*vertexMass (levelPieces s j [P]) + γ*vertexMass (nextLayer s j [P]) := by
  have hb (B) (hB : B ∈ (s j P).boxes) := box_cost_regroup ((s j P).pieces B)
    (R := (s j P).rest B) (by simpa only [StageSplit.rest_graph _ hB] using (s j P).box_partition B hB)
    s (j+1) k c _ (hp B hB) (hq B hB)
  have hh := (stage_cost s j P).trans (add_le_add (le_refl _) (costMass_bound _ _ hb))
  have hc := (pastCycles_after_first s j k P).length_eq
  have hm := vertexMass_perm (pastPieces_after_first s j k P)
  rw [hc,List.length_append,Nat.cast_add,List.length_flatMap,hm,vertexMass_append,
    vertexMass_flatMap,vertexMass_flatMap,advance_after_first,vertexMass_flatMap]
  simp only [levelPieces,nextLayer,List.flatMap_singleton,StageSplit.children_mass,vertexMass_flatMap]
  simp only [List.sum_map_add,List.sum_map_mul_left] at hh
  simp only [Nat.cast_list_sum,List.map_map,Function.comp_def,vertexMass] at hh ⊢
  linarith

lemma selected_prefix_cost (s : SplitSystem V) (i k) (P : AssignedPiece V) (c α β γ : ℝ)
    (hp : ∀ Q ∈ pastPieces s 0 (i+(k+1)) [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card)
    (hq : ∀ Q ∈ advance s 0 i [P], ∀ B ∈ (s i Q).boxes,
      (decompositionCost (graphUnion ((advance s (i+1) k [(s i Q).rest B]).map AssignedPiece.graph ++
        ((s i Q).pieces B).map AssignedPiece.graph)):ℝ) ≤
      c*vertexMass ((s i Q).pieces B) + α*vertexMass (advance s (i+1) k [(s i Q).rest B]) +
      β*vertexMass ((s i Q).pieces B) + γ*B.vertices.card) :
    (decompositionCost P.graph:ℝ) ≤ ((pastCycles s 0 (i+(k+1)) [P]).length:ℝ) +
      c*vertexMass (pastPieces s 0 (i+(k+1)) [P]) + α*vertexMass (advance s 0 (i+(k+1)) [P]) +
      β*vertexMass (levelPieces s i (advance s 0 i [P])) + γ*vertexMass (advance s 0 (i+1) [P]) := by
  have he : pastPieces s 0 (i+(k+1)) [P] = pastPieces s 0 i [P] ++
      pastPieces s i (k+1) (advance s 0 i [P]) := by rw [pastPieces_add,Nat.zero_add]
  have hp₀ : ∀ Q ∈ pastPieces s 0 i [P], (decompositionCost Q.graph:ℝ) ≤ c*Q.vertices.card := by
    intro Q hQ; apply hp; rw [he]; exact List.mem_append_left _ hQ
  have hpp (Q) (hQ : Q ∈ advance s 0 i [P]) (B) (hB : B ∈ (s i Q).boxes)
      (R) (hR : R ∈ pastPieces s (i+1) k [(s i Q).rest B]) :
      (decompositionCost R.graph:ℝ) ≤ c*R.vertices.card := by
    apply hp R
    rw [he,List.mem_append]
    right
    have h₁ := pastPieces_flatMap s i (k+1) (advance s 0 i [P]) (fun Q => [Q])
    simp only [List.flatMap_singleton'] at h₁
    rw [h₁.mem_iff]
    apply List.mem_flatMap.mpr
    refine ⟨Q,hQ,?_⟩
    rw [(pastPieces_after_first s i k Q).mem_iff,List.mem_append]
    exact Or.inr (List.mem_flatMap.mpr ⟨B,hB,hR⟩)
  have hh := (past_cost s 0 i P c hp₀).trans (add_le_add (le_refl _)
    (costMass_bound _ _ (fun Q hQ => selected_input_cost s i k Q c α β γ (hpp Q hQ) (hq Q hQ))))
  rw [pastCycles_add,pastPieces_add,advance_add,Nat.zero_add,List.length_append,Nat.cast_add,vertexMass_append]
  simp only [List.sum_map_add,List.sum_map_mul_left,pastCycles_sum,pastPieces_sum,advance_sum] at hh
  have hS : ((advance s 0 i [P]).map (fun Q => vertexMass (levelPieces s i [Q]))).sum =
      vertexMass (levelPieces s i (advance s 0 i [P])) := by
    simp only [levelPieces,List.flatMap_singleton,vertexMass_flatMap]
  have hN : ((advance s 0 i [P]).map (fun Q => vertexMass (nextLayer s i [Q]))).sum =
      vertexMass (advance s 0 (i+1) [P]) := by
    simp only [nextLayer,List.flatMap_singleton,advance_succ,Nat.zero_add,vertexMass_flatMap]
  rw [hS,hN] at hh
  linarith

end
end ErdosGallai.Scale

end
end
end

end OAI
