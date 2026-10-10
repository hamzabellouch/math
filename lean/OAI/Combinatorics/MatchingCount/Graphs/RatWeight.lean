import Mathlib
import OAI.Combinatorics.MatchingCount.Graphs.EnlargementRun

namespace OAI

namespace MatchingFPRAS.StageAnalysis

open Finset MatchingFPRAS.Switching MatchingFPRAS.Initializer

variable {V : Type*} [Fintype V] [LinearOrder V]

noncomputable def ratWeight (w : V → V → ℚ) (m : Mate V) : ℚ :=
  ∏ x, if x < m.val x then w x (m.val x) else 1

noncomputable def ratPartition (w : V → V → ℚ) (R : Finset V) : ℚ :=
  ∑ m ∈ matchings R,ratWeight w m

lemma ratWeight_cast (w : V → V → ℚ) (m : Mate V) :
    (ratWeight w m:ℝ)=weight (fun x y => (w x y:ℝ)) m := by
  unfold ratWeight weight
  push_cast
  apply prod_congr rfl
  intro x _
  split_ifs <;> simp

lemma ratPartition_cast (w : V → V → ℚ) (R : Finset V) :
    (ratPartition w R:ℝ)=partition (fun x y => (w x y:ℝ)) R := by
  unfold ratPartition partition
  push_cast
  exact sum_congr rfl fun m _ => ratWeight_cast w m

lemma partition_pos_of_even (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (R : Finset V) (he : Even (Fintype.card V-R.card)) : 0 < partition w R := by
  have hm : 0 < (matchings R).card := by rw [matchings_card]; exact pairingCount_pos_of_even _ he
  apply Finset.sum_pos
  · intro m _
    unfold weight
    apply Finset.prod_pos
    intro x _
    split_ifs <;> first | exact hw _ _ | norm_num
  · exact Finset.card_pos.mp hm

lemma selected_card (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    (univ.filter fun x => x < m.val x).card=(Fintype.card V-R.card)/2 := by
  have hh : HasHoles m Rᶜᶜ := by simpa using hm
  have hc := mate_edge_count m Rᶜ hh
  rw [Finset.card_compl] at hc
  omega

lemma weight_factor (t : ℝ) (w : V → V → ℝ) (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    weight (fun x y => t*w x y) m=t^((Fintype.card V-R.card)/2)*weight w m := by
  unfold weight
  rw [←prod_filter (fun x => x < m.val x) (fun x => t*w x (m.val x)),
    ←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x)),
    prod_mul_distrib,prod_const,selected_card m R hm]

lemma weight_mono (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (hle : ∀ x y,x≠y → w x y ≤ w₁ x y) (m : Mate V) : weight w m ≤ weight w₁ m := by
  apply Finset.prod_le_prod₀
  · intro x _
    split_ifs <;> first | exact hw _ _ | norm_num
  · intro x _
    split_ifs with h
    · exact hle _ _ h.ne
    · rfl

theorem partition_reweight (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hlo : ∀ x y,x≠y → t*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y) (R : Finset V) :
    t^(Fintype.card V/2)*partition w R ≤ partition w₁ R ∧
      partition w₁ R ≤ partition w R := by
  have hw₁ : ∀ m : Mate V,0 ≤ weight w₁ m := by
    intro m
    unfold weight
    apply prod_nonneg
    intro x _
    split_ifs with h
    · exact (mul_nonneg ht (hw _ _)).trans (hlo _ _ h.ne)
    · norm_num
  constructor
  · rw [partition,mul_sum]
    apply sum_le_sum
    intro m hm
    have hcard : (Fintype.card V-R.card)/2 ≤ Fintype.card V/2 := Nat.div_le_div_right (Nat.sub_le _ _)
    calc
      _ ≤ t^((Fintype.card V-R.card)/2)*weight w m :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one ht ht1 hcard) (weight_nonneg w hw m)
      _ = weight (fun x y => t*w x y) m := (weight_factor t w m R ((mem_matchings _ _).mp hm)).symm
      _ ≤ weight w₁ m := weight_mono _ _ (fun x y => mul_nonneg ht (hw x y)) hlo m
  · apply sum_le_sum
    intro m _
    apply Finset.prod_le_prod₀
    · intro x _
      split_ifs with h
      · exact (mul_nonneg ht (hw _ _)).trans (hlo _ _ h.ne)
      · norm_num
    · intro x _
      split_ifs with h
      · exact hhi _ _ h.ne
      · rfl

lemma cooling_half (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ)/2 ≤ ((1+1/(n:ℝ))⁻¹)^(n/2) := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hb : 0 < 1+1/(n:ℝ) := by positivity
  have hp : (1+1/(n:ℝ))^(n/2) ≤ Real.exp ((n/2:ℕ)/n) := by
    have h := pow_le_pow_left₀ hb.le (by simpa [add_comm] using Real.add_one_le_exp (1/(n:ℝ))) (n/2)
    simpa only [←Real.exp_nat_mul,div_eq_mul_inv,one_mul] using h
  have he : ((n/2:ℕ):ℝ)/(n:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ hnp).mpr
    have h : (n/2)*2 ≤ n := Nat.div_mul_le_self n 2
    have h' : ((n/2:ℕ):ℝ)*2 ≤ n := by exact_mod_cast h
    linarith
  have hexp : Real.exp (1/2:ℝ)<2 := by
    have hs : (Real.exp (1/2:ℝ))^2=Real.exp 1 := by rw [←Real.exp_nat_mul]; norm_num
    have h := Real.exp_one_lt_three
    have hpos := Real.exp_pos (1/2:ℝ)
    nlinarith
  rw [inv_pow]
  exact (le_inv_comm₀ (by norm_num) (pow_pos hb _)).mpr (by
    norm_num
    simpa only [one_div] using hp.trans ((Real.exp_le_exp.mpr he).trans hexp.le))

theorem partition_cooling (hn : 2 ≤ Fintype.card V)
    (w w₁ : V → V → ℝ) (hw : ∀ x y,0 ≤ w x y)
    (hlo : ∀ x y,x≠y → (1+1/(Fintype.card V:ℝ))⁻¹*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y) (R : Finset V) :
    partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R := by
  have ht : 0 ≤ (1+1/(Fintype.card V:ℝ))⁻¹ := by positivity
  have ht1 : (1+1/(Fintype.card V:ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
    have h : 0 ≤ 1/(Fintype.card V:ℝ) := by positivity
    linarith)
  have h := partition_reweight w w₁ hw _ ht ht1 hlo hhi R
  refine ⟨?_,h.2⟩
  have hh := mul_le_mul_of_nonneg_right (cooling_half _ hn) (partition_nonneg w hw R)
  linarith

theorem holeRatio_cooling (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 ≤ w x y) (hz : 0 < partition w ∅)
    (h : ∀ R,partition w R/2 ≤ partition w₁ R ∧ partition w₁ R ≤ partition w R)
    (R : Finset V) : Switching.holeRatio w R/2 ≤ Switching.holeRatio w₁ R ∧ Switching.holeRatio w₁ R ≤ 2*Switching.holeRatio w R := by
  have hz₁ : 0 < partition w₁ ∅ := lt_of_lt_of_le (half_pos hz) (h ∅).1
  have hR := partition_nonneg w hw R
  have hR₁ : 0 ≤ partition w₁ R := (by positivity : 0 ≤ partition w R/2).trans (h R).1
  unfold Switching.holeRatio
  constructor
  · apply (le_div_iff₀ hz₁).mpr
    have hd : partition w R/partition w ∅/2*partition w₁ ∅ ≤ partition w R/2 := by
      calc
        _ ≤ partition w R/partition w ∅/2*partition w ∅ :=
          mul_le_mul_of_nonneg_left (h ∅).2 (by positivity)
        _ = _ := by field_simp [hz.ne']
    exact hd.trans (h R).1
  · apply (div_le_iff₀ hz₁).mpr
    have hd : partition w R ≤ (2*(partition w R/partition w ∅))*partition w₁ ∅ := by
      calc
        _ = (2*(partition w R/partition w ∅))*(partition w ∅/2) := by field_simp [hz.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left (h ∅).1 (by positivity)
    exact (h R).2.trans hd



open Finset MatchingFPRAS.Switching

variable {V : Type*} [Fintype V] [LinearOrder V]

lemma mate_vertex_product (s : V → ℝ) (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    (∏ x ∈ univ.filter (fun x => x < m.val x),s x*s (m.val x))=∏ x ∈ Rᶜ,s x := by
  let L := univ.filter fun x => x < m.val x
  let H := univ.filter fun x => m.val x < x
  have himg : L.image m.val=H := by
    ext x
    simp only [L,H,mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨a,ha,rfl⟩
      simpa using ha
    · intro hx
      exact ⟨m.val x,by simpa using hx,mate_mate m x⟩
  have hdis : Disjoint L H := by
    apply disjoint_left.mpr
    intro x hx hy
    exact lt_asymm (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hunion : L∪H=Rᶜ := by
    ext x
    simp only [L,H,mem_union,mem_filter,mem_univ,true_and,mem_compl]
    rw [←ne_iff_lt_or_gt]
    simpa only [ne_eq,eq_comm] using not_congr (hm x)
  have hp : (∏ x ∈ L,s (m.val x))=∏ x ∈ H,s x := by
    rw [←himg]
    exact (prod_image m.property.injective.injOn).symm
  change (∏ x ∈ L,s x*s (m.val x))=_
  rw [prod_mul_distrib,hp,←prod_union hdis,hunion]

theorem weight_vertex_scaling (w : V → V → ℝ) (s : V → ℝ)
    (m : Mate V) (R : Finset V) (hm : HasHoles m R) :
    weight (fun x y => w x y*s x*s y) m=weight w m*(∏ x ∈ Rᶜ,s x) := by
  unfold weight
  rw [←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x)*s x*s (m.val x)),
    ←prod_filter (fun x => x < m.val x) (fun x => w x (m.val x))]
  calc
    _ = (∏ x ∈ univ.filter (fun x => x < m.val x),w x (m.val x)*(s x*s (m.val x))) := by
      apply prod_congr rfl
      intro x _
      ring
    _ = _ := by rw [prod_mul_distrib,mate_vertex_product s m R hm]

theorem partition_vertex_scaling (w : V → V → ℝ) (s : V → ℝ) (R : Finset V) :
    partition (fun x y => w x y*s x*s y) R=partition w R*(∏ x ∈ Rᶜ,s x) := by
  unfold partition
  rw [sum_mul]
  exact sum_congr rfl fun m hm => weight_vertex_scaling w s m R ((mem_matchings _ _).mp hm)

theorem holeRatio_vertex_scaling (w : V → V → ℝ) (s : V → ℝ) (hs : ∀ x,0 < s x) (R : Finset V) :
    Switching.holeRatio (fun x y => w x y*s x*s y) R=Switching.holeRatio w R/(∏ x ∈ R,s x) := by
  have hp : (∏ x : V,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have hR : (∏ x ∈ R,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have hc : (∏ x ∈ Rᶜ,s x)≠0 := prod_ne_zero_iff.mpr (fun x _ => (hs x).ne')
  have he : (∏ x ∈ R,s x)*(∏ x ∈ Rᶜ,s x)=∏ x,s x := prod_mul_prod_compl R s
  unfold Switching.holeRatio
  rw [partition_vertex_scaling,partition_vertex_scaling,compl_empty]
  by_cases hz : partition w ∅=0
  · simp [hz]
  · rw [←he]
    field_simp

end MatchingFPRAS.StageAnalysis

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

open scoped Classical

lemma sourceBagZ_pos (w : V → V → ℝ) (hw : ∀ x y,0 < w x y)
    (hz : 0 < partition w ∅) (K D : ℕ) : 0 < sourceBagZ w K D := by
  apply (sourceRealPortion_full_pos w hz K).trans_le
  apply partitionWeight_mono BagEdge.Incident _ _ (sourceRealPortion_nonneg w hw K)
  intro e
  exact le_add_of_nonneg_right (div_nonneg (bagHeight_pos w K _).le (Nat.cast_nonneg D))

lemma sourceBagZ_bounds (hn : 2 ≤ Fintype.card V) (w : V → V → ℝ)
    (hw : ∀ x y,0 < w x y) (hz : 0 < partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x ≤ 1)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) :
    sourceC w K*partition w ∅ ≤ sourceBagZ w K (sourceD (V:=V) K) ∧
      sourceBagZ w K (sourceD (V:=V) K) ≤ 2*(sourceC w K*partition w ∅) := by
  have h := source_bag_inflation hn w hw hz hrlo hrhi K hK
  change 1 ≤ _ / _ ∧ _ / _ ≤ 2 at h
  have he : partitionWeight BagEdge.Incident (sourceRealPortion w K) univ=sourceC w K*partition w ∅ :=
    sourceRealPortion_full w hz K
  have hb : sourceBagZ w K (sourceD (V:=V) K)=
      partitionWeight BagEdge.Incident (fun e : BagEdge (sourceBags w K) =>
        sourceRealPortion w K e+(2:ℝ)^e.val.val.2.1.val/inflationScale (V:=SourceVertex V K) (holeScale V)) univ := by
    unfold sourceBagZ sourceBagWeight bagHeight
    rw [sourceD_cast]
  rw [←hb,he] at h
  have hp := mul_pos (sourceC_pos w K) hz
  exact ⟨by simpa using (le_div_iff₀ hp).mp h.1,(div_le_iff₀ hp).mp h.2⟩

theorem source_observable_means (hn : 2 ≤ Fintype.card V) (w w₁ : V → V → ℝ)
    (hw : ∀ x y,0 < w x y) (hz : 0 < partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4 ≤ rowMax hn w x) (hrhi : ∀ x,rowMax hn w x ≤ 1)
    (hlo : ∀ x y,x≠y → (1+1/(Fintype.card V:ℝ))⁻¹*w x y ≤ w₁ x y)
    (hhi : ∀ x y,x≠y → w₁ x y ≤ w x y)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) :
    let D := sourceD (V:=V) K
    let a := ∑ q : SourceMarked w K,sourceLaw w K D q*observableA w K q
    let d := ∑ q : SourceMarked w K,sourceLaw w K D q*observableD w w₁ K q
    (∑ q : SourceMarked w K,sourceLaw w K D q)=1 ∧
    (∀ q : SourceMarked w K,0 ≤ sourceLaw w K D q) ∧
    (1:ℝ)/2 ≤ a ∧ (1:ℝ)/4 ≤ d ∧
    d/a=partition w₁ ∅/partition w ∅ ∧ (1:ℝ)/2 ≤ d/a ∧ d/a ≤ 1 ∧
    (∀ e : LogicalEdge V,
      (D:ℝ)*(∑ q : SourceMarked w K,sourceLaw w K D q*observableProbe w w₁ K e q)/d=
        Switching.holeRatio w₁ {source e,target e}) := by
  dsimp only
  let D := sourceD (V:=V) K
  have hp := sourceBagZ_pos w hw hz K D
  have hb := sourceBagZ_bounds hn w hw hz hrlo hrhi K hK
  have hc := partition_cooling hn w w₁ (fun x y => (hw x y).le) hlo hhi ∅
  have hz₁ : 0 < partition w₁ ∅ := (half_pos hz).trans_le hc.1
  have hC := sourceC_pos w K
  have hDn : (D:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt (sourceD_one (V:=V) K))
  refine ⟨sourceLaw_sum w K D hp.ne',sourceLaw_nonneg w hw K D hp.le,?_,?_,?_,?_,?_,?_⟩
  · rw [observableA_mean w hz]
    apply (le_div_iff₀ hp).mpr
    nlinarith [hb.2]
  · rw [observableD_mean w w₁ hw hz₁]
    apply (le_div_iff₀ hp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc.1 hC.le,hb.2]
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    field_simp [hC.ne',hz.ne',hp.ne']
    simpa only [D] using div_self hp.ne'
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (le_div_iff₀ hz).mpr (by linarith)
  · rw [observableD_mean w w₁ hw hz₁,observableA_mean w hz]
    have he : (sourceC w K*partition w₁ ∅/sourceBagZ w K D)/
        (sourceC w K*partition w ∅/sourceBagZ w K D)=partition w₁ ∅/partition w ∅ := by
      field_simp [hC.ne',hz.ne',hp.ne']
    rw [he]
    exact (div_le_one hz).mpr hc.2
  · intro e
    rw [observableProbe_mean w w₁ hw,observableD_mean w w₁ hw hz₁]
    unfold Switching.holeRatio
    dsimp only [D] at hDn hp ⊢
    field_simp [hC.ne',hz₁.ne',hp.ne',hDn]

end MatchingFPRAS.Enlargement

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset

abbrev alpha : ℝ := 1/100000

lemma others_nonempty {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : (univ.erase i).Nonempty := by
  let j : Fin n := ⟨if i.val=0 then 1 else 0, by split_ifs <;> omega⟩
  refine ⟨j,mem_erase.mpr ⟨?_,mem_univ _⟩⟩
  apply Fin.ne_of_val_ne
  dsimp [j]; split_ifs <;> omega

def rowMaximum {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : ℝ :=
  (univ.erase i).sup' (others_nonempty hn i) (fun j => G i j / v j)

def scaleUpdate {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) : Fin n → ℝ :=
  Function.update v i (rowMaximum hn G v i)

def scalingTrace {n : ℕ} (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun _ => 2
  | k+1 => if hk : k<n then scaleUpdate hn G (scalingTrace hn G k) ⟨k,hk⟩ else scalingTrace hn G k



open Finset

variable {n : ℕ}

structure ScaleInvariant (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ) : Prop where
  lower : ∀ i, alpha/2 ≤ v i
  upper : ∀ i, v i ≤ 2
  feasible : ∀ i j, i≠j → G i j ≤ v i*v j

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℝ} {v : Fin n → ℝ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℝ) (v v' : Fin n → ℝ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm

end MatchingFPRAS.RealStage

end

end OAI
