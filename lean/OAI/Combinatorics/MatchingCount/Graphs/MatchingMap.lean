import Mathlib
import OAI.Combinatorics.MatchingCount.Probability.Variance
import OAI.Combinatorics.MatchingCount.Graphs.EdgeLow

namespace OAI

namespace MatchingFPRAS.Transport

open Finset

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

variable [DecidableEq V] [DecidableEq E] [DecidableEq F]

variable (inc : E → V → Prop) (inc' : F → V → Prop) (f : E ↪ F)

variable (hinc : ∀ e x,inc' (f e) x ↔ inc e x)

include hinc in
omit [Fintype V] [Fintype E] [Fintype F] [DecidableEq V] [DecidableEq E] [DecidableEq F] in
lemma matching_map_iff [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq V] [DecidableEq E] [DecidableEq F] (S : Finset E) (U : Finset V) :
    MatchingOn inc' (S.map f) U ↔ MatchingOn inc S U := by
  constructor
  · intro hM
    refine ⟨fun e he x hx => hM.1 (f e) (Finset.mem_map.mpr ⟨e,he,rfl⟩) x ((hinc e x).mpr hx),?_⟩
    intro x hx
    obtain ⟨q,⟨hq,hqx⟩,hu⟩ := hM.2 x hx
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
    refine ⟨e,⟨he,(hinc e x).mp hqx⟩,?_⟩
    intro e' he'
    apply f.injective
    exact hu (f e') ⟨Finset.mem_map.mpr ⟨e',he'.1,rfl⟩,(hinc e' x).mpr he'.2⟩
  · intro hM
    constructor
    · intro q hq x hx
      obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
      exact hM.1 e he x ((hinc e x).mp hx)
    · intro x hx
      obtain ⟨e,⟨he,hex⟩,hu⟩ := hM.2 x hx
      refine ⟨f e,⟨Finset.mem_map.mpr ⟨e,he,rfl⟩,(hinc e x).mpr hex⟩,?_⟩
      intro q hq
      obtain ⟨e',he',rfl⟩ := Finset.mem_map.mp hq.1
      exact congrArg f (hu e' ⟨he',(hinc e' x).mp hq.2⟩)

noncomputable def matchingMap (U : Finset V) (M : Matchings inc U) : Matchings inc' U :=
  ⟨M.val.map f,(matching_map_iff inc inc' f hinc M.val U).mpr M.property⟩

lemma matchingMap_injective (U : Finset V) : Function.Injective (matchingMap inc inc' f hinc U) := by
  intro a b h
  apply Subtype.ext
  exact Finset.map_injective f (congrArg Subtype.val h)

noncomputable def edgeExtension (w : E → ℝ) (q : F) : ℝ := by
  classical
  exact if h : ∃ e,f e=q then w h.choose else 0

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_on [Fintype F] [DecidableEq E] (w : E → ℝ) (e : E) : edgeExtension f w (f e)=w e := by
  classical
  unfold edgeExtension
  rw [dite_eq_left ⟨e,rfl⟩]
  exact congrArg w (f.injective (Exists.choose_spec (show ∃ e',f e'=f e from ⟨e,rfl⟩)))

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_off [Fintype F] [DecidableEq E] (w : E → ℝ) (q : F) (hq : ¬∃ e,f e=q) : edgeExtension f w q=0 := by
  classical
  simp [edgeExtension,hq]

omit [Fintype F] [DecidableEq E] in
lemma edgeExtension_nonneg [Fintype F] [DecidableEq E] (w : E → ℝ) (hw : ∀ e,0≤w e) (q : F) : 0≤edgeExtension f w q := by
  classical
  unfold edgeExtension
  split_ifs <;> first | exact hw _ | norm_num

lemma matchingMap_weight (w : E → ℝ) (U : Finset V) (M : Matchings inc U) :
    (∏ q∈(matchingMap inc inc' f hinc U M).val,edgeExtension f w q)=∏ e∈M.val,w e := by
  dsimp [matchingMap]
  rw [Finset.prod_map]
  simp_rw [edgeExtension_on]

include hinc in

theorem partition_embedding (w : E → ℝ) (U : Finset V) :
    partitionWeight inc' (edgeExtension f w) U=partitionWeight inc w U := by
  classical
  unfold partitionWeight
  symm
  apply Finset.sum_bij_ne_zero (fun M _ _ => matchingMap inc inc' f hinc U M)
  · intros; exact Finset.mem_univ _
  · intro a _ _ b _ _ h
    exact matchingMap_injective inc inc' f hinc U h
  · intro N _ hN
    have hr : ∀ q∈N.val,∃ e,f e=q := by
      intro q hq
      by_contra hn
      apply hN
      exact Finset.prod_eq_zero hq (edgeExtension_off f w q hn)
    let S := univ.filter fun e : E => f e∈N.val
    have hS : S.map f=N.val := by
      ext q
      constructor
      · intro hq
        obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hq
        exact (Finset.mem_filter.mp he).2
      · intro hq
        obtain ⟨e,rfl⟩ := hr q hq
        exact Finset.mem_map.mpr ⟨e,by simp [S,hq],rfl⟩
    let M : Matchings inc U := ⟨S,(matching_map_iff inc inc' f hinc S U).mp (hS.symm ▸ N.property)⟩
    have hM : matchingMap inc inc' f hinc U M=N := Subtype.ext hS
    refine ⟨M,Finset.mem_univ _,?_,hM⟩
    rw [←matchingMap_weight inc inc' f hinc w U M,hM]
    exact hN
  · intro M _ _
    exact (matchingMap_weight inc inc' f hinc w U M).symm

end MatchingFPRAS.Transport

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def sourceRealLabel (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : SourceLabel w K :=
  edgeLabel (sourceRealB w K) (sourceRealB_comm w K) (sourceRealB_tri w K)
    (realLeft K) (realRight K) (sourceLevels w K) e

omit [Nontrivial V] in
lemma real_edge_not_diag [Nontrivial V] (K : ℕ) (e : SourceRealEdge V K) :
    ¬(edge source target (4*(2*K+2)) e.1 e.2).IsDiag := by
  rw [edge,Sym2.mk_isDiag_iff]
  intro he
  have hi := atVertex_injective source target (4*(2*K+2)) e.1 (source_ne_target e.1) he
  have := congrArg Fin.val hi
  simp at this

noncomputable def sourceColoredReal (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) :
    BagEdge (sourceBags w K) :=
  ⟨⟨(edge source target (4*(2*K+2)) e.1 e.2,sourceRealLabel w K e),real_edge_not_diag K e⟩,by
    intro x hx
    apply (mem_memberships _ _ _ (realLeft K) (realRight K) (sourceLevels w K) x _).mpr
    refine ⟨e,?_,rfl⟩
    simpa [ColoredEdge.Incident,Incident,realLeft,realRight,edge] using hx⟩

lemma sourceColoredReal_injective (w : V → V → ℝ) (K : ℕ) :
    Function.Injective (sourceColoredReal w K) := by
  intro e f h
  apply edge_injective source target (4*(2*K+2)) (by omega)
  exact congrArg (fun q : BagEdge (sourceBags w K) => q.val.val.1) h

noncomputable def sourceRealEmbedding (w : V → V → ℝ) (K : ℕ) :
    SourceRealEdge V K ↪ BagEdge (sourceBags w K) :=
  ⟨sourceColoredReal w K,sourceColoredReal_injective w K⟩

noncomputable def sourceRealActivity (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) : ℝ :=
  pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w) e.1 e.2

noncomputable def sourceRealPortion (w : V → V → ℝ) (K : ℕ) : BagEdge (sourceBags w K) → ℝ :=
  by classical exact edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K)

lemma sourceRealPortion_partition (w : V → V → ℝ) (K : ℕ)
    (R : Finset V) (U : LogicalEdge V → Finset (Fin (4*(2*K+2)))) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (survivors (4*(2*K+2)) R U)=
    realHolePartition source target (4*(2*K+2)) R U
      (pathActivity (2*K+2) (fun e => bottleneck w (source e) (target e))
        (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e)) (logicalActivity w)) := by
  classical
  rw [show sourceRealPortion w K=edgeExtension (sourceRealEmbedding w K) (sourceRealActivity w K) from rfl]
  rw [partition_embedding (fun (q : SourceRealEdge V K) x => x∈edge source target (4*(2*K+2)) q.1 q.2)
    BagEdge.Incident (sourceRealEmbedding w K) (fun _ _ => Iff.rfl)]
  exact realMatching_partition source target (4*(2*K+2)) source_ne_target R U _

noncomputable def holeTerminals (K : ℕ) (H : Finset (SourceVertex V K)) : Finset V :=
  by classical exact univ.filter fun x => Sum.inl x∈H

noncomputable def holeInternals (K : ℕ) (H : Finset (SourceVertex V K)) (e : LogicalEdge V) :
    Finset (Fin (4*(2*K+2))) := by classical exact univ.filter fun i => Sum.inr (e,i)∈H

omit [Nontrivial V] in
lemma hole_decomposition [Nontrivial V] (K : ℕ) (H : Finset (SourceVertex V K)) :
    enlargedHoles (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)=H := by
  ext x
  cases x with
  | inl x => simp [holeTerminals]
  | inr ei => rcases ei with ⟨e,i⟩; simp [holeInternals]

omit [Nontrivial V] in
lemma survivors_decomposition [Nontrivial V] (K : ℕ) (H : Finset (SourceVertex V K)) :
    survivors (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)=univ \ H := by
  ext x
  cases x with
  | inl x => simp [holeTerminals]
  | inr ei => rcases ei with ⟨e,i⟩; simp [holeInternals]

omit [Nontrivial V] in
lemma survivors_empty [Nontrivial V] (K : ℕ) : survivors (V := V) (E := LogicalEdge V) (4*(2*K+2)) ∅ (fun _ => ∅)=univ := by
  ext x
  cases x with
  | inl x => simp
  | inr ei => rcases ei with ⟨e,i⟩; simp

lemma sourceRealActivity_pos (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : SourceRealEdge V K) : 0<sourceRealActivity w K e := by
  have hl : 0<logicalActivity w e.1 := by
    unfold logicalActivity edgeActivity
    split_ifs <;> exact hw _ _
  exact hl.trans_le (profile_lower _ _ _ _ _
    (edgeActivity_le_bottleneck w _ _ (source_ne_target e.1)) e.2)

lemma sourceRealPortion_nonneg (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (K : ℕ)
    (e : BagEdge (sourceBags w K)) : 0 ≤ sourceRealPortion w K e := by
  classical
  exact edgeExtension_nonneg _ _ (fun q => (sourceRealActivity_pos w hw K q).le) e

lemma sourceRealPortion_full (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) univ =
      (∏ e, pathConstant (2*K+2) (bottleneck w (source e) (target e))
        (sourceHeight w (source e)) (sourceHeight w (target e))) * partition w ∅ := by
  rw [←survivors_empty (V := V) K,sourceRealPortion_partition]
  exact intact_partition_identity w hz _ _ _ _

lemma sourceRealPortion_full_pos (w : V → V → ℝ) (hz : 0<partition w ∅) (K : ℕ) :
    0<partitionWeight BagEdge.Incident (sourceRealPortion w K) univ := by
  rw [sourceRealPortion_full w hz K]
  apply mul_pos _ hz
  exact Finset.prod_pos fun e _ => pathConstant_pos _ _ _ _
    (zero_lt_one.trans_le (one_le_bottleneck w _ _))

lemma sourceRealPortion_hole_bound (hn : 2≤Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (hz : 0<partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4≤rowMax hn w x) (hrhi : ∀ x,rowMax hn w x≤1)
    (K : ℕ) (H : Finset (SourceVertex V K)) (hH : Even H.card) :
    partitionWeight BagEdge.Incident (sourceRealPortion w K) (univ \ H) /
      partitionWeight BagEdge.Incident (sourceRealPortion w K) univ *
      pairingCapacity (sourceRealB w K) H hH ≤ 2*holeScale V^(H.card/2) := by
  have heven : Even (enlargedHoles (4*(2*K+2)) (holeTerminals K H) (holeInternals K H)).card :=
    (hole_decomposition K H).symm ▸ hH
  have ht := lifted_hole_bound hn w hw hz hrlo hrhi (2*K+2) (by omega)
    (fun e => sourceHeight w (source e)) (fun e => sourceHeight w (target e))
    (fun e => sourceHeight_nonneg w _) (fun e => sourceHeight_nonneg w _)
    (holeTerminals K H) (holeInternals K H) heven
  rw [←sourceRealPortion_partition w K,←sourceRealPortion_partition w K,
    survivors_empty,survivors_decomposition] at ht
  simpa only [hole_decomposition, sourceRealB] using ht

theorem source_bag_inflation (hn : 2≤Fintype.card V)
    (w : V → V → ℝ) (hw : ∀ x y,0<w x y) (hz : 0<partition w ∅)
    (hrlo : ∀ x,(1:ℝ)/4≤rowMax hn w x) (hrhi : ∀ x,rowMax hn w x≤1)
    (K : ℕ) (hK : ∀ x y,x≠y → edgeActivity w x y≤(4:ℝ)^K) :
    let D := inflationScale (V := SourceVertex V K) (holeScale V)
    let realZ := partitionWeight BagEdge.Incident (sourceRealPortion w K) univ
    let bagZ := partitionWeight BagEdge.Incident
      (fun e => sourceRealPortion w K e+(2:ℝ)^e.val.val.2.1.val/D) univ
    1≤bagZ/realZ ∧ bagZ/realZ≤2 := by
  classical
  apply bag_inflation_of_hole_estimate (sourceBags w K) (Fintype.card_pos)
    (sourceBag_card_le_two w K hK) (sourceRealB w K)
    (fun l => (2:ℝ)^l.1.val) (fun _ => by positivity)
  · intro e
    apply sourceBag_height w K (edgeLow_ne_high e.val.val.1 e.val.property)
    · exact e.property _ (edgeLow_mem _)
    · exact e.property _ (edgeHigh_mem _)
  · exact sourceRealPortion_nonneg w hw K
  · exact sourceRealPortion_full_pos w hz K
  · exact holeScale_pos
  · intro H hH
    convert sourceRealPortion_hole_bound hn w hw hz hrlo hrhi K H hH using 1
    congr 3
    ext x
    simp



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _

noncomputable local instance (w : V → V → ℝ) (K : ℕ) : Fintype (BagEdge (sourceBags w K)) := Fintype.ofFinite _

noncomputable def bagHeight (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : ℝ := (2:ℝ)^l.1.val

lemma bagHeight_one (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 1 ≤ bagHeight w K l := by
  exact one_le_pow₀ (by norm_num)

lemma bagHeight_pos (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : 0 < bagHeight w K l :=
  zero_lt_one.trans_le (bagHeight_one w K l)

lemma bagHeight_le (w : V → V → ℝ) (K : ℕ) (l : SourceLabel w K) : bagHeight w K l ≤ 4^K := by
  have hl : l.1.val ≤ 2*K := (Nat.le_of_lt_succ l.1.isLt).trans (sourceLevels_le w K)
  calc
    _  ≤  (2:ℝ)^(2*K) := pow_le_pow_right₀ (by norm_num) hl
    _ = _ := by rw [pow_mul]; norm_num

lemma bagHeight_adjacent (w : V → V → ℝ) (K : ℕ) (a b : SourceLabel w K)
    (hab : (sourceTree w K).Adj a b) : bagHeight w K a ≤ 2*bagHeight w K b := by
  change Hierarchy.Parent _ _ _ a b ∨ Hierarchy.Parent _ _ _ b a at hab
  rcases hab with hab|hab
  · have he : b.1.val=a.1.val+1 := by have := hab.1; omega
    change (2:ℝ)^a.1.val ≤ 2*2^b.1.val
    rw [he,pow_succ]
    have hz : 0 ≤ (2:ℝ)^a.1.val := by positivity
    nlinarith
  · have he : a.1.val=b.1.val+1 := by have := hab.1; omega
    change (2:ℝ)^a.1.val ≤ 2*2^b.1.val
    rw [he,pow_succ]
    nlinarith

lemma sourceRealActivity_le_strength (w : V → V → ℝ) (K : ℕ) (e : SourceRealEdge V K) :
    sourceRealActivity w K e ≤ sourceRealB w K (realLeft K e) (realRight K e) := by
  exact edge_activity_le_realBottleneck source target source_ne_target (2*K+2) (by omega) _ _ _ _ e.1 e.2

lemma sourceRealActivity_le_height (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) (e : SourceRealEdge V K) :
    sourceRealActivity w K e ≤ 2*bagHeight w K (sourceRealLabel w K e) := by
  apply (sourceRealActivity_le_strength w K e).trans
  have hh := dyadic_upper_of_lt (sourceLevels w K)
    (sourceRealB w K (realLeft K e) (realRight K e))
    ((source_strength_le_max w K hw e).trans_lt (maxSourceHeight_lt w K hw))
  change _ ≤ 2*(2:ℝ)^(dyadicLevel (sourceLevels w K) (sourceRealB w K (realLeft K e) (realRight K e))).val
  rw [pow_succ,mul_comm] at hh
  exact hh.le

lemma sourceRealPortion_le_height (w : V → V → ℝ) (K : ℕ)
    (hw : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K) (e : BagEdge (sourceBags w K)) :
    sourceRealPortion w K e ≤ 2*bagHeight w K e.val.val.2 := by
  classical
  by_cases he : ∃ q,sourceRealEmbedding w K q=e
  · obtain ⟨q,rfl⟩ := he
    rw [sourceRealPortion,edgeExtension_on]
    exact sourceRealActivity_le_height w K hw q
  · rw [sourceRealPortion,edgeExtension_off _ _ _ he]
    exact mul_nonneg (by norm_num) (bagHeight_pos _ _ _).le

noncomputable def sourceBagWeight (w : V → V → ℝ) (K D : ℕ)
    (e : BagEdge (sourceBags w K)) : ℝ :=
  sourceRealPortion w K e+bagHeight w K e.val.val.2/D

lemma sourceBagWeight_range (w : V → V → ℝ) (K D : ℕ) (hD : 1 ≤ D)
    (hw : ∀ x y,0 < w x y) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K)
    (e : BagEdge (sourceBags w K)) :
    bagHeight w K e.val.val.2/D ≤ sourceBagWeight w K D e ∧
      sourceBagWeight w K D e ≤ 3*bagHeight w K e.val.val.2 := by
  have hr := sourceRealPortion_nonneg w hw K e
  have hu := sourceRealPortion_le_height w K hK e
  have hq : bagHeight w K e.val.val.2/(D:ℝ) ≤ bagHeight w K e.val.val.2 :=
    div_le_self (bagHeight_pos _ _ _).le (by exact_mod_cast hD)
  dsimp [sourceBagWeight]
  constructor <;> linarith

lemma sourceBagWeight_global (w : V → V → ℝ) (K D : ℕ) (hD : 1 ≤ D)
    (hw : ∀ x y,0 < w x y) (hK : ∀ x y,x≠y → edgeActivity w x y ≤ (4:ℝ)^K)
    (e : BagEdge (sourceBags w K)) :
    (D:ℝ)⁻¹ ≤ sourceBagWeight w K D e ∧ sourceBagWeight w K D e ≤ 3*4^K := by
  have hh := sourceBagWeight_range w K D hD hw hK e
  constructor
  · calc
      (D:ℝ)⁻¹ = 1/(D:ℝ) := (one_div _).symm
      _ ≤ bagHeight w K e.val.val.2/(D:ℝ) :=
        div_le_div_of_nonneg_right (bagHeight_one w K e.val.val.2) (Nat.cast_nonneg D)
      _ ≤ _ := hh.1
  · exact hh.2.trans (mul_le_mul_of_nonneg_left (bagHeight_le w K _) (by norm_num))

noncomputable def sourceD (K : ℕ) : ℕ :=
  100*Fintype.card (SourceVertex V K)^2*(100000000*(Fintype.card V+1)^4)

lemma sourceD_one (K : ℕ) : 1 ≤ sourceD (V:=V) K := by
  have hn : 0 < Fintype.card (SourceVertex V K) := Fintype.card_pos
  have hp : 0 < sourceD (V:=V) K := by
    dsimp [sourceD]
    positivity
  omega

omit [Nontrivial V] in
lemma sourceD_cast [Nontrivial V] (K : ℕ) :
    (sourceD (V:=V) K:ℝ)=inflationScale (V:=SourceVertex V K) (holeScale V) := by
  simp only [sourceD,inflationScale,holeScale,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]

end MatchingFPRAS.Enlargement

end OAI
