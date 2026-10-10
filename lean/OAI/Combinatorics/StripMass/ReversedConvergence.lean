import Mathlib
import OAI.Combinatorics.StripMass.DeformationWeights

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open _root_.Matrix _root_.OAI.Matrix Set
open scoped BigOperators Classical

lemma L_reflection (u : ℝ) : L (3*lambda-u)=L u := by
  have ha : 2*lambda+(3*lambda-u)=Real.pi-(3*lambda+u) := by unfold lambda; ring
  have hb : 3*lambda+(3*lambda-u)=Real.pi-(2*lambda+u) := by unfold lambda; ring
  unfold L
  rw [ha,hb,Real.sin_pi_sub,Real.sin_pi_sub,mul_comm]

lemma physicalWeights_reflection (u : ℝ) :
    physicalWeights (3*lambda-u)=
      ⟨(physicalWeights u).U,(physicalWeights u).B,(physicalWeights u).A,
        (physicalWeights u).F,(physicalWeights u).E⟩ := by
  unfold physicalWeights
  dsimp only
  rw [L_reflection,show 3*lambda-(3*lambda-u)=u by ring,
    show 2*lambda-(3*lambda-u)=u-lambda by ring,
    show (3*lambda-u)-lambda=2*lambda-u by ring]
  congr 1 <;> ring

lemma physicalWeights_lambda : physicalWeights lambda=(⟨rho,rho^2,rho^2,rho^2,0⟩ : Weights ℝ) := by
  have hh:=physicalWeights_reflection (2*lambda)
  rw [show 3*lambda-2*lambda=lambda by ring,physicalWeights_two_lambda] at hh
  exact hh

lemma physicalWeights_lambda_nonneg (s : Tile) : 0≤(physicalWeights lambda).tile s := by
  rw [physicalWeights_lambda]
  have hrho : 0<rho := by unfold rho; positivity
  cases s <;> simp only [Weights.tile] <;> positivity

lemma physicalWeights_reverse_pos {t : ℝ} (ht : t∈Ioc 0 lambda) :
    0<(physicalWeights t).A ∧ 0<(physicalWeights t).B ∧ 0<(physicalWeights t).U := by
  have hh:=physicalWeights_deformation_pos ht
  rw [physicalWeights_reflection] at hh
  exact ⟨hh.2.2,hh.2.1,hh.1⟩

lemma physicalWeights_reverse_tile_nonneg {t : ℝ} (ht : t∈Icc 0 lambda)
    (s : Tile) (hs : ¬s.Occupied 0) : 0≤(physicalWeights t).tile s := by
  rcases eq_or_lt_of_le ht.1 with rfl | ht₀
  · rw [physicalWeights_zero]
    cases s <;> norm_num [identityWeights,Weights.tile]
  · obtain ⟨hA,hB,hU⟩:=physicalWeights_reverse_pos ⟨ht₀,ht.2⟩
    cases s <;> simp_all [Tile.Occupied,Tile.Adj,Tile.edges,Weights.tile]
    any_goals positivity

def augmentedReversedWeights (n : ℕ) : Fin (n+1) → Weights ℝ :=
  Fin.snoc (fun _ : Fin n=>physicalWeights lambda) northInjectionWeights

def reverseDeformationAngles (n : ℕ) (t : ℝ) : Fin (n+1) → ℝ :=
  Fin.cons (3*lambda-t) (fun _=>2*lambda)

def reverseDeformationWeights (n : ℕ) (t : ℝ) : Fin (n+1+1) → Weights ℝ :=
  Fin.cons (physicalWeights t) (augmentedReversedWeights n)

lemma reverseDeformationWeights_eq (n : ℕ) (t : ℝ) :
    reverseDeformationWeights n t=Fin.snoc
      (fun i=>physicalWeights (3*lambda-reverseDeformationAngles n t i)) northInjectionWeights := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i
  · change physicalWeights t=
      (Fin.snoc (fun i : Fin (n+1)=>physicalWeights (3*lambda-reverseDeformationAngles n t i))
        northInjectionWeights : Fin (n+1+1) → Weights ℝ) ((0 : Fin (n+1)).castSucc)
    rw [Fin.snoc_castSucc]
    simp only [reverseDeformationAngles,Fin.cons_zero,show 3*lambda-(3*lambda-t)=t by ring]
  · rw [reverseDeformationWeights,Fin.cons_succ]
    refine Fin.lastCases ?_ (fun j=>?_) j
    · rw [augmentedReversedWeights,Fin.snoc_last,Fin.succ_last,Fin.snoc_last]
    · rw [augmentedReversedWeights,Fin.snoc_castSucc,Fin.succ_castSucc,Fin.snoc_castSucc]
      simp only [reverseDeformationAngles,Fin.cons_succ,show 3*lambda-2*lambda=lambda by ring]

lemma reverseDeformationWeights_physical (n : ℕ) :
    reverseDeformationWeights n lambda=augmentedReversedWeights (n+1) := by
  rw [reverseDeformationWeights_eq]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;>
    simp only [reverseDeformationAngles,Fin.cons_zero,Fin.cons_succ,
      show 3*lambda-(3*lambda-lambda)=lambda by ring,show 3*lambda-2*lambda=lambda by ring]

lemma reverseDeformationWeights_flat (n : ℕ) : reverseDeformationWeights n 0 0=identityWeights := by
  simp [reverseDeformationWeights,physicalWeights_zero]

lemma augmentedReversed_tile_nonneg (n : ℕ) (i : Fin (n+1)) (s : Tile) :
    0≤(augmentedReversedWeights n i).tile s := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simpa only [augmentedReversedWeights,Fin.snoc_last] using northInjection_nonneg s
  · simpa only [augmentedReversedWeights,Fin.snoc_castSucc] using physicalWeights_lambda_nonneg s

lemma reverseDeformationWeights_nonnegative (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    ColumnNonnegative (reverseDeformationWeights n t) := by
  intro p q s hs
  apply Finset.prod_nonneg
  intro i _
  refine Fin.cases ?_ (fun j=>?_) i
  · exact physicalWeights_reverse_tile_nonneg ht (s 0) (hs.south 0 rfl)
  · exact augmentedReversed_tile_nonneg n j (s j.succ)

lemma physicalWeights_lambda_pos :
    0<(physicalWeights lambda).A ∧ 0<(physicalWeights lambda).B ∧ 0<(physicalWeights lambda).U :=
  physicalWeights_reverse_pos ⟨lambda_pos,le_rfl⟩

lemma reverseDeformationWeights_accessible (n : ℕ) {t : ℝ} (ht : t∈Ioc 0 lambda) :
    PositiveMatrix.Accessible (restrictedColumn (reverseDeformationWeights n t))
      (injectionColumn (reverseDeformationWeights n t)) := by
  apply column_accessible _ (reverseDeformationWeights_nonnegative n ⟨ht.1.le,ht.2⟩)
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_reverse_pos ht).1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [reverseDeformationWeights,augmentedReversedWeights,northInjectionWeights]
      · simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.1
  · intro i
    refine Fin.cases ?_ (fun j=>?_) i
    · exact (physicalWeights_reverse_pos ht).2.1
    · refine Fin.lastCases ?_ (fun j=>?_) j
      · norm_num [reverseDeformationWeights,augmentedReversedWeights,northInjectionWeights]
      · simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.2.1
  · intro i hi
    revert hi
    refine Fin.cases ?_ (fun j=>?_) i
    · intro _; exact (physicalWeights_reverse_pos ht).2.2
    · revert j
      apply Fin.lastCases
      · intro hh
        simp only [Fin.val_succ,Fin.val_last] at hh
        omega
      · intro j _
        simpa only [reverseDeformationWeights,Fin.cons_succ,augmentedReversedWeights,Fin.snoc_castSucc]
          using physicalWeights_lambda_pos.2.2

lemma reverseDeformationAngles_scalar_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    angleScalar (reverseDeformationAngles n t)≠0 := by
  have hh:=deformationAngles_scalar_ne_zero n ht
  rw [angleScalar,angleEvaluation_scalar] at hh ⊢
  have he : (fun i=>(Real.cos (2*reverseDeformationAngles n t i-3*lambda):ℂ))=
      (fun i=>(Real.cos (2*deformationAngles n t i-3*lambda):ℂ)) := by
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [reverseDeformationAngles,deformationAngles,Fin.cons_zero,
        show 2*(3*lambda-t)-3*lambda= -(2*t-3*lambda) by ring,Real.cos_neg]
    · simp only [reverseDeformationAngles,deformationAngles,Fin.cons_succ,
        show 2*(2*lambda)-3*lambda=lambda by ring,show 2*lambda-3*lambda= -lambda by ring,Real.cos_neg]
  rw [he]
  exact hh

lemma reverseDeformationAngles_L_ne_zero (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda)
    (i : Fin (n+1)) : L (3*lambda-reverseDeformationAngles n t i)≠0 := by
  refine Fin.cases ?_ (fun j=>?_) i
  · simp only [reverseDeformationAngles,Fin.cons_zero,show 3*lambda-(3*lambda-t)=t by ring]
    rw [←L_reflection t]
    exact (L_deformation_pos ht).ne'
  · simp only [reverseDeformationAngles,Fin.cons_succ]
    rw [L_reflection]
    simpa only [show 3*lambda-lambda=2*lambda by ring] using
      (L_deformation_pos (t:=lambda) ⟨lambda_pos.le,le_rfl⟩).ne'

lemma reverseDeformationWeights_stationary (n : ℕ) {t : ℝ} (ht : t∈Icc 0 lambda) :
    (restrictedColumn (reverseDeformationWeights n t)).mulVec
        (fun p=>angleAugmented (reverseDeformationAngles n t) p.val)+
      injectionColumn (reverseDeformationWeights n t)=fun p=>angleAugmented (reverseDeformationAngles n t) p.val := by
  rw [reverseDeformationWeights_eq]
  exact angleAugmented_restricted_stationary _ (reverseDeformationAngles_L_ne_zero n ht)
    (reverseDeformationAngles_scalar_ne_zero n ht)

lemma continuousOn_reverseDeformationWeights_tile (n : ℕ) (i : Fin (n+1+1)) (s : Tile) :
    ContinuousOn (fun t=>(reverseDeformationWeights n t i).tile s) (Icc 0 lambda) := by
  refine Fin.cases ?_ (fun j=>?_) i
  · change ContinuousOn (fun t=>(physicalWeights t).tile s) (Icc 0 lambda)
    cases s <;> simp only [physicalWeights,Weights.tile]
    · exact continuousOn_const
    all_goals
      apply ContinuousOn.div
      · fun_prop
      · unfold L; fun_prop
      · intro t ht
        rw [←L_reflection t]
        exact (L_deformation_pos ht).ne'
  · change ContinuousOn (fun _ : ℝ=>(augmentedReversedWeights n j).tile s) (Icc 0 lambda)
    exact continuousOn_const

lemma continuousOn_reverseDeformationColumn (n : ℕ) :
    ContinuousOn (fun t=>restrictedColumn (reverseDeformationWeights n t)) (Icc 0 lambda) := by
  have hh:=continuousOn_column (reverseDeformationWeights n) (continuousOn_reverseDeformationWeights_tile n)
  apply continuousOn_pi.mpr
  intro p
  apply continuousOn_pi.mpr
  intro q
  exact continuousOn_pi.mp (continuousOn_pi.mp hh p.val) q.val

lemma continuous_reverseDeformationAngles (n : ℕ) : Continuous (reverseDeformationAngles n) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const.sub continuous_id
  · exact continuous_const

lemma continuousOn_reverseDeformationVector (n : ℕ) :
    ContinuousOn (fun t=>fun p : NonemptyPairing (n+1+1)=>angleAugmented (reverseDeformationAngles n t) p.val)
      (Icc 0 lambda) := by
  have hc:=continuousOn_angleAugmented (S:=reverseDeformationAngles n '' Icc 0 lambda) (by
    rintro u ⟨t,ht,rfl⟩
    exact reverseDeformationAngles_scalar_ne_zero n ht)
  have hh:=hc.comp (continuous_reverseDeformationAngles n).continuousOn (fun t ht=>⟨t,ht,rfl⟩)
  apply continuousOn_pi.mpr
  intro p
  exact continuousOn_pi.mp hh p.val

lemma summablePowers_identity_bottom {n : ℕ} (w : Fin (n+1) → Weights ℝ)
    (hzero : w 0=identityWeights) (hw : ColumnNonnegative w)
    (hs : PositiveMatrix.SummablePowers (restrictedColumn (fun i=>w i.succ))) :
    PositiveMatrix.SummablePowers (restrictedColumn w) := by
  let e:=Pairing.nonemptyBottomSplit n
  apply (PositiveMatrix.summablePowers_reindex_iff _ e).mp
  apply PositiveMatrix.summablePowers_of_zero_rows
  · exact fun i j=>hw.restricted (e i) (e j)
  · have he : ((restrictedColumn w).submatrix e e).toBlocks₁₁=
        restrictedColumn (fun i=>w i.succ) := by
      ext q p
      exact column_padBottom w p.val q.val
    rw [he]
    exact hs
  · intro q i
    exact column_identity_bottom_row w hzero (e i).val q.val.val (not_not.mp q.property)

 

theorem augmentedReversed_summablePowers (n : ℕ) :
    PositiveMatrix.SummablePowers (restrictedColumn (augmentedReversedWeights n)) := by
  induction n with
  | zero =>
    intro p
    exact (p.property (Pairing.eq_empty_of_le_one (by omega) p.val)).elim
  | succ n ih =>
    rw [←reverseDeformationWeights_physical]
    apply PositiveMatrix.summablePowers_on_Icc
      (fun t=>restrictedColumn (reverseDeformationWeights n t))
      (fun t=>injectionColumn (reverseDeformationWeights n t))
      (fun t=>fun p=>angleAugmented (reverseDeformationAngles n t) p.val)
      lambda_pos.le (continuousOn_reverseDeformationColumn n) (continuousOn_reverseDeformationVector n)
      (fun t ht=>(reverseDeformationWeights_nonnegative n ht).restricted)
      (fun t ht=>(reverseDeformationWeights_nonnegative n ht).injection)
      (fun t ht=>reverseDeformationWeights_stationary n ht)
      ?_ (fun t ht=>reverseDeformationWeights_accessible n ht)
      lambda ⟨lambda_pos.le,le_rfl⟩
    apply summablePowers_identity_bottom _ (reverseDeformationWeights_flat n)
      (reverseDeformationWeights_nonnegative n ⟨le_rfl,lambda_pos.le⟩)
    simpa only [reverseDeformationWeights,Fin.cons_succ] using ih

end

 

 

noncomputable section
open scoped Classical
namespace Tile

 

def horizontalPort : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def horizontal : Tile → Tile
  | .vertical₀ => .cap
  | .vertical₁ => .cup
  | .cap => .vertical₀
  | .cup => .vertical₁
  | .verticalPair => .capCup
  | .capCup => .verticalPair
  | t => t

@[simp] lemma horizontal_involutive (t : Tile) : t.horizontal.horizontal=t := by cases t <;> rfl

lemma horizontal_adj (t : Tile) (a b : Fin 4) :
    t.horizontal.Adj (horizontalPort a) (horizontalPort b) ↔ t.Adj a b := by
  revert t a b
  decide

lemma horizontal_occupied (t : Tile) (a : Fin 4) :
    t.horizontal.Occupied (horizontalPort a) ↔ t.Occupied a := by
  revert t a
  decide

lemma horizontal_weight (w : Weights ℝ) (t : Tile) :
    (⟨w.U,w.B,w.A,w.F,w.E⟩ : Weights ℝ).tile t.horizontal = w.tile t := by
  cases t <;> rfl

lemma physical_horizontal_weight (u : ℝ) (t : Tile) :
    (physicalWeights (3*lambda-u)).tile t.horizontal=(physicalWeights u).tile t := by
  rw [physicalWeights_reflection,horizontal_weight]

lemma physical_horizontal_weight_two (t : Tile) :
    (physicalWeights (2*lambda)).tile t.horizontal=(physicalWeights lambda).tile t := by
  simpa only [show 3*lambda-lambda=2*lambda by ring] using physical_horizontal_weight lambda t

 

lemma physical_horizontal (t : Tile) : t.horizontal≠.verticalPair ↔ t≠.capCup := by
  cases t <;> decide

end Tile
end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open scoped Classical
open Diagram

namespace Diagram.Tile
 

def representative (t : Tile) (upper : Bool) : Fin 4 :=
  if upper then if t.Occupied 0 then 0 else 1
  else if t.Occupied 2 then 2 else 3

lemma representative_side (t : Tile) (b : Bool) :
    decide ((t.representative b).val<2)=b := by
  cases b <;> simp [representative] <;> split <;> decide

lemma representative_occupied (t : Tile) (ht : t≠.verticalPair) (b : Bool) :
    t.Occupied (t.representative b) ↔ if b then t.upperUsed else t.lowerUsed := by
  revert t b
  decide

lemma occupied_triangle (t : Tile) (ht : t≠.verticalPair) (p : Fin 4) (hp : t.Occupied p) :
    if decide (p.val<2) then t.upperUsed = true else t.lowerUsed = true := by
  revert t p
  decide

lemma reach_representative (t : Tile) (ht : t≠.verticalPair) (p : Fin 4) (hp : t.Occupied p) :
    Relation.ReflTransGen t.Adj p (t.representative (decide (p.val<2))) := by
  cases t <;> fin_cases p <;>
    simp_all [representative,Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals first | exact .refl | exact .single (by decide)

lemma reach_middle (t : Tile) (ht : t≠.verticalPair) (hm : t.middle) :
    Relation.ReflTransGen t.Adj (t.representative true) (t.representative false) := by
  cases t <;> simp_all [middle,representative,Tile.Occupied,Tile.Adj,Tile.edges]
  all_goals exact .single (by decide)

lemma adjacent_projects (t : Tile) (ht : t≠.verticalPair) (a b : Fin 4) (h : t.Adj a b) :
    decide (a.val<2)=decide (b.val<2) ∨ t.middle := by
  revert t a b
  decide
end Diagram.Tile

abbrev HoneycombPort := Cell × Fin 4

def portTriangle (v : HoneycombPort) : Triangle :=
  (v.1.1,v.1.2,decide (v.2.val<2))

namespace HoneycombAssignment
variable {N : ℕ}

 

def portWiring (D : HoneycombAssignment N) (v w : HoneycombPort) : Prop :=
  (v.1=w.1 ∧ (D.tile v.1).Adj v.2 w.2) ∨
  (v.1.2=w.1.2 ∧ v.1.1+1=w.1.1 ∧ v.2=2 ∧ w.2=1 ∧ (D.tile v.1).Occupied 2) ∨
  (w.1.2=v.1.2 ∧ w.1.1+1=v.1.1 ∧ w.2=2 ∧ v.2=1 ∧ (D.tile w.1).Occupied 2) ∨
  (v.1.1=w.1.1 ∧ v.1.2+1=w.1.2 ∧ w.1.2<N ∧ v.2=3 ∧ w.2=0 ∧ (D.tile v.1).Occupied 3) ∨
  (w.1.1=v.1.1 ∧ w.1.2+1=v.1.2 ∧ v.1.2<N ∧ w.2=3 ∧ v.2=0 ∧ (D.tile w.1).Occupied 3)

lemma portWiring_symm (D : HoneycombAssignment N) {v w : HoneycombPort} :
    D.portWiring v w → D.portWiring w v := by
  intro h
  rcases h with ⟨he,h⟩ | h | h | h | h
  · exact Or.inl ⟨he.symm,by simpa only [he] using (Tile.adj_symm _).mp h⟩
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

instance portWiring_symm_instance (D : HoneycombAssignment N) : Std.Symm D.portWiring :=
  ⟨fun _ _=>D.portWiring_symm⟩

lemma port_used (D : HoneycombAssignment N) (v : HoneycombPort) :
    Graph.Used D.portWiring v ↔ (D.tile v.1).Occupied v.2 := by
  constructor
  · rintro ⟨w,h⟩
    rcases v with ⟨⟨i,j⟩,a⟩
    rcases w with ⟨⟨k,l⟩,b⟩
    dsimp only [portWiring,Prod.fst,Prod.snd] at h
    rcases h with ⟨_,h⟩ | ⟨_,_,rfl,_,h⟩ | ⟨hj,hi,_,rfl,h⟩ |
      ⟨_,_,_,rfl,_,h⟩ | ⟨hi,hj,hn,_,rfl,h⟩
    · exact ⟨b,h⟩
    · exact h
    · have hh := (D.horizontal k l).mp h
      simpa only [hi,hj] using hh
    · exact h
    · have hh := (D.vertical k l (by omega)).mp h
      simpa only [hi,hj] using hh
  · rintro ⟨p,hp⟩
    exact ⟨(v.1,p),Or.inl ⟨rfl,hp⟩⟩

lemma port_in_strip (D : HoneycombAssignment N) {q : Cell} {a : Fin 4}
    (h : (D.tile q).Occupied a) : q.2<N := by
  by_contra hn
  have hh := D.outside q.1 q.2 (by omega)
  exact Tile.vacant_not_occupied a (hh ▸ h)

 

lemma port_projects_used (D : HoneycombAssignment N) {v : HoneycombPort}
    (hv : Graph.Used D.portWiring v) : portTriangle v∈D.graph.support := by
  have hp := (D.port_used v).mp hv
  have h := Tile.occupied_triangle (D.tile v.1) (D.physical v.1) v.2 hp
  rcases v with ⟨⟨i,j⟩,a⟩
  dsimp only [portTriangle]
  by_cases ha : a.val<2
  · simpa only [ha,decide_true,ite_true,←D.up_support_iff,up] using h
  · simpa only [ha,decide_false,Bool.false_eq_true,ite_false,←D.down_support_iff,down] using h

lemma tile_reach (D : HoneycombAssignment N) (q : Cell) {a b : Fin 4}
    (h : Relation.ReflTransGen (D.tile q).Adj a b) :
    Relation.ReflTransGen D.portWiring (q,a) (q,b) :=
  Graph.map_reach (fun a=>(q,a)) (fun _ _ h=>.single (Or.inl ⟨rfl,h⟩)) h

lemma port_projects_edge (D : HoneycombAssignment N) {v w : HoneycombPort}
    (h : D.portWiring v w) : Relation.ReflTransGen D.graph.Adj (portTriangle v) (portTriangle w) := by
  rcases v with ⟨⟨i,j⟩,a⟩
  rcases w with ⟨⟨k,l⟩,b⟩
  dsimp only [portWiring,Prod.fst,Prod.snd] at h
  rcases h with ⟨he,h⟩ | ⟨hj,hi,ha,hb,h⟩ | ⟨hj,hi,hb,ha,h⟩ |
    ⟨hi,hj,hn,ha,hb,h⟩ | ⟨hi,hj,hn,hb,ha,h⟩
  · cases he
    rcases Tile.adjacent_projects (D.tile (i,j)) (D.physical (i,j)) a b h with hp | hm
    · have : portTriangle ((i,j),a)=portTriangle ((i,j),b) := by
        simp only [portTriangle,hp]
      exact this ▸ Relation.ReflTransGen.refl
    · have hn := D.port_in_strip (show (D.tile (i,j)).Occupied a from ⟨b,h⟩)
      have he : D.graph.Adj (up i j) (down i j) := (tileGraph_middle N D.tile i j).mpr ⟨hn,hm⟩
      by_cases ha : a.val<2 <;> by_cases hb : b.val<2
      · simp only [portTriangle,ha,hb,decide_true]; exact .refl
      · simpa only [portTriangle,ha,hb,decide_true,decide_false,up,down] using Relation.ReflTransGen.single he
      · simpa only [portTriangle,ha,hb,decide_true,decide_false,up,down] using
          Relation.ReflTransGen.single (D.graph.symm.symm _ _ he)
      · simp only [portTriangle,ha,hb,decide_false]; exact .refl
  · subst k; subst l; subst a; subst b
    have hh : D.graph.Adj (down i j) (up (i+1) j) :=
      (D.down_neighbors i j _).mpr ⟨D.port_in_strip h,Or.inr (Or.inl ⟨rfl,h⟩)⟩
    exact .single hh
  · subst i; subst j; subst a; subst b
    have hh : D.graph.Adj (down k l) (up (k+1) l) :=
      (D.down_neighbors k l _).mpr ⟨D.port_in_strip h,Or.inr (Or.inl ⟨rfl,h⟩)⟩
    exact .single (D.graph.symm.symm _ _ hh)
  · subst k; subst l; subst a; subst b
    exact .single ((D.down_neighbors i j _).mpr ⟨by omega,Or.inr (Or.inr ⟨hn,rfl,h⟩)⟩)
  · subst i; subst j; subst a; subst b
    exact .single (D.graph.symm.symm _ _
      ((D.down_neighbors k l _).mpr ⟨by omega,Or.inr (Or.inr ⟨hn,rfl,h⟩)⟩))

def representative (D : HoneycombAssignment N) (v : Triangle) : HoneycombPort :=
  ((v.1,v.2.1),(D.tile (v.1,v.2.1)).representative v.2.2)

lemma representative_projects (D : HoneycombAssignment N) (v : Triangle) :
    portTriangle (D.representative v)=v := by
  rcases v with ⟨i,j,b⟩
  change (i,j,decide (((D.tile (i,j)).representative b).val<2))=(i,j,b)
  rw [Tile.representative_side]

lemma representative_used (D : HoneycombAssignment N) {v : Triangle}
    (hv : v∈D.graph.support) : Graph.Used D.portWiring (D.representative v) := by
  rw [D.port_used]
  rcases v with ⟨i,j,b⟩
  change (D.tile (i,j)).Occupied ((D.tile (i,j)).representative b)
  rw [Tile.representative_occupied _ (D.physical (i,j))]
  cases b
  · exact (D.down_support_iff i j).mp hv
  · exact (D.up_support_iff i j).mp hv

lemma port_to_representative (D : HoneycombAssignment N) {v : HoneycombPort}
    (hv : Graph.Used D.portWiring v) :
    Relation.ReflTransGen D.portWiring v (D.representative (portTriangle v)) :=
  D.tile_reach v.1 (Tile.reach_representative _ (D.physical v.1) _ ((D.port_used v).mp hv))

lemma edge_between_representatives (D : HoneycombAssignment N) {v w : HoneycombPort}
    (h : D.portWiring v w) : Relation.ReflTransGen D.portWiring
      (D.representative (portTriangle v)) (D.representative (portTriangle w)) :=
  ((symm (D.port_to_representative ⟨w,h⟩)).tail h).trans
    (D.port_to_representative ⟨v,D.portWiring_symm h⟩)

lemma up_lifts_edge (D : HoneycombAssignment N) (i : ℤ) (j : ℕ) (w : Triangle)
    (h : D.graph.Adj (up i j) w) :
    Relation.ReflTransGen D.portWiring (D.representative (up i j)) (D.representative w) := by
  rcases (D.up_neighbors i j w).mp h with ⟨hn,⟨rfl,hm⟩ | ⟨rfl,hw⟩ | ⟨hj,rfl,hs⟩⟩
  · exact D.tile_reach (i,j) (Tile.reach_middle _ (D.physical (i,j)) hm)
  · have he : (D.tile (i-1,j)).Occupied 2 := by
      exact (D.horizontal (i-1) j).mpr (by simpa only [sub_add_cancel] using hw)
    exact D.edge_between_representatives (v:=((i,j),1)) (w:=((i-1,j),2))
      (Or.inr (Or.inr (Or.inl ⟨rfl,by dsimp; omega,rfl,rfl,he⟩)))
  · have he : (D.tile (i,j-1)).Occupied 3 := by
      have hn' : j-1+1<N := by omega
      have hh := (D.vertical i (j-1) hn').mpr
      exact hh (by simpa only [show j-1+1=j by omega] using hs)
    exact D.edge_between_representatives (v:=((i,j),0)) (w:=((i,j-1),3))
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,by dsimp; omega,hn,rfl,rfl,he⟩))))

lemma lifts_edge (D : HoneycombAssignment N) {v w : Triangle} (h : D.graph.Adj v w) :
    Relation.ReflTransGen D.portWiring (D.representative v) (D.representative w) := by
  rcases v with ⟨i,j,b⟩
  cases b
  · rcases w with ⟨k,l,b⟩
    cases b
    · have hh := (tileGraph_allowed N D.tile h).1
      simp [adjacent,upDownAdjacent] at hh
    · exact symm (D.up_lifts_edge k l (down i j) (D.graph.symm.symm _ _ h))
  · exact D.up_lifts_edge i j w h

 

lemma port_reach_iff (D : HoneycombAssignment N) {v w : HoneycombPort}
    (hv : Graph.Used D.portWiring v) (hw : Graph.Used D.portWiring w) :
    Relation.ReflTransGen D.portWiring v w ↔
      Relation.ReflTransGen D.graph.Adj (portTriangle v) (portTriangle w) := by
  constructor
  · exact Graph.map_reach portTriangle (fun _ _=>D.port_projects_edge)
  · intro h
    exact ((D.port_to_representative hv).trans
      (Graph.map_reach D.representative (fun _ _=>D.lifts_edge) h)).trans
      (symm (D.port_to_representative hw))

 

lemma port_drains_iff (D : HoneycombAssignment N) {root : HoneycombPort}
    (hr : Graph.Used D.portWiring root) :
    Graph.DrainsAt D.portWiring root ↔ Graph.DrainsAt D.graph.Adj (portTriangle root) := by
  constructor
  · intro h v w hvw
    obtain ⟨a,ha⟩ := D.representative_used (show v∈D.graph.support from ⟨w,hvw⟩)
    have hh := Graph.map_reach portTriangle (fun _ _=>D.port_projects_edge) (h _ _ ha)
    simpa only [D.representative_projects] using hh
  · intro h v w hvw
    have hv := D.port_projects_used (show Graph.Used D.portWiring v from ⟨w,hvw⟩)
    obtain ⟨a,ha⟩ := hv
    exact (D.port_reach_iff ⟨w,hvw⟩ hr).mpr (h _ _ ha)

end HoneycombAssignment
end
end CriticalStrip

end OAI
