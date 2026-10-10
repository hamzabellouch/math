import Mathlib
import OAI.Analysis.BoundedHochschild.PathStages

namespace OAI

/-! Simultaneous finite path tests and construction of stage assignments. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open MeasureTheory Filter Topology
open scoped ComplexOrder
namespace HochschildRare
open HochschildWalk
variable {M : Type*} [CStarAlgebra M]

def signedValue {A : Type*} (v : A → unitary M) (a : A × Bool) : unitary M :=
  if a.2 then v a.1 else (v a.1)⁻¹

def pathValue {A : Type*} {r n : ℕ} (v : A → unitary M)
    (w : Fin r × Fin n → A × Bool) (i : Fin r) : unitary M :=
  word (fun j => signedValue v (w (i,j)))

 

def FinitePathTests [PartialOrder M] (τ : M →ₚ[ℂ] ℂ) : Prop :=
  ∀ (C D T : Type) [Fintype C] [Fintype D] [Fintype T],
    Nonempty D → ∀ (v : C → unitary M) (r n : T → ℕ)
      (w : ∀ t, Fin (r t) × Fin (n t) → (C ⊕ D) × Bool)
      (q : ∀ t, FreeGroup (Fin (r t))),
    (∀ t, q t ≠ 1) →
    (∀ t, ∃ (s : Fin (r t) → Fin (n t)) (a : Fin (r t) → D),
      (∀ i, (w t (i,s i)).1 = Sum.inr (a i)) ∧
      (∀ i z, (w t z).1 = Sum.inr (a i) → z=(i,s i))) →
    ∀ ε : ℝ, 0 < ε → ∃ u : D → unitary M,
      ∀ t, ‖τ (FreeGroup.lift (pathValue (Sum.elim v u) (w t)) (q t) : M)‖ < ε

def assignedLabel (v : ℕ → unitary M)
    (a : ∀ k, Fin (labels k) → unitary M) : Label → unitary M
  | .inl j => v j
  | .inr t => a t.1 t.2

abbrev StepCoeff (k : ℕ) := Fin (baseCut k) ⊕ ((j : Fin k) × Fin (labels j.val))
def stepEmbedding (k : ℕ) : (StepCoeff k ⊕ Fin (labels k)) → Label
  | .inl (.inl j) => .inl j.val
  | .inl (.inr a) => .inr ⟨a.1.val,a.2⟩
  | .inr j => .inr ⟨k,j⟩

lemma stepEmbedding_injective (k : ℕ) : Function.Injective (stepEmbedding k) := by
  rintro (a|a) (b|b)
  · rcases a with a|⟨s,a⟩ <;> rcases b with b|⟨t,b⟩
    · simp only [stepEmbedding,Sum.inl.injEq,Fin.val_inj]
      exact id
    · simp [stepEmbedding]
    · simp [stepEmbedding]
    · intro h
      have hst : s=t := Fin.ext (congrArg Sigma.fst (Sum.inr.inj h))
      subst t
      have hab : a=b := eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
      subst b
      rfl
  · rcases a with a|⟨s,a⟩
    · simp [stepEmbedding]
    · intro h
      have := congrArg Sigma.fst (Sum.inr.inj h)
      exact False.elim ((Nat.ne_of_lt s.isLt) this)
  · rcases b with b|⟨t,b⟩
    · simp [stepEmbedding]
    · intro h
      have := congrArg Sigma.fst (Sum.inr.inj h)
      exact False.elim ((Nat.ne_of_lt t.isLt) this.symm)
  · intro h
    exact congrArg Sum.inr (eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2)

lemma goodPath_step_range {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (i : Fin r × Fin (time k)) :
    (w i).1 ∈ Set.range (stepEmbedding k) := by
  obtain ⟨a,ha⟩ := goodPath_label_in_range w hw i
  rcases a with a|⟨s,a⟩
  · exact ⟨.inl (.inl a),ha⟩
  · by_cases hs : s.val < k
    · exact ⟨.inl (.inr ⟨⟨s.val,hs⟩,a⟩),ha⟩
    · have hsk : s.val=k := by omega
      refine ⟨.inr (Fin.cast (congrArg labels hsk) a),?_⟩
      change Sum.inr ⟨k,Fin.cast (congrArg labels hsk) a⟩=(w i).1
      rw [← ha]
      apply congrArg Sum.inr
      exact (Sigma.ext hsk (by apply (Fin.heq_ext_iff (congrArg labels hsk)).mpr; rfl)).symm

lemma lift_pathValue (v : Label → unitary M) {r n : ℕ}
    (w : Fin r × Fin n → Increment) (q : FreeGroup (Fin r)) :
    FreeGroup.lift v (FreeGroup.lift
      (fun i => word (fun j => incrementValue (w (i,j)))) q) =
      FreeGroup.lift (pathValue v w) q := by
  apply FreeGroup.lift_unique ((FreeGroup.lift v).comp (FreeGroup.lift _))
  intro i
  simp only [MonoidHom.coe_comp,Function.comp_apply,FreeGroup.lift_apply_of,
    word,map_list_prod,List.map_ofFn,pathValue]
  congr 2
  funext j
  cases h : (w (i,j)).2 <;> simp [incrementValue,signedValue,h]

abbrev StageTest (k : ℕ) := (r : Fin (k+2)) ×
  {w : Fin r.val × Fin (time k) → Increment // w ∉ stageBad k r.val} ×
  {q : FreeGroup (Fin r.val) // q ≠ 1 ∧ q.toWord.length ≤ k+1}

instance stageTestFintype (k : ℕ) : Fintype (StageTest k) := by
  classical
  letI (r : Fin (k+2)) : Fintype {w : Fin r.val × Fin (time k) → Increment //
      w ∉ stageBad k r.val} := (goodPaths_finite k r.val).fintype
  letI (r : Fin (k+2)) : Fintype {q : FreeGroup (Fin r.val) //
      q ≠ 1 ∧ q.toWord.length ≤ k+1} := (boundedWords_finite r.val (k+1)).fintype
  infer_instance

def encodePath {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (z : Fin r × Fin (time k)) :
    (StepCoeff k ⊕ Fin (labels k)) × Bool :=
  ((goodPath_step_range w hw z).choose,(w z).2)

lemma encodePath_decodes {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) (z : Fin r × Fin (time k)) :
    stepEmbedding k (encodePath w hw z).1=(w z).1 :=
  (goodPath_step_range w hw z).choose_spec

lemma encodePath_distinguished {k r : ℕ} (w : Fin r × Fin (time k) → Increment)
    (hw : w ∉ stageBad k r) :
    ∃ (s : Fin r → Fin (time k)) (a : Fin r → Fin (labels k)),
      (∀ i, (encodePath w hw (i,s i)).1=Sum.inr (a i)) ∧
      (∀ i z, (encodePath w hw z).1=Sum.inr (a i) → z=(i,s i)) := by
  obtain ⟨s,a,ha,huniq,_⟩ := goodPath_distinguished w hw
  refine ⟨s,a,fun i => ?_,fun i z hz => ?_⟩
  · apply stepEmbedding_injective k
    rw [encodePath_decodes,ha]
    rfl
  · apply huniq i z
    rw [← encodePath_decodes w hw z,hz]
    rfl

def stageCoeff (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    (k : ℕ) : StepCoeff k → unitary M := fun b =>
  assignedLabel v a (stepEmbedding k (Sum.inl b))

lemma updated_step (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    (k : ℕ) (u : Fin (labels k) → unitary M) (b : StepCoeff k ⊕ Fin (labels k)) :
    assignedLabel v (Function.update a k u) (stepEmbedding k b)=
      Sum.elim (stageCoeff v a k) u b := by
  classical
  rcases b with (b|⟨j,b⟩)|b
  · rfl
  · simp [assignedLabel,stepEmbedding,stageCoeff,Function.update_of_ne (Nat.ne_of_lt j.isLt)]
  · simp [assignedLabel,stepEmbedding]

lemma pathValue_updated (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M)
    {k r : ℕ} (u : Fin (labels k) → unitary M)
    (w : Fin r × Fin (time k) → Increment) (hw : w ∉ stageBad k r) :
    pathValue (assignedLabel v (Function.update a k u)) w =
      pathValue (Sum.elim (stageCoeff v a k) u) (encodePath w hw) := by
  funext i
  unfold pathValue
  congr 1
  funext j
  have hh := updated_step v a k u (encodePath w hw (i,j)).1
  rw [encodePath_decodes] at hh
  unfold signedValue
  change (if (w (i,j)).2 then _ else _)=(if (w (i,j)).2 then _ else _)
  rw [hh]

variable [PartialOrder M]

def AtStage (τ : M →ₚ[ℂ] ℂ) (v : ℕ → unitary M)
    (a : ∀ k, Fin (labels k) → unitary M) (k : ℕ) : Prop :=
  ∀ r, r ≤ k+1 → ∀ w : Fin r × Fin (time k) → Increment, w ∉ stageBad k r →
    ∀ q : FreeGroup (Fin r), q ≠ 1 → q.toWord.length ≤ k+1 →
      ‖τ (FreeGroup.lift (assignedLabel v a) (FreeGroup.lift
        (fun i => word (fun j => incrementValue (w (i,j)))) q) : M)‖ < 1/(k+1:ℝ)

 

theorem exists_stage_choice (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (a : ∀ k, Fin (labels k) → unitary M) (k : ℕ) :
    ∃ u : Fin (labels k) → unitary M, AtStage τ v (Function.update a k u) k := by
  classical
  obtain ⟨u,hu⟩ := hf (StepCoeff k) (Fin (labels k)) (StageTest k)
    ⟨⟨0,labels_pos k⟩⟩ (stageCoeff v a k) (fun t => t.1.val) (fun _ => time k)
    (fun t => encodePath t.2.1.val t.2.1.property) (fun t => t.2.2.val)
    (fun t => t.2.2.property.1)
    (fun t => encodePath_distinguished t.2.1.val t.2.1.property)
    (1/(k+1:ℝ)) (by positivity)
  refine ⟨u,fun r hr w hw q hq hqn => ?_⟩
  let t : StageTest k := ⟨⟨r,by omega⟩,⟨w,hw⟩,⟨q,hq,hqn⟩⟩
  have ht := hu t
  change ‖τ (FreeGroup.lift (pathValue (Sum.elim (stageCoeff v a k) u) (encodePath w hw)) q : M)‖ < _ at ht
  rw [lift_pathValue,pathValue_updated]
  exact ht

lemma atStage_congr (τ : M →ₚ[ℂ] ℂ) (v : ℕ → unitary M)
    (a b : ∀ k, Fin (labels k) → unitary M) (k : ℕ)
    (hab : ∀ j, j ≤ k → a j=b j) (ha : AtStage τ v a k) : AtStage τ v b k := by
  intro r hr w hw q hq hqn
  have hpath : pathValue (assignedLabel v a) w=pathValue (assignedLabel v b) w := by
    funext i
    unfold pathValue
    congr 1
    funext j
    have he : assignedLabel v a (w (i,j)).1=assignedLabel v b (w (i,j)).1 := by
      obtain ⟨s,hs⟩ := goodPath_label_in_range w hw (i,j)
      rw [← hs]
      rcases s with s|⟨t,s⟩
      · rfl
      · change a t.val s=b t.val s
        rw [hab t.val (by omega)]
    simp only [signedValue,he]
  have hh := ha r hr w hw q hq hqn
  rw [lift_pathValue,hpath,← lift_pathValue] at hh
  exact hh

 

def stageAssignments (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) : ℕ → (∀ k, Fin (labels k) → unitary M)
  | 0 => fun _ _ => 1
  | k+1 => Function.update (stageAssignments τ hf v k) k
      (exists_stage_choice τ hf v (stageAssignments τ hf v k) k).choose

lemma stageAssignments_spec (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (k : ℕ) : AtStage τ v (stageAssignments τ hf v (k+1)) k :=
  (exists_stage_choice τ hf v (stageAssignments τ hf v k) k).choose_spec

lemma stageAssignments_stable (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) (j k : ℕ) (hjk : j+1 ≤ k) :
    stageAssignments τ hf v k j=stageAssignments τ hf v (j+1) j := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    rw [stageAssignments,Function.update_of_ne (by omega : j ≠ k),ih]

 

theorem exists_label_of_finite_paths (τ : M →ₚ[ℂ] ℂ) (hf : FinitePathTests τ)
    (v : ℕ → unitary M) :
    ∃ label : Label → unitary M, (∀ j, label (Sum.inl j)=v j) ∧
      StageTests (fun g => ‖τ (FreeGroup.lift label g : M)‖) := by
  let a : ∀ k, Fin (labels k) → unitary M := fun k => stageAssignments τ hf v (k+1) k
  refine ⟨assignedLabel v a,fun _ => rfl,?_⟩
  change ∀ k, AtStage τ v a k
  intro k
  apply atStage_congr τ v (stageAssignments τ hf v (k+1)) a k
    (fun j hj => stageAssignments_stable τ hf v j (k+1) (by omega))
  exact stageAssignments_spec τ hf v k

end HochschildRare
end

end OAI
