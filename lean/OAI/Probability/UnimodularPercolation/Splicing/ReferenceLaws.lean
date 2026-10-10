import Mathlib
import OAI.Probability.UnimodularPercolation.Splicing.Replay

namespace OAI

/-! Reference Laws for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteJointMass
attribute [local instance] Classical.propDecidable Classical.decEq

 

def jointOutput (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₁ y₂ : ℕ → V) (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E)) : JointSpliceState E :=
  (ωf,(runMasks (replayMasks G x η₁ y₁ c₁ ω₁) (ω₁,η₁)).2,
    (runMasks (replayMasks G x η₂ y₂ c₂ ω₂) (ω₂,η₂)).2)

def jointRestored (G : BondGraph V E) (x : V) (η₁ η₂ : ℕ → Set E)
    (y₂ : ℕ → V) (ω₁ ω₂ : Set E) (c₂ : List (ℕ × E)) : JointSpliceState E :=
  (exchangeOn (maskUnion (replayMasks G x η₂ y₂ c₂ ω₂)) ω₁ ω₂,η₁,η₂)

 

theorem finite_joint_mass_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (B : Finset (JointSpliceState E))
    (hB : ∀ a, jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a))) ≤
      ∑ s ∈ B, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p s := by
  let out (a : I) := jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
    (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a)
  let rest (a : I) := jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a)
  have hinj : Function.Injective rest := by
    intro a b he
    have hη₁ : η₁ a = η₁ b := congrArg (fun s : JointSpliceState E => s.2.1) he
    have hη₂ : η₂ a = η₂ b := congrArg (fun s : JointSpliceState E => s.2.2) he
    have gb₁ : SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ b) (c₁ b) (ωf b) := by
      rw [hη₁]; exact h₁ b
    have gb₂ : SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ b) (c₂ b) (ωf b) := by
      rw [hη₂]; exact h₂ b
    have grb₁ : FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ b) (ω₁ b) := by
      rw [hη₁]; exact hr₁ b
    have grb₂ : FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ b) (ω₂ b) := by
      rw [hη₂]; exact hr₂ b
    have hfield : exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ a) (ω₂ a))) (ω₁ a) (ω₂ a) =
        exchangeOn (maskUnion (replayMasks G x (η₂ a) (y₂ (η₂ a)) (c₂ b) (ω₂ b))) (ω₁ b) (ω₂ b) := by
      have hh := congrArg Prod.fst he
      simpa only [rest,jointRestored,← hη₂] using hh
    obtain ⟨hcode₁,hcode₂,hfieldf,haux₁,haux₂⟩ := joint_restore_seeded_unique G x
      (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) choose₁ choose₂ k 0 0
      (ω₁ a) (ω₂ a) (ωf a) (ω₁ b) (ω₂ b) (ωf b)
      (c₁ a) (c₂ a) (c₁ b) (c₂ b) (h₁ a) (h₂ a) gb₁ gb₂
      (hc₁ a) (hc₂ a) (hc₁ b) (hc₂ b) (hsep a) (hsep b)
      (hr₁ a) (hr₂ a) grb₁ grb₂ hfield
    have hout : out a = out b := by
      apply Prod.ext hfieldf
      apply Prod.ext
      · simpa only [out,jointOutput,hη₁] using haux₁
      · simpa only [out,jointOutput,hη₂] using haux₂
    exact hir (Prod.ext hout (Prod.ext hcode₁ hcode₂))
  have hw : ∀ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (out a) =
      jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p (rest a) := by
    intro a
    apply (h₁ a).joint_weight G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) k 0 0
      (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hsep a) Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
    · intro q hq
      have hr := (h₁ a).seam_data G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (ωf a) (c₁ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
    · intro q hq
      have hr := (h₂ a).seam_data G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (ωf a) (c₂ a) q hq
      exact Finset.mem_Icc.mpr ⟨hr.1,hr.2.1⟩
  change (∑ a, jointTupleWeight Q _ _ p (out a)) ≤ _
  simp_rw [hw]
  rw [← Finset.sum_image hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hs
    exact hB a
  · intro s _ _
    exact jointTupleWeight_nonneg Q _ _ p s

end FiniteJointMass

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section TrajectorySupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
def trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V) : ℕ → Set V
  | 0 => ∅
  | k+1 => trajectoryUnion G η y k ∪ cluster G (η (k+1)) (y (k+1))

theorem mem_trajectoryUnion (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k : ℕ) (v : V) : v ∈ trajectoryUnion G η y k ↔
      ∃ i, 1 ≤ i ∧ i ≤ k ∧ v ∈ cluster G (η i) (y i) := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    simp only [trajectoryUnion,Set.mem_union,ih]
    constructor
    · rintro (⟨i,hi,hik,hv⟩ | hv)
      · exact ⟨i,hi,by omega,hv⟩
      · exact ⟨k+1,by omega,by omega,hv⟩
    · rintro ⟨i,hi,hik,hv⟩
      by_cases he : i = k+1
      · exact Or.inr (he ▸ hv)
      · exact Or.inl ⟨i,hi,by omega,hv⟩

theorem trajectoryUnion_finite_cap (G : BondGraph V E) (η : ℕ → Set E) (y : ℕ → V)
    (k M : ℕ) (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (trajectoryUnion G η y k).Finite ∧ (trajectoryUnion G η y k).ncard ≤ k*M := by
  induction k with
  | zero => simp [trajectoryUnion]
  | succ k ih =>
    obtain ⟨hf,hc⟩ := ih (fun i hi hik => hcaps i hi (by omega))
    obtain ⟨hf',hc'⟩ := hcaps (k+1) (by omega) (by omega)
    refine ⟨hf.union hf',?_⟩
    calc
      _ ≤ (trajectoryUnion G η y k).ncard + (cluster G (η (k+1)) (y (k+1))).ncard := Set.ncard_union_le ..
      _ ≤ k*M+M := Nat.add_le_add hc hc'
      _ = (k+1)*M := by ring

 

theorem SpliceTrace.added_subset_trajectory (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) :
    cluster G ωf x \ cluster G ω x ⊆ trajectoryUnion G η y k := by
  induction h with
  | stop => exact fun _ hv => (hv.2 hv.1).elim
  | @step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht ih =>
    let S := cluster G ω x
    let B := cluster G (η i ∩ internalEdges G Sᶜ) (y i)
    let ω' := spliceField G S B e ω (η i)
    have hC : cluster G ω' x = S ∪ B := splice_cluster G ω (η i) x (y i) hy e a b hab he ha hb
    intro v hv
    by_cases hv' : v ∈ cluster G ω' x
    · rw [hC] at hv'
      have hvB := hv'.resolve_left hv.2
      exact (mem_trajectoryUnion G η y k v).mpr
        ⟨i,by omega,hik,conn_mono G Set.inter_subset_left hvB⟩
    · exact ih ⟨hv.1,hv'⟩

 

theorem SpliceTrace.trajectory_hits (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf) (hc : c ≠ []) :
    (cluster G ω x ∩ trajectoryUnion G η y k).Nonempty := by
  cases h with
  | stop => exact (hc rfl).elim
  | step j i ω e a b rest ωf hn hji hik hmax hy he hab ha hb ht =>
    exact ⟨a,ha,(mem_trajectoryUnion G η y k a).mpr ⟨i,by omega,hik,
      (edge_cluster_sides G (η i) (y i) he hab).mpr (conn_mono G Set.inter_subset_left hb)⟩⟩

 

theorem SpliceTrace.added_finite_cap (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j M : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (cluster G ωf x \ cluster G ω x).Finite ∧ (cluster G ωf x \ cluster G ω x).ncard ≤ k*M := by
  obtain ⟨hf,hc⟩ := trajectoryUnion_finite_cap G η y k M hcaps
  have hs := h.added_subset_trajectory G x η y k j ω ωf c
  exact ⟨hf.subset hs,(Set.ncard_le_ncard hs hf).trans hc⟩

end TrajectorySupport

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section JointReferenceEvent
attribute [local instance] Classical.propDecidable Classical.decEq

theorem SpliceTrace.joint_restored_field_symm (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 =
      (jointRestored G x η₂ η₁ y₁ ω₂ ω₁ c₁).1 := by
  apply exchange_patch_symm _ _ ω₁ ω₂ ωf
    (h₁.masks_disjoint G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep)
  · intro e he
    rw [← h₁.replay_eq G x η₁ y₁ k j₁ ω₁ ωf c₁]
    exact (replaySplice_off_masks G x η₁ y₁ c₁ ω₁ e he).symm
  · intro e he
    rw [← h₂.replay_eq G x η₂ y₂ k j₂ ω₂ ωf c₂]
    exact (replaySplice_off_masks G x η₂ y₂ c₂ ω₂ e he).symm

theorem SpliceTrace.joint_restored_root (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x =
      cluster G ω₁ x ∩ cluster G ω₂ x := by
  cases c₁ with
  | nil => exact (hc₁ rfl).elim
  | cons q r₁ =>
    obtain ⟨i₁,e₁⟩ := q
    cases c₂ with
    | nil => exact (hc₂ rfl).elim
    | cons q r₂ =>
      obtain ⟨i₂,e₂⟩ := q
      exact h₁.joint_root G x η₁ η₂ y₁ y₂ k j₁ j₂ i₁ i₂ ω₁ ω₂ ωf e₁ e₂ r₁ r₂ h₂ hsep

 

theorem SpliceTrace.joint_trajectory_hits (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x)) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    (A ∩ trajectoryUnion G η₁ y₁ k).Nonempty ∧ (A ∩ trajectoryUnion G η₂ y₂ k).Nonempty := by
  intro A
  have hv₁ := (h₁.joint_virtual G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep).1
  have hv₂ := (h₂.joint_virtual G x η₂ η₁ y₂ y₁ k j₂ j₁ ω₂ ω₁ ωf c₂ c₁ h₁ hc₂ hc₁
    (hsep.symm G _ _)).1
  refine ⟨hv₁.trajectory_hits G x η₁ y₁ k j₁ _ ω₂ c₁ hc₁,?_⟩
  change (cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x ∩ _).Nonempty
  rw [h₁.joint_restored_field_symm G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hsep]
  exact hv₂.trajectory_hits G x η₂ y₂ k j₂ _ ω₁ c₂ hc₂

 

theorem SpliceTrace.joint_restored_size (G : BondGraph V E) (x : V)
    (η₁ η₂ : ℕ → Set E) (y₁ y₂ : ℕ → V) (k j₁ j₂ n M : ℕ)
    (ω₁ ω₂ ωf : Set E) (c₁ c₂ : List (ℕ × E))
    (h₁ : SpliceTrace G x η₁ y₁ k j₁ ω₁ c₁ ωf)
    (h₂ : SpliceTrace G x η₂ y₂ k j₂ ω₂ c₂ ωf)
    (hc₁ : c₁ ≠ []) (hc₂ : c₂ ≠ [])
    (hsep : GraphSeparated G (cluster G ωf x \ cluster G ω₁ x)
      (cluster G ωf x \ cluster G ω₂ x))
    (hf : (cluster G ω₁ x).Finite) (hn : n ≤ (cluster G ω₁ x).ncard)
    (h2n : (cluster G ω₁ x).ncard < 2*n)
    (hcap₂ : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η₂ i) (y₂ i)).Finite ∧ (cluster G (η₂ i) (y₂ i)).ncard ≤ M) :
    let A := cluster G (jointRestored G x η₁ η₂ y₂ ω₁ ω₂ c₂).1 x
    A.Finite ∧ n-k*M ≤ A.ncard ∧ A.ncard < 2*n := by
  intro A
  have hA : A = cluster G ω₁ x ∩ cluster G ω₂ x :=
    h₁.joint_restored_root G x η₁ η₂ y₁ y₂ k j₁ j₂ ω₁ ω₂ ωf c₁ c₂ h₂ hc₁ hc₂ hsep
  have hdiff : A = cluster G ω₁ x \ (cluster G ωf x \ cluster G ω₂ x) := by
    rw [hA]
    ext v
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,fun hh => hh.2 h2⟩
    · rintro ⟨h1,h2⟩
      refine ⟨h1,?_⟩
      by_contra hn
      exact h2 ⟨h₁.cluster_subset G x η₁ y₁ k j₁ ω₁ ωf c₁ h1,hn⟩
  obtain ⟨hBfin,hBcap⟩ := h₂.added_finite_cap G x η₂ y₂ k j₂ M ω₂ ωf c₂ hcap₂
  have hlower := Set.ncard_le_ncard_sdiff_add_ncard (cluster G ω₁ x)
    (cluster G ωf x \ cluster G ω₂ x) hBfin
  rw [← hdiff] at hlower
  refine ⟨hA ▸ hf.inter_of_left _,by omega,?_⟩
  rw [hA]
  exact (Set.ncard_inter_le_ncard_left _ _ hf).trans_lt h2n

end JointReferenceEvent

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SmallHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
def hangingSide (G : BondGraph V E) (ω : Set E) (x : V) (e : E) : Set V :=
  cluster G ω x \ cluster G (ω \ {e}) x

theorem hangingSide_finite (G : BondGraph V E) (ω : Set E) (x : V) (e : E)
    (hC : (cluster G ω x).Finite) : (hangingSide G ω x e).Finite := hC.subset Set.sdiff_subset

theorem mem_hangingSide_iff_pivotal (G : BondGraph V E) (ω : Set E) (x z : V)
    (e : E) (he : e ∈ ω) : z ∈ hangingSide G ω x e ↔ OpenMarkedPivotal G ω {z} x e := by
  constructor
  · rintro ⟨hz,hn⟩
    exact ⟨he,⟨z,rfl,hz⟩,fun ⟨y,hy,hxy⟩ => hn ((Set.mem_singleton_iff.mp hy) ▸ hxy)⟩
  · rintro ⟨_,⟨y,hy,hxy⟩,hn⟩
    exact ⟨(Set.mem_singleton_iff.mp hy) ▸ hxy,fun hz => hn ⟨z,rfl,hz⟩⟩

theorem hangingSide_ncard_add_rank (G : BondGraph V E) (ω : Set E) (x : V)
    (e : E) (hC : (cluster G ω x).Finite) :
    (hangingSide G ω x e).ncard + pivotalRank G ω x e = (cluster G ω x).ncard := by
  have hs : cluster G (ω \ {e}) x ⊆ cluster G ω x := fun _ h => conn_mono G Set.sdiff_subset h
  rw [hangingSide,Set.ncard_sdiff hs (hC.subset hs)]
  exact Nat.sub_add_cancel (Set.ncard_le_ncard hs hC)

 

noncomputable def smallSeparatingBonds (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) : Finset E :=
  (separatingBonds G ω x z).filter fun e => (hangingSide G ω x e).ncard ≤ v

theorem smallSeparatingBonds_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : (smallSeparatingBonds G ω x z v).card ≤ v := by
  have hh := Finset.card_le_card_of_injOn (s := smallSeparatingBonds G ω x z v)
    (t := Finset.Icc 1 v) (fun e => (hangingSide G ω x e).ncard)
  have hmap : Set.MapsTo (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) (↑(Finset.Icc 1 v)) := by
    intro e he
    obtain ⟨he,hcap⟩ := Finset.mem_filter.mp he
    have hp := (mem_separatingBonds G ω x z e).mp he
    exact Finset.mem_Icc.mpr ⟨(Set.ncard_pos (hangingSide_finite G ω x e hC)).mpr
      ⟨z,(mem_hangingSide_iff_pivotal G ω x z e hp.1).mpr hp⟩,hcap⟩
  have hinj : Set.InjOn (fun e => (hangingSide G ω x e).ncard)
      (↑(smallSeparatingBonds G ω x z v)) := by
    intro e he f hf heq
    apply pivotalRank_injective_of_cluster_finite G ω {z} x hC
      ((mem_separatingBonds G ω x z e).mp (Finset.mem_filter.mp he).1)
      ((mem_separatingBonds G ω x z f).mp (Finset.mem_filter.mp hf).1)
    change (hangingSide G ω x e).ncard = (hangingSide G ω x f).ncard at heq
    have he' := hangingSide_ncard_add_rank G ω x e hC
    have hf' := hangingSide_ncard_add_rank G ω x f hC
    omega
  simpa only [Nat.card_Icc, Nat.add_sub_cancel] using hh hmap hinj

noncomputable def smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  (smallSeparatingBonds G ω x z v).biUnion fun e => (hangingSide_finite G ω x e hC).toFinset

theorem mem_smallHangingThrough (G : BondGraph V E) (ω : Set E) (x z w : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) : w ∈ smallHangingThrough G ω x z v hC ↔
      ∃ e, OpenMarkedPivotal G ω {z} x e ∧ (hangingSide G ω x e).ncard ≤ v ∧
        w ∈ hangingSide G ω x e := by
  simp [smallHangingThrough, smallSeparatingBonds, and_assoc]

theorem smallHangingThrough_card_le (G : BondGraph V E) (ω : Set E) (x z : V)
    (v : ℕ) (hC : (cluster G ω x).Finite) :
    (smallHangingThrough G ω x z v hC).card ≤ v*v := by
  calc
    _ ≤ ∑ e ∈ smallSeparatingBonds G ω x z v, (hangingSide_finite G ω x e hC).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e ∈ smallSeparatingBonds G ω x z v, v := by
      apply Finset.sum_le_sum
      intro e he
      rw [← Set.ncard_eq_toFinset_card (hangingSide G ω x e) (hangingSide_finite G ω x e hC)]
      exact (Finset.mem_filter.mp he).2
    _ = (smallSeparatingBonds G ω x z v).card*v := by simp
    _ ≤ v*v := Nat.mul_le_mul_right v (smallSeparatingBonds_card_le G ω x z v hC)

end SmallHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section NearHanging
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem hangingSide_laminar (G : BondGraph V E) (ω : Set E) (x : V)
    (e f : E) (he : e ∈ ω) (hf : f ∈ ω) :
    Disjoint (hangingSide G ω x e) (hangingSide G ω x f) ∨
      hangingSide G ω x e ⊆ hangingSide G ω x f ∨
      hangingSide G ω x f ⊆ hangingSide G ω x e := by
  by_cases hd : Disjoint (hangingSide G ω x e) (hangingSide G ω x f)
  · exact Or.inl hd
  obtain ⟨z,hze,hzf⟩ := Set.not_disjoint_iff.mp hd
  by_cases hef : e = f
  · exact Or.inr (Or.inl (hef ▸ Set.Subset.refl _))
  rcases pivotal_rootSides_nested G ω {z} x
    ((mem_hangingSide_iff_pivotal G ω x z e he).mp hze)
    ((mem_hangingSide_iff_pivotal G ω x z f hf).mp hzf) hef with h | h
  · exact Or.inr (Or.inr (Set.sdiff_subset_sdiff_right h.1))
  · exact Or.inr (Or.inl (Set.sdiff_subset_sdiff_right h.1))

noncomputable def graphNeighbors (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) : Finset V := A.biUnion (neighbors G hloc)

theorem graphNeighbors_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (A : Finset V) (d : ℕ) (hdeg : ∀ a, degree G a ≤ d) :
    (graphNeighbors G hloc A).card ≤ A.card*d := by
  calc
    _ ≤ ∑ a ∈ A, (neighbors G hloc a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ A, d := Finset.sum_le_sum fun a _ =>
      (neighbors_card_le_degree G hloc a).trans (hdeg a)
    _ = _ := by simp

 

noncomputable def nearHangingEndpoints (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v : ℕ) (hC : (cluster G ω x).Finite) : Finset V :=
  ((hangingSide_finite G ω x e hC).toFinset ∪ smallHangingThrough G ω x z v hC) ∪
    (graphNeighbors G hloc (hangingSide_finite G ω x e hC).toFinset).biUnion
      (fun a => smallHangingThrough G ω x a v hC)

theorem nearHangingEndpoints_card_le (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x z : V) (e : E) (v d : ℕ) (hC : (cluster G ω x).Finite)
    (hcap : (hangingSide G ω x e).ncard ≤ v) (hdeg : ∀ a, degree G a ≤ d) :
    (nearHangingEndpoints G hloc ω x z e v hC).card ≤ v+v^2+d*v^3 := by
  let B := (hangingSide_finite G ω x e hC).toFinset
  let N := graphNeighbors G hloc B
  have hB : B.card ≤ v := by
    simpa only [B,← Set.ncard_eq_toFinset_card (hangingSide G ω x e)
      (hangingSide_finite G ω x e hC)] using hcap
  have hN : N.card ≤ v*d := (graphNeighbors_card_le G hloc B d hdeg).trans
    (Nat.mul_le_mul_right d hB)
  have hU : (N.biUnion fun a => smallHangingThrough G ω x a v hC).card ≤ d*v^3 := by
    calc
      _ ≤ ∑ a ∈ N, (smallHangingThrough G ω x a v hC).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ N, v*v := Finset.sum_le_sum fun a _ => smallHangingThrough_card_le G ω x a v hC
      _ = N.card*(v*v) := by simp
      _ ≤ (v*d)*(v*v) := Nat.mul_le_mul_right (v*v) hN
      _ = d*v^3 := by ring
  calc
    _ ≤ (B ∪ smallHangingThrough G ω x z v hC).card +
        (N.biUnion fun a => smallHangingThrough G ω x a v hC).card := Finset.card_union_le ..
    _ ≤ (B.card + (smallHangingThrough G ω x z v hC).card) + d*v^3 :=
      Nat.add_le_add (Finset.card_union_le ..) hU
    _ ≤ (v+v*v)+d*v^3 := Nat.add_le_add_right
      (Nat.add_le_add hB (smallHangingThrough_card_le G ω x z v hC)) _
    _ = v+v^2+d*v^3 := by ring

theorem mem_nearHangingEndpoints_of_not_separated (G : BondGraph V E)
    (hloc : LocallyFinite G) (ω : Set E) (x z w : V) (e f : E) (v : ℕ)
    (hC : (cluster G ω x).Finite)
    (he : OpenMarkedPivotal G ω {z} x e) (hf : OpenMarkedPivotal G ω {w} x f)
    (hcap : (hangingSide G ω x f).ncard ≤ v)
    (hn : ¬GraphSeparated G (hangingSide G ω x e) (hangingSide G ω x f)) :
    w ∈ nearHangingEndpoints G hloc ω x z e v hC := by
  have hz := (mem_hangingSide_iff_pivotal G ω x z e he.1).mpr he
  have hw := (mem_hangingSide_iff_pivotal G ω x w f hf.1).mpr hf
  rcases hangingSide_laminar G ω x e f he.1 hf.1 with hd | hsub | hsub
  · have hadj : ∃ a ∈ hangingSide G ω x e, ∃ b ∈ hangingSide G ω x f, Adj G a b := by
      by_contra h
      apply hn
      refine ⟨hd,?_⟩
      intro a ha b hb hab
      exact h ⟨a,ha,b,hb,hab⟩
    obtain ⟨a,ha,b,hb,hab⟩ := hadj
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_biUnion.mpr ⟨a,?_,(mem_neighbors G hloc a b).mpr hab⟩,?_⟩
    · exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr ha
    · exact (mem_smallHangingThrough G ω x b w v hC).mpr
        ⟨f,(mem_hangingSide_iff_pivotal G ω x b f hf.1).mp hb,hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact (mem_smallHangingThrough G ω x z w v hC).mpr
      ⟨f,(mem_hangingSide_iff_pivotal G ω x z f hf.1).mp (hsub hz),hcap,hw⟩
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    exact (hangingSide_finite G ω x e hC).mem_toFinset.mpr (hsub hw)

end NearHanging

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 
abbrev FiniteField (Q : Finset E) := ↥Q.powerset

def finiteFieldSet (Q : Finset E) (ω : FiniteField Q) : Set E := (ω.val : Set E)

noncomputable def finiteFieldWeight (Q : Finset E) (p : ℝ) (ω : FiniteField Q) : ℝ :=
  bernoulliWeight Q ω.val p

@[simp] theorem domainBits_finiteFieldSet (Q : Finset E) (ω : FiniteField Q) :
    domainBits Q (finiteFieldSet Q ω) = ω.val := by
  ext e
  have hs := Finset.mem_powerset.mp ω.property
  simp only [mem_domainBits,finiteFieldSet,Finset.mem_coe]
  exact ⟨fun h => h.2,fun h => ⟨hs h,h⟩⟩

theorem finiteFieldWeight_nonneg (Q : Finset E) (p : unitInterval) (ω : FiniteField Q) :
    0 ≤ finiteFieldWeight Q p ω := bernoulliWeight_nonneg _ _ p

theorem sum_finiteFieldWeight (Q : Finset E) (p : ℝ) :
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω = 1 := by
  rw [show (fun ω : FiniteField Q => finiteFieldWeight Q p ω) =
    (fun ω : FiniteField Q => bernoulliWeight Q ω.val p) from rfl,Finset.sum_coe_sort Q.powerset (fun ω => bernoulliWeight Q ω p)]
  simpa only [bernoulliPolynomial,bernoulliWeight,mul_one,one_mul] using bernoulliPolynomial_const Q 1 p

 

def finiteFieldFamily (Q : Finset E) (J : Finset ℕ) (η : ↥J → FiniteField Q) : ℕ → Set E :=
  fun i => if hi : i ∈ J then finiteFieldSet Q (η ⟨i,hi⟩) else ∅

@[simp] theorem finiteFieldFamily_at (Q : Finset E) (J : Finset ℕ)
    (η : ↥J → FiniteField Q) (i : ↥J) :
    finiteFieldFamily Q J η i = finiteFieldSet Q (η i) := by
  simp [finiteFieldFamily,i.property]

noncomputable def finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) : ℝ := ∏ i, finiteFieldWeight Q p (η i)

theorem finiteFamilyWeight_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (η : ↥J → FiniteField Q) : 0 ≤ finiteFamilyWeight Q J p η :=
  Finset.prod_nonneg fun _ _ => finiteFieldWeight_nonneg Q p _

theorem sum_finiteFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ) :
    ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η = 1 := by
  unfold finiteFamilyWeight
  rw [← Fintype.prod_sum]
  simp only [sum_finiteFieldWeight,Finset.prod_const_one]

theorem prod_fieldFamilyWeight (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (η : ↥J → FiniteField Q) :
    (∏ i ∈ J, bernoulliWeight Q (domainBits Q (finiteFieldFamily Q J η i)) p) =
      finiteFamilyWeight Q J p η := by
  rw [← Finset.prod_coe_sort J]
  simp only [finiteFieldFamily_at,domainBits_finiteFieldSet,finiteFamilyWeight,finiteFieldWeight]

abbrev FiniteJointData (Q : Finset E) (J₁ J₂ : Finset ℕ) :=
  FiniteField Q × (↥J₁ → FiniteField Q) × (↥J₂ → FiniteField Q)

def encodeFiniteJoint (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : FiniteJointData Q J₁ J₂) : JointSpliceState E :=
  (finiteFieldSet Q s.1,finiteFieldFamily Q J₁ s.2.1,finiteFieldFamily Q J₂ s.2.2)

theorem finiteFieldSet_injective (Q : Finset E) : Function.Injective (finiteFieldSet Q) := by
  intro a b he
  exact Subtype.ext (Finset.coe_injective he)

theorem finiteFieldFamily_injective (Q : Finset E) (J : Finset ℕ) :
    Function.Injective (finiteFieldFamily Q J) := by
  intro a b he
  funext i
  apply finiteFieldSet_injective Q
  simpa only [finiteFieldFamily_at] using congrFun he i

theorem encodeFiniteJoint_injective (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Function.Injective (encodeFiniteJoint Q J₁ J₂) := by
  intro a b he
  apply Prod.ext (finiteFieldSet_injective Q (congrArg Prod.fst he))
  exact Prod.ext (finiteFieldFamily_injective Q J₁ (congrArg (fun s => s.2.1) he))
    (finiteFieldFamily_injective Q J₂ (congrArg (fun s => s.2.2) he))

theorem jointTupleWeight_encode (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (s : FiniteJointData Q J₁ J₂) :
    jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) =
      finiteFieldWeight Q p s.1 * finiteFamilyWeight Q J₁ p s.2.1 *
        finiteFamilyWeight Q J₂ p s.2.2 := by
  simp only [jointTupleWeight,encodeFiniteJoint,domainBits_finiteFieldSet,
    prod_fieldFamilyWeight,finiteFieldWeight]

 

theorem sum_jointTupleWeight_encode (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ) :
    ∑ s : FiniteJointData Q J₁ J₂, jointTupleWeight Q J₁ J₂ p (encodeFiniteJoint Q J₁ J₂ s) = 1 := by
  simp_rw [jointTupleWeight_encode]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type,← Finset.mul_sum,sum_finiteFamilyWeight,mul_one,
    ← Finset.mul_sum,sum_finiteFamilyWeight,mul_one]
  exact sum_finiteFieldWeight Q p

end FiniteReferenceLaw

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteReferenceFactor
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def finiteFamilyEvent (Q : Finset E) (J : Finset ℕ) (p : ℝ)
    (H : (ℕ → Set E) → Prop) : ℝ :=
  ∑ η : ↥J → FiniteField Q, finiteFamilyWeight Q J p η *
    if H (finiteFieldFamily Q J η) then 1 else 0

theorem finiteFamilyEvent_nonneg (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (H : (ℕ → Set E) → Prop) : 0 ≤ finiteFamilyEvent Q J p H := by
  apply Finset.sum_nonneg
  intro η _
  exact mul_nonneg (finiteFamilyWeight_nonneg Q J p η) (by split <;> norm_num)

theorem finiteFamilyEvent_le_one (Q : Finset E) (J : Finset ℕ) (p : unitInterval)
    (H : (ℕ → Set E) → Prop) : finiteFamilyEvent Q J p H ≤ 1 := by
  rw [← sum_finiteFamilyWeight Q J p]
  apply Finset.sum_le_sum
  intro η _
  exact mul_le_of_le_one_right (finiteFamilyWeight_nonneg Q J p η) (by split <;> norm_num)

noncomputable def finiteJointDomain (Q : Finset E) (J₁ J₂ : Finset ℕ) :
    Finset (JointSpliceState E) := Finset.univ.image (encodeFiniteJoint Q J₁ J₂)

theorem finiteJointDomain_event_factor (Q : Finset E) (J₁ J₂ : Finset ℕ) (p : ℝ)
    (P : Set E → Prop) (H₁ H₂ : Set E → (ℕ → Set E) → Prop) :
    (∑ s ∈ (finiteJointDomain Q J₁ J₂).filter (fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2),
      jointTupleWeight Q J₁ J₂ p s) =
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if P (finiteFieldSet Q ω) then
        finiteFamilyEvent Q J₁ p (H₁ (finiteFieldSet Q ω)) *
        finiteFamilyEvent Q J₂ p (H₂ (finiteFieldSet Q ω)) else 0) := by
  rw [Finset.sum_filter,finiteJointDomain,Finset.sum_image (encodeFiniteJoint_injective Q J₁ J₂).injOn,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro ω _
  rw [Fintype.sum_prod_type]
  by_cases hP : P (finiteFieldSet Q ω)
  · simp only [encodeFiniteJoint, hP, true_and,ite_true]
    have heq (η₁ : ↥J₁ → FiniteField Q) (η₂ : ↥J₂ → FiniteField Q) :
      (if H₁ (finiteFieldSet Q ω) (finiteFieldFamily Q J₁ η₁) ∧
        H₂ (finiteFieldSet Q ω) (finiteFieldFamily Q J₂ η₂) then
        jointTupleWeight Q J₁ J₂ p
          (finiteFieldSet Q ω,finiteFieldFamily Q J₁ η₁,finiteFieldFamily Q J₂ η₂) else 0) =
      finiteFieldWeight Q p ω *
        (finiteFamilyWeight Q J₁ p η₁ * if H₁ (finiteFieldSet Q ω) (finiteFieldFamily Q J₁ η₁) then 1 else 0) *
        (finiteFamilyWeight Q J₂ p η₂ * if H₂ (finiteFieldSet Q ω) (finiteFieldFamily Q J₂ η₂) then 1 else 0) := by
      have hw := jointTupleWeight_encode Q J₁ J₂ p (ω,η₁,η₂)
      change jointTupleWeight Q J₁ J₂ p (finiteFieldSet Q ω,finiteFieldFamily Q J₁ η₁,finiteFieldFamily Q J₂ η₂) = _ at hw
      rw [hw]
      split_ifs <;> simp_all
    simp_rw [heq,← Finset.mul_sum,← Finset.sum_mul]
    rw [← Finset.mul_sum,mul_assoc]
    rfl
  · simp [encodeFiniteJoint,hP]

 

theorem mem_finiteJointDomain_of_support (Q : Finset E) (J₁ J₂ : Finset ℕ)
    (s : JointSpliceState E) (hω : s.1 ⊆ (Q : Set E))
    (hη₁ : ∀ i, s.2.1 i ⊆ (Q : Set E)) (hη₂ : ∀ i, s.2.2 i ⊆ (Q : Set E))
    (hz₁ : ∀ i ∉ J₁, s.2.1 i = ∅) (hz₂ : ∀ i ∉ J₂, s.2.2 i = ∅) :
    s ∈ finiteJointDomain Q J₁ J₂ := by
  let desc (ω : Set E) : FiniteField Q := ⟨domainBits Q ω,Finset.mem_powerset.mpr (domainBits_subset Q ω)⟩
  have hdesc (ω : Set E) (h : ω ⊆ (Q : Set E)) : finiteFieldSet Q (desc ω) = ω := by
    ext e
    simp only [finiteFieldSet,desc,Finset.mem_coe,mem_domainBits]
    exact ⟨fun hh => hh.2,fun hh => ⟨h hh,hh⟩⟩
  let a : FiniteJointData Q J₁ J₂ := (desc s.1,fun i => desc (s.2.1 i),fun i => desc (s.2.2 i))
  apply Finset.mem_image.mpr
  refine ⟨a,Finset.mem_univ _,?_⟩
  apply Prod.ext (hdesc s.1 hω)
  apply Prod.ext
  · funext i
    change (if hi : i ∈ J₁ then finiteFieldSet Q (desc (s.2.1 i)) else ∅) = s.2.1 i
    by_cases hi : i ∈ J₁
    · simp only [hi,dite_true,hdesc _ (hη₁ i)]
    · simp only [hi,dite_false,hz₁ i hi]
  · funext i
    change (if hi : i ∈ J₂ then finiteFieldSet Q (desc (s.2.2 i)) else ∅) = s.2.2 i
    by_cases hi : i ∈ J₂
    · simp only [hi,dite_true,hdesc _ (hη₂ i)]
    · simp only [hi,dite_false,hz₂ i hi]

theorem exchangeOn_subset (M ω η Q : Set E) (hω : ω ⊆ Q) (hη : η ⊆ Q) :
    exchangeOn M ω η ⊆ Q := by
  rintro e (⟨he,_⟩ | ⟨he,_⟩)
  · exact hω he
  · exact hη he

end FiniteReferenceFactor

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section FiniteSeparatedSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem finite_separated_second_moment_le {I : Type*} [Fintype I]
    (G : BondGraph V E) (x : V) (k n M : ℕ) (p : unitInterval) (Q : Finset E)
    (η₁ η₂ : I → ℕ → Set E) (y₁ y₂ : (ℕ → Set E) → ℕ → V)
    (success₁ success₂ : (ℕ → Set E) → Prop)
    (choose₁ choose₂ : ℕ → Set E → E)
    (ω₁ ω₂ ωf : I → Set E) (c₁ c₂ : I → List (ℕ × E))
    (hir : Function.Injective (fun a =>
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a),
        c₁ a,c₂ a)))
    (h₁ : ∀ a, SpliceTrace G x (η₁ a) (y₁ (η₁ a)) k 0 (ω₁ a) (c₁ a) (ωf a))
    (h₂ : ∀ a, SpliceTrace G x (η₂ a) (y₂ (η₂ a)) k 0 (ω₂ a) (c₂ a) (ωf a))
    (hc₁ : ∀ a, c₁ a ≠ []) (hc₂ : ∀ a, c₂ a ≠ [])
    (hsep : ∀ a, GraphSeparated G (cluster G (ωf a) x \ cluster G (ω₁ a) x)
      (cluster G (ωf a) x \ cluster G (ω₂ a) x))
    (hr₁ : ∀ a, FollowsContactRule G x (η₁ a) (y₁ (η₁ a)) choose₁ (c₁ a) (ω₁ a))
    (hr₂ : ∀ a, FollowsContactRule G x (η₂ a) (y₂ (η₂ a)) choose₂ (c₂ a) (ω₂ a))
    (hbin : ∀ a, (cluster G (ω₁ a) x).Finite ∧ n ≤ (cluster G (ω₁ a) x).ncard ∧
      (cluster G (ω₁ a) x).ncard < 2*n)
    (hcap₂ : ∀ a i, 1 ≤ i → i ≤ k → (cluster G (η₂ a i) (y₂ (η₂ a) i)).Finite ∧
      (cluster G (η₂ a i) (y₂ (η₂ a) i)).ncard ≤ M)
    (hsc₁ : ∀ a, success₁ (η₁ a)) (hsc₂ : ∀ a, success₂ (η₂ a))
    (hsω₁ : ∀ a, ω₁ a ⊆ (Q : Set E)) (hsω₂ : ∀ a, ω₂ a ⊆ (Q : Set E))
    (hsη₁ : ∀ a i, η₁ a i ⊆ (Q : Set E)) (hsη₂ : ∀ a i, η₂ a i ⊆ (Q : Set E))
    (hz₁ : ∀ a i, i ∉ Finset.Icc 1 k → η₁ a i = ∅)
    (hz₂ : ∀ a i, i ∉ Finset.Icc 1 k → η₂ a i = ∅) :
    (∑ a, jointTupleWeight Q (Finset.Icc 1 k) (Finset.Icc 1 k) p
      (jointOutput G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a))) ≤
    ∑ ω : FiniteField Q, finiteFieldWeight Q p ω *
      (if (cluster G (finiteFieldSet Q ω) x).Finite ∧
        n-k*M ≤ (cluster G (finiteFieldSet Q ω) x).ncard ∧
        (cluster G (finiteFieldSet Q ω) x).ncard < 2*n then
        finiteFamilyEvent Q (Finset.Icc 1 k) p (fun η => success₁ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₁ η) k).Nonempty) *
        finiteFamilyEvent Q (Finset.Icc 1 k) p (fun η => success₂ η ∧
          (cluster G (finiteFieldSet Q ω) x ∩ trajectoryUnion G η (y₂ η) k).Nonempty) else 0) := by
  let J := Finset.Icc 1 k
  let P (ω : Set E) := (cluster G ω x).Finite ∧ n-k*M ≤ (cluster G ω x).ncard ∧
    (cluster G ω x).ncard < 2*n
  let H₁ (ω : Set E) (η : ℕ → Set E) := success₁ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₁ η) k).Nonempty
  let H₂ (ω : Set E) (η : ℕ → Set E) := success₂ η ∧
    (cluster G ω x ∩ trajectoryUnion G η (y₂ η) k).Nonempty
  let B := (finiteJointDomain Q J J).filter fun s => P s.1 ∧ H₁ s.1 s.2.1 ∧ H₂ s.1 s.2.2
  have hB (a : I) : jointRestored G x (η₁ a) (η₂ a) (y₂ (η₂ a)) (ω₁ a) (ω₂ a) (c₂ a) ∈ B := by
    apply Finset.mem_filter.mpr
    refine ⟨mem_finiteJointDomain_of_support Q J J _
      (exchangeOn_subset _ _ _ _ (hsω₁ a) (hsω₂ a)) (hsη₁ a) (hsη₂ a) (hz₁ a) (hz₂ a),?_⟩
    have hroot := (h₁ a).joint_restored_size G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 n M (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
      (hbin a).1 (hbin a).2.1 (hbin a).2.2 (hcap₂ a)
    have hhits := (h₁ a).joint_trajectory_hits G x (η₁ a) (η₂ a) (y₁ (η₁ a)) (y₂ (η₂ a))
      k 0 0 (ω₁ a) (ω₂ a) (ωf a) (c₁ a) (c₂ a) (h₂ a) (hc₁ a) (hc₂ a) (hsep a)
    exact ⟨hroot,⟨hsc₁ a,hhits.1⟩,hsc₂ a,hhits.2⟩
  have h := finite_joint_mass_le G x k p Q η₁ η₂ y₁ y₂ choose₁ choose₂ ω₁ ω₂ ωf c₁ c₂
    hir h₁ h₂ hc₁ hc₂ hsep hr₁ hr₂ B hB
  apply h.trans_eq
  convert finiteJointDomain_event_factor Q J J p P H₁ H₂ using 1 <;> simp [B,J,P,H₁,H₂]

end FiniteSeparatedSecondMoment

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SeededForward
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_seeded_spliceTrace (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k M : ℕ)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (choose : ℕ → Set E → E)
    (hchoose : ∀ i K, K.Finite → K.Nonempty → choose i K ∈ K)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (N : ℕ) (hfin : (cluster G ω x).Finite) (hN : (cluster G ω x).ncard ≤ N) :
    ∃ steps ωf, SpliceTrace G x η y k j ω steps ωf ∧
      FollowsContactRule G x η y choose steps ω ∧ steps.length ≤ k-j ∧
      y k ∈ cluster G ωf x ∧ (cluster G ωf x).Finite ∧
      (cluster G ωf x).ncard ≤ N+(k-j)*M := by
  generalize hn : k-j = n
  induction n using Nat.strong_induction_on generalizing j ω N with
  | h n ih =>
    by_cases hz : y k ∈ cluster G ω x
    · refine ⟨[],ω,SpliceTrace.stop j ω hz,?_,by simp,hz,hfin,?_⟩
      · exact List.Forall₂.nil
      · exact hN.trans (Nat.le_add_right ..)
    · obtain ⟨i,hiI,hmeet,hyi,hmax⟩ :=
        exists_maximal_splice_index G η y k j hj hchain (cluster G ω x) hyj hz
      obtain ⟨hji,hik⟩ := Finset.mem_Icc.mp hiI
      have hi1 : i ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨by omega,hik⟩
      let B := cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)
      let K := contactSet G (η i) B
      have hBC : B ⊆ cluster G (η i) (y i) := fun _ h => conn_mono G Set.inter_subset_left h
      have hBK : K.Finite := contactSet_finite G hloc (η i) B ((hcaps i hi1).1.subset hBC)
      have hK : K.Nonempty := by
        obtain ⟨e,a,b,he,hab,ha,hb⟩ := exists_splice_contact G (η i) (cluster G ω x) (y i) hyi hmeet
        exact ⟨e,he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun h => slit_cluster_subset G (cluster G ω x) (η i) (y i) hyi h ha⟩
      let e := choose i K
      have heK : e ∈ contactSet G (η i) B := hchoose i K hBK hK
      change e ∈ contactSet G (η i)
        (cluster G (η i ∩ internalEdges G (cluster G ω x)ᶜ) (y i)) at heK
      rw [contactSet_deleted_cluster G (η i) (cluster G ω x) (y i) hyi] at heK
      obtain ⟨he,b,hb,a,ha,hba⟩ := heK
      have hab : G e = s(a,b) := hba.trans (Sym2.eq_swap ..)
      let ω' := spliceField G (cluster G ω x) B e ω (η i)
      have hcap := splice_cluster_cap G ω (η i) x (y i) hyi e a b hab he ha hb N M hfin hN
        (hcaps i hi1).1 (hcaps i hi1).2
      have hyt : y i ∈ cluster G ω' x := by
        change y i ∈ cluster G (spliceField G (cluster G ω x) B e ω (η i)) x
        rw [splice_cluster G ω (η i) x (y i) hyi e a b hab he ha hb]
        exact Or.inr (mem_cluster_self G _ _)
      obtain ⟨steps,ωf,htrace,hrule,hlen,hconn,hf,hs⟩ :=
        ih (k-i) (by omega) i hik ω' hyt (N+M) hcap.1 hcap.2 rfl
      refine ⟨(i,e)::steps,ωf,
        SpliceTrace.step j i ω e a b steps ωf hz (by omega) hik hmax hyi he hab ha hb htrace,
        ?_,?_,hconn,hf,?_⟩
      · exact (followsContactRule_cons G x η y choose i e steps ω).mpr ⟨rfl,hrule⟩
      · simp only [List.length_cons]
        omega
      · have hm : (k-i+1)*M ≤ (k-j)*M := Nat.mul_le_mul_right M (by omega)
        rw [Nat.add_mul,one_mul] at hm
        calc
          _ ≤ (N+M)+(k-i)*M := hs
          _ ≤ N+(k-j)*M := by omega
          _ = N+n*M := by rw [hn]

 

theorem existsUnique_seeded_spliceTrace (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k M : ℕ)
    (hchain : ∀ i ∈ Finset.Icc 1 k, Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i ∈ Finset.Icc 1 k, (cluster G (η i) (y i)).Finite ∧
      (cluster G (η i) (y i)).ncard ≤ M)
    (choose : ℕ → Set E → E)
    (hchoose : ∀ i K, K.Finite → K.Nonempty → choose i K ∈ K)
    (j : ℕ) (hj : j ≤ k) (ω : Set E) (hyj : y j ∈ cluster G ω x)
    (hfin : (cluster G ω x).Finite) :
    ∃! out : List (ℕ × E) × Set E,
      SpliceTrace G x η y k j ω out.1 out.2 ∧
      FollowsContactRule G x η y choose out.1 ω := by
  obtain ⟨c,ωf,ht,hr,_⟩ := exists_seeded_spliceTrace G hloc x η y k M hchain hcaps
    choose hchoose j hj ω hyj _ hfin (le_refl _)
  refine ⟨(c,ωf),⟨ht,hr⟩,?_⟩
  rintro ⟨d,σf⟩ ⟨hs,hd⟩
  obtain ⟨hc,hf⟩ := hs.seeded_unique G x η y k j ω σf ωf d c ht choose hd hr
  exact Prod.ext hc hf

end SeededForward
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SpliceLocalSupport
attribute [local instance] Classical.propDecidable Classical.decEq

 
theorem reachBall_triangle (G : BondGraph V E) (x y : V) (n m : ℕ)
    (hy : y ∈ reachBall G x n) : reachBall G y m ⊆ reachBall G x (n+m) := by
  induction m with
  | zero => simpa only [reachBall,Nat.add_zero,Set.singleton_subset_iff] using hy
  | succ m ih =>
    intro z hz
    rcases hz with hz | hz
    · exact Or.inl (ih hz)
    · apply Or.inr
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq] at hz ⊢
      obtain ⟨a,ha,haz⟩ := hz
      exact ⟨a,ih ha,haz⟩

 
theorem capped_cluster_ball_of_mem (G : BondGraph V E) (ω : Set E) (x y : V)
    (hfin : (cluster G ω x).Finite) (M : ℕ) (hM : (cluster G ω x).ncard ≤ M)
    (hy : y ∈ cluster G ω x) : cluster G ω x ⊆ reachBall G y M := by
  have he := cluster_eq_of_conn G ω hy
  rw [he] at hfin hM ⊢
  exact finite_cluster_subset_reachBall G ω y hfin M hM

 

theorem oldChain_local_support (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k M N : ℕ)
    (hstart : y 0 ∈ reachBall G x N)
    (hchain : ∀ i, 1 ≤ i → i ≤ k → Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    (∀ i, i ≤ k → y i ∈ reachBall G x (N+i*M)) ∧
      trajectoryUnion G η y k ⊆ reachBall G x (N+k*M) := by
  have hvertex : ∀ i, i ≤ k → y i ∈ reachBall G x (N+i*M) := by
    intro i
    induction i with
    | zero => simpa using hstart
    | succ i ih =>
      intro hik
      obtain ⟨hf,hM⟩ := hcaps (i+1) (by omega) hik
      have hc := capped_cluster_ball_of_mem G (η (i+1)) (y (i+1)) (y i) hf M hM
        (by simpa only [Nat.add_sub_cancel,cluster,Set.mem_ofPred_eq] using hchain (i+1) (by omega) hik)
      have hh := reachBall_triangle G x (y i) (N+i*M) M (ih (by omega))
        (hc (mem_cluster_self G _ _))
      convert hh using 1
      congr 1
      ring
  refine ⟨hvertex,?_⟩
  intro v hv
  obtain ⟨i,hi,hik,hv⟩ := (mem_trajectoryUnion G η y k v).mp hv
  obtain ⟨hf,hM⟩ := hcaps i hi hik
  have hc := capped_cluster_ball_of_mem G (η i) (y i) (y (i-1)) hf M hM (hchain i hi hik)
  have hh := reachBall_triangle G x (y (i-1)) (N+(i-1)*M) M
    (hvertex (i-1) (by omega)) (hc hv)
  apply reachBall_mono_local G x _ hh
  have hmul : i*M ≤ k*M := Nat.mul_le_mul_right M hik
  have he : (i-1)*M+M = i*M := by
    calc _ = (i-1+1)*M := by ring
         _ = i*M := by rw [Nat.sub_add_cancel hi]
  omega

 

theorem SpliceTrace.masks_in_deterministic_ball (G : BondGraph V E)
    (hloc : LocallyFinite G) (x : V) (η : ℕ → Set E) (y : ℕ → V)
    (k j M N : ℕ) (ω ωf : Set E) (c : List (ℕ × E))
    (h : SpliceTrace G x η y k j ω c ωf)
    (hstart : y 0 ∈ reachBall G x N)
    (hchain : ∀ i, 1 ≤ i → i ≤ k → Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M) :
    maskUnion (replayMasks G x η y c ω) ⊆
      (incidentSupport G hloc (finite_reachBall hloc x (N+k*M)).toFinset : Set E) := by
  intro e he
  obtain ⟨b,hb,hbe⟩ := h.masks_incident G x η y k j ω ωf c e he
  have hbt := h.added_subset_trajectory G x η y k j ω ωf c hb
  have hball := (oldChain_local_support G x η y k M N hstart hchain hcaps).2 hbt
  exact (mem_incidentSupport G hloc _ e).mpr ⟨b,by simpa using hball,hbe⟩

 

theorem oldChain_query_support (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k M N R : ℕ)
    (hstart : y 0 ∈ reachBall G x N)
    (hchain : ∀ i, 1 ≤ i → i ≤ k → Conn G (η i) (y i) (y (i-1)))
    (hcaps : ∀ i, 1 ≤ i → i ≤ k →
      (cluster G (η i) (y i)).Finite ∧ (cluster G (η i) (y i)).ncard ≤ M)
    (i : ℕ) (hi : i ≤ k) :
    reachBall G (y i) R ⊆ reachBall G x (N+k*M+R) := by
  have hv := (oldChain_local_support G x η y k M N hstart hchain hcaps).1 i hi
  intro z hz
  have hh := reachBall_triangle G x (y i) (N+i*M) R hv hz
  exact reachBall_mono_local G x (by nlinarith) hh

end SpliceLocalSupport
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section UniformContactSelector
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def uniformRank (K : ℕ) (hK : 0 < K) (t : unitInterval) : Fin K :=
  ⟨min ⌊(K:ℝ)*(t:ℝ)⌋₊ (K-1), lt_of_le_of_lt (min_le_right ..) (by omega)⟩

theorem uniformRank_val_of_lt_one (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) : (uniformRank K hK t).val = ⌊(K:ℝ)*(t:ℝ)⌋₊ := by
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  have hf : ⌊(K:ℝ)*(t:ℝ)⌋₊ < K := (Nat.floor_lt (mul_nonneg (Nat.cast_nonneg _) t.property.1)).mpr (by nlinarith)
  exact min_eq_left (by omega)

theorem uniformRank_eq_iff (K : ℕ) (hK : 0 < K) (t : unitInterval)
    (ht : (t:ℝ) < 1) (a : Fin K) :
    uniformRank K hK t = a ↔ t ∈ contactInterval K a.val := by
  rw [Fin.ext_iff,uniformRank_val_of_lt_one K hK t ht,
    Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) t.property.1)]
  have hp : (0:ℝ) < K := by exact_mod_cast hK
  simp only [contactInterval,Set.mem_ofPred_eq,Nat.cast_add,Nat.cast_one]
  rw [div_le_iff₀ hp,lt_div_iff₀ hp]
  simp only [mul_comm]

theorem volume_uniformRank_fiber (K : ℕ) (hK : 0 < K) (a : Fin K) :
    volume {t : unitInterval | uniformRank K hK t = a} =
      ENNReal.ofReal ((K:ℝ)⁻¹) := by
  rw [← volume_contactInterval K a.val a.isLt]
  apply measure_congr
  filter_upwards [(volume : Measure unitInterval).ae_ne 1] with t ht
  exact propext (uniformRank_eq_iff K hK t (lt_of_le_of_ne t.property.2
    (fun he => ht (Subtype.ext he))) a)

 

noncomputable def uniformContact (K : Finset E) (hK : K.Nonempty)
    (t : unitInterval) : E :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val

theorem uniformContact_mem (K : Finset E) (hK : K.Nonempty) (t : unitInterval) :
    uniformContact K hK t ∈ K :=
  ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).property

theorem uniformContact_eq_iff (K : Finset E) (hK : K.Nonempty) (t : unitInterval)
    (e : E) (he : e ∈ K) :
    uniformContact K hK t = e ↔
      uniformRank K.card (Finset.card_pos.mpr hK) t = K.equivFin ⟨e,he⟩ := by
  unfold uniformContact
  change ((K.equivFin).symm (uniformRank K.card (Finset.card_pos.mpr hK) t)).val =
    (⟨e,he⟩ : ↥K).val ↔ _
  rw [← Subtype.ext_iff]
  exact K.equivFin.symm_apply_eq

theorem volume_uniformContact_fiber (K : Finset E) (hK : K.Nonempty)
    (e : E) (he : e ∈ K) : volume {t : unitInterval | uniformContact K hK t = e} =
      ENNReal.ofReal ((K.card:ℝ)⁻¹) := by
  simp_rw [uniformContact_eq_iff K hK _ e he]
  exact volume_uniformRank_fiber K.card (Finset.card_pos.mpr hK) _

 

noncomputable def chooseContact [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) : E :=
  if hf : K.Finite then if hn : K.Nonempty then
    uniformContact hf.toFinset (by simpa using hn) (seed i)
  else Classical.arbitrary E else Classical.arbitrary E

theorem chooseContact_mem [Nonempty E] (seed : ℕ → unitInterval)
    (i : ℕ) (K : Set E) (hf : K.Finite) (hn : K.Nonempty) :
    chooseContact seed i K ∈ K := by
  simp only [chooseContact,dite_eq_left hf,dite_eq_left hn]
  exact hf.mem_toFinset.mp (uniformContact_mem _ _ _)

end UniformContactSelector
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section SeededTraceLaw
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Nonempty E]

 
theorem chooseContact_congr (u v : ℕ → unitInterval) (i : ℕ) (K : Set E)
    (h : u i = v i) : chooseContact u i K = chooseContact v i K := by
  unfold chooseContact
  split_ifs <;> simp only [h]

 
noncomputable def replaySeedFiber (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) : List (ℕ × E) → Set E → ℕ → Set unitInterval
  | [], _, _ => Set.univ
  | (j,e)::c, ω, i =>
    let S := cluster G ω x
    let B := cluster G (η j ∩ internalEdges G Sᶜ) (y j)
    if i = j then {t | chooseContact (fun _ => t) j (contactSet G (η j) B) = e}
    else replaySeedFiber G x η y c (spliceField G S B e ω (η j)) i

theorem replaySeedFiber_univ (G : BondGraph V E) (x : V) (η : ℕ → Set E)
    (y : ℕ → V) (c : List (ℕ × E)) (ω : Set E) (i : ℕ)
    (hi : ∀ q ∈ c, i ≠ q.1) : replaySeedFiber G x η y c ω i = Set.univ := by
  induction c generalizing ω with
  | nil => rfl
  | cons q c ih =>
    obtain ⟨j,e⟩ := q
    simp only [replaySeedFiber,ite_eq_right (hi (j,e) (by simp))]
    exact ih _ (fun q hq => hi q (by simp [hq]))

theorem SpliceTrace.follows_iff_seedFiber (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (seed : ℕ → unitInterval) :
    FollowsContactRule G x η y (chooseContact seed) c ω ↔
      ∀ i, 1 ≤ i → i ≤ k → seed i ∈ replaySeedFiber G x η y c ω i := by
  induction h with
  | stop j ω hz => simp [FollowsContactRule,replayContacts,replaySeedFiber]
  | @step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht ih =>
    rw [followsContactRule_cons,ih]
    have htail : replaySeedFiber G x η y c
        (spliceField G (cluster G ω x)
          (cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)) e ω (η l)) l = Set.univ := by
      apply replaySeedFiber_univ
      intro q hq
      have hq' := ht.seam_data G x η y k l _ ωf c q hq
      omega
    constructor
    · rintro ⟨hc,hr⟩ i hi hik
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,ite_true,Set.mem_ofPred_eq]
        exact (chooseContact_congr _ _ l _ rfl).trans hc
      · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik
    · intro hr
      constructor
      · have hh := hr l (by omega) hlk
        simp only [replaySeedFiber,ite_true,Set.mem_ofPred_eq] at hh
        exact (chooseContact_congr _ _ l _ rfl).trans hh
      · intro i hi hik
        by_cases hil : i = l
        · subst i
          rw [htail]
          trivial
        · simpa only [replaySeedFiber,ite_eq_right hil] using hr i hi hik

 

def finiteContactSeeds (k : ℕ) (u : Fin k → unitInterval) (i : ℕ) : unitInterval :=
  if hi : 1 ≤ i ∧ i ≤ k then u ⟨i-1,by omega⟩ else 0

@[simp] theorem finiteContactSeeds_at (k : ℕ) (u : Fin k → unitInterval) (i : Fin k) :
    finiteContactSeeds k u (i.val+1) = u i := by
  have hi : 1 ≤ i.val+1 ∧ i.val+1 ≤ k := ⟨by omega,by omega⟩
  simp only [finiteContactSeeds,dite_eq_left hi,Nat.add_sub_cancel]

theorem SpliceTrace.seed_event_eq_pi (G : BondGraph V E) (x : V)
    (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf) :
    {u : Fin k → unitInterval | FollowsContactRule G x η y
      (chooseContact (finiteContactSeeds k u)) c ω} =
      Set.pi Set.univ (fun i => replaySeedFiber G x η y c ω (i.val+1)) := by
  ext u
  rw [Set.mem_ofPred_eq,h.follows_iff_seedFiber G x η y k j ω ωf c]
  simp only [Set.mem_pi,Set.mem_univ,true_implies]
  constructor
  · intro hu i
    simpa only [finiteContactSeeds_at] using hu (i.val+1) (by omega) (by omega)
  · intro hu i hi hik
    have hh := hu ⟨i-1,by omega⟩
    have hii : 1 ≤ i ∧ i ≤ k := ⟨hi,hik⟩
    simpa only [finiteContactSeeds,dite_eq_left hii,Nat.sub_add_cancel hi] using hh

 

theorem SpliceTrace.volume_seedFiber (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ∀ i, volume (replaySeedFiber G x η y c ω i) =
      ENNReal.ofReal ((traceContactCount G η y ωf x c i : ℝ)⁻¹) := by
  induction c generalizing j ω with
  | nil => simp [replaySeedFiber,traceContactCount]
  | cons q c ih =>
    obtain ⟨l,e⟩ := q
    have hcut := h.head_cut G x η y k j l ω ωf e c
    cases h with
    | step j l ω e a b c ωf hn hjl hlk hm hy he hab ha hb ht =>
      intro i
      by_cases hil : i = l
      · subst i
        simp only [replaySeedFiber,ite_true,traceContactCount,seamContactCount,hcut]
        let B := cluster G (η l ∩ internalEdges G (cluster G ω x)ᶜ) (y l)
        let K := contactSet G (η l) B
        have hB : B.Finite := (hcaps l (by omega) hlk).subset (fun _ h => conn_mono G Set.inter_subset_left h)
        have hK : K.Finite := contactSet_finite G hloc (η l) B hB
        have heK : e ∈ K := ⟨he,b,a,hab.trans (Sym2.eq_swap ..),hb,
          fun haB => slit_cluster_subset G (cluster G ω x) (η l) (y l) hy haB ha⟩
        have hnK : K.Nonempty := ⟨e,heK⟩
        change volume {t : unitInterval | chooseContact (fun _ => t) l K = e} = _
        simp only [chooseContact,dite_eq_left hK,dite_eq_left hnK]
        rw [volume_uniformContact_fiber _ _ e (hK.mem_toFinset.mpr heK)]
        rw [← Set.ncard_eq_toFinset_card K hK]
      · simpa only [replaySeedFiber,traceContactCount,ite_eq_right hil] using ih l _ ht i

 
theorem SpliceTrace.seed_probability (G : BondGraph V E) (hloc : LocallyFinite G)
    (x : V) (η : ℕ → Set E) (y : ℕ → V) (k j : ℕ) (ω ωf : Set E)
    (c : List (ℕ × E)) (h : SpliceTrace G x η y k j ω c ωf)
    (hcaps : ∀ i, 1 ≤ i → i ≤ k → (cluster G (η i) (y i)).Finite) :
    ((volume : Measure (Fin k → unitInterval))
      {u | FollowsContactRule G x η y (chooseContact (finiteContactSeeds k u)) c ω}).toReal =
      ∏ i : Fin k, (traceContactCount G η y ωf x c (i.val+1):ℝ)⁻¹ := by
  rw [h.seed_event_eq_pi G x η y k j ω ωf c,MeasureTheory.volume_pi,Measure.pi_pi,ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [h.volume_seedFiber G hloc x η y k j ω ωf c hcaps,ENNReal.toReal_ofReal (by positivity)]

end SeededTraceLaw
end Percolation

end OAI
