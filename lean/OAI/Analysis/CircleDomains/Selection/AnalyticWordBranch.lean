import OAI.Analysis.CircleDomains.Selection.LusinInput
import Mathlib.Topology.MetricSpace.PiNat

namespace OAI

/-! A branch through finite Baire words identifies an actual point of a
continuous image. This is the topological step for completed measurability. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def baireWordCylinder (s : List ℕ) : Set (ℕ → ℕ) :=
    {b | PiNat.res b s.length = s}

 theorem baireWordCylinder_nil : baireWordCylinder [] = univ := by
  ext b
  simp [baireWordCylinder]

 theorem baireWordCylinder_children (s : List ℕ) :
    (⋃ k, baireWordCylinder (k::s)) = baireWordCylinder s := by
  ext b
  simp only [mem_iUnion,baireWordCylinder,mem_ofPred_eq,List.length_cons,PiNat.res_succ]
  constructor
  · rintro ⟨k,hk⟩
    exact (List.cons.inj hk).2
  · intro hb
    exact ⟨b s.length,by rw [hb]⟩

 theorem isOpen_baireWordCylinder (s : List ℕ) : IsOpen (baireWordCylinder s) := by
  induction s with
  | nil => rw [baireWordCylinder_nil]; exact isOpen_univ
  | cons k s ih =>
    have he : baireWordCylinder (k::s) =
        (fun b : ℕ → ℕ => b s.length) ⁻¹' {k} ∩ baireWordCylinder s := by
      ext b
      simp only [baireWordCylinder,mem_ofPred_eq,List.length_cons,PiNat.res_succ,
        List.cons.injEq,mem_inter_iff,mem_preimage,mem_singleton_iff]
    rw [he]
    exact ((isOpen_discrete {k}).preimage (continuous_apply s.length)).inter ih

 theorem eq_of_prefix_closures {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) {b : ℕ → ℕ} {x : X}
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder b n)) : x = f b := by
  by_contra hne
  have hd : 0 < dist x (f b) := dist_pos.mpr hne
  obtain ⟨V,⟨c,n,rfl⟩,hb,hV⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ => ℕ)).exists_subset_of_mem_open
      (show b ∈ f ⁻¹' Metric.ball (f b) (dist x (f b)/2) from Metric.mem_ball_self (half_pos hd))
      (Metric.isOpen_ball.preimage hf)
  have he : PiNat.cylinder b n = PiNat.cylinder c n := PiNat.mem_cylinder_iff_eq.mp hb
  have hsub : f '' PiNat.cylinder b n ⊆ Metric.closedBall (f b) (dist x (f b)/2) := by
    rintro z ⟨a,ha,rfl⟩
    exact Metric.ball_subset_closedBall (hV (he ▸ ha))
  have hclosed := (closure_minimal hsub Metric.isClosed_closedBall) (hx n)
  exact (not_lt_of_ge (Metric.mem_closedBall.mp hclosed)) (half_lt_self hd)

 theorem mem_range_of_prefix_closures {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) {b : ℕ → ℕ} {x : X}
    (hx : ∀ n, x ∈ closure (f '' PiNat.cylinder b n)) : x ∈ range f :=
  ⟨b,(eq_of_prefix_closures hf hx).symm⟩

 theorem mem_range_of_word_hull_branch {X : Type*} [MetricSpace X]
    {f : (ℕ → ℕ) → X} (hf : Continuous f) (B : List ℕ → Set X) {x : X}
    (hroot : x ∈ B [])
    (hnext : ∀ s, x ∈ B s → ∃ k, x ∈ B (k::s))
    (hB : ∀ s, B s ⊆ closure (f '' baireWordCylinder s)) : x ∈ range f := by
  classical
  let pick (s : List ℕ) (hs : x ∈ B s) := Classical.choose (hnext s hs)
  have hpick (s : List ℕ) (hs : x ∈ B s) : x ∈ B (pick s hs :: s) :=
    Classical.choose_spec (hnext s hs)
  let p : ℕ → {s : List ℕ // x ∈ B s} :=
    Nat.rec ⟨[],hroot⟩ (fun _ s => ⟨pick s.val s.property :: s.val,hpick s.val s.property⟩)
  let b : ℕ → ℕ := fun n => pick (p n).val (p n).property
  have hres (n : ℕ) : PiNat.res b n = (p n).val := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change b n :: PiNat.res b n = b n :: (p n).val
      rw [ih]
  apply mem_range_of_prefix_closures hf (b := b)
  intro n
  have hh := hB (p n).val (p n).property
  have he : baireWordCylinder (p n).val = PiNat.cylinder b n := by
    rw [← hres n,PiNat.cylinder_eq_res]
    ext c
    simp only [baireWordCylinder,PiNat.res_length,mem_ofPred_eq]
  rwa [he] at hh

end CircleDomainRigidity

end

end OAI
