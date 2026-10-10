import Mathlib
import OAI.Combinatorics.KMedian.Geometry.GreedyPacking
import OAI.Combinatorics.KMedian.Optimization.ComputedNearest
import OAI.Combinatorics.KMedian.Rounding.RationalPhysicalKernel

namespace OAI


                                                
section
namespace MetricKMedian.Completion.Rational
open Finset PhysicalPotential CopyState Preparation
variable {j : ℕ} {I : Type*} [DecidableEq I]

def packing : ℕ → Finset (Fin j) → (Fin j → ℚ) → (Fin j → Finset I) → Finset (Fin j)
  | 0, _, _, _ => ∅
  | t+1, U, R, B => if h : U.Nonempty then
      let c := firstNearest U R h
      insert c (packing t (U.filter (fun i => Disjoint (B c) (B i))) R B)
    else ∅

theorem packing_spec (t : ℕ) (U : Finset (Fin j)) (R : Fin j → ℚ) (B : Fin j → Finset I)
    (hU : U.card ≤ t) (hB : ∀ c ∈ U, (B c).Nonempty) :
    packing t U R B ⊆ U ∧ (↑(packing t U R B) : Set (Fin j)).PairwiseDisjoint B ∧
      ∀ c ∈ U, ∃ a ∈ packing t U R B, R a ≤ R c ∧ ¬ Disjoint (B c) (B a) := by
  induction t generalizing U with
  | zero =>
    have hu : U=∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
    subst U
    simp [packing]
  | succ t ih =>
    by_cases hu : U.Nonempty
    · let c := firstNearest U R hu
      have hc : c∈U := (firstNearest_spec U R hu).1
      have hmin : ∀ i∈U, R c ≤ R i := (firstNearest_spec U R hu).2
      let V := U.filter (fun i => Disjoint (B c) (B i))
      have hVU : V ⊆ U := filter_subset _ _
      have hcV : c∉V := by
        intro h
        have hd := (mem_filter.mp h).2
        obtain ⟨a,ha⟩ := hB c hc
        exact disjoint_left.mp hd ha ha
      have hlt : V.card<U.card := card_lt_card <|
        Finset.ssubset_iff_subset_ne.mpr ⟨hVU,fun he => hcV (he ▸ hc)⟩
      obtain ⟨hsub,hdis,hcover⟩ := ih V (by omega) (fun i hi => hB i (hVU hi))
      rw [packing, dite_eq_left hu]
      change insert c (packing t V R B) ⊆ U ∧ _
      refine ⟨insert_subset hc (hsub.trans hVU),?_,?_⟩
      · rw [coe_insert]
        apply hdis.insert
        intro a ha _
        exact (mem_filter.mp (hsub ha)).2
      · intro i hi
        by_cases hiv : i∈V
        · obtain ⟨a,ha,hr,hd⟩ := hcover i hiv
          exact ⟨a,mem_insert_of_mem ha,hr,hd⟩
        · exact ⟨c,mem_insert_self _ _,hmin i hi,
            fun hd => hiv (mem_filter.mpr ⟨hi,hd.symm⟩)⟩
    · have hue : U=∅ := not_nonempty_iff_eq_empty.mp hu
      subst U
      simp [packing]

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}
local instance : LinearOrder (Copy (F := F) Δ) := RationalPhysicalKernel.copyOrder

def uncovered (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) Δ)) : Finset (Fin j) :=
  univ.filter (fun c => ¬ ∃ f ∈ integral Δ A, d c f ≤ 5*R c)

def pick (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (c : Fin j) : Copy (F := F) Δ := (B c).min' (hB c)

def output (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) : Finset F :=
  integral Δ A ∪ (packing j (uncovered d R A) R B).image (fun c => (pick B hB c).1)

theorem output_spec (d : Fin j → F → ℚ) (R : Fin j → ℚ)
    (location : F → X) (client : Fin j → X)
    (hdist : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (hR : ∀ c, 0 ≤ R c) {g : ℝ} (hg : 0≤g) (hunit : g*(Δ:ℝ)=1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (hB : ∀ c, (B c).Nonempty) (hm : ∀ c, mass g (B c)=1)
    (hd : ∀ c i, i∈B c → d c i.1 ≤ R c)
    (hbackup : ∀ c, (¬∃ f∈integral Δ A, d c f ≤ 5*R c) → B c ⊆ A) :
    integral Δ A ⊆ output d R A B hB ∧
    ((output d R A B hB).card:ℝ) ≤ mass g A ∧
    ∀ c, ∃ f∈output d R A B hB, d c f ≤ 5*R c := by
  let Q := integral Δ A
  let U := uncovered d R A
  let C := packing j U R B
  have hpick : ∀ c, pick B hB c∈B c := fun c => min'_mem _ _
  have hcard : U.card ≤ j := (card_le_univ U).trans_eq (Fintype.card_fin j)
  obtain ⟨hCU,hdis,hcover⟩ := packing_spec j U R B hcard (fun c _ => hB c)
  have hres : resets Δ Q ⊆ A := by
    intro i hi
    exact (mem_integral Δ A i.1).mp ((mem_resets Δ Q i).mp hi)
      ((mem_slots Δ i.1 i).mpr rfl)
  have hbucket : ∀ c∈U, B c ⊆ A \ resets Δ Q := by
    intro c hc i hi
    have hn := (mem_filter.mp hc).2
    refine mem_sdiff.mpr ⟨hbackup c hn hi,?_⟩
    intro hir
    have hif := (mem_resets Δ Q i).mp hir
    exact hn ⟨i.1,hif,(hd c i hi).trans (by linarith only [hR c])⟩
  have hcount : (C.card:ℝ) ≤ mass g A-(Q.card:ℝ) := by
    have hh := packing_mass hg C B (A \ resets Δ Q)
      (fun c hc => hbucket c (hCU hc)) hdis (fun c _ => (hm c).ge)
    rw [mass_sdiff g hres,reset_mass Δ Q hunit] at hh
    exact hh
  refine ⟨subset_union_left,?_,?_⟩
  · have hh : ((output d R A B hB).card:ℝ) ≤ (Q.card:ℝ)+(C.card:ℝ) := by
      exact_mod_cast (card_union_le Q (C.image (fun c => (pick B hB c).1))).trans
        (Nat.add_le_add_left card_image_le Q.card)
    linarith only [hh,hcount]
  · intro c
    by_cases hc : c∈U
    · obtain ⟨a,ha,hRa,hinter⟩ := hcover c hc
      refine ⟨(pick B hB a).1,mem_union_right Q (mem_image.mpr ⟨a,ha,rfl⟩),?_⟩
      have hh := packed_connection client (fun i : Copy (F := F) Δ => location i.1)
        (fun c => (R c:ℝ)) B (fun c i hi => by rw [hdist]; exact_mod_cast hd c i hi)
        (by exact_mod_cast hRa) hinter (hpick a)
      rw [hdist] at hh
      have hr : (0:ℝ)≤R c := by exact_mod_cast hR c
      have hhh : (d c (pick B hB a).1:ℝ) ≤ 5*(R c:ℝ) := by linarith only [hh,hr]
      exact_mod_cast hhh
    · have hex : ∃ f∈Q, d c f ≤ 5*R c := by
        simpa only [U,uncovered,mem_filter,mem_univ,true_and,not_not] using hc
      obtain ⟨f,hf,hfd⟩ := hex
      exact ⟨f,mem_union_left _ hf,hfd⟩

end MetricKMedian.Completion.Rational
end

end OAI
