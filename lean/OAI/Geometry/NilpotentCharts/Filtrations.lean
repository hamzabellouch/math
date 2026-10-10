import Mathlib

namespace OAI

/-! Closed lower-central filtrations and monotone positive coordinate weights. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace StretchedFiltration
open Subgroup
variable {G : Type*} [Group G]

 
lemma rotate_le (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ N) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  let f := QuotientGroup.mk' N
  have hmap (S : Subgroup G) (hS : S ≤ N) : S.map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff S).mpr
    simpa [f, QuotientGroup.ker_mk'] using hS
  have h₁' : ⁅⁅B.map f, C.map f⁆, A.map f⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap _ h₁
  have h₂' : ⁅⁅C.map f, A.map f⁆, B.map f⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap _ h₂
  have h : (⁅⁅A, B⁆, C⁆).map f = ⊥ := by
    simpa only [Subgroup.map_commutator] using
      Subgroup.commutator_commutator_eq_bot_of_rotate h₁' h₂'
  have := (Subgroup.map_eq_bot_iff _).mp h
  simpa [f, QuotientGroup.ker_mk'] using this

 
theorem lower_bracket (a b : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries a, (⊤ : Subgroup G).lowerCentralSeries b⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (a + b + 1) := by
  induction a generalizing b with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero, Subgroup.commutator_comm,
      ← Subgroup.lowerCentralSeries_succ]
    simp
  | succ a ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply rotate_le
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G),
        ← Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1)
    · have h := Subgroup.commutator_mono
        (show ⁅(⊤ : Subgroup G).lowerCentralSeries b,
            (⊤ : Subgroup G).lowerCentralSeries a⁆ ≤
            (⊤ : Subgroup G).lowerCentralSeries (a + b + 1) from by
          rw [Subgroup.commutator_comm]
          exact ih b) (le_refl (⊤ : Subgroup G))
      simpa only [← Subgroup.lowerCentralSeries_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

 

def stretch (D : ℕ) (i : ℕ) : Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries ((i - 1) / D)

lemma stretch_antitone (D : ℕ) : Antitone (stretch (G := G) D) := by
  intro i j hij
  exact (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.div_le_div_right (Nat.sub_le_sub_right hij 1))

@[simp] lemma stretch_zero (D : ℕ) : stretch (G := G) D 0 = ⊤ := by
  simp [stretch]

@[simp] lemma stretch_one (D : ℕ) : stretch (G := G) D 1 = ⊤ := by
  simp [stretch]

lemma stretch_eq_top {D i : ℕ} (hD : 0 < D) (hi : i ≤ D) :
    stretch (G := G) D i = ⊤ := by
  have : i - 1 < D := by omega
  simp [stretch, Nat.div_eq_of_lt this]

lemma stretch_terminal {D s : ℕ} (hD : 0 < D)
    (hs : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    stretch (G := G) D (s * D + 1) = ⊥ := by
  simpa [stretch, Nat.mul_div_cancel, Nat.ne_of_gt hD] using hs

lemma stretch_bracket {D : ℕ} (hD : 0 < D) (i j : ℕ) :
    ⁅stretch (G := G) D i, stretch (G := G) D j⁆ ≤ stretch (G := G) D (i + j) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [Nat.zero_add, stretch_zero]
    unfold stretch
    exact Subgroup.commutator_le_right _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Nat.add_zero, stretch_zero]
    unfold stretch
    exact Subgroup.commutator_le_left _ _
  apply (lower_bracket ((i - 1) / D) ((j - 1) / D)).trans
  apply (⊤ : Subgroup G).lowerCentralSeries_antitone
  have h₁ := Nat.mod_lt (i - 1) hD
  have h₂ := Nat.mod_lt (j - 1) hD
  have h₃ := Nat.div_add_mod (i - 1) D
  have h₄ := Nat.div_add_mod (j - 1) D
  have h₅ := Nat.div_add_mod (i + j - 1) D
  have h₆ := Nat.mod_lt (i + j - 1) hD
  by_contra h
  have hh : ((i - 1) / D + (j - 1) / D + 2) * D ≤ (i + j - 1) / D * D :=
    Nat.mul_le_mul_right D (by omega)
  have hsum : i + j - 1 = (i - 1) + (j - 1) + 1 := by omega
  have hh' : D * ((i - 1) / D) + D * ((j - 1) / D) + 2 * D ≤
      D * ((i + j - 1) / D) := by nlinarith only [hh]
  omega

end StretchedFiltration
namespace RawClosedFiltration
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
lemma closure_commutator_le (A B N : Subgroup G) (hN : IsClosed (N : Set G))
    (h : ⁅A,B⁆ ≤ N) : ⁅A.topologicalClosure,B.topologicalClosure⁆ ≤ N := by
  apply Subgroup.commutator_le.mpr
  intro a ha b hb
  have hfixed : ∀ a ∈ A, ∀ b ∈ B.topologicalClosure, ⁅a,b⁆ ∈ N := by
    intro x hx y hy
    have hc : Continuous (fun y : G => ⁅x,y⁆) := by
      simp only [commutatorElement_def]
      fun_prop
    exact closure_minimal (s := (B : Set G)) (t := (fun y : G => ⁅x,y⁆) ⁻¹' (N : Set G))
      (fun y hy => h (Subgroup.commutator_mem_commutator hx hy))
      (hN.preimage hc) hy
  have hc : Continuous (fun x : G => ⁅x,b⁆) := by
    simp only [commutatorElement_def]
    fun_prop
  exact closure_minimal (s := (A : Set G)) (t := (fun x : G => ⁅x,b⁆) ⁻¹' (N : Set G))
    (fun x hx => hfixed x hx b hb) (hN.preimage hc) ha

def level (k : ℕ) : Subgroup G := ((⊤ : Subgroup G).lowerCentralSeries (k-1)).topologicalClosure
lemma antitone_level : Antitone (level (G := G)) := by
  intro i j hij
  exact Subgroup.topologicalClosure_mono ((⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.sub_le_sub_right hij 1))
lemma bracket_level (i j : ℕ) : ⁅level (G := G) i,level (G := G) j⁆ ≤ level (G := G) (i+j) := by
  apply closure_commutator_le _ _ _ (Subgroup.isClosed_topologicalClosure _)
  apply le_trans ?_ (Subgroup.le_topologicalClosure _)
  simpa only [StretchedFiltration.stretch,Nat.div_one] using StretchedFiltration.stretch_bracket (G := G) (by decide : 0<1) i j
@[simp] lemma level_zero : level (G := G) 0 = ⊤ := by
  apply top_unique
  intro g hg
  exact Subgroup.le_topologicalClosure _ (by simp [Subgroup.lowerCentralSeries_zero])
@[simp] lemma level_one : level (G := G) 1 = ⊤ := by
  apply top_unique
  intro g hg
  exact Subgroup.le_topologicalClosure _ (by simp [Subgroup.lowerCentralSeries_zero])
lemma level_terminal [T1Space G] {s : ℕ} (h : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    level (G := G) (s+1) = ⊥ := by
  ext g
  simp only [level,Nat.add_sub_cancel,h]
  change g ∈ closure ({1} : Set G) ↔ g = 1
  rw [isClosed_singleton.closure_eq]
  rfl

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
lemma comap_closure_map (π : G →* Q) (hc : Continuous π) (ho : IsOpenMap π)
    (A : Subgroup G) (hk : π.ker ≤ A.topologicalClosure) :
    (A.map π).topologicalClosure.comap π = A.topologicalClosure := by
  apply le_antisymm
  · have he := ho.preimage_closure_eq_closure_preimage hc (A.map π : Set Q)
    intro g hg
    change g ∈ π ⁻¹' closure (A.map π : Set Q) at hg
    rw [he] at hg
    apply closure_minimal (t := (A.topologicalClosure : Set G)) ?_
      (Subgroup.isClosed_topologicalClosure A) hg
    change (A.map π).comap π ≤ A.topologicalClosure
    rw [Subgroup.comap_map_eq]
    exact sup_le (Subgroup.le_topologicalClosure A) hk
  · apply Subgroup.topologicalClosure_minimal
    · intro g hg
      exact Subgroup.le_topologicalClosure _ (Subgroup.mem_map_of_mem π hg)
    · exact (Subgroup.isClosed_topologicalClosure _).preimage hc

lemma comap_level (π : G →* Q) (hc : Continuous π) (ho : IsOpenMap π)
    (hs : Surjective π) (k : ℕ) (hk : π.ker ≤ level (G := G) k) :
    (level (G := Q) k).comap π = level (G := G) k := by
  have H := comap_closure_map π hc ho ((⊤ : Subgroup G).lowerCentralSeries (k-1)) hk
  simpa only [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective π hs,level] using H
end RawClosedFiltration

namespace RawFilteredWeights
variable {n m : ℕ} (w : Fin n → ℕ) (s : ℕ)
lemma append_monotone (hw : Monotone w) (hb : ∀ i, w i ≤ s) :
    Monotone (Fin.append w (fun _ : Fin m => s+1)) := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · intro hij
      simp only [Fin.append_left]
      exact hw (by simpa only [Fin.le_def,Fin.val_castAdd] using hij)
    · intro hij
      simp only [Fin.append_left,Fin.append_right]
      exact (hb a).trans (Nat.le_succ s)
  · intro j
    refine Fin.addCases (fun b => ?_) (fun b => ?_) j
    · intro hij
      have hi : (Fin.natAdd n a).val ≤ (Fin.castAdd m b).val := hij
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hi
      omega
    · intro hij
      simp only [Fin.append_right,le_refl]
lemma append_pos (hw : ∀ i, 0 < w i) :
    ∀ i, 0 < Fin.append w (fun _ : Fin m => s+1) i := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hw j
  · simp only [Fin.append_right,Nat.zero_lt_succ]
lemma append_bound (hw : ∀ i, w i ≤ s) :
    ∀ i, Fin.append w (fun _ : Fin m => s+1) i ≤ s+1 := by
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using (hw j).trans (Nat.le_succ s)
  · simp only [Fin.append_right,le_refl]
lemma append_zero_iff {k : ℕ} (hk : k ≤ s+1) (a : Fin (n+m) → ℝ) :
    (∀ i, Fin.append w (fun _ : Fin m => s+1) i < k → a i = 0) ↔
      ∀ j, w j < k → a (Fin.castAdd m j) = 0 := by
  constructor
  · intro h j hj
    exact h _ (by simpa only [Fin.append_left] using hj)
  · intro h i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa only [Fin.append_left] using h j
    · simp only [Fin.append_right]
      intro hs
      omega
end RawFilteredWeights
end

end OAI
