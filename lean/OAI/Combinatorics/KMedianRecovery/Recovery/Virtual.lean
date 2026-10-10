import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Score

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

inductive Virtual (V : Type*) (a : ℕ)
  | real : V → Virtual V a
  | ball : Fin a → Virtual V a
  | permanent : Virtual V a
  deriving DecidableEq

noncomputable def virtualDistance {a : ℕ} (w : Fin a → V) (radius : Fin a → ℝ)
    (M : ℝ) (x : V) : Virtual V a → ℝ
  | .real s => dist x s
  | .ball i => dist x (w i) + radius i
  | .permanent => M

noncomputable def withGhosts {a : ℕ} (S : Finset V) : Finset (Virtual V a) :=
  S.image Virtual.real ∪ Finset.univ.image Virtual.ball ∪ {Virtual.permanent}

omit [PseudoMetricSpace V] in
lemma withGhosts_nonempty {a : ℕ} (S : Finset V) : (@withGhosts V _ a S).Nonempty := by
  exact ⟨Virtual.permanent,by simp [withGhosts]⟩

omit [PseudoMetricSpace V] in
@[simp] lemma real_mem_withGhosts {a : ℕ} {S : Finset V} {s : V} :
    Virtual.real s ∈ @withGhosts V _ a S ↔ s ∈ S := by simp [withGhosts]

omit [PseudoMetricSpace V] in
@[simp] lemma ball_mem_withGhosts {a : ℕ} (S : Finset V) (i : Fin a) :
    Virtual.ball i ∈ withGhosts S := by simp [withGhosts]

omit [PseudoMetricSpace V] in
@[simp] lemma permanent_mem_withGhosts {a : ℕ} (S : Finset V) :
    (Virtual.permanent : Virtual V a) ∈ withGhosts S := by simp [withGhosts]

noncomputable def virtualNearest {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) : ℝ :=
  (withGhosts S).inf' (withGhosts_nonempty S) (virtualDistance w radius M x)

noncomputable def nearestTag {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) : Virtual V a :=
  Classical.choose (Finset.exists_min_image (withGhosts S)
    (virtualDistance w radius M x) (withGhosts_nonempty S))

lemma nearestTag_mem {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) :
    nearestTag S w radius M x ∈ withGhosts S :=
  (Classical.choose_spec (Finset.exists_min_image (withGhosts S)
    (virtualDistance w radius M x) (withGhosts_nonempty S))).1

lemma nearestTag_distance {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V) :
    virtualDistance w radius M x (nearestTag S w radius M x) =
      virtualNearest S w radius M x := by
  apply le_antisymm
  · apply Finset.le_inf'
    exact (Classical.choose_spec (Finset.exists_min_image (withGhosts S)
      (virtualDistance w radius M x) (withGhosts_nonempty S))).2
  · exact Finset.inf'_le _ (nearestTag_mem S w radius M x)

lemma virtualNearest_nonneg {a : ℕ} (S : Finset V) (w : Fin a → V)
    (radius : Fin a → ℝ) (M : ℝ) (x : V)
    (hr : ∀ i, 0 ≤ radius i) (hM : 0 ≤ M) : 0 ≤ virtualNearest S w radius M x := by
  apply Finset.le_inf'
  intro t _
  cases t with
  | real s => exact dist_nonneg
  | ball i => exact add_nonneg dist_nonneg (hr i)
  | permanent => exact hM

noncomputable def distanceTo (S : Finset V) (hS : S.Nonempty) (x : V) : ℝ :=
  S.inf' hS (dist x)

omit [DecidableEq V] in
lemma distanceTo_nonneg (S : Finset V) (hS : S.Nonempty) (x : V) :
    0 ≤ distanceTo S hS x := Finset.le_inf' hS _ (fun _ _ => dist_nonneg)

omit [DecidableEq V] in
lemma distanceTo_le {S : Finset V} (hS : S.Nonempty) (x : V) {s : V} (hs : s ∈ S) :
    distanceTo S hS x ≤ dist x s := Finset.inf'_le _ hs

omit [DecidableEq V] in
lemma distanceTo_triangle (S : Finset V) (hS : S.Nonempty) (x y : V) :
    distanceTo S hS x ≤ dist x y + distanceTo S hS y := by
  obtain ⟨z,hz,hm⟩ := Finset.exists_min_image S (dist y) hS
  have he : dist y z = distanceTo S hS y :=
    le_antisymm (Finset.le_inf' hS _ hm) (Finset.inf'_le _ hz)
  exact (distanceTo_le hS x hz).trans (by rw [← he]; exact dist_triangle _ _ _)

lemma cappedCost_nonneg {E : Type*} (baseline : ℝ) (distance : E → ℝ) (X : Finset E)
    (hb : 0 ≤ baseline) (hd : ∀ e ∈ X, 0 ≤ distance e) :
    0 ≤ cappedCost baseline distance X := (Finset.le_fold_min _).mpr ⟨hb,hd⟩

lemma le_cappedCost {E : Type*} (baseline : ℝ) (distance : E → ℝ) (X : Finset E)
    {x : ℝ} (hb : x ≤ baseline) (hd : ∀ e ∈ X, x ≤ distance e) :
    x ≤ cappedCost baseline distance X := (Finset.le_fold_min _).mpr ⟨hb,hd⟩

omit [PseudoMetricSpace V] in

lemma completion_cardinality (S Q Red Blue Add : Finset V)
    (hQ : Q ⊆ S) (hRed : Red ⊆ S \ Q) (hBlue : Blue ⊆ S \ Q)
    (hRB : Disjoint Red Blue)
    (hcount : Add.card ≤ Q.card + Red.card + Blue.card) :
    ((S \ (Q ∪ Red ∪ Blue)) ∪ Add).card ≤ S.card := by
  have hQR : Disjoint Q Red := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hRed hx')).2 hx
  have hQB : Disjoint Q Blue := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp (hBlue hx')).2 hx
  have hd : Disjoint (Q ∪ Red) Blue := Finset.disjoint_union_left.mpr ⟨hQB,hRB⟩
  have hs : Q ∪ Red ∪ Blue ⊆ S :=
    Finset.union_subset (Finset.union_subset hQ (hRed.trans Finset.sdiff_subset))
      (hBlue.trans Finset.sdiff_subset)
  have hc := Finset.card_sdiff_add_card_eq_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_union_of_disjoint hQR] at hc
  exact (Finset.card_union_le _ _).trans (by omega)

noncomputable def assignmentWeight {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) : ℝ :=
  ((D.filter (fun p => assignment p = Virtual.real s)).card : ℝ)

omit [PseudoMetricSpace V] in
lemma assignmentWeight_nonneg {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) : 0 ≤ assignmentWeight D assignment s := by
  exact Nat.cast_nonneg _

omit [PseudoMetricSpace V] in
lemma assignmentWeight_sum {a : ℕ} (D : Finset V)
    (assignment : V → Virtual V a) (s : V) (charge : ℝ) :
    (∑ p ∈ D, if assignment p = Virtual.real s then charge else 0) =
      assignmentWeight D assignment s * charge := by
  rw [← Finset.sum_filter]
  simp [assignmentWeight]

end MetricKMedianRecovery.Completion

end OAI
