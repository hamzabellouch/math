import OAI.Combinatorics.Ryser.Selection.Definitions
import OAI.Combinatorics.Ryser.Geometry.ProjectionMoments
import OAI.Combinatorics.Ryser.Probability.Variance
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace OAI

open scoped BigOperators
noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [instFintypeF : Fintype F] [DecidableEq F] {n : ℕ}

def equationLoss (U : Finset (Point F)) (d : Direction F) (c : F)
    (x : Point F) : ℝ := (sliceCount U d (projection d x + c) : ℝ)

def lossByDirections (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F)) (x : Point F) : ℝ :=
  ∑ i ∈ I, ∑ d ∈ dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
    equationLoss (U i) d (projection d (v - u)) x

def targetLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Point F → ℝ :=
  lossByDirections data I U j data.dirs

def sourceLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : Point F → ℝ :=
  lossByDirections data I U j (fun _ => data.dirs j)

def entryLoss (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) : ℝ :=
  targetLoss data I U j x + sourceLoss data I U j x

def frozenMass (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) : ℝ :=
  ∑ i ∈ I, (U i).card

def sourceEnergy (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) : ℝ :=
  ∑ i ∈ I, ∑ d ∈ data.dirs j, sliceEnergy (U i) d

theorem equationLoss_nonneg (U : Finset (Point F)) (d : Direction F)
    (c : F) (x : Point F) : 0 ≤ equationLoss U d c x := let _ := instFintypeF; by
  exact Nat.cast_nonneg _

theorem equationLoss_le (U : Finset (Point F)) (d : Direction F)
    (c : F) (x : Point F) : equationLoss U d c x ≤ Fintype.card F := by
  change (sliceCount U d (projection d x + c) : ℝ) ≤ (Fintype.card F : ℝ)
  exact_mod_cast sliceCount_le_card_field U d (projection d x + c)

theorem expectation_equationLoss (U : Finset (Point F)) (d : Direction F)
    (c : F) :
    (FiniteLaw.uniform (Point F)).expectation (equationLoss U d c) =
      (U.card : ℝ) / Fintype.card F := by
  exact expectation_uniform_shifted_slice U d c

theorem variance_equationLoss (U : Finset (Point F)) (d : Direction F)
    (c : F) :
    (FiniteLaw.uniform (Point F)).variance (equationLoss U d c) =
      sliceEnergy U d := by
  exact variance_uniform_shifted_slice U d c

private theorem sum_le_of_card_le {A : Type*} (s : Finset A) (N : ℕ)
    (f : A → ℝ) (b : ℝ) (hcard : s.card ≤ N) (hb : 0 ≤ b)
    (hf : ∀ a ∈ s, f a ≤ b) : (∑ a ∈ s, f a) ≤ N * b := by
  calc
    (∑ a ∈ s, f a) ≤ ∑ _a ∈ s, b := Finset.sum_le_sum hf
    _ = (s.card : ℝ) * b := by simp
    _ ≤ (N : ℝ) * b := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb

private theorem triple_sum_le {A B C : Type*} (s : Finset A)
    (t : Finset B) (u : Finset C) (N : ℕ) (f : A → B → C → ℝ)
    (b : ℝ) (hs : s.card ≤ N) (ht : t.card ≤ N) (hu : u.card ≤ N)
    (hb : 0 ≤ b) (hf : ∀ a ∈ s, ∀ c ∈ t, ∀ e ∈ u, f a c e ≤ b) :
    (∑ a ∈ s, ∑ c ∈ t, ∑ e ∈ u, f a c e) ≤ (N : ℝ) ^ 3 * b := by
  calc
    _ ≤ (N : ℝ) * ((N : ℝ) * ((N : ℝ) * b)) := by
      apply sum_le_of_card_le s N _ _ hs (by positivity)
      intro a ha
      apply sum_le_of_card_le t N _ _ ht (by positivity)
      intro c hc
      exact sum_le_of_card_le u N _ b hu hb (hf a ha c hc)
    _ = _ := by ring

private theorem variance_sum_le_of_card_le {A Ω : Type*} [Fintype Ω]
    (mu : FiniteLaw Ω) (s : Finset A) (N : ℕ) (f : A → Ω → ℝ)
    (hs : s.card ≤ N) :
    mu.variance (fun x => ∑ a ∈ s, f a x) ≤
      (N : ℝ) * ∑ a ∈ s, mu.variance (f a) := by
  refine (mu.variance_sum_le s f).trans ?_
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hs)
  exact Finset.sum_nonneg (fun a _ => mu.variance_nonneg (f a))

private theorem variance_triple_sum_le {A B C Ω : Type*} [Fintype Ω]
    (mu : FiniteLaw Ω) (s : Finset A) (t : Finset B) (u : Finset C)
    (N : ℕ) (f : A → B → C → Ω → ℝ)
    (hs : s.card ≤ N) (ht : t.card ≤ N) (hu : u.card ≤ N) :
    mu.variance (fun x => ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, f a b c x) ≤
      (N : ℝ) ^ 3 * ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, mu.variance (f a b c) := by
  calc
    _ ≤ (N : ℝ) * ∑ a ∈ s,
        mu.variance (fun x => ∑ b ∈ t, ∑ c ∈ u, f a b c x) :=
      variance_sum_le_of_card_le mu s N _ hs
    _ ≤ (N : ℝ) * ∑ a ∈ s, (N : ℝ) * ∑ b ∈ t,
        (N : ℝ) * ∑ c ∈ u, mu.variance (f a b c) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro a ha
      refine (variance_sum_le_of_card_le mu t N _ ht).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
      apply Finset.sum_le_sum
      intro b hb
      exact variance_sum_le_of_card_le mu u N _ hu
    _ = _ := by simp only [← Finset.mul_sum]; ring

theorem lossByDirections_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F)) (x : Point F) :
    0 ≤ lossByDirections data I U j dirs x := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun d _ =>
    Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      equationLoss_nonneg (U i) d (projection d (v - u)) x))))

theorem lossByDirections_le (D : ℕ) (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F))
    (hW : ∀ i, (data.W i).card ≤ D) (hdirs : ∀ i, (dirs i).card ≤ D)
    (x : Point F) :
    lossByDirections data I U j dirs x ≤
      (D : ℝ) ^ 3 * I.card * Fintype.card F := by
  calc
    _ ≤ ∑ _i ∈ I, (D : ℝ) ^ 3 * Fintype.card F := by
      apply Finset.sum_le_sum
      intro i hi
      exact triple_sum_le (dirs i) (data.W i) (data.W j) D _ _
        (hdirs i) (hW i) (hW j) (Nat.cast_nonneg _) (fun d _ u _ v _ =>
          equationLoss_le (U i) d (projection d (v - u)) x)
    _ = _ := by simp; ring

theorem expectation_lossByDirections_le (D : ℕ) (data : Data F n)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (dirs : Fin n → Finset (Direction F))
    (hW : ∀ i, (data.W i).card ≤ D) (hdirs : ∀ i, (dirs i).card ≤ D) :
    (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j dirs) ≤
      (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := by
  calc
    _ = ∑ i ∈ I, ∑ d ∈ dirs i, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        (U i).card / (Fintype.card F : ℝ) := by
      unfold lossByDirections
      simp_rw [FiniteLaw.expectation_finset_sum]
      simp_rw [expectation_equationLoss]
    _ ≤ ∑ i ∈ I, (D : ℝ) ^ 3 * ((U i).card / (Fintype.card F : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact triple_sum_le (dirs i) (data.W i) (data.W j) D _ _
        (hdirs i) (hW i) (hW j) (by positivity) (fun _ _ _ _ _ _ => le_rfl)
    _ = _ := by simp only [frozenMass, ← Finset.mul_sum, ← Finset.sum_div]; ring

theorem entryLoss_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) :
    0 ≤ entryLoss data I U j x :=
  add_nonneg (lossByDirections_nonneg data I U j data.dirs x)
    (lossByDirections_nonneg data I U j (fun _ => data.dirs j) x)

theorem entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (x : Point F) :
    entryLoss data I U j x ≤ 2 * (D : ℝ) ^ 3 * I.card * Fintype.card F := by
  have ht := lossByDirections_le D data I U j data.dirs hdata.2.1 hdata.2.2.1 x
  have hs := lossByDirections_le D data I U j (fun _ => data.dirs j)
    hdata.2.1 (fun _ => hdata.2.2.1 j) x
  unfold entryLoss targetLoss sourceLoss
  linarith

theorem expectation_entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).expectation (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := by
  have ht := expectation_lossByDirections_le D data I U j data.dirs
    hdata.2.1 hdata.2.2.1
  have hs := expectation_lossByDirections_le D data I U j (fun _ => data.dirs j)
    hdata.2.1 (fun _ => hdata.2.2.1 j)
  unfold entryLoss
  rw [FiniteLaw.expectation_add]
  change (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j data.dirs) +
    (FiniteLaw.uniform (Point F)).expectation (lossByDirections data I U j
      (fun _ => data.dirs j)) ≤ _
  calc
    _ ≤ (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F +
        (D : ℝ) ^ 3 * frozenMass I U / Fintype.card F := add_le_add ht hs
    _ = _ := by ring

theorem sourceEnergy_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) :
    0 ≤ sourceEnergy data I U j := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg
    (fun d _ => sliceEnergy_nonneg (U i) d))

theorem variance_sourceLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (sourceLoss data I U j) ≤
      (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j := by
  let mu := FiniteLaw.uniform (Point F)
  have htarget (i : Fin n) :
      mu.variance (fun x => ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
        equationLoss (U i) d (projection d (v - u)) x) ≤
        (D : ℝ) ^ 5 * ∑ d ∈ data.dirs j, sliceEnergy (U i) d := by
    calc
      _ ≤ (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          mu.variance (equationLoss (U i) d (projection d (v - u))) :=
        variance_triple_sum_le mu (data.dirs j) (data.W i) (data.W j) D _
          (hdata.2.2.1 j) (hdata.2.1 i) (hdata.2.1 j)
      _ = (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j, ∑ _u ∈ data.W i, ∑ _v ∈ data.W j,
          sliceEnergy (U i) d := by simp only [mu, variance_equationLoss]
      _ ≤ (D : ℝ) ^ 3 * ∑ d ∈ data.dirs j,
          (D : ℝ) * ((D : ℝ) * sliceEnergy (U i) d) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro d hd
        apply sum_le_of_card_le (data.W i) D _ _ (hdata.2.1 i) (mul_nonneg (Nat.cast_nonneg D) (sliceEnergy_nonneg (U i) d))
        intro u hu
        exact sum_le_of_card_le (data.W j) D _ _ (hdata.2.1 j)
          (sliceEnergy_nonneg (U i) d) (fun _ _ => le_rfl)
      _ = _ := by simp only [← Finset.mul_sum]; ring
  calc
    _ ≤ (I.card : ℝ) * ∑ i ∈ I, mu.variance (fun x =>
        ∑ d ∈ data.dirs j, ∑ u ∈ data.W i, ∑ v ∈ data.W j,
          equationLoss (U i) d (projection d (v - u)) x) :=
      mu.variance_sum_le I _
    _ ≤ (I.card : ℝ) * ∑ i ∈ I, (D : ℝ) ^ 5 *
        ∑ d ∈ data.dirs j, sliceEnergy (U i) d :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => htarget i))
        (Nat.cast_nonneg _)
    _ = _ := by simp only [sourceEnergy, ← Finset.mul_sum]; ring

def targetDirectionGroup (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (d : Direction F) (t : F) : ℝ :=
  ∑ i ∈ I.filter (fun i => d ∈ data.dirs i), ∑ u ∈ data.W i, ∑ v ∈ data.W j,
    (sliceCount (U i) d (t + projection d (v - u)) : ℝ)

theorem targetDirectionGroup_nonneg (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (d : Direction F) (t : F) :
    0 ≤ targetDirectionGroup data I U j d t := let _ := instFintypeF; by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun u _ =>
    Finset.sum_nonneg (fun v _ => Nat.cast_nonneg _)))

theorem targetDirectionGroup_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n)
    (d : Direction F) (t : F) :
    targetDirectionGroup data I U j d t ≤ (D : ℝ) ^ 3 * Fintype.card F := by
  have hcount : (I.filter (fun i => d ∈ data.dirs i)).card ≤ D := by
    refine (Finset.card_le_card ?_).trans (hdata.2.2.2 d)
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  calc
    _ ≤ (D : ℝ) * ((D : ℝ) * ((D : ℝ) * Fintype.card F)) := by
      apply sum_le_of_card_le _ D _ _ hcount (by positivity)
      intro i hi
      apply sum_le_of_card_le _ D _ _ (hdata.2.1 i) (by positivity)
      intro u hu
      apply sum_le_of_card_le _ D _ _ (hdata.2.1 j) (Nat.cast_nonneg _)
      intro v hv
      exact_mod_cast sliceCount_le_card_field (U i) d (t + projection d (v - u))
    _ = _ := by ring

theorem targetLoss_eq_sum_groups (data : Data F n) (I : Finset (Fin n))
    (U : Fin n → Finset (Point F)) (j : Fin n) (x : Point F) :
    targetLoss data I U j x =
      ∑ d ∈ I.biUnion data.dirs, targetDirectionGroup data I U j d (projection d x) := let _ := instFintypeF; by
  classical
  symm
  unfold targetDirectionGroup
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hfilter : (I.biUnion data.dirs).filter (fun d => d ∈ data.dirs i) =
      data.dirs i := by
    ext d
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun hd => ⟨Finset.mem_biUnion.mpr ⟨i, hi, hd⟩, hd⟩⟩
  rw [← Finset.sum_filter, hfilter]
  rfl

theorem variance_targetLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (targetLoss data I U j) ≤
      (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 := by
  let mu := FiniteLaw.uniform (Point F)
  let S := I.biUnion data.dirs
  have hS : S.card ≤ I.card * D := by
    refine Finset.card_biUnion_le.trans ?_
    calc
      (∑ i ∈ I, (data.dirs i).card) ≤ ∑ _i ∈ I, D :=
        Finset.sum_le_sum (fun i _ => hdata.2.2.1 i)
      _ = I.card * D := by simp
  have heq : targetLoss data I U j = fun x =>
      ∑ d ∈ S, targetDirectionGroup data I U j d (projection d x) := by
    funext x
    exact targetLoss_eq_sum_groups data I U j x
  rw [heq]
  calc
    _ = ∑ d ∈ S, mu.variance (fun x =>
        targetDirectionGroup data I U j d (projection d x)) := by
      apply mu.variance_sum_of_pairwise_covariance_zero
      intro d hd e he hde
      exact covariance_uniform_projection d e hde
        (targetDirectionGroup data I U j d) (targetDirectionGroup data I U j e)
    _ ≤ ∑ _d ∈ S, ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      exact mu.variance_le_sq_of_bounds _
        (fun x => targetDirectionGroup_nonneg data I U j d (projection d x))
        (fun x => targetDirectionGroup_le D data hdata I U j d (projection d x))
    _ = (S.card : ℝ) * ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 := by simp
    _ ≤ ((I.card * D : ℕ) : ℝ) * ((D : ℝ) ^ 3 * Fintype.card F) ^ 2 :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (sq_nonneg _)
    _ = _ := by simp only [Nat.cast_mul]; ring

theorem variance_entryLoss_le (D : ℕ) (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (U : Fin n → Finset (Point F)) (j : Fin n) :
    (FiniteLaw.uniform (Point F)).variance (entryLoss data I U j) ≤
      2 * (D : ℝ) ^ 7 * I.card * (Fintype.card F : ℝ) ^ 2 +
        2 * (D : ℝ) ^ 5 * I.card * sourceEnergy data I U j := by
  have ht := variance_targetLoss_le D data hdata I U j
  have hs := variance_sourceLoss_le D data hdata I U j
  have hsum := (FiniteLaw.uniform (Point F)).variance_add_le
    (targetLoss data I U j) (sourceLoss data I U j)
  change (FiniteLaw.uniform (Point F)).variance
    (fun x => targetLoss data I U j x + sourceLoss data I U j x) ≤ _
  linarith

end RyserCoveringCounterexample.Selection

end

end OAI
