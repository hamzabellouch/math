import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorGraph
import OAI.MathematicalPhysics.ContinuumCoulomb.ManyBody.MediatorScaleBounds

namespace OAI

/-! The three actual mediator stages. Only the original central bonds
survive the last subdivision; each original spoke becomes a nine-link
path, giving eighteen new spins and nineteen positive bonds per edge. -/

namespace ContinuumCoulomb.MediatorIteration
open Matrix MediatorGraph
open scoped BigOperators Kronecker InnerProductSpace

structure Bonds (n r : ℕ) where
  left : Fin r → Fin n
  right : Fin r → Fin n
  weight : Fin r → ℚ

def Bonds.NoLoops {n r : ℕ} (F : Bonds n r) : Prop := ∀ e, F.left e ≠ F.right e

noncomputable def Bonds.matrix {n r : ℕ} (F : Bonds n r) :
    Matrix (SourceSpinBasis n) (SourceSpinBasis n) ℂ :=
  sourceGraphMatrix n r F.left F.right (fun e => (F.weight e : ℝ))

def empty (n : ℕ) : Bonds n 0 where
  left := Fin.elim0
  right := Fin.elim0
  weight := Fin.elim0

def lift {n q : ℕ} (r : ℕ) (F : Bonds n q) : Bonds (n + r * 2) q where
  left e := old n r (F.left e)
  right e := old n r (F.right e)
  weight := F.weight

def central (n r : ℕ) (Delta : ℚ) : Bonds (n + r * 2) r where
  left e := fresh n r e 0
  right e := fresh n r e 1
  weight _ := Delta

def spokes {n r : ℕ} (F : Bonds n r) (member : Fin r → Fin 2)
    (amplitude : Fin r → ℚ) : Bonds (n + r * 2) (r * 2) where
  left a := old n r (if (finProdFinEquiv.symm a).2 = 0 then
    F.left (finProdFinEquiv.symm a).1 else F.right (finProdFinEquiv.symm a).1)
  right a := fresh n r (finProdFinEquiv.symm a).1
    (if (finProdFinEquiv.symm a).2 = 0 then 0 else member (finProdFinEquiv.symm a).1)
  weight a := amplitude (finProdFinEquiv.symm a).1

def join {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) : Bonds n (q + r) where
  left a := Sum.elim F.left K.left (finSumFinEquiv.symm a)
  right a := Sum.elim F.right K.right (finSumFinEquiv.symm a)
  weight a := Sum.elim F.weight K.weight (finSumFinEquiv.symm a)

theorem empty_noLoops (n : ℕ) : (empty n).NoLoops := by intro e; exact Fin.elim0 e

theorem lift_noLoops {n q : ℕ} (r : ℕ) (F : Bonds n q) (hF : F.NoLoops) :
    (lift r F).NoLoops := by
  intro e h
  exact hF e (old_injective n r h)

theorem central_noLoops (n r : ℕ) (Delta : ℚ) : (central n r Delta).NoLoops := by
  intro e h
  have hpair := fresh_injective n r (a₁ := (e, 0)) (a₂ := (e, 1)) h
  have := congrArg Prod.snd hpair
  norm_num at this

theorem spokes_noLoops {n r : ℕ} (F : Bonds n r) (member : Fin r → Fin 2)
    (amplitude : Fin r → ℚ) : (spokes F member amplitude).NoLoops := by
  intro a
  exact old_ne_fresh n r _ _ _

theorem join_noLoops {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (hF : F.NoLoops) (hK : K.NoLoops) : (join F K).NoLoops := by
  intro a
  obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective a
  cases b with
  | inl e => simpa [join] using hF e
  | inr e => simpa [join] using hK e

theorem join_matrix {n q r : ℕ} (F : Bonds n q) (K : Bonds n r) :
    (join F K).matrix = F.matrix + K.matrix := by
  unfold Bonds.matrix sourceGraphMatrix
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, join, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

theorem empty_matrix (n : ℕ) : (empty n).matrix = 0 := by
  simp [Bonds.matrix, sourceGraphMatrix]

theorem stage_matrix_split {n q r : ℕ} (K : Bonds n q) (F : Bonds n r)
    (member : Fin r → Fin 2) (Delta : ℚ) (amplitude : Fin r → ℚ) :
    stageMatrix n q r K.left K.right K.weight F.left F.right member Delta amplitude =
      (lift r K).matrix + (central n r Delta).matrix + (spokes F member amplitude).matrix := by
  unfold stageMatrix sourceGraphMatrix
  rw [← (edgeEquiv q r).sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, stageLeft, stageRight, stageWeight,
    Equiv.symm_apply_apply]
  unfold Bonds.matrix sourceGraphMatrix
  rw [← (finProdFinEquiv : Fin r × Fin 2 ≃ Fin (r * 2)).sum_comp]
  simp only [Fintype.sum_prod_type, spokes, Equiv.symm_apply_apply, lift, central]
  push_cast
  abel

def secondBound (r W G : ℕ) : ℕ := MediatorParameters.secondWeight r W G
def thirdBound (r W G : ℕ) : ℕ := MediatorParameters.thirdWeight r W G

def member (J : ℚ) : Fin 2 := if J < 0 then 0 else 1

theorem member_eq (J : ℚ) : member J = signedMediatorMember (J : ℝ) := by
  simp only [member, signedMediatorMember, Rat.cast_lt_zero]

def deltaOne (r W G : ℕ) : ℕ := MediatorParameters.delta r W G
def deltaTwo (r W G : ℕ) : ℕ := MediatorParameters.delta (r * 2) (secondBound r W G) G
def deltaThree (r W G : ℕ) : ℕ :=
  MediatorParameters.delta (r * 2 + r * 2 * 2) (thirdBound r W G) G

def firstCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) : Bonds (n + r * 2) r :=
  central n r (deltaOne r W G)

def firstSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) : Bonds (n + r * 2) (r * 2) :=
  spokes F (fun e => member (F.weight e))
    (fun e => MediatorParameters.spoke r W G (F.weight e))

def secondCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2) := central _ _ (deltaTwo r W G)

def secondSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2 * 2) :=
  spokes (firstSpokes F W G) (fun e => member ((firstSpokes F W G).weight e))
    (fun e => MediatorParameters.spoke (r * 2) (secondBound r W G) G ((firstSpokes F W G).weight e))

def secondPaths {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r * 2 + r * 2 * 2) :=
  join (secondCentral F W G) (secondSpokes F W G)

def retainedCentral {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) r := lift (r * 2) (firstCentral F W G)

def thirdCentral {n r : ℕ} (_F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (r * 2 + r * 2 * 2) :=
  central _ _ (deltaThree r W G)

def thirdSpokes {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) ((r * 2 + r * 2 * 2) * 2) :=
  spokes (secondPaths F W G) (fun e => member ((secondPaths F W G).weight e))
    (fun e => MediatorParameters.spoke (r * 2 + r * 2 * 2) (thirdBound r W G) G
      ((secondPaths F W G).weight e))

def finalGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2)
      (r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2)) :=
  join (lift (r * 2 + r * 2 * 2) (retainedCentral F W G))
    (join (thirdCentral F W G) (thirdSpokes F W G))

def firstGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2) (r + r * 2) := join (firstCentral F W G) (firstSpokes F W G)

def secondGraph {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    Bonds (n + r * 2 + r * 2 * 2) (r + (r * 2 + r * 2 * 2)) :=
  join (retainedCentral F W G) (secondPaths F W G)

theorem final_vertex_count (n r : ℕ) :
    n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2 = n + 18 * r := by omega

theorem final_edge_count (r : ℕ) :
    r + ((r * 2 + r * 2 * 2) + (r * 2 + r * 2 * 2) * 2) = 19 * r := by omega

theorem finalGraph_noLoops {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (finalGraph F W G).NoLoops := by
  exact join_noLoops _ _
    (lift_noLoops _ _ (lift_noLoops _ _ (central_noLoops _ _ _)))
    (join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _))

theorem join_weight_property {n q r : ℕ} (F : Bonds n q) (K : Bonds n r)
    (P : ℚ → Prop) (hF : ∀ e, P (F.weight e)) (hK : ∀ e, P (K.weight e)) :
    ∀ e, P ((join F K).weight e) := by
  intro e
  obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective e
  cases a with
  | inl a => simpa [join] using hF a
  | inr a => simpa [join] using hK a

theorem firstSpokes_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (secondBound r W G : ℝ) ≤ |((firstSpokes F W G).weight e : ℝ)| ∧
      |((firstSpokes F W G).weight e : ℝ)| ≤ secondBound r W G := by
  intro e
  exact MediatorParameters.second_spoke_bounds r hW hG (hJ _) (hJl _)

theorem secondPaths_bounds {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 1 / (thirdBound r W G : ℝ) ≤ |((secondPaths F W G).weight e : ℝ)| ∧
      |((secondPaths F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  apply join_weight_property _ _
    (fun J => 1 / (thirdBound r W G : ℝ) ≤ |(J : ℝ)| ∧ |(J : ℝ)| ≤ thirdBound r W G)
  · intro e
    have h := MediatorParameters.third_central_bounds r (W := W) hG
    change 1 / (thirdBound r W G : ℝ) ≤ |(deltaTwo r W G : ℝ)| ∧
      |(deltaTwo r W G : ℝ)| ≤ thirdBound r W G
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ deltaTwo r W G)]
    simpa only [deltaTwo, secondBound, thirdBound, Nat.mul_comm] using h
  · intro e
    have hbound := firstSpokes_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1
    have h := MediatorParameters.third_spoke_bounds r hG hbound.2 hbound.1
    simpa only [secondSpokes, spokes, secondBound, thirdBound, Nat.mul_comm] using h

theorem firstCentral_weight_sum {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    (∑ e, |((firstCentral F W G).weight e : ℝ)|) = r * (deltaOne r W G : ℝ) := by
  simp [firstCentral, central]

theorem firstCentral_bound {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    3 * ∑ e, |((firstCentral F W G).weight e : ℝ)| ≤ secondBound r W G := by
  rw [firstCentral_weight_sum]
  rw [← mul_assoc]
  have h : 3 * r * deltaOne r W G ≤ secondBound r W G := by
    unfold deltaOne secondBound MediatorParameters.secondWeight
    omega
  exact_mod_cast h

theorem retainedCentral_bound {n r : ℕ} (F : Bonds n r) (W G : ℕ) :
    3 * ∑ e, |((retainedCentral F W G).weight e : ℝ)| ≤ thirdBound r W G := by
  change 3 * ∑ e, |((firstCentral F W G).weight e : ℝ)| ≤ thirdBound r W G
  rw [firstCentral_weight_sum]
  rw [← mul_assoc]
  have h : 3 * r * deltaOne r W G ≤ thirdBound r W G := by
    unfold deltaOne thirdBound MediatorParameters.thirdWeight
    omega
  exact_mod_cast h

def offset {n r : ℕ} (F : Bonds n r) (W G : ℕ) : ℚ :=
  (3 * r * deltaOne r W G + 3 * ∑ e, |F.weight e|) +
    (3 * (r * 2) * deltaTwo r W G + 3 * ∑ e, |(firstSpokes F W G).weight e|) +
    (3 * (r * 2 + r * 2 * 2) * deltaThree r W G + 3 * ∑ e, |(secondPaths F W G).weight e|)

theorem lift_empty_matrix (n r : ℕ) : (lift r (empty n)).matrix = 0 := by
  simp [Bonds.matrix, sourceGraphMatrix]

theorem family_stage_bound {n q r W G : ℕ} (K : Bonds n q) (F : Bonds n r)
    (hK : K.NoLoops) (hF : F.NoLoops) (hW : 0 < W) (hG : 0 < G)
    (hKweight : 3 * ∑ e, |(K.weight e : ℝ)| ≤ W)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2)
        ((lift r K).matrix + (central n r (MediatorParameters.delta r W G)).matrix +
          (spokes F (fun e => member (F.weight e))
            (fun e => MediatorParameters.spoke r W G (F.weight e))).matrix) +
      3 * r * MediatorParameters.delta r W G + 3 * ∑ e, |(F.weight e : ℝ)| -
        sourceMatrixBottom n (K.matrix + F.matrix)| ≤ 1 / (512 * (G : ℝ)) := by
  have h := MediatorGraph.stage_bottom n q r hW hG K.left K.right hK K.weight hKweight
    F.left F.right hF F.weight hJ hJl
  rw [stage_matrix_split] at h
  simpa only [member_eq, Bonds.matrix] using h

theorem first_stage {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2) (firstGraph F W G).matrix +
      3 * r * deltaOne r W G + 3 * ∑ e, |(F.weight e : ℝ)| -
        sourceMatrixBottom n F.matrix| ≤ 1 / (512 * (G : ℝ)) := by
  have h := family_stage_bound (empty n) F (empty_noLoops n) hF hW hG (by simp) hJ hJl
  rw [lift_empty_matrix, empty_matrix, zero_add, zero_add] at h
  simpa only [firstGraph, join_matrix, firstCentral, firstSpokes, deltaOne] using h

theorem second_stage {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2) (secondGraph F W G).matrix +
      3 * (r * 2) * deltaTwo r W G + 3 * ∑ e, |((firstSpokes F W G).weight e : ℝ)| -
        sourceMatrixBottom (n + r * 2) (firstGraph F W G).matrix| ≤ 1 / (512 * (G : ℝ)) := by
  have hW2 : 0 < secondBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.secondWeight_two_le r W G)
  have hbounds := firstSpokes_bounds F hW hG hJ hJl
  have h := family_stage_bound (firstCentral F W G) (firstSpokes F W G)
    (central_noLoops _ _ _) (spokes_noLoops _ _ _) hW2 hG
    (firstCentral_bound F W G) (fun e => (hbounds e).2) (fun e => (hbounds e).1)
  simpa only [secondGraph, firstGraph, join_matrix, retainedCentral, secondPaths,
    secondCentral, secondSpokes, deltaTwo, add_assoc, Nat.cast_mul, Nat.cast_ofNat] using h

theorem third_stage {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (finalGraph F W G).matrix +
      3 * (r * 2 + r * 2 * 2) * deltaThree r W G +
        3 * ∑ e, |((secondPaths F W G).weight e : ℝ)| -
      sourceMatrixBottom (n + r * 2 + r * 2 * 2) (secondGraph F W G).matrix| ≤
        1 / (512 * (G : ℝ)) := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hbounds := secondPaths_bounds F hW hG hJ hJl
  have h := family_stage_bound (retainedCentral F W G) (secondPaths F W G)
    (lift_noLoops _ _ (central_noLoops _ _ _))
    (join_noLoops _ _ (central_noLoops _ _ _) (spokes_noLoops _ _ _))
    hW3 hG (retainedCentral_bound F W G) (fun e => (hbounds e).2) (fun e => (hbounds e).1)
  simpa only [finalGraph, secondGraph, join_matrix, thirdCentral, thirdSpokes,
    deltaThree, add_assoc, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] using h

/-- Three concrete rational graph stages give the promised finite-spin
energy comparison, including all three exact rational scalar offsets. -/
theorem three_stage_bottom {n r W G : ℕ} (F : Bonds n r) (hF : F.NoLoops)
    (hW : 0 < W) (hG : 0 < G) (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W)
    (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    |sourceMatrixBottom (n + r * 2 + r * 2 * 2 + (r * 2 + r * 2 * 2) * 2) (finalGraph F W G).matrix +
      (offset F W G : ℝ) - sourceMatrixBottom n F.matrix| ≤ 3 / (512 * (G : ℝ)) := by
  have h1 := first_stage F hF hW hG hJ hJl
  have h2 := second_stage F hW hG hJ hJl
  have h3 := third_stage F hW hG hJ hJl
  have h12 := (abs_add_le _ _).trans (add_le_add h2 h1)
  have h123 := (abs_add_le _ _).trans (add_le_add h3 h12)
  convert h123 using 1
  · congr 1
    simp only [offset, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat,
      Rat.cast_sum, Rat.cast_abs]
    ring
  · ring

theorem finalGraph_positive {n r W G : ℕ} (F : Bonds n r) (hW : 0 < W) (hG : 0 < G)
    (hJ : ∀ e, |(F.weight e : ℝ)| ≤ W) (hJl : ∀ e, 1 / (W : ℝ) ≤ |(F.weight e : ℝ)|) :
    ∀ e, 0 < (finalGraph F W G).weight e := by
  have hW3 : 0 < thirdBound r W G := lt_of_lt_of_le (by norm_num)
    (MediatorParameters.thirdWeight_two_le r W G)
  have hdelta1 : 0 < deltaOne r W G := by
    unfold deltaOne MediatorParameters.delta
    exact pow_pos (MediatorParameters.scale_pos r hW hG) 2
  have hdelta3 : 0 < deltaThree r W G := by
    unfold deltaThree MediatorParameters.delta
    exact pow_pos (MediatorParameters.scale_pos _ hW3 hG) 2
  apply join_weight_property _ _ (fun J => 0 < J)
  · intro e
    change (0 : ℚ) < deltaOne r W G
    exact_mod_cast hdelta1
  · apply join_weight_property _ _ (fun J => 0 < J)
    · intro e
      change (0 : ℚ) < deltaThree r W G
      exact_mod_cast hdelta3
    · intro e
      exact MediatorParameters.spoke_pos _ hW3 hG
        (secondPaths_bounds F hW hG hJ hJl (finProdFinEquiv.symm e).1).1

end ContinuumCoulomb.MediatorIteration

end OAI
