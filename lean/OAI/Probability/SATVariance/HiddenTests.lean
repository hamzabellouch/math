import OAI.Probability.SATVariance.PairEvolution

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory

namespace RandomKSAT

open scoped Classical ENNReal

def familyKill.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : ℝ :=
  if ∃ b ∈ S, ∀ i, Satisfies (cs i) b then 0 else 1

lemma familyKill_nonneg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : 0 ≤ familyKill S cs := by
  unfold familyKill
  split <;> norm_num

lemma familyKill_le_one.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) : familyKill S cs ≤ 1 := by
  unfold familyKill
  split <;> norm_num

lemma familyKill_residual.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι]
    (S : Finset (Assignment u)) (cs : ι → Clause u s) :
    familyKill S cs = 1-alive u (residual S cs) := by
  have he : (residual S cs).Nonempty ↔ ∃ b ∈ S, ∀ i, Satisfies (cs i) b := by
    simp only [Finset.Nonempty, residual, Finset.mem_filter]
  unfold familyKill alive
  simp only [he]
  split <;> norm_num

lemma familyKill_equiv.{u_1, u_2} {u s : ℕ} {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (S : Finset (Assignment u)) (cs : κ → Clause u s) (e : ι ≃ κ) :
    familyKill S (fun i => cs (e i)) = familyKill S cs := by
  have he : (∃ b ∈ S, ∀ i, Satisfies (cs (e i)) b) ↔ ∃ b ∈ S, ∀ i, Satisfies (cs i) b := by
    constructor
    · rintro ⟨b,hb,hi⟩
      exact ⟨b,hb, fun j => by simpa using hi (e.symm j)⟩
    · rintro ⟨b,hb,hi⟩
      exact ⟨b,hb, fun j => hi (e j)⟩
  simp only [familyKill, he]

lemma familyKill_avg_fin {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) (m : ℕ) :
    favg (fun cs : Fin m → Clause u s => familyKill S cs) = blockKill u s S m := by
  let := clause_nonempty u s hsu
  simp_rw [familyKill_residual]
  rw [favg_sub, favg_const, blockKill_iterate hsu, clauseStep_iterate_avg]

lemma familyKill_avg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι] (hsu : s ≤ u)
    (S : Finset (Assignment u)) :
    favg (fun cs : ι → Clause u s => familyKill S cs) = blockKill u s S (Fintype.card ι) := by
  let e := (Fintype.equivFin ι).symm.arrowCongr (Equiv.refl (Clause u s))
  rw [← favg_equiv e]
  have he (cs : Fin (Fintype.card ι) → Clause u s) :
      familyKill S (e cs) = familyKill S cs :=
    familyKill_equiv S cs (Fintype.equivFin ι)
  simp_rw [he]
  exact familyKill_avg_fin hsu S _

lemma blockKill_mono_length {u s : ℕ} (hsu : s ≤ u) (S : Finset (Assignment u)) :
    Monotone (blockKill u s S) := by
  let := streamLaw_probability u s hsu
  intro m d hmd
  unfold blockKill
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono
  intro ω hm hd
  rcases hd with ⟨b,hb,ht⟩
  exact hm ⟨b,hb,fun i hi => ht i (lt_of_lt_of_le hi hmd)⟩

lemma restricted_familyKill_avg.{u_1} {u s : ℕ} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (hsu : s ≤ u) (S : Finset (Assignment u)) (A : Finset ι) :
    favg (fun cs : ι → Clause u s => familyKill S (fun i : A => cs i)) =
      blockKill u s S A.card := by
  let := clause_nonempty u s hsu
  rw [favg_pi_restrict (fun i => i ∈ A) (familyKill S)]
  convert (familyKill_avg (ι := A) hsu S) using 1
  · congr 1
    exact Subsingleton.elim _ _
  · rw [Fintype.card_coe]

def testIndices {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (m : ℕ) (j : Fin k) : Finset (Fin M) :=
  Finset.univ.filter fun i => i.val < m ∧ TestAt a (env i) j

lemma forcedPrefix_familyKill {u k M : ℕ} (a : Assignment k) (env : Fin M → RootData u k)
    (o : Fin M → Clause u k) (ys : Fin k → Fin M → Clause u (k-1)) (m : ℕ)
    (hforced : ∀ x ∈ pairPrefix Finset.univ
      (fun i => refreshData a (env i) (o i, fun j => ys j i)) m, x.1 = a)
    (j : Fin k) (hj : Available a env j) :
    familyKill (fibrePrefix a env o m) (fun i : testIndices a env m j => ys j i) = 1 := by
  unfold familyKill
  rw [ite_eq_right]
  rintro ⟨b,hb,ht⟩
  apply forcedPrefix_testKills a env o ys m hforced j hj
  refine ⟨b,hb,fun i hi hit => ?_⟩
  exact ht ⟨i, by simp [testIndices, hi, hit]⟩

lemma prod_filter_indicator.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι] (A : Finset ι) (q : ℝ) :
    (∏ j : ι, if j ∈ A then q else 1) = q^A.card := by
  classical
  rw [← Finset.prod_filter]
  simp

lemma forcedPrefix_probability {u k M d : ℕ} (hku : k ≤ u) (a : Assignment k)
    (env : Fin M → RootData u k) (o : Fin M → Clause u k) (m : ℕ)
    (J : Finset (Fin k)) (hJ : ∀ j ∈ J, Available a env j)
    (hd : ∀ j, (testIndices a env m j).card ≤ d) :
    favg (fun ys : Fin k → Fin M → Clause u (k-1) =>
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m)) ≤
          alive u (fibrePrefix a env o m) * blockKill u (k-1) (fibrePrefix a env o m) d ^ J.card := by
  let := clause_nonempty u (k-1) (by omega)
  let S := fibrePrefix a env o m
  let q := blockKill u (k-1) S d
  let F (j : Fin k) (w : Fin M → Clause u (k-1)) : ℝ :=
    if j ∈ J then familyKill S (fun i : testIndices a env m j => w i) else 1
  have hF : ∀ j w, 0 ≤ F j w := by
    intro j w
    dsimp only [F]
    split
    · exact familyKill_nonneg _ _
    · norm_num
  have hp (ys : Fin k → Fin M → Clause u (k-1)) :
      forcedReward a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m) ≤
          alive u S * ∏ j, F j (ys j) := by
    unfold forcedReward
    split_ifs with h
    · have hprod : (∏ j, F j (ys j)) = 1 := by
        apply Finset.prod_eq_one
        intro j _
        dsimp only [F]
        split_ifs with hj
        · exact forcedPrefix_familyKill a env o ys m h.2 j (hJ j hj)
        · rfl
      rw [hprod, mul_one]
      have hh := forcedReward_le_alive a (pairPrefix Finset.univ
        (fun i => refreshData a (env i) (o i, fun j => ys j i)) m)
      rw [fibre_pairPrefix_refresh] at hh
      simpa only [forcedReward, ite_eq_left h] using hh
    · exact mul_nonneg (alive_nonneg _ _) (Finset.prod_nonneg fun j _ => hF j _)
  have havg (j : Fin k) : favg (F j) ≤ if j ∈ J then q else 1 := by
    by_cases hj : j ∈ J
    · simp only [F, ite_eq_left hj]
      rw [restricted_familyKill_avg (by omega)]
      exact blockKill_mono_length (by omega) S (hd j)
    · simp only [F, ite_eq_right hj, favg_const, le_refl]
  calc
    _ ≤ favg (fun ys : Fin k → Fin M → Clause u (k-1) => alive u S * ∏ j, F j (ys j)) :=
      favg_mono hp
    _ = alive u S * ∏ j, favg (F j) := by rw [favg_mul, favg_pi_product]
    _ ≤ alive u S * ∏ j : Fin k, if j ∈ J then q else 1 := by
      apply mul_le_mul_of_nonneg_left _ (alive_nonneg _ _)
      exact Finset.prod_le_prod₀ (fun j _ => favg_nonneg (hF j)) (fun j _ => havg j)
    _ = _ := by rw [prod_filter_indicator]

end RandomKSAT

end

end OAI
