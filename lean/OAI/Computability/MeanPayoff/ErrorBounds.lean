import OAI.Computability.MeanPayoff.Traversal

namespace OAI

section

namespace MeanPayoff
namespace RandomTree

theorem map_bind {α β γ : Type} (t : RandomTree α) (f : α → RandomTree β) (g : β → γ) :
    (t.bind f).map g = t.bind (fun a => (f a).map g) := by
  induction t with
  | leaf a => rfl
  | coin l r il ir => simpa only [map, bind] using congrArg₂ coin il ir

theorem failure_and_metadata {α : Type} (t : RandomTree α) (A B : α → Prop) (h : t.All A) :
    t.probability (fun a => ¬(A a ∧ B a)) ≤ t.probability (fun a => ¬B a) := by
  apply probability_mono_all
  exact all_mono t h (fun a ha hf hb => hf ⟨ha, hb⟩)

end RandomTree

def nodeError (n Bmax : ℕ) : ℚ :=
  (2 * (n : ℚ) * Bmax + globalListBound n Bmax + 3) * epsilon n Bmax

theorem nodeError_nonneg (n Bmax : ℕ) : 0 ≤ nodeError n Bmax := by
  unfold nodeError
  exact mul_nonneg (by positivity) (epsilon_nonneg _ _)

theorem orientStage_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : HighAccuracy G P _ up δ) (hlo : HighAccuracy G P _ lo δ)
    (y : Vec (Fin G.n)) (hy : AdmissibleSub (operator G) I.a I.b y P)
    (hc : (I.C : ℤ) < deviation G y I.a → (4 / 5) * P.k < mass P.alpha (highCore I y)) :
    ((orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).bind
      (fun O => finishChoice G P hR lower I hB O up lo)).probability (fun p => ¬y ≤ p.val) ≤
      ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ := by
  let t := orientPlus (orient G P hR lower I) (globalJ G.n Bmax)
  let A := fun O : Orientation P => O.exceptions.length ≤ globalListBound G.n Bmax
  let B := fun O : Orientation P => (I.C : ℤ) < deviation G y I.a → HighAlternative I P y O
  have he := epsilon_nonneg G.n Bmax
  have ht : t.probability (fun O => ¬(A O ∧ B O)) ≤ epsilon G.n Bmax := by
    apply (RandomTree.failure_and_metadata t A B (orientPlus_length G P hR lower I)).trans
    apply RandomTree.imp_error t _ _ he
    intro hd
    exact orientPlus_high G P hR lower hl I y hy (hc hd)
  apply le_trans (RandomTree.bind_error t (fun O => finishChoice G P hR lower I hB O up lo)
    (fun O => A O ∧ B O) (fun p : BoxVector I => ¬y ≤ p.val)
    (ε := (globalListBound G.n Bmax : ℚ) * epsilon G.n Bmax + δ)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) he) hδ) ht ?_) (by ring_nf; rfl)
  intro O hO
  apply (finishChoice_high G P hR lower hl I hB O up lo hδ hup hlo y hy hO.2).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hO.1) he) le_rfl

theorem orientStage_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (hB : 128 * globalS Bmax < I.width)
    (up : RandomTree (BoxVector (I.capHigh I.C I.C_positive (I.C_smaller hB).le)))
    (lo : RandomTree (BoxVector (I.capLow I.C I.C_positive (I.C_smaller hB).le)))
    {δ : ℚ} (hδ : 0 ≤ δ)
    (hup : LowAccuracy G P _ up δ) (hlo : LowAccuracy G P _ lo δ)
    (z : Vec (Fin G.n)) (hz : AdmissibleSuper (operator G) I.a I.b z P)
    (hc : (I.C : ℤ) < deviation G I.b z → (4 / 5) * P.m < mass P.beta (lowCore I z)) :
    ((orientPlus (orient G P hR lower I) (globalJ G.n Bmax)).bind
      (fun O => finishChoice G P hR lower I hB O up lo)).probability (fun p => ¬p.val ≤ z) ≤
      ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ := by
  let t := orientPlus (orient G P hR lower I) (globalJ G.n Bmax)
  let A := fun O : Orientation P => O.exceptions.length ≤ globalListBound G.n Bmax
  let B := fun O : Orientation P => (I.C : ℤ) < deviation G I.b z → LowAlternative I P z O
  have he := epsilon_nonneg G.n Bmax
  have ht : t.probability (fun O => ¬(A O ∧ B O)) ≤ epsilon G.n Bmax := by
    apply (RandomTree.failure_and_metadata t A B (orientPlus_length G P hR lower I)).trans
    apply RandomTree.imp_error t _ _ he
    intro hd
    exact orientPlus_low G P hR lower hl I z hz (hc hd)
  apply le_trans (RandomTree.bind_error t (fun O => finishChoice G P hR lower I hB O up lo)
    (fun O => A O ∧ B O) (fun p : BoxVector I => ¬p.val ≤ z)
    (ε := (globalListBound G.n Bmax : ℚ) * epsilon G.n Bmax + δ)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _) he) hδ) ht ?_) (by ring_nf; rfl)
  intro O hO
  apply (finishChoice_low G P hR lower hl I hB O up lo hδ hup hlo z hz hO.2).trans
  exact add_le_add (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hO.1) he) le_rfl



theorem node_error_step {n Bmax : ℕ} (I : SolveBox n Bmax) :
    (2 * (volume I.b I.a : ℚ) + 2) * epsilon n Bmax +
      (((globalListBound n Bmax : ℚ) + 1) * epsilon n Bmax +
        ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax) ≤ (I.width : ℚ) * nodeError n Bmax := by
  have he := epsilon_nonneg n Bmax
  have hv : (volume I.b I.a : ℚ) ≤ (n : ℚ) * Bmax := by exact_mod_cast I.volume_le
  have hp : ((I.width - 1 : ℕ) : ℚ) + 1 = I.width := by
    exact_mod_cast Nat.sub_add_cancel I.positive
  calc
    _ = (2 * (volume I.b I.a : ℚ) + globalListBound n Bmax + 3) * epsilon n Bmax +
        ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax := by ring
    _ ≤ nodeError n Bmax + ((I.width - 1 : ℕ) : ℚ) * nodeError n Bmax := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_right (by linarith only [hv]) he
    _ = _ := by rw [← hp]; ring

theorem solveWidth_high (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (y : Vec (Fin G.n))
    (hy : AdmissibleSub (operator G) I.a I.b y P) :
    (solveWidth G P hR lower I).probability (fun p => ¬y ≤ p.val) ≤
      (I.width : ℚ) * nodeError G.n Bmax := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · have hc : y ≤ (I.exactVector G).val := box_comparison G hy.1 (basic_spec G I.a I.b I.ordered).2.1
    rw [solveWidth, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc)]
    exact mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
  · have hB : 128 * globalS Bmax < I.width := lt_of_not_ge hsmall
    rw [solveWidth, dite_eq_right hsmall]
    dsimp only
    let δ : ℚ := ((I.width - 1 : ℕ) : ℚ) * nodeError G.n Bmax
    have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
    have he := epsilon_nonneg G.n Bmax
    apply le_trans (RandomTree.bind_error (tighten P hR lower I hB) _
      (TightHigh G P y) (fun p : BoxVector I => ¬y ≤ p.val)
      (ε := ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ)
      (add_nonneg (mul_nonneg (by positivity) he) hδ)
      (tighten_high G P hR lower hl I hB y hy) ?_) (node_error_step I)
    intro T hT
    obtain ⟨u, hyu, hu, hcore⟩ := hT
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by change 128 * globalS Bmax < T.box.width; rw [T.width_eq]; exact hB
    let up := solveWidth G P hR lower (K.capHigh K.C K.C_positive (K.C_smaller hK).le)
    let lo := solveWidth G P hR lower (K.capLow K.C K.C_positive (K.C_smaller hK).le)
    have hc : K.C ≤ I.width - 1 := by have hh := K.C_smaller hK; have hw := T.width_eq; dsimp [K] at hh ⊢; omega
    have hup : HighAccuracy G P _ up δ := by
      intro v hv
      apply (solveWidth_high G P hR lower hl (K.capHigh K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    have hlo : HighAccuracy G P _ lo δ := by
      intro v hv
      apply (solveWidth_high G P hR lower hl (K.capLow K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    change ((orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind
      (fun O => (finishChoice G P hR lower K hK O up lo).map T.include)).probability
        (fun p => ¬y ≤ p.val) ≤ _
    rw [← RandomTree.map_bind]
    apply RandomTree.map_error _ T.include (fun p : BoxVector K => u ≤ p.val) _
      (orientStage_high G P hR lower hl K hK up lo hδ hup hlo u hu hcore)
    intro p hp hf
    exact hf (hyu.trans hp)
termination_by I.width
decreasing_by
  all_goals
    change K.C < I.width
    rw [← T.width_eq]
    exact K.C_smaller hK



theorem solveWidth_low (G : Game) {Bmax : ℕ} (P : Budgets G.n) (hR : 1 ≤ P.parameter)
    (lower : LowerSolver (Bmax := Bmax) P) (hl : LowerComparisons G P lower)
    (I : SolveBox G.n Bmax) (z : Vec (Fin G.n))
    (hz : AdmissibleSuper (operator G) I.a I.b z P) :
    (solveWidth G P hR lower I).probability (fun p => ¬p.val ≤ z) ≤
      (I.width : ℚ) * nodeError G.n Bmax := by
  by_cases hsmall : I.width ≤ 128 * globalS Bmax
  · have hc : (I.exactVector G).val ≤ z := box_comparison G (basic_spec G I.a I.b I.ordered).1 hz.1
    rw [solveWidth, dite_eq_left hsmall, RandomTree.probability_leaf, ite_eq_right (not_not_intro hc)]
    exact mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
  · have hB : 128 * globalS Bmax < I.width := lt_of_not_ge hsmall
    rw [solveWidth, dite_eq_right hsmall]
    dsimp only
    let δ : ℚ := ((I.width - 1 : ℕ) : ℚ) * nodeError G.n Bmax
    have hδ : 0 ≤ δ := mul_nonneg (Nat.cast_nonneg _) (nodeError_nonneg _ _)
    have he := epsilon_nonneg G.n Bmax
    apply le_trans (RandomTree.bind_error (tighten P hR lower I hB) _
      (TightLow G P z) (fun p : BoxVector I => ¬p.val ≤ z)
      (ε := ((globalListBound G.n Bmax : ℚ) + 1) * epsilon G.n Bmax + δ)
      (add_nonneg (mul_nonneg (by positivity) he) hδ)
      (tighten_low G P hR lower hl I hB z hz) ?_) (node_error_step I)
    intro T hT
    obtain ⟨u, huz, hu, hcore⟩ := hT
    let K := T.box
    have hK : 128 * globalS Bmax < K.width := by change 128 * globalS Bmax < T.box.width; rw [T.width_eq]; exact hB
    let up := solveWidth G P hR lower (K.capHigh K.C K.C_positive (K.C_smaller hK).le)
    let lo := solveWidth G P hR lower (K.capLow K.C K.C_positive (K.C_smaller hK).le)
    have hc : K.C ≤ I.width - 1 := by have hh := K.C_smaller hK; have hw := T.width_eq; dsimp [K] at hh ⊢; omega
    have hup : LowAccuracy G P _ up δ := by
      intro v hv
      apply (solveWidth_low G P hR lower hl (K.capHigh K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    have hlo : LowAccuracy G P _ lo δ := by
      intro v hv
      apply (solveWidth_low G P hR lower hl (K.capLow K.C K.C_positive (K.C_smaller hK).le) v hv).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (nodeError_nonneg _ _)
    change ((orientPlus (orient G P hR lower K) (globalJ G.n Bmax)).bind
      (fun O => (finishChoice G P hR lower K hK O up lo).map T.include)).probability
        (fun p => ¬p.val ≤ z) ≤ _
    rw [← RandomTree.map_bind]
    apply RandomTree.map_error _ T.include (fun p : BoxVector K => p.val ≤ u) _
      (orientStage_low G P hR lower hl K hK up lo hδ hup hlo u hu hcore)
    intro p hp hf
    exact hf (hp.trans huz)
termination_by I.width
decreasing_by
  all_goals
    change K.C < I.width
    rw [← T.width_eq]
    exact K.C_smaller hK



theorem root_error_coefficient (n Bmax : ℕ) :
    Bmax * (2 * n * Bmax + globalListBound n Bmax + 3) * 16 ≤ 2 ^ globalJ n Bmax := by
  by_cases hB : Bmax = 0
  · simp [hB]
  have hb : 1 ≤ Bmax := by omega
  let s := globalS Bmax
  let k := s * (n + 1)
  have hs : 16 ≤ s := globalS_large Bmax
  have hsk : s ≤ k := by dsimp [k]; nlinarith
  have hk : 16 ≤ k := hs.trans hsk
  have hn : n ≤ k := by dsimp [k]; nlinarith
  have hg : globalG Bmax ≤ s := by
    have h := globalS_lower Bmax
    change 131072 * (globalG Bmax + 1) ≤ s at h
    omega
  have hclog : Nat.clog 2 (Bmax + 1) ≤ s := by unfold globalG at hg; omega
  have hBs : Bmax ≤ 2 ^ s :=
    (Nat.le_succ Bmax).trans ((Nat.clog_le_iff_le_pow (by norm_num)).mp hclog)
  have hk6 : k ^ 2 ≤ k ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hk7 : k ^ 2 ≤ k ^ 7 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hJ : globalJ n Bmax ≤ 3 * k ^ 6 := by
    have hpow : 1 ≤ k ^ 6 := Nat.one_le_pow _ _ (by omega)
    change 2 * k ^ 6 + 1 ≤ 3 * k ^ 6
    omega
  have hM : globalListBound n Bmax ≤ 9 * k ^ 7 := by
    have hfac : 2 * globalG Bmax + 3 ≤ 3 * k := by omega
    calc
      _ ≤ (3 * k ^ 6) * (3 * k) := Nat.mul_le_mul hJ hfac
      _ = 9 * k ^ 7 := by ring
  have hpoly : 2 * n + globalListBound n Bmax + 3 ≤ 10 * k ^ 7 := by
    have hx : 2 * n + 3 ≤ k ^ 7 := by nlinarith
    omega
  have hpowK : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
  have hten : 10 ≤ 2 ^ (3 * k) := by
    apply le_trans (show 10 ≤ 2 ^ 4 by norm_num)
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpolyExp : 10 * k ^ 7 ≤ 2 ^ (10 * k) := by
    calc
      _ ≤ 2 ^ (3 * k) * (2 ^ k) ^ 7 := Nat.mul_le_mul hten (Nat.pow_le_pow_left hpowK 7)
      _ = 2 ^ (10 * k) := by
        rw [← pow_mul, ← pow_add, show 3 * k + k * 7 = 10 * k by omega]
  have hN : Bmax * (2 * n * Bmax + globalListBound n Bmax + 3) ≤ 2 ^ (12 * k) := by
    calc
      _ ≤ Bmax ^ 2 * (2 * n + globalListBound n Bmax + 3) := by
        have hscale : Bmax * (globalListBound n Bmax + 3) ≤
            Bmax ^ 2 * (globalListBound n Bmax + 3) :=
          Nat.mul_le_mul_right _ (by nlinarith : Bmax ≤ Bmax ^ 2)
        nlinarith only [hscale]
      _ ≤ (2 ^ s) ^ 2 * (10 * k ^ 7) := Nat.mul_le_mul (Nat.pow_le_pow_left hBs 2) hpoly
      _ ≤ (2 ^ s) ^ 2 * 2 ^ (10 * k) := Nat.mul_le_mul_left _ hpolyExp
      _ = 2 ^ (s * 2 + 10 * k) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (12 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAbsorb : 12 * k + 4 ≤ globalJ n Bmax := by
    change 12 * k + 4 ≤ 2 * k ^ 6 + 1
    nlinarith
  calc
    _ ≤ 2 ^ (12 * k) * 16 := Nat.mul_le_mul_right 16 hN
    _ = 2 ^ (12 * k + 4) := by rw [pow_add]; rfl
    _ ≤ 2 ^ globalJ n Bmax := Nat.pow_le_pow_right (by norm_num) hAbsorb

theorem root_error_small (n Bmax : ℕ) : (Bmax : ℚ) * nodeError n Bmax ≤ 1 / 16 := by
  have h := root_error_coefficient n Bmax
  have hq : ((Bmax : ℚ) * (2 * n * Bmax + globalListBound n Bmax + 3)) * 16 ≤
      (2 : ℚ) ^ globalJ n Bmax := by exact_mod_cast h
  have hp : 0 < (2 : ℚ) ^ globalJ n Bmax := pow_pos (by norm_num) _
  dsimp [nodeError, epsilon]
  rw [div_pow, one_pow, ← mul_assoc, mul_one_div, div_le_iff₀ hp]
  linarith only [hq]

theorem width_error_small {n Bmax : ℕ} (I : SolveBox n Bmax) :
    (I.width : ℚ) * nodeError n Bmax ≤ 1 / 16 := by
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr I.bounded)
    (nodeError_nonneg _ _)).trans (root_error_small n Bmax)

end MeanPayoff
end

end OAI
