import OAI.Combinatorics.TreeEdit.CircleSeparation
import OAI.Combinatorics.TreeEdit.WordOperations

namespace OAI

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma representative_toAddCircle {M : ℕ} [NeZero M] (a : ZMod M) :
    representative (ZMod.toAddCircle a) = (a.val : ℝ) / M := by
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have hm : (a.val : ℝ) / M ∈ Set.Ico (0 : ℝ) 1 :=
    ⟨by positivity, (div_lt_one hM).mpr (by exact_mod_cast a.val_lt)⟩
  have he : (representative (ZMod.toAddCircle a) : UnitAddCircle) = ((a.val : ℝ) / M : ℝ) :=
    (representative_coe _).trans (ZMod.toAddCircle_apply a)
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := (0 : ℝ)) (by simpa only [Set.mem_Ico, zero_add] using representative_mem (ZMod.toAddCircle a)) (by simpa only [zero_add] using hm)).mp he

lemma bin_grid {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) (a : ZMod M) :
    (bin R (ZMod.toAddCircle a)).val = a.val / D := by
  have hR : (R : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne R)
  have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  change ⌊(R : ℝ) * representative (ZMod.toAddCircle a)⌋₊ = _
  rw [representative_toAddCircle]
  have he : (R : ℝ) * ((a.val : ℝ) / M) = (a.val : ℝ) / D := by
    have hMr : (M : ℝ) = (R : ℝ) * D := by exact_mod_cast hM
    rw [hMr]; field_simp
  rw [he]
  have hh := Nat.mul_cast_floor_div_cancel (R := ℝ) hD.ne' ((a.val : ℝ) / D)
  rw [div_mul_cancel₀ _ hDr, Nat.floor_natCast] at hh
  exact hh.symm

lemma bin_grid_step {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) (a : ZMod M)
    (ha : a.val % D ≠ D - 1) : bin R (ZMod.toAddCircle a) = bin R (ZMod.toAddCircle (a + 1)) := by
  apply Fin.ext
  rw [bin_grid hD hM, bin_grid hD hM]
  have hval : (a + 1).val = a.val + 1 := by
    have hm : a.val + 1 < M := by
      by_contra hn
      have he : a.val = M - 1 := by have := a.val_lt; omega
      have hmod : (M - 1) % D = D - 1 := by
        have hR := NeZero.pos R
        have he : M - 1 = (R - 1) * D + (D - 1) := by
          have := Nat.sub_add_cancel (show 1 ≤ R from hR)
          have := Nat.sub_add_cancel (show 1 ≤ D from hD)
          have : M - 1 + 1 = M := Nat.sub_add_cancel (NeZero.pos M)
          nlinarith
        rw [he]
        simp only [Nat.add_mod, Nat.mul_mod_left, zero_add, Nat.mod_eq_of_lt (by omega : D - 1 < D)]
      exact ha (he ▸ hmod)
    have hm1 : 1 < M := by omega
    let : Fact (1 < M) := ⟨hm1⟩
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hm]
  rw [hval]
  symm
  apply Nat.div_eq_of_lt_le
  · exact (Nat.div_mul_le_self a.val D).trans (by omega)
  · have hh := Nat.div_add_mod a.val D
    have hr := Nat.mod_lt a.val hD
    have hr' : a.val % D + 1 < D := by omega
    nlinarith

lemma mean_comp_hom {A B : Type*} [Fintype A] [Fintype B] [AddGroup A] [AddGroup B]
    (f : A →+ B) (hf : Function.Surjective f) (g : B → ℝ) : mean (g ∘ f) = mean g := by
  change mean (fun a => g (f a)) = mean g
  rw [mean_fiberwise]
  simp_rw [hom_uniform f hf]
  rw [mean, Finset.mul_sum]

lemma mean_translate {A : Type*} [Fintype A] [AddGroup A] (y : A) (f : A → ℝ) :
    mean (fun x => f (x + y)) = mean f := mean_equiv (Equiv.addRight y) f

noncomputable def mapState {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) : (h : ℕ) → State A m h →+ State B m h
  | 0 => f
  | h + 1 => AddMonoidHom.pi (fun i : Fin m => (mapState f h).comp (Pi.evalAddMonoidHom _ i))

lemma mapState_diagonal {A B : Type} [AddCommGroup A] [AddCommGroup B] {m : ℕ}
    (f : A →+ B) (h : ℕ) (a : A) :
    mapState (m := m) f h (diagonal (A := A) (m := m) h a) = diagonal (A := B) (m := m) h (f a) := by
  induction h with
  | zero => rfl
  | succ h ih => exact funext fun _ => ih

noncomputable def sample {M m : ℕ} [NeZero M] (h : ℕ) : State (ZMod M) m h →+ State UnitAddCircle m h :=
  mapState ZMod.toAddCircle h

noncomputable def child {A : Type} [AddCommGroup A] {m : ℕ} (h : ℕ) (i : Fin m) :
    State A m h →+ State A m (h + 1) := AddMonoidHom.single (fun _ : Fin m => State A m h) i

noncomputable def sampledWord {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (T R : ℕ) [NeZero R]
    (h : ℕ) (C : Config I L (g * s) h) (x : State (ZMod M) (g * s) h) :=
  word r j T R h C (sample (M := M) (m := g * s) h x)

lemma point_grid {M P : ℕ} [NeZero M] (hP : 0 < P) (hPM : P ∣ M) :
    ZMod.toAddCircle (M / P : ZMod M) = point P := by
  rw [ZMod.toAddCircle_natCast]
  dsimp [point]
  congr 1
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne M)
  have hPr : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have he : ((M / P : ℕ) : ℝ) * P = M := by exact_mod_cast Nat.div_mul_cancel hPM
  field_simp
  linarith

lemma bin_step_mean {M R D : ℕ} [NeZero M] [NeZero R] (hD : 0 < D) (hM : M = R * D) :
    mean (fun a : ZMod M => (ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] : ℝ)) ≤ (D : ℝ)⁻¹ := by
  classical
  let : NeZero D := ⟨hD.ne'⟩
  have hDM : D ∣ M := by rw [hM]; exact dvd_mul_left _ _
  let f : ZMod M →+ ZMod D := (ZMod.castHom hDM (ZMod D)).toAddMonoidHom
  have he (a : ZMod M) : a.val % D = D - 1 ↔ f a = (D - 1 : ℕ) := by
    apply Iff.trans _ (ZMod.val_injective (n := D)).eq_iff
    change a.val % D = D - 1 ↔ (ZMod.castHom hDM (ZMod D) a).val = ((D-1 : ℕ) : ZMod D).val
    rw [cast_hom_val hDM, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : D - 1 < D)]
  have hh := mean_le (fun a : ZMod M => show
      (ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] : ℝ) ≤
        (if f a = (D - 1 : ℕ) then 1 else 0) from by
    by_cases ha : f a = (D - 1 : ℕ)
    · simp only [ha, ↓reduceIte]
      have hh : ed [bin R (ZMod.toAddCircle a)] [bin R (ZMod.toAddCircle (a + 1))] ≤ 1 :=
        ed_le_of_script (EditScript.cons (EditStep.substitute [] [] _ _) (EditScript.nil _))
      exact_mod_cast hh
    · simp only [ha, ↓reduceIte]
      rw [bin_grid_step hD hM a (fun hz => ha ((he a).mp hz)), ed_self]
      norm_num)
  have hp := hom_uniform f (ZMod.castHom_surjective hDM) (D - 1 : ℕ)
  apply hh.trans_eq
  calc
    _ = probability (fun a : ZMod M => f a = ((D-1 : ℕ) : ZMod D)) := by
      unfold probability
      congr 1
      funext a
      split_ifs <;> rfl
    _ = _ := by simpa only [ZMod.card] using hp

lemma mean_eval {A : Type*} [Fintype A] [AddCommGroup A]
    {m : ℕ} (i : Fin m) (f : A → ℝ) :
    mean (fun x : Fin m → A => f (x i)) = mean f := by
  exact mean_comp_hom (Pi.evalAddMonoidHom _ i) (fun a => ⟨fun _ => a, rfl⟩) f

noncomputable def cycle {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (h : ℕ) (C : Config I L (g * s) (h + 1)) :
    State (ZMod M) (g * s) (h + 1) := fun i => diagonal (A := ZMod M) (m := g * s) h
      ((coefficient r j C.1 (C.2 i).1 i) • (M / period r j C.1 : ZMod M))

lemma sampledWord_succ {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g * s) (h + 1)) (x : State (ZMod M) (g * s) (h + 1)) :
    sampledWord r j T R (h+1) C x = Words.cycles (fun a i =>
      sampledWord r j T R h (C.2 i).2 (x i + a.val • cycle (M := M) r j h C i)) := by
  unfold sampledWord
  simp only [word]
  congr 1
  funext a i
  apply congrArg (word r j T R h (C.2 i).2)
  dsimp [cycle, sample]
  change sample (M := M) (m := g*s) h (x i) +
    diagonal (A := UnitAddCircle) (m := g*s) h ((a.val * coefficient r j C.1 (C.2 i).1 i) • point (period r j C.1)) = _
  dsimp only [sample]
  simp only [map_add, map_nsmul, mapState_diagonal, point_grid (period_pos hr j C.1) (hPM C.1), mul_smul]

lemma sampledWord_diagonal_step {I : Type} {g s L M T R D : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hM : M = R * D)
    (h : ℕ) (C : Config I L (g * s) h) :
    mean (fun x : State (ZMod M) (g * s) h =>
      (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g * s) h 1)).val : ℝ)) ≤
      (FiniteTree.length (g * s) T h : ℝ) / D := by
  induction h with
  | zero =>
    have hw (x : ZMod M) : (sampledWord r j T R 0 C x).val = [bin R (ZMod.toAddCircle x)] := by
      change List.ofFn (fun _ : Fin 1 => bin R (ZMod.toAddCircle x)) = _
      simp [List.ofFn_succ]
    simp only [hw]
    exact (bin_step_mean hD hM).trans_eq (by simp [FiniteTree.length, one_div])
  | succ h ih =>
    let f (i : Fin (g*s)) (x : State (ZMod M) (g*s) h) :=
      (ed (sampledWord r j T R h (C.2 i).2 x).val
        (sampledWord r j T R h (C.2 i).2 (x + diagonal (A := ZMod M) (m := g*s) h 1)).val : ℝ)
    have hp (x : State (ZMod M) (g*s) (h+1)) :
        (ed (sampledWord r j T R (h+1) C x).val
          (sampledWord r j T R (h+1) C (x + diagonal (A := ZMod M) (m := g*s) (h+1) 1)).val : ℝ) ≤
        ∑ a : Fin T, ∑ i : Fin (g*s), f i (x i + a.val • cycle (M := M) r j h C i) := by
      rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
      have hh := Words.ed_cycles (T := T)
        (fun a i => sampledWord r j T R h (C.2 i).2 (x i + a.val • cycle (M := M) r j h C i))
        (fun a i => sampledWord r j T R h (C.2 i).2 ((x + diagonal (A := ZMod M) (m := g*s) (h+1) 1) i + a.val • cycle (M := M) r j h C i))
      have he (a : Fin T) (i : Fin (g*s)) :
          (x + diagonal (A := ZMod M) (m := g*s) (h+1) 1) i + a.val • cycle (M := M) r j h C i =
          (x i + a.val • cycle (M := M) r j h C i) + diagonal (A := ZMod M) (m := g*s) h 1 := by
        change x i + diagonal (A := ZMod M) (m := g*s) h 1 + _ = _
        abel
      simpa only [he, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr hh
    apply (mean_le hp).trans
    rw [mean_sum]
    calc
      _ = ∑ a : Fin T, ∑ i : Fin (g*s), mean (f i) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [mean_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact (mean_eval i (fun y => f i (y + a.val • cycle (M := M) r j h C i))).trans
          (mean_translate _ (f i))
      _ ≤ ∑ _a : Fin T, ∑ _i : Fin (g*s), (FiniteTree.length (g*s) T h : ℝ) / D := by
        apply Finset.sum_le_sum
        intro a _
        exact Finset.sum_le_sum fun i _ => ih (C.2 i).2
      _ = _ := by simp [FiniteTree.length, Finset.sum_const, Finset.card_univ]; ring

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma mean_ed_add {A β : Type*} [Fintype A] [AddCommGroup A] (f : A → List β) (u v : A) :
    mean (fun x => (ed (f x) (f (x + (u + v))) : ℝ)) ≤
      mean (fun x => (ed (f x) (f (x + u)) : ℝ)) + mean (fun x => (ed (f x) (f (x + v)) : ℝ)) := by
  have hh := mean_le (fun x => (Nat.cast_le (α := ℝ)).mpr (ed_triangle (f x) (f (x+u)) (f (x+(u+v)))))
  simp only [Nat.cast_add, ← add_assoc] at hh
  rw [mean_add, mean_translate u (fun x => (ed (f x) (f (x+v)) : ℝ))] at hh
  simpa only [add_assoc] using hh

lemma mean_ed_nsmul {A β : Type*} [Fintype A] [AddCommGroup A] (f : A → List β) (u : A) (a : ℕ) :
    mean (fun x => (ed (f x) (f (x + a • u)) : ℝ)) ≤
      a * mean (fun x => (ed (f x) (f (x + u)) : ℝ)) := by
  induction a with
  | zero => simp [ed_self, mean]
  | succ a ih =>
    rw [succ_nsmul]
    apply (mean_ed_add f _ _).trans
    calc
      _ ≤ (a : ℝ) * mean (fun x => (ed (f x) (f (x+u)) : ℝ)) + mean (fun x => (ed (f x) (f (x+u)) : ℝ)) := add_le_add ih (le_refl _)
      _ = _ := by push_cast; ring

lemma sampledWord_tiny {I : Type} {g s L M T R D Q J : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (hD : 0 < D) (hQ : 0 < Q) (hMR : M = R * D) (hMQ : M = J * Q)
    (h : ℕ) (C : Config I L (g*s) h) (a : ℕ) (ha : a ≤ J) :
    mean (fun x : State (ZMod M) (g*s) h =>
      (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g*s) h (a : ZMod M))).val : ℝ)) ≤
      (FiniteTree.length (g*s) T h : ℝ) * R / Q := by
  have he : diagonal (A := ZMod M) (m := g*s) h (a : ZMod M) = a • diagonal (A := ZMod M) (m := g*s) h 1 := by
    rw [← map_nsmul]; simp [nsmul_eq_mul]
  rw [he]
  calc
    _ ≤ a * mean (fun x => (ed (sampledWord r j T R h C x).val
        (sampledWord r j T R h C (x + diagonal (A := ZMod M) (m := g*s) h 1)).val : ℝ)) := mean_ed_nsmul _ _ _
    _ ≤ (a : ℝ) * ((FiniteTree.length (g*s) T h : ℝ) / D) :=
      mul_le_mul_of_nonneg_left (sampledWord_diagonal_step r j hr hPM hD hMR h C) (by positivity)
    _ ≤ (J : ℝ) * ((FiniteTree.length (g*s) T h : ℝ) / D) := mul_le_mul_of_nonneg_right (by exact_mod_cast ha) (by positivity)
    _ = _ := by
      have hDr : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
      have he : (R : ℝ) * D = (J : ℝ) * Q := by exact_mod_cast hMR.symm.trans hMQ
      field_simp
      nlinarith

lemma sampledWord_cycle_cost {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g*s) (h+1)) (x : State (ZMod M) (g*s) (h+1))
    (a : ℕ) (ha : a ≤ T) :
    ed (sampledWord r j T R (h+1) C x).val
      (sampledWord r j T R (h+1) C (x + a • cycle (M := M) r j h C)).val ≤
        2 * a * ((g*s) * FiniteTree.length (g*s) T h) := by
  rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
  apply Words.ed_cycles_shift ha
  intro b i
  apply congrArg (sampledWord r j T R h (C.2 i).2)
  change x i + (b.val + a) • cycle (M := M) r j h C i =
    (x i + a • cycle (M := M) r j h C i) + b.val • cycle (M := M) r j h C i
  rw [add_nsmul]
  abel

lemma cycle_period {I : Type} {g s L M : ℕ} [NeZero M]
    (r : I → ℕ) (j : Fin g → I) (h : ℕ) (C : Config I L (g*s) (h+1))
    (hPM : period r j C.1 ∣ M) : period r j C.1 • cycle (M := M) r j h C = 0 := by
  funext i
  change period r j C.1 • diagonal (A := ZMod M) (m := g*s) h
    ((coefficient r j C.1 (C.2 i).1 i) • (M / period r j C.1 : ZMod M)) = 0
  rw [← map_nsmul, smul_comm]
  have he : period r j C.1 • (M / period r j C.1 : ZMod M) = 0 := by
    rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hPM]
    exact ZMod.natCast_self M
  rw [he, smul_zero, map_zero]

end TreeEdit.TorusTree

namespace TreeEdit.TorusTree
open scoped BigOperators
open Classical FiniteProbability

lemma sampledWord_child_mean {I : Type} {g s L M T R : ℕ} [NeZero M] [NeZero R]
    (r : I → ℕ) (j : Fin g → I) (hr : ∀ i, 0 < r i)
    (hPM : ∀ σ : Equiv.Perm I, period r j σ ∣ M)
    (h : ℕ) (C : Config I L (g*s) (h+1)) (i : Fin (g*s)) (z : State (ZMod M) (g*s) h) :
    mean (fun x : State (ZMod M) (g*s) (h+1) =>
      (ed (sampledWord r j T R (h+1) C x).val
        (sampledWord r j T R (h+1) C (x + child (A := ZMod M) h i z)).val : ℝ)) ≤
      T * mean (fun x : State (ZMod M) (g*s) h =>
        (ed (sampledWord r j T R h (C.2 i).2 x).val
          (sampledWord r j T R h (C.2 i).2 (x + z)).val : ℝ)) := by
  let f (x : State (ZMod M) (g*s) h) :=
    (ed (sampledWord r j T R h (C.2 i).2 x).val
      (sampledWord r j T R h (C.2 i).2 (x + z)).val : ℝ)
  have hp (x : State (ZMod M) (g*s) (h+1)) :
      (ed (sampledWord r j T R (h+1) C x).val
        (sampledWord r j T R (h+1) C (x + child (A := ZMod M) h i z)).val : ℝ) ≤
      ∑ a : Fin T, f (x i + a.val • cycle (M := M) r j h C i) := by
    rw [sampledWord_succ r j hr hPM, sampledWord_succ r j hr hPM]
    have hh := Words.ed_cycles (T := T)
      (fun a v => sampledWord r j T R h (C.2 v).2 (x v + a.val • cycle (M := M) r j h C v))
      (fun a v => sampledWord r j T R h (C.2 v).2 ((x + child (A := ZMod M) h i z) v + a.val • cycle (M := M) r j h C v))
    apply (Nat.cast_le (α := ℝ)).mpr hh |>.trans
    simp only [Nat.cast_sum]
    apply Finset.sum_le_sum
    intro a _
    rw [Finset.sum_eq_single i]
    · simp only [child, Pi.add_apply, AddMonoidHom.single_apply, Pi.single_eq_same]
      change (ed _ (sampledWord r j T R h (C.2 i).2 ((x i + z) + a.val • cycle (M := M) r j h C i)).val : ℝ) ≤ _
      rw [add_right_comm (x i) z]
    · intro v _ hvi
      simp [child, hvi, ed_self]
    · simp
  apply (mean_le hp).trans_eq
  rw [mean_sum]
  calc
    _ = ∑ _a : Fin T, mean f := by
      apply Finset.sum_congr rfl
      intro a _
      exact (mean_eval i (fun y => f (y + a.val • cycle (M := M) r j h C i))).trans (mean_translate _ f)
    _ = _ := by simp [f]

end TreeEdit.TorusTree

end OAI
