import OAI.Dynamics.ConditionalShuffle.HybridRaw

namespace OAI

noncomputable section
open scoped Classical
namespace Thorp.Conditional.Hybrid
open Revealed.Split Revealed.Disintegration

abbrev Public (d t : ℕ) := Fin t → Option (Coins d)

def energy (d : ℕ) (v : RawState (d+1)) (t : ℕ) (s : Fin t → Bool) : ℝ :=
  mean (fun ω : History (d+1) t => rawEnergy (raw d v t s ω))

lemma tagged_deviation {ι : Type*} (d : ℕ)
    (B : Position (d+1) → Bool) (tag : Position (d+1)) (ht : B tag = true)
    (e : ι → Position (d+1)) (he : ∀ i, B (e i) = false) (t : ℕ) (s : Fin t → Bool)
    (f : Public (d+1) t → (Fin (t+1) → ι → Position (d+1)) → Position (d+1) → ℝ)
    (hf : ∀ q p y, |f q p y| ≤ 1) :
    |mean (fun ω : History (d+1) t =>
      f (publicHistory s ω) (exposedPath (d+1) e t ω) (run (d+1) t ω tag) -
      (1 / (freeCount B : ℝ)) * ∑ y, if B ((run (d+1) t ω).symm y) then
        f (publicHistory s ω) (exposedPath (d+1) e t ω) y else 0)| ≤
      Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) *
        energy d (initialState (d+1) B tag ht).raw t s) := by
  have hh := flow_joint d (initialState (d+1) B tag ht).raw e he t s f
  have hl : mean (fun ω : History (d+1) t =>
      f (publicHistory s ω) (exposedPath (d+1) e t ω) (run (d+1) t ω tag) -
      (1 / (freeCount B : ℝ)) * ∑ y, if B ((run (d+1) t ω).symm y) then
        f (publicHistory s ω) (exposedPath (d+1) e t ω) y else 0) =
      mean (fun ω : History (d+1) t => ∑ x, (initialState (d+1) B tag ht).raw.weight x *
        f (publicHistory s ω) (exposedPath (d+1) e t ω) (run (d+1) t ω x)) := by
    apply mean_congr; intro ω
    change _ = ∑ x, centeredPoint B tag x *
      f (publicHistory s ω) (exposedPath (d+1) e t ω) (run (d+1) t ω x)
    rw [centeredPoint_test]
    congr 2
    simpa only [Equiv.symm_apply_apply] using
      (Equiv.sum_comp (run (d+1) t ω) (fun y => if B ((run (d+1) t ω).symm y) then
        f (publicHistory s ω) (exposedPath (d+1) e t ω) y else 0)).symm
  rw [hl, hh]
  exact mean_weighted_test_le _ _ (fun ω y => hf _ _ _)

lemma completion_error {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (d : ℕ) (L : Sum ι α ≃ Position (d+1)) {k : ℕ} (e : Fin k → α)
    (tag : α) (ht : freeOf e tag = true) (t : ℕ) (s : Fin t → Bool)
    (f : Public (d+1) t → (Fin (t+1) → ι → Position (d+1)) → (Fin (k+1) → Position (d+1)) → ℝ)
    (hf : ∀ q p z, |f q p z| ≤ 1) :
    |mean (fun ω : History (d+1) t =>
        f (publicHistory s ω) (splitPath L t ω) (splitTuple L t ω (Fin.snoc e tag))) -
      mean (fun ω : History (d+1) t =>
        pathComplete (f (publicHistory s ω)) (splitPath L t ω) (splitTuple L t ω e))| ≤
      Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * energy d
        (initialState (d+1) (avoid (Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (e j)))))
          (L (.inr tag)) (by rwa [avoid_equiv_right])).raw t s) := by
  let z : Sum ι (Fin k) → Position (d+1) :=
    Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (e j)))
  let B := avoid z
  let F (q : Public (d+1) t) (p : Fin (t+1) → Sum ι (Fin k) → Position (d+1)) (y : Position (d+1)) :=
    f q (fun a i => p a (.inl i)) (Fin.snoc (fun j => p (Fin.last t) (.inr j)) y)
  have hh := tagged_deviation d B (L (.inr tag)) ((avoid_equiv_right L e tag).trans ht)
    z (avoid_exposed z) t s F (fun q p y => hf _ _ _)
  have ho (ω : History (d+1) t) :
      (fun a i => exposedPath (d+1) z t ω a (.inl i)) = splitPath L t ω :=
    exposedPath_comp (d+1) z Sum.inl t ω
  have he (ω : History (d+1) t) :
      (fun j => exposedPath (d+1) z t ω (Fin.last t) (.inr j)) = splitTuple L t ω e := by
    rw [exposedPath_last]; rfl
  have hF (q) (ω : History (d+1) t) (y : Position (d+1)) :
      F q (exposedPath (d+1) z t ω) y = f q (splitPath L t ω) (Fin.snoc (splitTuple L t ω e) y) := by
    change f _ _ _ = _; rw [ho, he]
  have hB (ω : History (d+1) t) (y : Position (d+1)) :
      B ((run (d+1) t ω).symm y) =
        avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e)) y := by
    rw [splitPath_last]
    have hz : Sum.elim (fun i => run (d+1) t ω (L (.inl i))) (splitTuple L t ω e) =
        (run (d+1) t ω) ∘ z := by funext i; cases i <;> rfl
    rw [hz]; exact (avoid_perm z (run (d+1) t ω) y).symm
  have hcount (ω : History (d+1) t) :
      freeCount (avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e))) = freeCount B := by
    rw [splitPath_last]
    change freeCount (avoid (Sum.elim (fun i => (L.trans (run (d+1) t ω)) (.inl i))
      (fun j => (L.trans (run (d+1) t ω)) (.inr (e j))))) = _
    rw [freeCount_avoid_equiv, show freeCount B = freeCount (freeOf e) from freeCount_avoid_equiv L e]
  simp_rw [hF, hB] at hh
  rw [← mean_sub]
  convert hh using 1
  congr 1
  apply mean_congr; intro ω
  rw [splitTuple_snoc]
  congr 1
  exact congrArg (fun n : ℕ => (1/(n : ℝ)) * ∑ y,
    if avoid (Sum.elim (splitPath L t ω (Fin.last t)) (splitTuple L t ω e)) y then
      f (publicHistory s ω) (splitPath L t ω) (Fin.snoc (splitTuple L t ω e) y) else 0) (hcount ω)

theorem tuple_test {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
    (d t m : ℕ) (s : Fin t → Bool) (ε : ℝ)
    (hE : ∀ (B : Position (d+1) → Bool) (tag) (ht : B tag = true),
      m ≤ freeCount B → freeCount B ≤ Fintype.card α →
      energy d (initialState (d+1) B tag ht).raw t s ≤ ε)
    (L : Sum ι α ≃ Position (d+1)) (k : ℕ) (hk : k+m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e)
    (f : Public (d+1) t → (Fin (t+1) → ι → Position (d+1)) → (Fin k → Position (d+1)) → ℝ)
    (hf : ∀ q p z, |f q p z| ≤ 1) :
    |mean (fun ω : History (d+1) t => f (publicHistory s ω) (splitPath L t ω) (splitTuple L t ω e)) -
      mean (fun ω : History (d+1) t => mean (fun σ : Equiv.Perm α =>
        f (publicHistory s ω) (splitPath L t ω) (splitTuple L t ω (σ ∘ e))))| ≤
      (k : ℝ) * Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * ε) := by
  induction k with
  | zero =>
      have hz (ω : History (d+1) t) (σ : Equiv.Perm α) :
          splitTuple L t ω (σ ∘ e) = splitTuple L t ω e := Subsingleton.elim _ _
      simp_rw [hz, mean_const]
      simp
  | succ k ih =>
      have he0 : Function.Injective (Fin.init e) := by
        intro i j hij; exact Fin.castSucc_inj.mp (he hij)
      have ht : freeOf (Fin.init e) (e (Fin.last k)) = true := by
        apply (freeOf_true _ _).mpr; intro i hi
        exact Fin.castSucc_ne_last i (he hi)
      let B := avoid (Sum.elim (fun i => L (.inl i)) (fun j => L (.inr (Fin.init e j))))
      have htag : B (L (.inr (e (Fin.last k)))) = true := (avoid_equiv_right _ _ _).trans ht
      have hcount : freeCount B = Fintype.card α - k := by
        rw [show freeCount B = freeCount (freeOf (Fin.init e)) from freeCount_avoid_equiv L (Fin.init e),
          freeCount_freeOf _ he0]
      have henergy := hE B _ htag (by omega) (by omega)
      have hz := completion_error d L (Fin.init e) (e (Fin.last k)) ht t s f hf
      rw [Fin.snoc_init_self] at hz
      have hestimate : Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) *
          energy d (initialState (d+1) B (L (.inr (e (Fin.last k)))) htag).raw t s) ≤
          Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * ε) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left henergy (Nat.cast_nonneg _))
      have hnext := ih (by omega) (Fin.init e) he0
        (fun q => pathComplete (f q)) (fun q => pathComplete_bound (f q) (hf q))
      have hu (ω : History (d+1) t) := uniform_splitTuple_completion L e he t ω (f (publicHistory s ω))
      simp_rw [hu]
      have htri := abs_sub_le
        (mean (fun ω : History (d+1) t => f (publicHistory s ω) (splitPath L t ω) (splitTuple L t ω e)))
        (mean (fun ω : History (d+1) t => pathComplete (f (publicHistory s ω)) (splitPath L t ω)
          (splitTuple L t ω (Fin.init e))))
        (mean (fun ω : History (d+1) t => mean (fun σ : Equiv.Perm α =>
          pathComplete (f (publicHistory s ω)) (splitPath L t ω) (splitTuple L t ω (σ ∘ Fin.init e)))))
      have hz' := hz.trans hestimate
      push_cast
      nlinarith

lemma assignment_test {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]
    (d t m : ℕ) (s : Fin t → Bool) (ε : ℝ)
    (hE : ∀ (B : Position (d+1) → Bool) (tag) (ht : B tag = true),
      m ≤ freeCount B → freeCount B ≤ Fintype.card α →
      energy d (initialState (d+1) B tag ht).raw t s ≤ ε)
    (L : Sum ι α ≃ Position (d+1)) (k : ℕ) (hk : k+m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e)
    (f : Public (d+1) t → (Fin (t+1) → ι → Position (d+1)) → (Fin k → α) → ℝ)
    (hf : ∀ q p z, |f q p z| ≤ 1) :
    |mean (fun ω : History (d+1) t => f (publicHistory s ω) (splitPath L t ω)
        (assignment (L.trans (run (d+1) t ω)) ∘ e)) -
      mean (fun ω : History (d+1) t => mean (fun σ : Equiv.Perm α =>
        f (publicHistory s ω) (splitPath L t ω) (σ ∘ e)))| ≤
      (k : ℝ) * Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * ε) := by
  let F (q : Public (d+1) t) (p : Fin (t+1) → ι → Position (d+1)) (z : Fin k → Position (d+1)) :=
    f q p (fun j => indexRight (frameFor L (p (Fin.last t))) (z j))
  have hh := tuple_test d t m s ε hE L k hk e he F (fun q p z => hf _ _ _)
  have hF (ω : History (d+1) t) (a : Fin k → α) :
      F (publicHistory s ω) (splitPath L t ω) (splitTuple L t ω a) =
        f (publicHistory s ω) (splitPath L t ω) (assignment (L.trans (run (d+1) t ω)) ∘ a) := by
    dsimp only [F, splitTuple]
    rw [splitPath_last, indexRight_tuple]
  simp_rw [hF] at hh
  have hu (ω : History (d+1) t) := mean_perm_comp (assignment (L.trans (run (d+1) t ω)))
    e (f (publicHistory s ω) (splitPath L t ω))
  simp_rw [hu] at hh
  exact hh

lemma marginal_bound {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α] [Nonempty α]
    (d t m : ℕ) (s : Fin t → Bool) (ε : ℝ)
    (hE : ∀ (B : Position (d+1) → Bool) (tag) (ht : B tag = true),
      m ≤ freeCount B → freeCount B ≤ Fintype.card α →
      energy d (initialState (d+1) B tag ht).raw t s ≤ ε)
    (L : Sum ι α ≃ Position (d+1)) (k : ℕ) (hk : k+m ≤ Fintype.card α)
    (e : Fin k → α) (he : Function.Injective e) :
    let μ := fairMass (fun ω : History (d+1) t =>
      ((publicHistory s ω, splitPath L t ω), assignment (L.trans (run (d+1) t ω))))
    (∑ p, marginal μ p * tv (Trim.push (conditional μ p) (fun g : Equiv.Perm α => g ∘ e))
      (fairMass (fun g : Equiv.Perm α => g ∘ e))) ≤
      (k : ℝ) / 2 * Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * ε) := by
  have hh := conditional_projection_le_of_test
    (fun ω : History (d+1) t => (publicHistory s ω, splitPath L t ω))
    (fun ω : History (d+1) t => assignment (L.trans (run (d+1) t ω)))
    (fun g : Equiv.Perm α => g ∘ e) ((k : ℝ) * Real.sqrt ((Fintype.card (Position (d+1)) : ℝ) * ε))
    (fun f hf => assignment_test d t m s ε hE L k hk e he
      (fun q p z => f ((q,p),z)) (fun q p z => hf _))
  exact hh.trans_eq (by ring)

end Thorp.Conditional.Hybrid

end

end OAI
