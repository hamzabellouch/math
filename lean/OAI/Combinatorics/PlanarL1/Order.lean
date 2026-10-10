import Mathlib

namespace OAI

section

namespace PlanarL1.Ordered

/-- Running minimum toward a target in the circle cut at its root, index zero.
The exceptional root retains its global minimum. -/
noncomputable def running {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : ℝ :=
  if i = 0 then f 0 else (Finset.uIcc i b).inf' Finset.nonempty_uIcc f

lemma running_zero {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    running b f 0 = f 0 := by simp [running]

lemma running_le {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) : running b f i ≤ f i := by
  by_cases hi : i = 0
  · simp [running, hi]
  · simp only [running, ite_eq_right hi]
    exact Finset.inf'_le f (Finset.left_mem_uIcc)

lemma le_running {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) (i : Fin (n + 1)) : f 0 ≤ running b f i := by
  by_cases hi : i = 0
  · simp [running, hi]
  · simp only [running, ite_eq_right hi]
    exact Finset.le_inf' _ _ (fun j _ => hmin j)

lemma running_target {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    running b f b = f b := by
  by_cases hb : b = 0
  · simp [running, hb]
  · simp [running, hb]

lemma running_mono_left {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) {i j : Fin (n + 1)} (hij : i ≤ j) (hjb : j ≤ b) :
    running b f i ≤ running b f j := by
  by_cases hi : i = 0
  · rw [hi, running_zero]
    exact le_running b f hmin j
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le i))
  simp only [running, ite_eq_right hi, ite_eq_right hj]
  apply Finset.inf'_mono f _ Finset.nonempty_uIcc
  intro z hz
  simp only [Finset.mem_uIcc, min_eq_left (hij.trans hjb), max_eq_right (hij.trans hjb), min_eq_left hjb, max_eq_right hjb] at hz ⊢
  exact ⟨hij.trans hz.1, hz.2⟩

lemma running_mono_right {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    {i j : Fin (n + 1)} (hbi : b ≤ i) (hij : i ≤ j) :
    running b f j ≤ running b f i := by
  by_cases hi : i = 0
  · have hb : b = 0 := le_antisymm (hi ▸ hbi) (Fin.zero_le b)
    subst b
    have hj : running 0 f j ≤ f 0 := by
      by_cases hz : j = 0
      · simp [hz, running_zero]
      · simp only [running, ite_eq_right hz]
        exact Finset.inf'_le f Finset.right_mem_uIcc
    simpa only [hi, running_zero] using hj
  have hj : j ≠ 0 := by intro hj; subst j; exact hi (le_antisymm hij (Fin.zero_le i))
  simp only [running, ite_eq_right hi, ite_eq_right hj]
  apply Finset.inf'_mono f _ Finset.nonempty_uIcc
  intro z hz
  simp only [Finset.mem_uIcc, min_eq_right hbi, max_eq_left hbi, min_eq_right (hbi.trans hij), max_eq_left (hbi.trans hij)] at hz ⊢
  exact ⟨hz.1, hz.2.trans hij⟩

/-- Collision inequality for a chord is exactly what is needed to make running
minima respect its switch, including chords that straddle the target. -/
lemma running_switch {n : ℕ} (b : Fin (n + 1)) (f : Fin (n + 1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i) {p q : Fin (n + 1)} (hpq : p < q) (he : f p = f q)
    (hcollision : p ≠ 0 → ∀ z, p ≤ z → z ≤ q → f p ≤ f z) :
    running b f p = running b f q := by
  by_cases hp : p = 0
  · rw [hp, running_zero]
    exact le_antisymm (le_running b f hmin q) ((running_le b f q).trans_eq (hp ▸ he).symm)
  have hq : q ≠ 0 := by intro hz; subst q; exact (not_lt_of_ge (Fin.zero_le p)) hpq
  simp only [running, ite_eq_right hp, ite_eq_right hq]
  by_cases hqb : q ≤ b
  · have hpb := hpq.le.trans hqb
    apply le_antisymm
    · apply Finset.inf'_mono f _ Finset.nonempty_uIcc
      intro z hz
      simp only [Finset.mem_uIcc, min_eq_left hqb, max_eq_right hqb, min_eq_left hpb, max_eq_right hpb] at hz ⊢
      exact ⟨hpq.le.trans hz.1, hz.2⟩
    · apply Finset.le_inf'
      intro z hz
      have hz' : p ≤ z ∧ z ≤ b := by
        simpa only [Finset.mem_uIcc, min_eq_left hpb, max_eq_right hpb] using hz
      by_cases hqz : q ≤ z
      · exact Finset.inf'_le f (by simpa only [Finset.mem_uIcc, min_eq_left hqb, max_eq_right hqb] using And.intro hqz hz'.2)
      · exact (Finset.inf'_le f Finset.left_mem_uIcc).trans
          (he ▸ hcollision hp z hz'.1 (lt_of_not_ge hqz).le)
  · by_cases hbp : b ≤ p
    · have hbq := hbp.trans hpq.le
      apply le_antisymm
      · apply Finset.le_inf'
        intro z hz
        have hz' : b ≤ z ∧ z ≤ q := by
          simpa only [Finset.mem_uIcc, min_eq_right hbq, max_eq_left hbq] using hz
        by_cases hzp : z ≤ p
        · exact Finset.inf'_le f (by simpa only [Finset.mem_uIcc, min_eq_right hbp, max_eq_left hbp] using And.intro hz'.1 hzp)
        · exact (Finset.inf'_le f Finset.left_mem_uIcc).trans
            (hcollision hp z (lt_of_not_ge hzp).le hz'.2)
      · apply Finset.inf'_mono f _ Finset.nonempty_uIcc
        intro z hz
        simp only [Finset.mem_uIcc, min_eq_right hbp, max_eq_left hbp, min_eq_right hbq, max_eq_left hbq] at hz ⊢
        exact ⟨hz.1, hz.2.trans hpq.le⟩
    · have hpb : p ≤ b := (lt_of_not_ge hbp).le
      have hbq : b ≤ q := (lt_of_not_ge hqb).le
      have hleft : (Finset.uIcc p b).inf' Finset.nonempty_uIcc f = f p := by
        apply le_antisymm (Finset.inf'_le f Finset.left_mem_uIcc)
        apply Finset.le_inf'
        intro z hz
        have hz' : p ≤ z ∧ z ≤ b := by
          simpa only [Finset.mem_uIcc, min_eq_left hpb, max_eq_right hpb] using hz
        exact hcollision hp z hz'.1 (hz'.2.trans hbq)
      have hright : (Finset.uIcc q b).inf' Finset.nonempty_uIcc f = f p := by
        apply le_antisymm ((Finset.inf'_le f Finset.left_mem_uIcc).trans_eq he.symm)
        apply Finset.le_inf'
        intro z hz
        have hz' : b ≤ z ∧ z ≤ q := by
          simpa only [Finset.mem_uIcc, min_eq_right hbq, max_eq_left hbq] using hz
        exact hcollision hp z (hpb.trans hz'.1) hz'.2
      exact hleft.trans hright.symm

lemma finite_inf_lipschitz {X ι : Type*} [PseudoMetricSpace X] (S : Finset ι)
    (hne : S.Nonempty) (f : ι → X → ℝ) (L : NNReal)
    (hf : ∀ i ∈ S, LipschitzWith L (f i)) :
    LipschitzWith L (fun x => S.inf' hne (fun i => f i x)) := by
  have hbound (x y : X) : S.inf' hne (fun i => f i x) - S.inf' hne (fun i => f i y) ≤
      L * dist x y := by
    obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' hne (fun i => f i y)
    have hl := (hf i hi).dist_le_mul x y
    rw [Real.dist_eq] at hl
    have hle := Finset.inf'_le (fun i => f i x) hi
    rw [he]
    linarith [(abs_le.mp hl).2]
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  constructor
  · have h := hbound y x
    rw [dist_comm y x] at h
    linarith
  · exact hbound x y

lemma running_lipschitz {n : ℕ} {X : Type*} [PseudoMetricSpace X] (b i : Fin (n + 1))
    (f : Fin (n + 1) → X → ℝ) (L : NNReal) (hf : ∀ j, LipschitzWith L (f j)) :
    LipschitzWith L (fun x => running b (fun j => f j x) i) := by
  by_cases hi : i = 0
  · simpa only [hi, running_zero] using hf 0
  · simp only [running, ite_eq_right hi]
    exact finite_inf_lipschitz _ _ f L (fun j _ => hf j)

end PlanarL1.Ordered

end

section

namespace PlanarL1.Ordered

lemma rotate_unimodal_neg {k : ℕ} (b : Fin (k+1)) (f : Fin (k+1) → ℝ)
    (hmin : ∀ i, f 0 ≤ f i)
    (hl : ∀ i j, i ≤ j → j ≤ b → f i ≤ f j)
    (hr : ∀ i j, b ≤ i → i ≤ j → f j ≤ f i) :
    (∀ i, -f b ≤ -f (i+b)) ∧
    (∀ i j : Fin (k+1), i ≤ j → j ≤ -b → -f (i+b) ≤ -f (j+b)) ∧
    (∀ i j : Fin (k+1), -b ≤ i → i ≤ j → -f (j+b) ≤ -f (i+b)) := by
  have hmax (i : Fin (k+1)) : f i ≤ f b := by
    rcases le_total i b with hi | hi
    · exact hl i b hi le_rfl
    · exact hr b i le_rfl hi
  by_cases hb : b=0
  · have he (i : Fin (k+1)) : f i=f 0 := le_antisymm (hb ▸ hmax i) (hmin i)
    simp only [he,le_refl,implies_true,and_self]
  have hbpos : 0 < b.val := by exact Nat.pos_of_ne_zero (fun h => hb (Fin.ext h))
  have hv : (-b).val=k+1-b.val := by
    simp only [Fin.val_neg,ite_eq_right hb]
  have add_before (i : Fin (k+1)) (hi : i < -b) : (i+b).val=i.val+b.val := by
    rw [Fin.val_add,Nat.mod_eq_of_lt]
    change i.val < (-b).val at hi
    rw [hv] at hi
    omega
  have add_after (i : Fin (k+1)) (hi : -b ≤ i) :
      (i+b).val=i.val+b.val-(k+1) := by
    rw [Fin.val_add,Nat.mod_eq_sub_mod (by change (-b).val ≤ i.val at hi; rw [hv] at hi; omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun i => neg_le_neg (hmax _),?_,?_⟩
  · intro i j hij hj
    by_cases he : j = -b
    · rw [he,neg_add_cancel]
      exact neg_le_neg (hmin _)
    · have hjs : j < -b := lt_of_le_of_ne hj he
      have his : i < -b := hij.trans_lt hjs
      apply neg_le_neg
      apply hr
      · change b.val ≤ (i+b).val
        rw [add_before i his]
        omega
      · change (i+b).val ≤ (j+b).val
        rw [add_before i his,add_before j hjs]
        exact Nat.add_le_add_right hij b.val
  · intro i j hi hij
    apply neg_le_neg
    apply hl
    · change (i+b).val ≤ (j+b).val
      rw [add_after i hi,add_after j (hi.trans hij)]
      exact Nat.sub_le_sub_right (Nat.add_le_add_right hij b.val) _
    · change (j+b).val ≤ b.val
      rw [add_after j (hi.trans hij)]
      omega
end PlanarL1.Ordered


end

end OAI
