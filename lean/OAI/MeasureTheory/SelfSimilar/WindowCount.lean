import OAI.MeasureTheory.SelfSimilar.PairBands

namespace OAI

namespace EntropyRateDimension.Windows
open scoped BigOperators

abbrev Retained (σ : ℕ → ℝ) (A' : ℝ) (n : ℕ) (a B L : ℤ) (j : ℕ) : Prop :=
  σ (j+n)-σ j ≤ A'*n ∧ a ≤ L-⌈σ j⌉ ∧ L-⌈σ j⌉ ≤ B

theorem retained_sum_le {q : ℕ} (n K : Fin q → ℕ) (a B : Fin q → ℤ) (A' : ℝ)
    (hsep : ∀ i h : Fin q, h < i → (B h : ℝ)<(a i : ℝ)-A'*n i-1)
    (σ : ℕ → ℝ) (hσ : Monotone σ) (L : ℤ)
    (g : ℕ → ℝ) (hg : Antitone g) (hgn : ∀ j, 0 ≤ g j) :
    (∑ i, ∑ k ∈ Finset.range (K i),
      if Retained σ A' (n i) (a i) (B i) L (k*n i) then
        g (k*n i)-g (k*n i+n i) else 0) ≤ g 0 := by
  classical
  let s := (Finset.univ.sigma (fun i : Fin q => Finset.range (K i))).filter
    (fun x => Retained σ A' (n x.1) (a x.1) (B x.1) L (x.2*n x.1))
  let u := fun x : (i : Fin q) × ℕ => x.2*n x.1
  let v := fun x : (i : Fin q) × ℕ => x.2*n x.1+n x.1
  have hd : (↑s : Set ((i : Fin q) × ℕ)).PairwiseDisjoint (fun x => Finset.Ico (u x) (v x)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    rcases x with ⟨i,k⟩
    rcases y with ⟨h,l⟩
    dsimp only [u,v]
    dsimp only at hx' hy'
    by_cases he : i=h
    · subst h
      exact multiples_disjoint (show k≠l by intro hkl; subst l; exact hxy rfl)
    · rcases lt_or_gt_of_ne he with hil | hli
      · have hb := finer_window_before hσ hy'.1 hy'.2.1 hx'.2.2 (hsep h i hil)
        apply Finset.disjoint_left.mpr
        intro t ht hu
        obtain ⟨ht1,ht2⟩ := Finset.mem_Ico.mp ht
        obtain ⟨hu1,hu2⟩ := Finset.mem_Ico.mp hu
        dsimp only at ht1 ht2 hu1 hu2
        omega
      · have hb := finer_window_before hσ hx'.1 hx'.2.1 hy'.2.2 (hsep i h hli)
        apply Finset.disjoint_left.mpr
        intro t ht hu
        obtain ⟨ht1,ht2⟩ := Finset.mem_Ico.mp ht
        obtain ⟨hu1,hu2⟩ := Finset.mem_Ico.mp hu
        dsimp only at ht1 ht2 hu1 hu2
        omega
  have hh := sum_disjoint_drops_le s u v (fun x _ => Nat.le_add_right _ _) hd g hg hgn
  simpa only [s,Finset.sum_filter,Finset.sum_sigma,u,v] using hh

theorem sum_target_shift (f : ℤ → ℝ) (a B c T : ℤ)
    (ha : 1 ≤ a) (hc : 0 ≤ c) (hB : B+c ≤ T) :
    (∑ L ∈ Finset.Icc 1 T, if a ≤ L-c ∧ L-c ≤ B then f (L-c) else 0)=
      ∑ ℓ ∈ Finset.Icc a B, f ℓ := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun L _ => L-c)
  · intro L hL
    exact Finset.mem_Icc.mpr (Finset.mem_filter.mp hL).2
  · intro L hL L' hL' hh
    omega
  · intro ℓ hℓ
    have hl := Finset.mem_Icc.mp hℓ
    refine ⟨ℓ+c,Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,by omega⟩,by omega⟩,by omega⟩
  · intro L _
    rfl

end EntropyRateDimension.Windows

end OAI
