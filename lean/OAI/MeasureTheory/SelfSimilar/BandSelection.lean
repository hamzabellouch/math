import OAI.MeasureTheory.SelfSimilar.GlobalCount

namespace OAI

universe uα uβ

namespace EntropyRateDimension.Typed
open scoped BigOperators

theorem exists_large_band_start {A A' : ℝ} (hA : 0 < A) (hAA : A' < A) (N : ℕ) (C : ℝ) :
    ∃ n : ℕ, 0 < n ∧ N ≤ n ∧ 1 ≤ bandStart A n ∧
      C < (bandStart A n : ℝ)-A'*n-1 := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (N : ℝ) (max (2/A) ((C+2)/(A-A'))))
  have hnN : N ≤ n := by exact_mod_cast ((le_max_left _ _).trans_lt hn).le
  have h2 : 2/A < (n : ℝ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hC : (C+2)/(A-A') < (n : ℝ) := (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt hn
  have h2' := (div_lt_iff₀ hA).mp h2
  have hC' := (div_lt_iff₀ (sub_pos.mpr hAA)).mp hC
  have hceil := Int.le_ceil (A*(n : ℝ))
  have hn0 : 0 < n := by
    have : (0 : ℝ)<n := (div_pos (by norm_num) hA).trans h2
    exact_mod_cast this
  refine ⟨n,hn0,hnN,?_,?_⟩
  · dsimp only [bandStart]
    have hc : (2 : ℝ) ≤ (⌈A*(n : ℝ)⌉ : ℝ) := by nlinarith
    have : (2 : ℤ) ≤ ⌈A*(n : ℝ)⌉ := by exact_mod_cast hc
    omega
  · dsimp only [bandStart]
    push_cast
    nlinarith

variable {α : Type uα} {β : Type uβ} [Fintype α] [DecidableEq β]

theorem select_separated_bands (S : System α) (tag : α → β)
    {A A' c : ℝ} (hA : 0 < A) (hAA : A' < A) {N : ℕ}
    (hb : ∀ n, N ≤ n → ∃ B : ℤ, bandStart A n ≤ B ∧
      c*n ≤ pairBudget S tag A' (bandStart A n) B n) (q : ℕ) :
    ∃ n : Fin q → ℕ, ∃ B : Fin q → ℤ,
      (∀ i, 0 < n i) ∧ (∀ i, 1 ≤ bandStart A (n i)) ∧
      (∀ i, c*n i ≤ pairBudget S tag A' (bandStart A (n i)) (B i) (n i)) ∧
      (∀ i h : Fin q, h < i → (B h : ℝ)<(bandStart A (n i) : ℝ)-A'*n i-1) := by
  classical
  induction q with
  | zero =>
    refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_,?_⟩ <;> intro i <;> exact i.elim0
  | succ q ih =>
    obtain ⟨n,B,hn,ha,hb',hsep⟩ := ih
    let C : ℝ := ∑ i, |(B i : ℝ)|
    have hC (i : Fin q) : (B i : ℝ) ≤ C :=
      (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (B j : ℝ)) (Finset.mem_univ i))
    obtain ⟨n',hn',hN,ha',hg⟩ := exists_large_band_start hA hAA N C
    obtain ⟨B',_,hb''⟩ := hb n' hN
    refine ⟨Fin.snoc n n',Fin.snoc B B',?_,?_,?_,?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hn'
      · simpa only [Fin.snoc_castSucc] using hn i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using ha'
      · simpa only [Fin.snoc_castSucc] using ha i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa only [Fin.snoc_last] using hb''
      · simpa only [Fin.snoc_castSucc] using hb' i
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro h
        refine Fin.lastCases ?_ (fun h => ?_) h
        · exact fun h => (lt_irrefl _ h).elim
        · intro _
          simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hC h).trans_lt hg
      · intro h
        refine Fin.lastCases ?_ (fun h => ?_) h
        · intro hh
          exact (not_lt_of_ge (Fin.le_last _) hh).elim
        · intro hh
          simpa only [Fin.snoc_castSucc] using hsep i h (by exact_mod_cast hh)

theorem exists_common_horizon {q : ℕ} (n : Fin q → ℕ) (hn : ∀ i, 0 < n i) (B : Fin q → ℤ) :
    ∃ H : ℕ, 0 < H ∧ (∀ i, n i ∣ H) ∧ (∀ i, B i ≤ (H : ℤ)) := by
  classical
  let P := ∏ i, n i
  let R := 1+∑ i, (B i).toNat
  have hP : 0 < P := Finset.prod_pos (fun i _ => hn i)
  have hR : 0 < R := by dsimp [R]; omega
  refine ⟨R*P,Nat.mul_pos hR hP,?_,?_⟩
  · intro i
    exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) R
  · intro i
    have hBi : (B i).toNat ≤ ∑ i, (B i).toNat := Finset.single_le_sum (fun j _ => Nat.zero_le ((B j).toNat)) (Finset.mem_univ i)
    have hle : (B i).toNat ≤ R*P := by
      have hP1 : 1 ≤ P := hP
      have hRP : R ≤ R*P := by simpa only [mul_one] using Nat.mul_le_mul_left R hP1
      apply le_trans _ hRP
      dsimp only [R]
      omega
    have hh : ((B i).toNat : ℤ) ≤ ((R*P : ℕ) : ℤ) := by exact_mod_cast hle
    omega

end EntropyRateDimension.Typed

end OAI
