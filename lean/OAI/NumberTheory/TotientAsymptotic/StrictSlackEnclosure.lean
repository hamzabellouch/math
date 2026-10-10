import OAI.NumberTheory.TotientAsymptotic.StrictSlackShell
import OAI.NumberTheory.TotientAsymptotic.PerturbationEnclosure
import OAI.NumberTheory.TotientAsymptotic.SimplexCube

namespace OAI

/-! A failing strict-slack witness puts its entire unit prime box in a thin shell. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

def strictSlackFailure (x : ℝ) (R N : ℕ) (hRN : R ≤ N) : Set (Fin N → ℝ) :=
  {u | B x-B x/(m x : ℝ)^4 < ∑ j, a (j.val+1)*u j ∨
    ∃ i : Fin R, prefixLinear N u (Fin.castLE hRN i) <
      u (Fin.castLE hRN i)/((m x-(i.val+1) : ℕ) : ℝ)^4}

lemma strict_slack_cube_enclosure {x : ℝ} {R N : ℕ} (hRN : R ≤ N)
    (hB : 0 ≤ B x) (hN : N < m x) {u v : Fin N → ℝ}
    (hu : u ∈ enlargedSimplex N (B x) (xi x 0) (fun i => xi x (i.val+1)))
    (hb : ∀ i, u i ≤ (11/10 : ℝ)*bandScale x (i.val+1))
    (hf : u ∈ strictSlackFailure x R N hRN)
    (hd : ∀ i, |u i-v i| ≤ 1) : v ∈ strictSlackShell x R N hRN := by
  have hv := banded_simplex_cube_additive hN hu hb hd
  rcases hf with hf | ⟨i,hi⟩
  · apply Or.inl
    refine ⟨hv,?_⟩
    intro hgood
    have he := (le_abs_self _).trans (prefixBudget_cube_error u v hd)
    have ht := top_cube_error_le_boxTop hB hN.le
    have hh := hgood.2
    dsimp [strictTopWidth] at hh
    linarith
  · apply Or.inr
    refine Set.mem_iUnion.mpr ⟨i,hv,?_⟩
    intro hgood
    have hh := hgood.1 (Fin.castLE hRN i)
    rw [raiseThreshold, Function.update_self] at hh
    have he := (neg_le_abs _).trans
      (prefixLinear_cube_error u v hd (Fin.castLE hRN i))
    have herr := row_cube_error_le_boxSlack hN (Fin.castLE hRN i)
    have hub := div_le_div_of_nonneg_right (hb (Fin.castLE hRN i))
      (show 0 ≤ ((m x-(i.val+1) : ℕ) : ℝ)^4 by positivity)
    simp only [Fin.val_castLE] at hh he herr hub
    dsimp [strictSlackWidth] at hh
    linarith

def FailsStrictSlack {x : ℝ} {H : ℕ} (η : RemainderDatum (L x H)) : Prop :=
  ∃ i ∈ Finset.Icc 0 (R x H),
    (1-1/((m x-i : ℕ) : ℝ)^4)*remainderCoord x η i <
      ∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r

lemma failing_remainder_strict_slack {x : ℝ} {H : ℕ}
    (hPH : P H ≤ H) {η : RemainderDatum (L x H)} (hf : FailsStrictSlack η) :
    primePrefixCoord η.primes ∈ strictSlackFailure x (R x H) (L x H)
      (by unfold R L; omega) := by
  have hRL : R x H ≤ L x H := by unfold R L; omega
  change primePrefixCoord η.primes ∈ strictSlackFailure x (R x H) (L x H) hRL
  change _ ∨ ∃ j : Fin (R x H), _
  obtain ⟨i,hi,hfail⟩ := hf
  have hiR := (Finset.mem_Icc.mp hi).2
  by_cases hi0 : i=0
  · subst i
    left
    have hsum : (∑ r ∈ Finset.Icc (0+1) (L x H), a (r-0)*remainderCoord x η r) =
        ∑ j : Fin (L x H), a (j.val+1)*primePrefixCoord η.primes j := by
      rw [prefix_sum_fin]
      simp only [Nat.zero_lt_succ,ite_true,Nat.sub_zero,remainderCoord_fin]
    rw [hsum,show remainderCoord x η 0=B x from rfl] at hfail
    simp only [Nat.sub_zero] at hfail
    convert hfail using 1
    ring
  · right
    let j : Fin (R x H) := ⟨i-1,by omega⟩
    have he : j.val+1=i := by dsimp [j]; omega
    refine ⟨j,?_⟩
    have hc : remainderCoord x η i =
        primePrefixCoord η.primes (Fin.castLE hRL j) := by
      rw [← he]
      exact remainderCoord_fin x η (Fin.castLE hRL j)
    have hsum : (∑ r ∈ Finset.Icc (i+1) (L x H), a (r-i)*remainderCoord x η r) =
        primePrefixCoord η.primes (Fin.castLE hRL j)-
          prefixLinear (L x H) (primePrefixCoord η.primes) (Fin.castLE hRL j) := by
      rw [prefix_sum_fin, prefixLinear_apply]
      simp only [remainderCoord_fin, Fin.val_castLE]
      have hh : ∀ k : Fin (L x H), (i < k.val+1) = (j.val < k.val) := by
        intro k
        apply propext
        omega
      simp only [hh, Fin.lt_def,Fin.val_castLE]
      have hd : ∀ k : Fin (L x H), k.val+1-i=k.val-j.val := by
        intro k
        omega
      simp only [hd]
      ring
    rw [hc,hsum] at hfail
    have hfail' := hfail
    simp only [sub_mul,one_mul,div_eq_mul_inv,one_mul] at hfail'
    change prefixLinear (L x H) (primePrefixCoord η.primes) (Fin.castLE hRL j) <
      primePrefixCoord η.primes (Fin.castLE hRL j)/((m x-(j.val+1) : ℕ) : ℝ)^4
    rw [he,div_eq_mul_inv]
    nlinarith

lemma failing_remainder_box_enclosure {x : ℝ} {H : ℕ}
    (hPH : P H < H) (hHm : H ≤ m x) (hP : 1 ≤ P H) (hB : 0 ≤ B x)
    {η : RemainderDatum (L x H)} (hη : IsBasicRemainder x H η) (hf : FailsStrictSlack η)
    {v : Fin (L x H) → ℝ} (hd : ∀ i, |primePrefixCoord η.primes i-v i| ≤ 1) :
    v ∈ strictSlackShell x (R x H) (L x H) (by unfold R L; omega) := by
  have hL : 0 < L x H := by unfold L; omega
  have hLm : L x H < m x := by unfold L; omega
  apply strict_slack_cube_enclosure _ hB hLm (basic_remainder_enlargedSimplex hL hη)
    _ (failing_remainder_strict_slack hPH.le hf) hd
  intro i
  have hh := (hη.2.1 (i.val+1) (Finset.mem_Icc.mpr ⟨by omega,by have := i.isLt; omega⟩)).2.2
  simpa only [remainderCoord_fin] using hh

end TotientAsymptotic

end

end OAI
