import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteCompositionGrowth

namespace OAI

/-! Uniform coarse derivative growth for the exterior ODE. Bounds on each
fixed derivative of its field suffice, independently of polynomial degree. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

private theorem time_pair_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Z : ℝ → E) (L t : ℝ) (hZ : ContDiffOn ℝ ∞ Z (Ioi L)) (ht : L < t) (i : ℕ) :
    iteratedDeriv i (fun s => (s,Z s)) t = (iteratedDeriv i id t,iteratedDeriv i Z t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_prodMk (f := fun s : ℝ => s) contDiffAt_id
    ((hZ t ht).contDiffAt (Ioi_mem_nhds ht)) (by simp : (i : ℕ∞ω) ≤ ∞)]
  rfl

theorem spectralRemote_ode_jet_growth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ) (F : ℕ → ℝ × E → E) (Z : ℕ → ℝ → E)
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hZ : ∀ᶠ n in atTop, ContDiffOn ℝ ∞ (Z n) (Ioi L))
    (hode : ∀ᶠ n in atTop, ∀ t ∈ Ioi L, HasDerivAt (Z n) (F n (t,Z n t)) t)
    (hbase : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi L, ‖Z n t‖ ≤ M)
    (hfield : ∀ k : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ n in atTop, ∀ t ∈ Ioi L,
      ∀ i ≤ k, ‖iteratedFDeriv ℝ i (F n) (t,Z n t)‖ ≤ M*Real.exp (2*t)) :
    ∀ k : ℕ, ∃ C D : ℝ, 0 ≤ C ∧ 1 ≤ D ∧ ∀ᶠ n in atTop,
      ∀ t ∈ Ioi (max L 0), ∀ i ≤ k, ‖iteratedDeriv i (Z n) t‖ ≤ D*Real.exp (C*t) := by
  intro k
  induction k with
  | zero =>
      obtain ⟨M,hM,hb⟩ := hbase
      refine ⟨0,max M 1,le_rfl,le_max_right _ _,?_⟩
      filter_upwards [hb] with n hn
      intro t ht i hi
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      subst i
      simpa only [iteratedDeriv_zero,zero_mul,Real.exp_zero,mul_one] using
        (hn t ((le_max_left L 0).trans_lt ht)).trans (le_max_left M 1)
  | succ k ih =>
      obtain ⟨C,D,hC,hD,hb⟩ := ih
      obtain ⟨M,hM,hMf⟩ := hfield k
      let C' := C+2+(k : ℝ)*C
      let A := (k.factorial : ℝ)*M*D^k
      let D' := max D A
      have hC' : 0 ≤ C' := by dsimp only [C']; positivity
      have hCC : C ≤ C' := by
        dsimp only [C']
        linarith [mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hC]
      have hDC : 1 ≤ D' := hD.trans (le_max_left _ _)
      refine ⟨C',D',hC',hDC,?_⟩
      filter_upwards [hb,hMf,hZ,hode] with n hn hMn hZn hOn
      intro t ht i hi
      have hLt : L < t := (le_max_left L 0).trans_lt ht
      have ht0 : 0 ≤ t := (le_max_right L 0).trans ht.le
      by_cases hik : i ≤ k
      · calc
          _ ≤ D*Real.exp (C*t) := hn t ht i hik
          _ ≤ D'*Real.exp (C'*t) := mul_le_mul (le_max_left _ _)
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCC ht0))
            (Real.exp_pos _).le (by dsimp only [D']; positivity)
      · have hi' : i = k+1 := by omega
        subst i
        have heq : EqOn (deriv (Z n)) (fun s => F n (s,Z n s)) (Ioi L) :=
          fun s hs => (hOn s hs).deriv
        rw [iteratedDeriv_succ',heq.iteratedDeriv_of_isOpen isOpen_Ioi k hLt]
        have hp : ContDiffOn ℝ ∞ (fun s => (s,Z n s)) (Ioi L) := contDiffOn_id.prodMk hZn
        have hinner : ∀ j, 1 ≤ j → j ≤ k →
            ‖iteratedDeriv j (fun s => (s,Z n s)) t‖ ≤ D*Real.exp (C*t) := by
          intro j hj hjk
          rw [time_pair_derivative (Z n) L t hZn hLt j,Prod.norm_def]
          have hj0 : j ≠ 0 := by omega
          have hid : ‖iteratedDeriv j (id : ℝ → ℝ) t‖ ≤ 1 := by
            by_cases hj1 : j = 1 <;> simp [iteratedDeriv_id,hj0,hj1]
          apply max_le
          · exact hid.trans (one_le_mul_of_one_le_of_one_le hD
              (Real.one_le_exp_iff.mpr (mul_nonneg hC ht0)))
          · exact hn t ht j hjk
        have hc := spectralRemote_composition_growth (fun s => (s,Z n s)) (F n) L t C D
          (M*Real.exp (2*t)) k hp (hF n) hLt ht0 hC hD (hMn t hLt) hinner
        have hbound : ‖iteratedDeriv k (fun s => F n (s,Z n s)) t‖ ≤
            A*Real.exp ((2+(k : ℝ)*C)*t) := by
          apply hc.trans_eq
          dsimp only [A]
          rw [add_mul,Real.exp_add]
          ring
        exact hbound.trans (mul_le_mul (le_max_right D A)
          (Real.exp_le_exp.mpr (by dsimp only [C']; nlinarith))
          (Real.exp_pos _).le (by dsimp only [D']; positivity))

end DefocusingNLS

end OAI
