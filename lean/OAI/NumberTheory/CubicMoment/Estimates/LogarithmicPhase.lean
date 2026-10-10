import OAI.NumberTheory.CubicMoment.Estimates.LogarithmicWeightFamily
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticTwistedTransform

namespace OAI

/-! Logarithmically bounded height twists preserve the smooth weight
family used by the low-height Type-I theorem. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

def linearHeightPhase (t x : ℝ) : ℂ := Complex.exp ((t*x:ℝ)*Complex.I)

lemma linearHeightPhase_derivative (t x : ℝ) :
    HasDerivAt (linearHeightPhase t) (linearHeightPhase t x*((t:ℂ)*Complex.I)) x := by
  have h := (((hasDerivAt_id x).const_mul t).ofReal_comp.mul_const Complex.I).cexp
  convert h using 1
  · funext y
    simp [linearHeightPhase]
  · simp [linearHeightPhase]

lemma linearHeightPhase_iteratedDeriv (t : ℝ) (n : ℕ) :
    iteratedDeriv n (linearHeightPhase t) =
      fun x => ((t:ℂ)*Complex.I)^n*linearHeightPhase t x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    rw [((linearHeightPhase_derivative t x).const_mul (((t:ℂ)*Complex.I)^n)).deriv]
    rw [pow_succ]
    ring

lemma linearHeightPhase_derivative_norm (t x : ℝ) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (linearHeightPhase t) x‖ = |t|^n := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,linearHeightPhase_iteratedDeriv]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_I,mul_one,linearHeightPhase,Complex.norm_exp_ofReal_mul_I]

abbrev logarithmicPhaseIndex {γ : Type*} (Y : γ → ℝ) (d : ℕ) :=
  {p : γ × ℝ // |p.2| ≤ (1+Real.log (Y p.1))^d}

def logarithmicPhaseWeight {γ : Type*} (Y : γ → ℝ) (W : γ → ℝ → ℂ) (d : ℕ)
    (i : logarithmicPhaseIndex Y d) (x : ℝ) : ℂ :=
  W i.val.1 x*mellinPhase i.val.2 x

def LogarithmicWeightFamily.phase {γ : Type*} {Y : γ → ℝ} {W : γ → ℝ → ℂ}
    (h : LogarithmicWeightFamily Y W) (d : ℕ) :
    LogarithmicWeightFamily (fun i : logarithmicPhaseIndex Y d => Y i.val.1)
      (logarithmicPhaseWeight Y W d) := by
  refine ⟨fun i => h.length_one i.val.1,
    fun i => phaseWeight_compact (h.compact i.val.1) i.val.2,
    fun i => phaseWeight_positive (h.positive i.val.1) i.val.2,
    fun i => phaseWeight_smooth (h.positive i.val.1) (h.smooth i.val.1) i.val.2,
    h.radius,h.radius_nonneg,?_,?_⟩
  · intro i u hu
    apply h.support_bound i.val.1 u
    apply tsupport_mul_subset_left hu
  · choose B A hB hb using h.derivative_bound
    intro n
    let E := d*n+∑ j ∈ Finset.range (n+1), A j
    let C := ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*B (n-j)
    have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hB _))
    refine ⟨C,E,hC,?_⟩
    intro i u
    let L := 1+Real.log (Y i.val.1)
    have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (h.length_one i.val.1)]
    have he : (fun v => logarithmicPhaseWeight Y W d i (Real.exp (-v))) =
        fun v => linearHeightPhase (-i.val.2) v*W i.val.1 (Real.exp (-v)) := by
      funext v
      dsimp [logarithmicPhaseWeight,linearHeightPhase,mellinPhase]
      rw [Real.log_exp]
      have hh : i.val.2*(-v) = (-i.val.2)*v := by ring
      rw [hh,mul_comm]
    rw [he]
    have hp : ContDiff ℝ ∞ (linearHeightPhase (-i.val.2)) := by
      unfold linearHeightPhase
      exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).mul
        contDiff_const).cexp
    have hw : ContDiff ℝ ∞ (fun v => W i.val.1 (Real.exp (-v))) :=
      (h.smooth i.val.1).comp (by fun_prop)
    apply (norm_iteratedFDeriv_mul_le hp hw u (n := n) (mod_cast le_top)).trans
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*B (n-j)*L^E := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
        have hBj := hB (n-j)
        have hphase : ‖iteratedFDeriv ℝ j (linearHeightPhase (-i.val.2)) u‖ ≤ L^(d*j) := by
          rw [linearHeightPhase_derivative_norm,abs_neg,pow_mul]
          exact pow_le_pow_left₀ (abs_nonneg _) i.property j
        have hA : A (n-j) ≤ ∑ k ∈ Finset.range (n+1), A k :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le _ _)))
        have hexp : d*j+A (n-j) ≤ E :=
          add_le_add (Nat.mul_le_mul_left d hjn) hA
        calc
          _ ≤ (n.choose j:ℝ)*L^(d*j)*(B (n-j)*L^(A (n-j))) := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg _)
            · exact hb (n-j) i.val.1 u
            · exact _root_.norm_nonneg _
            · positivity
          _ = (n.choose j:ℝ)*B (n-j)*L^(d*j+A (n-j)) := by rw [pow_add]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hexp) (by positivity)
      _ = C*L^E := by rw [Finset.sum_mul]

end CubicFirstMoment

end

end OAI
