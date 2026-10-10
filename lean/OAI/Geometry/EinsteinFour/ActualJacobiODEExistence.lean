import Mathlib.Analysis.ODE.ExistUnique

namespace OAI

/-! Global solutions of a bounded continuous linear equation, constructed
from Picard–Lindelöf on overlapping intervals. The uniform local time depends
on the operator bound, while the Picard ball may depend on the initial value. -/

namespace PositiveEinsteinFour.Jacobi

open Set Metric
open scoped Topology NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def LinearCurveOn (A : ℝ → E →L[ℝ] E) (γ : ℝ → E) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, HasDerivAt γ (A t (γ t)) t

theorem linear_uniform_local_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    (ε : ℝ) (hε : 0 < ε) (hsmall : 2 * (K : ℝ) * ε ≤ 1)
    (s : ℝ) (x : E) :
    ∃ γ : ℝ → E, γ s = x ∧ LinearCurveOn A γ (Ioo (s - ε) (s + ε)) := by
  let a : ℝ≥0 := ‖x‖₊ + 1
  let L : ℝ≥0 := 2 * K * a
  let s₀ : Icc (s - ε) (s + ε) := ⟨s, by constructor <;> linarith⟩
  have hlip (t : ℝ) : LipschitzWith K (A t) :=
    (A t).lipschitzWith.weaken (by exact_mod_cast hK t)
  have hpl : IsPicardLindelof (fun t y => A t y) s₀ x a 0 L K := by
    constructor
    · exact fun t _ => (hlip t).lipschitzOnWith
    · exact fun y _ => (hA.clm_apply continuous_const).continuousOn
    · intro t _ y hy
      have hyx : ‖y - x‖ ≤ (a : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hy
      have hx : ‖x‖ ≤ (a : ℝ) := by dsimp [a]; simp
      have hy' : ‖y‖ ≤ 2 * (a : ℝ) := by
        have h := norm_le_norm_sub_add y x
        linarith
      calc
        ‖A t y‖ ≤ (K : ℝ) * ‖y‖ := (A t).le_of_opNorm_le (hK t) y
        _ ≤ (K : ℝ) * (2 * (a : ℝ)) :=
          mul_le_mul_of_nonneg_left hy' K.coe_nonneg
        _ = (L : ℝ) := by simp only [L, NNReal.coe_mul, NNReal.coe_ofNat]; ring
    · have hleft : s + ε - (s₀ : ℝ) = ε := by dsimp [s₀]; ring
      have hright : (s₀ : ℝ) - (s - ε) = ε := by dsimp [s₀]; ring
      rw [hleft, hright, max_self]
      change (2 * (K : ℝ) * (a : ℝ)) * ε ≤ (a : ℝ) - 0
      nlinarith [mul_le_mul_of_nonneg_right hsmall a.coe_nonneg]
  obtain ⟨γ, hγ0, hγ⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, fun t ht => ?_⟩
  exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
theorem LinearCurveOn.mono {A : ℝ → E →L[ℝ] E} {γ : ℝ → E}
    {I J : Set ℝ} (hγ : LinearCurveOn A γ I) (hJI : J ⊆ I) :
    LinearCurveOn A γ J := fun t ht => hγ t (hJI ht)

omit [CompleteSpace E] in
theorem linear_curve_eqOn_interval (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {γ η : ℝ → E} {a b t : ℝ}
    (hγ : LinearCurveOn A γ (Ioo a b)) (hη : LinearCurveOn A η (Ioo a b))
    (ht : t ∈ Ioo a b) (heq : γ t = η t) : EqOn γ η (Ioo a b) := by
  apply ODE_solution_unique_of_mem_Ioo (s := fun _ => univ)
    (K := K) (v := fun r y => A r y) _ ht _ _ heq
  · intro r _
    exact ((A r).lipschitzWith.weaken (by exact_mod_cast hK r)).lipschitzOnWith
  · exact fun r hr => ⟨hγ r hr, mem_univ _⟩
  · exact fun r hr => ⟨hη r hr, mem_univ _⟩

omit [CompleteSpace E] in
theorem linear_curve_piecewise (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K)
    {γ η : ℝ → E} {a b c d t : ℝ}
    (hγ : LinearCurveOn A γ (Ioo a b)) (hη : LinearCurveOn A η (Ioo c d))
    (ht : t ∈ Ioo a b ∩ Ioo c d) (heq : γ t = η t) :
    LinearCurveOn A ((Ioo a b).piecewise γ η) (Ioo a b ∪ Ioo c d) := by
  classical
  have hover : EqOn γ η (Ioo (max a c) (min b d)) :=
    linear_curve_eqOn_interval A K hK
      (hγ.mono (Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)))
      (hη.mono (Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)))
      ⟨max_lt ht.1.1 ht.2.1, lt_min ht.1.2 ht.2.2⟩ heq
  have hother : EqOn ((Ioo a b).piecewise γ η) η (Ioo c d) := by
    intro r hr
    by_cases hab : r ∈ Ioo a b
    · rw [piecewise_eq_of_mem _ _ _ hab]
      exact hover ⟨max_lt hab.1 hr.1, lt_min hab.2 hr.2⟩
    · exact piecewise_eq_of_notMem _ _ _ hab
  intro r hr
  by_cases hab : r ∈ Ioo a b
  · have hnear : (Ioo a b).piecewise γ η =ᶠ[𝓝 r] γ := by
      filter_upwards [isOpen_Ioo.mem_nhds hab] with u hu
      exact piecewise_eq_of_mem _ _ _ hu
    have hd := (hγ r hab).congr_of_eventuallyEq hnear
    simpa only [hnear.self_of_nhds] using hd
  · have hcd : r ∈ Ioo c d := hr.resolve_left hab
    have hnear : (Ioo a b).piecewise γ η =ᶠ[𝓝 r] η := by
      filter_upwards [isOpen_Ioo.mem_nhds hcd] with u hu
      exact hother hu
    have hd := (hη r hcd).congr_of_eventuallyEq hnear
    simpa only [hnear.self_of_nhds] using hd

omit [CompleteSpace E] in
theorem extend_linear_curve_interval (A : ℝ → E →L[ℝ] E)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) {ε a : ℝ}
    (hε : 0 < ε) (ha : ε / 2 ≤ a)
    (hlocal : ∀ s x, ∃ γ : ℝ → E, γ s = x ∧
      LinearCurveOn A γ (Ioo (s - ε) (s + ε)))
    {γ : ℝ → E} (hγ : LinearCurveOn A γ (Ioo (-a) a)) :
    ∃ δ : ℝ → E, δ 0 = γ 0 ∧
      LinearCurveOn A δ (Ioo (-(a + ε / 2)) (a + ε / 2)) := by
  classical
  let c := a - ε / 4
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  obtain ⟨L, hL0, hL⟩ := hlocal (-c) (γ (-c))
  obtain ⟨R, hR0, hR⟩ := hlocal c (γ c)
  have htL : -c ∈ Ioo (-a) a ∩ Ioo (-c - ε) (-c + ε) := by
    constructor <;> constructor <;> linarith
  let ψ : ℝ → E := (Ioo (-a) a).piecewise γ L
  have hψ : LinearCurveOn A ψ (Ioo (-(a + ε / 2)) a) := by
    apply (linear_curve_piecewise A K hK hγ hL htL hL0.symm).mono
    intro t ht
    by_cases hta : -a < t
    · exact Or.inl ⟨hta, ht.2⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]
  have hψc : ψ c = γ c := piecewise_eq_of_mem _ _ _ ⟨by linarith, hca⟩
  have htR : c ∈ Ioo (-(a + ε / 2)) a ∩ Ioo (c - ε) (c + ε) := by
    constructor <;> constructor <;> linarith
  let δ : ℝ → E := (Ioo (-(a + ε / 2)) a).piecewise ψ R
  refine ⟨δ, ?_, ?_⟩
  · have ha0 : 0 < a := lt_of_lt_of_le (half_pos hε) ha
    simp only [δ, ψ, piecewise,
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-(a + ε / 2)) a from ⟨by linarith, ha0⟩),
      ite_eq_left (show (0 : ℝ) ∈ Ioo (-a) a from ⟨by linarith, ha0⟩)]
  · apply (linear_curve_piecewise A K hK hψ hR htR (hψc.trans hR0.symm)).mono
    intro t ht
    by_cases hta : t < a
    · exact Or.inl ⟨ht.1, hta⟩
    · right
      constructor <;> dsimp [c] at * <;> linarith [ht.1, ht.2]

/-- A continuous globally bounded operator coefficient admits a genuine
global linear solution through every initial value. -/
theorem exists_global_linear_solution (A : ℝ → E →L[ℝ] E) (hA : Continuous A)
    (K : ℝ≥0) (hK : ∀ t, ‖A t‖ ≤ K) (x : E) :
    ∃ Γ : ℝ → E, Γ 0 = x ∧ ∀ t, HasDerivAt Γ (A t (Γ t)) t := by
  classical
  let ε : ℝ := 1 / (2 * ((K : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : 2 * (K : ℝ) * ε ≤ 1 := by
    dsimp [ε]
    rw [← mul_div_assoc, mul_one]
    apply (div_le_one (by positivity)).mpr
    linarith [K.coe_nonneg]
  have hlocal := linear_uniform_local_solution A hA K hK ε hε hsmall
  let r (n : ℕ) : ℝ := ((n : ℝ) + 1) * ε / 2
  have hr (n : ℕ) : ε / 2 ≤ r n := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hmul : 0 ≤ (n : ℝ) * ε := mul_nonneg hn hε.le
    dsimp [r]
    nlinarith
  have hstep (n : ℕ) : r (n + 1) = r n + ε / 2 := by
    simp only [r, Nat.cast_add, Nat.cast_one]
    ring
  have hfam (n : ℕ) : ∃ γ : ℝ → E, γ 0 = x ∧ LinearCurveOn A γ (Ioo (-(r n)) (r n)) := by
    induction n with
    | zero =>
      obtain ⟨γ, h0, hγ⟩ := hlocal 0 x
      refine ⟨γ, h0, hγ.mono ?_⟩
      apply Ioo_subset_Ioo <;> simp only [r, Nat.cast_zero, zero_add, one_mul] <;> linarith
    | succ n ih =>
      obtain ⟨γ, h0, hγ⟩ := ih
      obtain ⟨δ, hδ0, hδ⟩ := extend_linear_curve_interval A K hK hε (hr n) hlocal hγ
      exact ⟨δ, hδ0.trans h0, by simpa only [hstep n] using hδ⟩
  have hinterval (a : ℝ) : ∃ γ : ℝ → E, γ 0 = x ∧ LinearCurveOn A γ (Ioo (-a) a) := by
    obtain ⟨n, hn⟩ := exists_nat_gt (a / (ε / 2))
    have han : a < (n : ℝ) * (ε / 2) := (div_lt_iff₀ (half_pos hε)).mp hn
    have har : a < r n := by dsimp [r]; nlinarith
    obtain ⟨γ, h0, hγ⟩ := hfam n
    exact ⟨γ, h0, hγ.mono (Ioo_subset_Ioo (by linarith) har.le)⟩
  choose γ h0 hγ using hinterval
  have compatible {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
      EqOn (γ a) (γ b) (Ioo (-a) a) := by
    apply linear_curve_eqOn_interval A K hK (hγ a)
      ((hγ b).mono (Ioo_subset_Ioo (by linarith) hab))
      (t := 0) ⟨by linarith, ha⟩
    exact (h0 a).trans (h0 b).symm
  let Γ : ℝ → E := fun t => γ (|t| + 1) t
  have hagrees (a : ℝ) (ha : 0 < a) : EqOn Γ (γ a) (Ioo (-a) a) := by
    intro t ht
    have hr' : 0 < |t| + 1 := by positivity
    have htr : t ∈ Ioo (-(|t| + 1)) (|t| + 1) := abs_lt.mp (lt_add_one _)
    rcases le_total a (|t| + 1) with hle | hle
    · exact (compatible ha hle ht).symm
    · exact compatible hr' hle htr
  refine ⟨Γ, h0 (|0| + 1), fun t => ?_⟩
  let a := |t| + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : t ∈ Ioo (-a) a := abs_lt.mp (lt_add_one _)
  have hnear : Γ =ᶠ[𝓝 t] γ a := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hagrees a ha hs
  have hd := (hγ a t ht).congr_of_eventuallyEq hnear
  simpa only [hnear.self_of_nhds] using hd

end
end PositiveEinsteinFour.Jacobi

end OAI
