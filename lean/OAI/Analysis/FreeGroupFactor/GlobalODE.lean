import OAI.Analysis.FreeGroupFactor.Model

namespace OAI

noncomputable section

universe uA uE uι

open Set Metric
open scoped NNReal Topology

open Set Metric
open scoped NNReal Topology
namespace FreeGroupFactorMain

theorem global_solution_of_bounded_lipschitz
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : E → E) (K L : ℝ≥0) (hf : LipschitzWith K f)
    (hbound : ∀ x, ‖f x‖ ≤ L) (x₀ : E) :
    ∃ X : ℝ → E, X 0 = x₀ ∧ ∀ t, HasDerivAt X (f (X t)) t := by
  have hlocal (R : ℝ) (hR : 0 < R) :
      ∃ X : ℝ → E, X 0 = x₀ ∧
        ∀ t ∈ Ioo (-R) R, HasDerivAt X (f (X t)) t := by
    let r : ℝ≥0 := NNReal.mk R hR.le
    have hp : IsPicardLindelof (fun _ : ℝ => f)
        (⟨0, by constructor <;> linarith⟩ : Icc (-R) R)
        x₀ (L * r) 0 L K := by
      constructor
      · intro t ht
        exact hf.lipschitzOnWith
      · intro x hx
        exact continuousOn_const
      · intro t ht x hx
        exact hbound x
      · simp [r, NNReal.coe_mul]
    obtain ⟨X, hX₀, hX⟩ := hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨X, hX₀, fun t ht => ?_⟩
    exact (hX t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose sol init deriv using hlocal
  have agree (R Q : ℝ) (hR : 0 < R) (hQ : 0 < Q) (t : ℝ)
      (htR : t ∈ Ioo (-R) R) (htQ : t ∈ Ioo (-Q) Q) :
      sol R hR t = sol Q hQ t := by
    have hm : 0 < min R Q := lt_min hR hQ
    have heq : EqOn (sol R hR) (sol Q hQ) (Ioo (-min R Q) (min R Q)) := by
      apply ODE_solution_unique_of_mem_Ioo
        (v := fun _ : ℝ => f) (s := fun _ => univ) (t₀ := 0)
        (fun _ _ => hf.lipschitzOnWith)
        (by constructor <;> linarith) _ _ (by rw [init, init])
      · intro u hu
        refine ⟨deriv R hR u ?_, mem_univ _⟩
        constructor <;> have := min_le_left R Q <;> linarith [hu.1, hu.2]
      · intro u hu
        refine ⟨deriv Q hQ u ?_, mem_univ _⟩
        constructor <;> have := min_le_right R Q <;> linarith [hu.1, hu.2]
    apply heq
    constructor
    · have hh : -t < min R Q := lt_min (by linarith [htR.1]) (by linarith [htQ.1])
      linarith
    · exact lt_min htR.2 htQ.2
  let X : ℝ → E := fun t => sol (|t| + 1) (by positivity) t
  have hEq (R : ℝ) (hR : 0 < R) : EqOn X (sol R hR) (Ioo (-R) R) := by
    intro t ht
    apply agree
    · constructor <;> linarith [neg_abs_le t, le_abs_self t]
    · exact ht
  refine ⟨X, ?_, fun t => ?_⟩
  · exact init _ _
  · let R := |t| + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have ht : t ∈ Ioo (-R) R := by
      dsimp [R]
      constructor <;> linarith [neg_abs_le t, le_abs_self t]
    have hh : X =ᶠ[nhds t] sol R hR :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (hEq R hR)
    rw [hEq R hR ht]
    exact (deriv R hR t ht).congr_of_eventuallyEq hh

end FreeGroupFactorMain

open scoped NNReal
namespace FreeGroupFactorMain

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialClip (x : E) : E := (max 1 ‖x‖)⁻¹ • x

theorem radialClip_eq {x : E} (hx : ‖x‖ ≤ 1) : radialClip x = x := by
  simp [radialClip, max_eq_left hx]

theorem norm_radialClip_le (x : E) : ‖radialClip x‖ ≤ 1 := by
  have ha : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [radialClip, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ha]
  simpa only [div_eq_mul_inv, mul_comm] using (div_le_one ha).mpr (le_max_right 1 ‖x‖)

theorem radialClip_lipschitz : LipschitzWith 2 (radialClip : E → E) := by
  have hle (x y : E) (hxy : max 1 ‖y‖ ≤ max 1 ‖x‖) :
      ‖radialClip x - radialClip y‖ ≤ 2 * ‖x - y‖ := by
    let a := max 1 ‖x‖
    let b := max 1 ‖y‖
    have ha1 : 1 ≤ a := le_max_left _ _
    have hb1 : 1 ≤ b := le_max_left _ _
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one ha1
    have hb : 0 < b := lt_of_lt_of_le zero_lt_one hb1
    have hba : b ≤ a := hxy
    have hiny : ‖y‖ ≤ b := le_max_right _ _
    have hdiff : a - b ≤ ‖x - y‖ := by
      have := (lipschitzWith_one_norm.const_max 1).dist_le_mul x y
      exact (le_abs_self (a - b)).trans (by simpa [a, b, Real.dist_eq, dist_eq_norm] using this)
    have hinv : a⁻¹ ≤ b⁻¹ := inv_anti₀ hb hba
    have hterm : (b⁻¹ - a⁻¹) * ‖y‖ ≤ a - b := by
      calc
        (b⁻¹ - a⁻¹) * ‖y‖ = (a - b) * (‖y‖ / (a * b)) := by
          field_simp
        _ ≤ (a - b) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hba)
          apply (div_le_one (mul_pos ha hb)).mpr
          exact hiny.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr ha1) hb.le])
        _ = a - b := mul_one _
    have hfirst : a⁻¹ * ‖x - y‖ ≤ ‖x - y‖ :=
      mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ ha).mpr ha1)
    have hid : radialClip x - radialClip y =
        a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y := by
      dsimp [radialClip, a, b]
      module
    rw [hid]
    calc
      ‖a⁻¹ • (x - y) + (a⁻¹ - b⁻¹) • y‖ ≤
          ‖a⁻¹ • (x - y)‖ + ‖(a⁻¹ - b⁻¹) • y‖ := norm_add_le _ _
      _ = a⁻¹ * ‖x - y‖ + (b⁻¹ - a⁻¹) * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr ha), abs_of_nonpos (sub_nonpos.mpr hinv)]
        ring
      _ ≤ 2 * ‖x - y‖ := by linarith
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_ofNat, dist_eq_norm]
  rcases le_total (max 1 ‖y‖) (max 1 ‖x‖) with h | h
  · exact hle x y h
  · simpa only [norm_sub_rev (radialClip y), norm_sub_rev y] using hle y x h

end FreeGroupFactorMain

open scoped NNReal BigOperators
namespace FreeGroupFactorMain

variable {E : Type uE} {A : Type uA} [NormedAddCommGroup E] [NormedRing A]

def BoundedLip (f : E → A) : Prop :=
  ∃ M K : ℝ, 0 ≤ M ∧ 0 ≤ K ∧ (∀ x, ‖f x‖ ≤ M) ∧
    ∀ x y, ‖f x - f y‖ ≤ K * ‖x - y‖

namespace BoundedLip

theorem const (c : A) : BoundedLip (fun _ : E => c) := by
  refine ⟨‖c‖, 0, norm_nonneg _, le_rfl, fun _ => le_rfl, ?_⟩
  intro x y
  simp

theorem add {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x + g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M + N, K + L, add_nonneg hM hN, add_nonneg hK hL, ?_, ?_⟩
  · intro x
    exact (norm_add_le _ _).trans (add_le_add (hfb x) (hgb x))
  · intro x y
    rw [show f x + g x - (f y + g y) = (f x - f y) + (g x - g y) by abel]
    exact (norm_add_le _ _).trans (by nlinarith only [hfl x y, hgl x y])

theorem mul {f g : E → A} (hf : BoundedLip f) (hg : BoundedLip g) :
    BoundedLip (fun x => f x * g x) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  obtain ⟨N, L, hN, hL, hgb, hgl⟩ := hg
  refine ⟨M * N, M * L + K * N, mul_nonneg hM hN,
    add_nonneg (mul_nonneg hM hL) (mul_nonneg hK hN), ?_, ?_⟩
  · intro x
    exact (norm_mul_le _ _).trans (mul_le_mul (hfb x) (hgb x) (norm_nonneg _) hM)
  · intro x y
    calc
      ‖f x * g x - f y * g y‖ =
          ‖f x * (g x - g y) + (f x - f y) * g y‖ := by
        congr 1
        noncomm_ring
      _ ≤ ‖f x‖ * ‖g x - g y‖ + ‖f x - f y‖ * ‖g y‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ M * (L * ‖x - y‖) + (K * ‖x - y‖) * N := by
        exact add_le_add
          (mul_le_mul (hfb x) (hgl x y) (norm_nonneg _) hM)
          (mul_le_mul (hfl x y) (hgb y) (norm_nonneg _)
            (mul_nonneg hK (norm_nonneg _)))
      _ = (M * L + K * N) * ‖x - y‖ := by ring

theorem star [StarRing A] [NormedStarGroup A] {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => star (f x)) := by
  obtain ⟨M, K, hM, hK, hfb, hfl⟩ := hf
  refine ⟨M, K, hM, hK, ?_, ?_⟩
  · simpa only [norm_star] using hfb
  · simpa only [← star_sub, norm_star] using hfl

theorem sum {ι : Type uι} (s : Finset ι) (f : ι → E → A)
    (hf : ∀ i ∈ s, BoundedLip (f i)) : BoundedLip (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (const (E := E) (0 : A))
  | @insert i s hi ih =>
    simpa [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem smul [NormedAlgebra ℂ A] (c : ℂ) {f : E → A} (hf : BoundedLip f) :
    BoundedLip (fun x => c • f x) := by
  simpa only [Algebra.smul_def] using (const (E := E) (algebraMap ℂ A c)).mul hf

theorem pi {ι : Type uι} [Fintype ι] {f : E → ι → A}
    (hf : ∀ i, BoundedLip (fun x => f x i)) : BoundedLip f := by
  classical
  choose M K hM hK hb hl using hf
  have hMs (i : ι) : M i ≤ ∑ j, M j :=
    Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
  have hKs (i : ι) : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i)
  have hMsum : 0 ≤ ∑ j, M j := Finset.sum_nonneg fun j _ => hM j
  have hKsum : 0 ≤ ∑ j, K j := Finset.sum_nonneg fun j _ => hK j
  refine ⟨∑ j, M j, ∑ j, K j, hMsum, hKsum, ?_, ?_⟩
  · intro x
    exact (pi_norm_le_iff_of_nonneg hMsum).mpr fun i => (hb i x).trans (hMs i)
  · intro x y
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hKsum (norm_nonneg _))).mpr
    intro i
    exact (hl i x y).trans (mul_le_mul_of_nonneg_right (hKs i) (norm_nonneg _))

theorem to_bounds {f : E → A} (hf : BoundedLip f) :
    ∃ M K : ℝ≥0, (∀ x, ‖f x‖ ≤ M) ∧ LipschitzWith K f := by
  obtain ⟨M, K, hM, hK, hb, hl⟩ := hf
  refine ⟨NNReal.mk M hM, NNReal.mk K hK, hb, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_mk] using hl x y

end BoundedLip
end FreeGroupFactorMain

end

end OAI
