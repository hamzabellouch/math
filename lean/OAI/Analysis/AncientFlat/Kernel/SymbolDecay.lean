import OAI.Analysis.AncientFlat.Kernel.SymbolJets
import OAI.Analysis.AncientFlat.Kernel.BilapNorm

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff
namespace FlatSimilarity
variable {V : Type} [NormedAddCommGroup V]
def decayWeight (x : V) : ℝ := (1+‖x‖)⁻¹
lemma decayWeight_pos (x : V) : 0<decayWeight x := by unfold decayWeight; positivity
lemma decayWeight_le_one (x : V) : decayWeight x≤1 := by
  apply inv_le_one_of_one_le₀
  linarith [norm_nonneg x]
lemma symbol_decay_le_weight (x : V) (n : ℕ) : (1+‖x‖)^(-(4:ℝ)-n)≤decayWeight x := by
  change _≤(1+‖x‖)⁻¹
  rw [←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
variable [InnerProductSpace ℝ V]
lemma decayWeight_smul (r : ℝ) (hr : 1≤r) (x : V) : decayWeight (r • x)≤decayWeight x := by
  unfold decayWeight
  rw [norm_smul,Real.norm_of_nonneg (by linarith)]
  apply inv_anti₀ (by positivity)
  nlinarith [norm_nonneg x]
omit [InnerProductSpace ℝ V] in
lemma decayWeight_translate (x z : V) : decayWeight x≤(1+‖x-z‖)*decayWeight z := by
  unfold decayWeight
  have h1 : 0<1+‖x‖ := by positivity
  have h2 : 0<1+‖z‖ := by positivity
  rw [←div_eq_mul_inv,inv_eq_one_div,div_le_div_iff₀ h1 h2]
  simp only [one_mul]
  have hn : ‖z‖≤‖x‖+‖x-z‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub x z
  nlinarith [mul_nonneg (norm_nonneg x) (norm_nonneg (x-z))]
lemma SymbolBounds.weighted_deviation_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ (∀ x, ‖iteratedFDeriv ℝ n (fun y => Af y-c^2) x‖≤C*decayWeight x) ∧
      (∀ x, ‖iteratedFDeriv ℝ n Bf x‖≤C*decayWeight x) := by
  obtain ⟨C,hC,hb⟩ := h.2.2.2.2 n
  have hb' (x : V) := (hb x).trans (mul_le_mul_of_nonneg_left (symbol_decay_le_weight x n) hC)
  exact ⟨C,hC,fun x => (le_add_of_nonneg_right (norm_nonneg _)).trans (hb' x),
    fun x => (le_add_of_nonneg_left (norm_nonneg _)).trans (hb' x)⟩
def movingDeviation (c : ℝ) (Af : V → ℝ) (t : ℝ) (x : V) : ℝ :=
  Real.exp (-t)/16*(Af (Real.exp (t/4) • x)-c^2)
lemma movingDeviation_smooth {c : ℝ} {Af : V → ℝ} (hf : ContDiff ℝ ∞ Af) (t : ℝ) :
    ContDiff ℝ ∞ (movingDeviation c Af t) :=
  contDiff_const.mul ((hf.comp (contDiff_const.smul contDiff_id)).sub contDiff_const)
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
lemma weighted_scale_jets (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ x, ‖iteratedFDeriv ℝ n f x‖≤C*decayWeight x) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (x : V) :
    ‖iteratedFDeriv ℝ n (fun y => f (Real.exp (t/4) • y)) x‖≤
      (Real.exp (1/4)^n*C)*decayWeight x := by
  rw [iteratedFDeriv_scale_real _ _ hf,norm_smul,Real.norm_of_nonneg (by positivity)]
  have hr : 1≤Real.exp (t/4) := Real.one_le_exp_iff.mpr (by linarith [ht.1])
  have he : Real.exp (t/4)≤Real.exp (1/4) := Real.exp_le_exp.mpr (by linarith [ht.2])
  calc
    _ ≤ Real.exp (1/4)^n*(C*decayWeight x) := mul_le_mul
      (pow_le_pow_left₀ (Real.exp_pos _).le he n)
      ((hb _).trans (mul_le_mul_of_nonneg_left (decayWeight_smul _ hr x) hC))
      (norm_nonneg _) (by positivity)
    _ = _ := by ring
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma movingDeviation_norm_jet {c : ℝ} {Af : V → ℝ} (hf : ContDiff ℝ ∞ Af)
    (n : ℕ) (t : ℝ) (x : V) :
    ‖iteratedFDeriv ℝ n (movingDeviation c Af t) x‖ =
      ‖Real.exp (-t)/16‖ * ‖iteratedFDeriv ℝ n (fun y => Af (Real.exp (t/4) • y)-c^2) x‖ := by
  have hg : ContDiff ℝ ∞ (fun y : V => Af (Real.exp (t/4) • y)-c^2) :=
    (hf.comp (contDiff_const.smul contDiff_id)).sub contDiff_const
  unfold movingDeviation
  have he := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (x := x) (a := Real.exp (-t)/16)
    (hg.of_le (by exact_mod_cast (le_top : (n:ℕ∞)≤⊤))).contDiffAt
  simpa only [smul_eq_mul,norm_smul] using congrArg norm he
lemma SymbolBounds.moving_weighted_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ x,
      ‖iteratedFDeriv ℝ n (movingDeviation c Af t) x‖≤C*decayWeight x ∧
      ‖iteratedFDeriv ℝ n (fun y => Bf (Real.exp (t/4) • y)) x‖≤C*decayWeight x := by
  obtain ⟨C,hC,hA,hB⟩ := h.weighted_deviation_jets n
  refine ⟨Real.exp (1/4)^n*C,by positivity,fun t ht x => ⟨?_,?_⟩⟩
  · rw [movingDeviation_norm_jet h.2.2.1]
    have hw : ‖Real.exp (-t)/16‖≤1 := by
      rw [Real.norm_of_nonneg (by positivity)]
      have he : Real.exp (-t)≤1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
      linarith
    calc
      _≤1*((Real.exp (1/4)^n*C)*decayWeight x) := mul_le_mul hw
        (weighted_scale_jets _ (h.2.2.1.sub contDiff_const) n C hC hA ht x) (norm_nonneg _) zero_le_one
      _=_ := one_mul _
  · exact weighted_scale_jets Bf h.2.2.2.1 n C hC hB ht x
lemma SymbolBounds.moving_four_weighted_jets {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf) :
    ∃ C : ℝ, 0≤C ∧ ∀ t ∈ Icc (0:ℝ) 1, ∀ n : ℕ, n≤4 → ∀ x,
      ‖iteratedFDeriv ℝ n (movingDeviation c Af t) x‖≤C*decayWeight x ∧
      ‖iteratedFDeriv ℝ n (fun y => Bf (Real.exp (t/4) • y)) x‖≤C*decayWeight x := by
  choose C hn hb using h.moving_weighted_jets
  refine ⟨∑ n ∈ Finset.range 5,C n,Finset.sum_nonneg (fun n _ => hn n),fun t ht n hn' x => ?_⟩
  have he : C n≤∑ n ∈ Finset.range 5,C n := Finset.single_le_sum (fun i _ => hn i) (by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hn')
  have he' := mul_le_mul_of_nonneg_right he (decayWeight_pos x).le
  exact ⟨((hb n t ht x).1).trans he',((hb n t ht x).2).trans he'⟩
lemma SymbolBounds.movingDeviation_temperate {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : (movingDeviation c Af t).HasTemperateGrowth := by
  apply FlatDuality.temperate_of_bounded_jets _ (movingDeviation_smooth h.2.2.1 t)
  intro n
  obtain ⟨C,hC,hb⟩ := h.moving_weighted_jets n
  exact ⟨C,fun x => ((hb t ht x).1).trans (mul_le_of_le_one_right hC (decayWeight_le_one x))⟩
lemma SymbolBounds.movingB_temperate {c : ℝ} {Af Bf : V → ℝ} (h : SymbolBounds c Af Bf)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : (fun x : V => Bf (Real.exp (t/4) • x)).HasTemperateGrowth := by
  apply FlatDuality.temperate_of_bounded_jets _ (h.2.2.2.1.comp (contDiff_const.smul contDiff_id))
  intro n
  obtain ⟨C,hC,hb⟩ := h.moving_weighted_jets n
  exact ⟨C,fun x => ((hb t ht x).2).trans (mul_le_of_le_one_right hC (decayWeight_le_one x))⟩
end FlatSimilarity

end

end OAI
