import OAI.NumberTheory.DirichletL.Foundation
import OAI.NumberTheory.DirichletL.Detector.GramLatticeDecay

namespace OAI

noncomputable section
open scoped BigOperators Classical FourierTransform SchwartzMap RealInnerProductSpace

namespace ProbeGramAnnularLattice
open ProbeGramLatticeDecay ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

def AnnularSupport (a b : ℝ) (W : 𝓢(Joint, ℂ)) : Prop :=
  Function.support W ⊆ {z : Joint | a ≤ ‖z.fst‖^2 ∧ ‖z.fst‖^2 ≤ b ∧
    a ≤ ‖z.snd‖^2 ∧ ‖z.snd‖^2 ≤ b}

theorem scaled_embedding_norm_sq (m : O) (N : ℝ) (hN : 0 ≤ N) :
    ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 = ‖eisEmbedding m‖^2 / N := by
  rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hN]

theorem physical_sample_eq_zero (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (W : 𝓢(Joint, ℂ)) (hW : AnnularSupport a b W)
    (N : ℝ) (hN : 0 < N) (hsmall : N < b⁻¹) (m : O × O) :
    W (physicalPoint N m) = 0 := by
  by_contra h
  have hw := hW h
  change a ≤ ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ∧
    ‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2 ≤ b ∧ _ at hw
  have hm : m.1 ≠ 0 := by
    intro hz
    have hh := hw.1
    rw [hz, map_zero, zero_div, norm_zero, zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hh
    linarith
  have hl := one_le_eisenstein_norm_sq m.1 hm
  have hu := hw.2.1
  rw [scaled_embedding_norm_sq m.1 N hN.le, div_le_iff₀ hN] at hu
  have hs : b*N < 1 := by
    have hh := mul_lt_mul_of_pos_left hsmall hb
    simpa only [mul_inv_cancel₀ hb.ne'] using hh
  linarith

def cauchyWeight (m : O) : ℝ := ((1+‖eisEmbedding m‖^2)^2)⁻¹

theorem cauchyWeight_summable : Summable cauchyWeight := by
  change Summable (fun m : O => ((1+‖eisEmbedding m‖^2)^2)⁻¹)
  simpa only [one_mul] using scaled_eisenstein_cauchy_summable 1 zero_lt_one

theorem cauchyWeight_mass_le : (∑' m : O, cauchyWeight m) ≤ 4*(1+Real.pi)^2 := by
  simpa only [cauchyWeight, one_mul] using scaled_eisenstein_cauchy_small 1 zero_lt_one le_rfl

theorem physical_subunit_majorant (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) (m : O × O) :
    ‖W (physicalPoint N m)‖ ≤ (2:ℝ)^8 * sourceControl (Finset.Iic (8,0)) W *
      (cauchyWeight m.1 * cauchyWeight m.2) := by
  have hn (m : O) : ‖eisEmbedding m‖^2 ≤ ‖eisEmbedding m / (Real.sqrt N : ℂ)‖^2 := by
    rw [scaled_embedding_norm_sq m N hN.le, le_div_iff₀ hN]
    exact mul_le_of_le_one_right (sq_nonneg _) hN1
  have hd : (1+‖eisEmbedding m.1‖^2)^2 * (1+‖eisEmbedding m.2‖^2)^2 ≤
      (1+‖eisEmbedding m.1 / (Real.sqrt N : ℂ)‖^2)^2 *
        (1+‖eisEmbedding m.2 / (Real.sqrt N : ℂ)‖^2)^2 := by
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.1)) 2)
      (pow_le_pow_left₀ (by positivity) (add_le_add (le_refl 1) (hn m.2)) 2) (by positivity) (by positivity)
  have hp := (mul_le_mul_of_nonneg_right hd (norm_nonneg (W (physicalPoint N m)))).trans
    (product_decay W (eisEmbedding m.1 / (Real.sqrt N : ℂ))
      (eisEmbedding m.2 / (Real.sqrt N : ℂ)))
  dsimp only [cauchyWeight]
  rw [← mul_inv, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using hp

theorem physical_subunit_bound (W : 𝓢(Joint, ℂ))
    (N : ℝ) (hN : 0 < N) (hN1 : N ≤ 1) :
    (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤
      ((2:ℝ)^8*(4*(1+Real.pi)^2)^2) * sourceControl (Finset.Iic (8,0)) W := by
  have hg := cauchyWeight_summable
  have hp := hg.mul_of_nonneg hg (fun _ => by unfold cauchyWeight; positivity)
    (fun _ => by unfold cauchyWeight; positivity)
  calc
    _ ≤ ∑' m : O × O, ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*
        (cauchyWeight m.1*cauchyWeight m.2) :=
      (physical_summable W N hN).tsum_le_tsum (physical_subunit_majorant W N hN hN1)
        (hp.mul_left _)
    _ = ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(∑' m : O, cauchyWeight m)^2 := by
      rw [tsum_mul_left, ← hg.tsum_mul_tsum hg hp, pow_two]
    _ ≤ ((2:ℝ)^8*sourceControl (Finset.Iic (8,0)) W)*(4*(1+Real.pi)^2)^2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (sourceControl_nonneg _ _))
      exact pow_le_pow_left₀ (tsum_nonneg (fun _ => by unfold cauchyWeight; positivity))
        cauchyWeight_mass_le 2
    _ = _ := by ring

theorem annular_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W → ∀ (N : ℝ), 0 < N →
        (∑' m : O × O, ‖W (physicalPoint N m)‖) ≤ C * sourceControl S W * N^2 := by
  obtain ⟨S₀,C₀,hC₀,h₀⟩ := physical_lattice_bound
  let K : ℝ := (2:ℝ)^8*(4*(1+Real.pi)^2)^2
  have hK : 0 < K := by dsimp [K]; positivity
  have hb : 0 < b := ha.trans hab
  refine ⟨S₀ ∪ Finset.Iic (8,0),C₀ + K*b^2,by positivity,?_⟩
  intro W hW N hN
  have hS₀ := sourceControl_mono (S := S₀) (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_left W
  have hS₁ := sourceControl_mono (S := Finset.Iic (8,0))
    (T := S₀ ∪ Finset.Iic (8,0)) Finset.subset_union_right W
  by_cases hN1 : 1 ≤ N
  · apply (h₀ W N hN1).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul (le_add_of_nonneg_right (by positivity)) hS₀
      (sourceControl_nonneg _ _) (by positivity)
  · by_cases hs : N < b⁻¹
    · have hz : (∑' m : O × O, ‖W (physicalPoint N m)‖) = 0 := by
        calc
          _ = ∑' _m : O × O, (0:ℝ) := tsum_congr (fun m => by
            rw [physical_sample_eq_zero a b ha hb W hW N hN hs m, norm_zero])
          _ = 0 := tsum_zero
      rw [hz]
      exact mul_nonneg (mul_nonneg (by positivity) (sourceControl_nonneg _ _)) (sq_nonneg _)
    · have hBN : 1 ≤ b*N := by
        have hh := mul_le_mul_of_nonneg_left (le_of_not_gt hs) hb.le
        simpa only [mul_inv_cancel₀ hb.ne'] using hh
      have hBN2 : 1 ≤ b^2*N^2 := by nlinarith [sq_nonneg (b*N-1)]
      calc
        _ ≤ K * sourceControl (Finset.Iic (8,0)) W :=
          physical_subunit_bound W N hN (le_of_not_ge hN1)
        _ ≤ K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W :=
          mul_le_mul_of_nonneg_left hS₁ hK.le
        _ ≤ (K * sourceControl (S₀ ∪ Finset.Iic (8,0)) W) * (b^2*N^2) :=
          le_mul_of_one_le_right (mul_nonneg hK.le (sourceControl_nonneg _ _)) hBN2
        _ = (K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by ring
        _ ≤ (C₀+K*b^2) * sourceControl (S₀ ∪ Finset.Iic (8,0)) W * N^2 := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀.le)
              (sourceControl_nonneg _ _)) (sq_nonneg _)

theorem weighted_summable (W : 𝓢(Joint, ℂ)) (d : O × O → ℂ) (B : ℝ)
    (hd : ∀ m, ‖d m‖ ≤ B) (N : ℝ) (hN : 0 < N) :
    Summable (fun m : O × O => d m * W (physicalPoint N m)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ ((physical_summable W N hN).mul_left B)
  intro m
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)

theorem annular_weighted_lattice_bound (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), AnnularSupport a b W →
      ∀ (d : O × O → ℂ) (B : ℝ), 0 ≤ B → (∀ m, ‖d m‖ ≤ B) →
      ∀ (N : ℝ), 0 < N →
        Summable (fun m : O × O => d m * W (physicalPoint N m)) ∧
        ‖∑' m : O × O, d m * W (physicalPoint N m)‖ ≤ C * sourceControl S W * B * N^2 := by
  obtain ⟨S,C,hC,hbound⟩ := annular_lattice_bound a b ha hab
  refine ⟨S,C,hC,?_⟩
  intro W hW d B hB hd N hN
  refine ⟨weighted_summable W d B hd N hN,?_⟩
  calc
    _ ≤ ∑' m : O × O, B * ‖W (physicalPoint N m)‖ := by
      apply (norm_tsum_le_tsum_norm ((weighted_summable W d B hd N hN).norm)).trans
      apply ((weighted_summable W d B hd N hN).norm).tsum_le_tsum _
        ((physical_summable W N hN).mul_left B)
      intro m
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hd m) (norm_nonneg _)
    _ = B * ∑' m : O × O, ‖W (physicalPoint N m)‖ := tsum_mul_left
    _ ≤ B * (C * sourceControl S W * N^2) := mul_le_mul_of_nonneg_left (hbound W hW N hN) hB
    _ = _ := by ring

end ProbeGramAnnularLattice

end

end OAI
