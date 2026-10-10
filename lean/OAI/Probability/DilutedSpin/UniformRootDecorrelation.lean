import OAI.Probability.DilutedSpin.ActualCharging
import OAI.Probability.DilutedSpin.SingletonRoot

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (n d N : ℕ)
    (T : (z : Z) → KernelTower (Ω z) n)
    (X : (z : Z) → FinitePath (Ω z) n → Fin N → ℝ)
    (m : Fin (n+1) → ℝ) (S : PrescribedTree n) (a b : S.Leaf)

noncomputable def pairRootMean : ℝ :=
  ∫ z, (S.sampleLaw (T z)).expect (fun x =>
    FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ

noncomputable def pairRootCovariance : ℝ :=
  (∫ z, pairObservableHistory (T z) m S a d
    (fun x y => FiniteLaw.dot (X z x) (X z y))
    (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ) -
  pairRootMean μ Ω n N T X S a b *
    (∫ z, pairObservableHistory (T z) m S a d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) (fun _ => 1) ∂μ)

omit [IsProbabilityMeasure μ] in
lemma pairRootCovariance_center (hd : d < n) (hab : splitDepth S a b = d)
    (hend : m (Fin.last n) = 1) :
    pairRootCovariance μ Ω n d N T X m S a b =
      (∫ z, pairObservableHistory (T z) m S a d
        (fun x y => FiniteLaw.dot (X z x) (X z y))
        (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) ∂μ) +
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)*(pairRootMean μ Ω n N T X S a b)^2 := by
  unfold pairRootCovariance
  have he (z : Z) := pairObservableHistory_const (T z) m hend S a d hd
    (fun x y => FiniteLaw.dot (X z x) (X z y))
  have hmarg (z : Z) : KernelTower.pairExpect n (T z) d
      (fun x y => FiniteLaw.dot (X z x) (X z y)) =
      (S.sampleLaw (T z)).expect (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))) := by
    have q := pair_marginal S (T z) a b (fun x y => FiniteLaw.dot (X z x) (X z y))
    rw [hab] at q
    exact q.symm
  simp_rw [he,hmarg]
  rw [integral_const_mul]
  change _ - pairRootMean μ Ω n N T X S a b *
    ((m ⟨d,by omega⟩-m ⟨d+1,by omega⟩)*pairRootMean μ Ω n N T X S a b) = _
  ring

/-- The single-copy conditional covariance estimate with the exact shared
root covariance. Applicability is to arbitrary old trees, not surrogate laws. -/
theorem root_decorrelation_bound (hd : d < n) (hab : splitDepth S a b = d)
    (v : S.Internal) (hav : freshSplitDepth S v a = d) (hbv : freshSplitDepth S v b = d)
    (hm : Monotone m) (hp : ∀ j, 0 ≤ m j) (hend : m (Fin.last n) = 1)
    (hX : ∀ z x i, |X z x i| ≤ 1)
    (hOld : ∀ z c, splitDepth S a c = d → ∀ x : Sample (Ω z) S,
      X z (S.pathAt c x) = X z (S.pathAt b x))
    (hE : Integrable (fun z => KernelTower.prefixEnergyAt n (T z) d (X z)) μ)
    (hA : Integrable (fun z => (S.sampleLaw (T z)).expect (fun x =>
      FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))^2)) μ)
    (hH : Integrable (fun z => pairObservableHistory (T z) m S a d
      (fun x y => FiniteLaw.dot (X z x) (X z y))
      (fun x => FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x)))) μ) :
    (-gamma S m v)*(∫ z, KernelTower.prefixEnergyAt n (T z) d (X z) ∂μ) ≤
      (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩) + pairRootCovariance μ Ω n d N T X m S a b := by
  have hi := integral_mono (hE.const_mul (-gamma S m v))
    ((hA.const_mul (m ⟨d+1,by omega⟩-m ⟨d,by omega⟩)).add hH)
    (fun z => general_decorrelation_bound_at n d hd (T z) m hm hp hend S a b v hab hav hbv
      (X z) (hOld z))
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul,integral_add (hA.const_mul _) hH,integral_const_mul] at hi
  rw [pairRootCovariance_center μ Ω n d N T X m S a b hd hab hend]
  have hAone : (∫ z, (S.sampleLaw (T z)).expect (fun x =>
      FiniteLaw.dot (X z (S.pathAt a x)) (X z (S.pathAt b x))^2) ∂μ) ≤ 1 := by
    calc
      _ ≤ ∫ _z : Z, (1:ℝ) ∂μ := integral_mono hA (integrable_const 1) (fun z => by
        calc
          _ ≤ (S.sampleLaw (T z)).expect (fun _ => (1:ℝ)) :=
            FiniteLaw.expect_mono _ (fun x => (sq_le_one_iff_abs_le_one _).mpr
              (FiniteLaw.abs_dot_le_one _ _ (hX z _) (hX z _)))
          _ = _ := FiniteLaw.expect_const _ _)
      _ = 1 := by simp
  have hδ : 0 ≤ m ⟨d+1,by omega⟩-m ⟨d,by omega⟩ := sub_nonneg.mpr (hm (by simp))
  have hv := mul_nonneg hδ (sq_nonneg (pairRootMean μ Ω n N T X S a b))
  have hs := mul_le_mul_of_nonneg_left hAone hδ
  linarith

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
variable {L : ℕ}

/-- Unlike a bound by all grid vertices, the exact full history mass is
uniform in the number of unary levels. -/
lemma pairHistoryMass_grid (hL : 0<L) (S : PrescribedTree L) (a : S.Leaf) :
    pairHistoryMass S (grid L 0 L) a=2*(leaves S:ℝ)-1 := by
  unfold pairHistoryMass
  rw [sum_abs_gamma_grid hL S,Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,card_leaf]
  have hp : 1≤leaves S := by
    rw [← card_leaf]
    exact Fintype.card_pos_iff.mpr ⟨a⟩
  rw [Nat.cast_sub hp]
  simp only [Nat.cast_one]
  ring

end DilutedSpinGlass.PrescribedTree
end

end

end OAI
