import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.OrderedAngularAssignmentsSublist

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set Metric
open scoped ContDiff Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_contDiffOn_derivative_bound {f : E → F} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (m : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ j ≤ m, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C := by
  have hbound (j : ℕ) : ∃ C : ℝ, ∀ x ∈ K,
      ‖iteratedFDerivWithin ℝ j f U x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤)) hU.uniqueDiffOn).mono hKU)
  induction m with
  | zero =>
    obtain ⟨C,hC⟩ := hbound 0
    refine ⟨max 1 C, le_max_left _ _, ?_⟩
    intro j hj x hx
    have : j=0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact (hC x hx).trans (le_max_right _ _)
  | succ m ih =>
    obtain ⟨D,hD,hboundD⟩ := ih
    obtain ⟨C,hC⟩ := hbound (m+1)
    refine ⟨max D C, hD.trans (le_max_left _ _), ?_⟩
    intro j hj x hx
    by_cases hjm : j ≤ m
    · exact (hboundD j hjm x hx).trans (le_max_left _ _)
    · have : j=m+1 := by omega
      subst j
      exact (hC x hx).trans (le_max_right _ _)

theorem compact_chart_derivative_bound
    {f : E → F} {w : E → ℂ} {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hf : ContDiffOn ℝ ∞ f U) (hw : ContDiffOn ℝ ∞ w U)
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : F → ℂ) (A : ℝ),
      ContDiff ℝ ∞ b → 1 ≤ A →
      tsupport (fun x => w x * b (f x)) ⊆ K →
      (∀ j ≤ m, ∀ y ∈ f '' K, ‖iteratedFDeriv ℝ j b y‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j (fun x => w x * b (f x)) x‖ ≤ D*A^j := by
  obtain ⟨M,hM,hMf⟩ := compact_contDiffOn_derivative_bound hU hK hKU hf m
  obtain ⟨W,hW,hWw⟩ := compact_contDiffOn_derivative_bound hU hK hKU hw m
  let B : ℝ := (m.factorial:ℝ)*C*M^m
  let D : ℝ := 2^m * W * B
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hW0 : 0 ≤ W := le_trans zero_le_one hW
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  intro b A hb hA hsupp hderiv j hj x
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  by_cases hx : x ∈ K
  · have hxU := hKU hx
    have hcomp (k : ℕ) (hkm : k ≤ m) :
        ‖iteratedFDerivWithin ℝ k (b ∘ f) U x‖ ≤ B*A^k := by
      have hbase := norm_iteratedFDerivWithin_comp_le (N := ∞) (t := univ)
        hb.contDiffOn hf (by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)) uniqueDiffOn_univ hU.uniqueDiffOn
        (fun _ _ => mem_univ _) hxU (C := C*A^k) (D := M)
        (fun i hik => by
          rw [iteratedFDerivWithin_univ]
          exact (hderiv i (hik.trans hkm) (f x) ⟨x,hx,rfl⟩).trans
            (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA hik) hC))
        (fun i hi hik => (hMf i (hik.trans hkm) x hx).trans
          (by simpa using pow_le_pow_right₀ hM hi))
      apply hbase.trans
      calc
        (k.factorial:ℝ)*(C*A^k)*M^k ≤ (m.factorial:ℝ)*(C*A^k)*M^m := by
          gcongr
        _ = B*A^k := by dsimp [B]; ring
    have hbg : ContDiffOn ℝ ∞ (b ∘ f) U := hb.comp_contDiffOn hf
    have hprod : ContDiffOn ℝ ∞ (fun x => w x * b (f x)) U := hw.mul hbg
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      ((hprod.contDiffAt (hU.mem_nhds hxU)).of_le (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))) hxU]
    have hbase := norm_iteratedFDerivWithin_mul_le hw hbg hU.uniqueDiffOn hxU
      (by exact_mod_cast (le_top : (j:ℕ∞) ≤ ⊤))
    apply hbase.trans
    have hsum : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = 2^j := by
      exact_mod_cast Nat.sum_range_choose j
    calc
      (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ) * ‖iteratedFDerivWithin ℝ i w U x‖ *
        ‖iteratedFDerivWithin ℝ (j-i) (b ∘ f) U x‖) ≤
          ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ) * W * (B*A^j) := by
            apply Finset.sum_le_sum
            intro i hi
            have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
            have hk : j-i ≤ m := (Nat.sub_le _ _).trans hj
            apply mul_le_mul
              (mul_le_mul_of_nonneg_left (hWw i (hij.trans hj) x hx) (by positivity))
              ((hcomp (j-i) hk).trans
                (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA (Nat.sub_le _ _)) hB))
              (norm_nonneg _) (by positivity)
      _ = 2^j * W * (B*A^j) := by rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
      _ ≤ 2^m * W * (B*A^j) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj) hW0)
          (mul_nonneg hB (pow_nonneg hA0 _))
      _ = D*A^j := by dsimp [D]; ring
  · have hx' : x ∉ tsupport (fun x => w x * b (f x)) := fun h => hx (hsupp h)
    have hz : iteratedFDeriv ℝ j (fun x => w x * b (f x)) x = 0 :=
      Function.notMem_support.mp (fun h => hx' (support_iteratedFDeriv_subset j h))
    rw [hz, norm_zero]
    dsimp [D]
    positivity

end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
