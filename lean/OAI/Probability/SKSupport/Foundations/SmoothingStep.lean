import Mathlib
import OAI.Probability.SKSupport.Foundations.VarianceHeatGradientBound

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace ZeroTemperatureSK.Heat
open ZeroTemperatureSK.Smoothing

lemma exists_smoothing_step {D δ : ℝ} (hD : 0 ≤ D) (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ δ/2 ∧
      8*kernelConstant*D*Real.sqrt η ≤ 1/2 := by
  have hκ := kernelConstant_nonneg
  let q : ℝ := 1/(16*(kernelConstant*D+1))
  have hq : 0 < q := by dsimp [q]; positivity
  let η := min (δ/2) (q^2)
  have hη : 0 < η := lt_min (by positivity) (sq_pos_of_pos hq)
  refine ⟨η,hη,min_le_left _ _,?_⟩
  have hs : Real.sqrt η ≤ q := Real.sqrt_le_iff.mpr ⟨hq.le,min_le_right _ _⟩
  calc
    8*kernelConstant*D*Real.sqrt η ≤ 8*kernelConstant*D*q :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (8*kernelConstant*D)/(16*(kernelConstant*D+1)) := by dsimp [q]; ring
    _ ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)

theorem finiteGradient_uniform_smoothing (m : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : ℝ → ℝ), RegularDatum f → LipschitzWith 1 f →
      ∀ (c : ℕ → ℝ≥0) (h : ℝ≥0) (N i : ℕ) (L : ℝ), 0 ≤ L →
      L+δ ≤ (N:ℝ)*h →
      (∀ s ∈ Icc (0:ℝ) (L+δ), finiteCoeff c h N i s ≤ D) →
      ∀ j ≤ m, ∀ t ∈ Icc (0:ℝ) L, ∀ x : ℝ,
        |iteratedDeriv j (deriv (finiteValue c h f N i t)) x| ≤ C := by
  induction m with
  | zero =>
    intro δ hδ
    refine ⟨1,by positivity,?_⟩
    intro f hf hLip c h N i L hL hhor hcoef j hj t ht x
    have hj0 : j = 0 := by omega
    subst j
    simpa only [iteratedDeriv_zero,Real.norm_eq_abs,NNReal.coe_one] using
      norm_deriv_le_of_lipschitz (x₀ := x) (finiteValue_lipschitz hLip c h N i t)
  | succ m ih =>
    intro δ hδ
    obtain ⟨C,hC,hbounds⟩ := ih (δ/2) (by positivity)
    obtain ⟨η,hη,hηδ,hηsmall⟩ := exists_smoothing_step hD hδ
    let R : ℝ := D*(∑ j ∈ Finset.range m,(m.choose (j+1):ℝ))*C^2
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let K : ℝ := 2*kernelConstant*(C+2*R*η)/Real.sqrt η
    have hκ := kernelConstant_nonneg
    have hK : 0 ≤ K := by dsimp [K]; positivity
    refine ⟨max C K,le_max_of_le_left hC,?_⟩
    intro f hf hLip c h N i L hL hhor hcoef j hj t ht x
    have hlow : ∀ k ≤ m, ∀ s ∈ Icc (0:ℝ) (L+δ/2), ∀ z : ℝ,
        |iteratedDeriv k (deriv (finiteValue c h f N i s)) z| ≤ C := by
      apply hbounds f hf hLip c h N i (L+δ/2) (by positivity)
      · linarith
      · intro s hs
        apply hcoef s
        constructor
        · exact hs.1
        · linarith [hs.2]
    by_cases hjm : j ≤ m
    · exact (hlow j hjm t ⟨ht.1,by linarith [ht.2]⟩ x).trans (le_max_left _ _)
    have hje : j = m+1 := by omega
    subst j
    let V : ℝ → ℝ → ℝ := fun r => iteratedDeriv m (deriv (finiteValue c h f N i r))
    let G : ℝ → ℝ → ℝ := fun r => iteratedDeriv m (finiteBurgersSource c h f N i r)
    have hU := finiteGradient_family hf hLip c h N i
    have hS := finiteBurgersSource_family hf hLip c h N i
    have hV : BoundedSmoothFamily V := hU.iteratedDeriv m
    have hG : BoundedSmoothFamily G := hS.iteratedDeriv m
    obtain ⟨A₀,hA₀⟩ := hG.bound
    obtain ⟨B₀,hB₀⟩ := hG.deriv.bound
    obtain ⟨C₀,hC₀⟩ := hV.deriv.bound
    have htb : t < t+η := by linarith
    have hbL : t+η ≤ L+δ/2 := by linarith [ht.2]
    have hbhor : t+η ≤ (N:ℝ)*h := by linarith
    have hterminal (z : ℝ) : |V (t+η) z| ≤ C :=
      hlow m le_rfl (t+η) ⟨by linarith [ht.1],hbL⟩ z
    have hsource (r : ℝ) (hr : r ∈ Icc t (t+η)) (z : ℝ) :
        |G r z| ≤ D*|deriv (V r) z|+R := by
      apply iteratedDeriv_finiteBurgersSource_bound hf hLip c h N i m hC hD
      · apply hcoef r
        exact ⟨ht.1.trans hr.1,by linarith [hr.2]⟩
      · intro k hk y
        exact hlow k hk r ⟨ht.1.trans hr.1,hr.2.trans hbL⟩ y
    have hmild (r : ℝ) (hr : r ∈ Ico t (t+η)) (z : ℝ) :
        V r z = varianceHeat (t+η-r) (V (t+η)) z+
          ∫ s in r..t+η, varianceHeat (s-r) (G s) z := by
      exact iteratedDeriv_mild hU hS (finiteGradient_mild hf hLip c h N i
        (ht.1.trans hr.1) hr.2.le hbhor) m z
    have hshort : 8*kernelConstant*D*Real.sqrt (t+η-t) ≤ 1/2 := by
      simpa only [add_sub_cancel_left] using hηsmall
    have hbound := uniform_gradient_bound_of_mild htb hC hD hR
      (hV.regular (t+η)) hG.measurable hG.regular hA₀ hB₀
      (fun r _ z => hC₀ r z) hterminal hsource hmild hshort x
    apply (show |iteratedDeriv (m+1) (deriv (finiteValue c h f N i t)) x| ≤ K from ?_).trans
      (le_max_right _ _)
    simpa only [V,K,iteratedDeriv_succ,add_sub_cancel_left] using hbound

end ZeroTemperatureSK.Heat

end
end
end
end
end

end OAI
