import OAI.Analysis.CircleDomains.Rigidity.IntervalTraceExtension
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace OAI

/-!
# Payment from smooth functions on open gaps

Finite energy supplies the endpoint traces, even when the function has
no prescribed values on the removed intervals. Bounds on the endpoint
traces are used only for the jumps across those intervals.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_from_open_gaps
    (n : ℕ) (a b : Fin (n + 1) → ℝ) (f : ℝ → ℝ) (d ρ : ℝ → ℝ)
    (A : Fin n → ℝ) (hab : ∀ i, a i < b i)
    (hd : ∀ i x, x ∈ Ioo (a i) (b i) → HasDerivAt f (d x) x)
    (hi : ∀ i, IntervalIntegrable d volume (a i) (b i))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ i x, x ∈ Ioo (a i) (b i) → |d x| ≤ ρ x)
    (hdisj : Pairwise (Disjoint on fun i => Ioo (a i) (b i)))
    (hzero : Tendsto f (𝓝[Ioo (a 0) (b 0)] (a 0)) (𝓝 0))
    (hone : Tendsto f (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))]
      (b (Fin.last n))) (𝓝 1))
    (hjump : ∀ (i : Fin n) u v,
      Tendsto f (𝓝[Ioo (a i.castSucc) (b i.castSucc)] (b i.castSucc)) (𝓝 u) →
      Tendsto f (𝓝[Ioo (a i.succ) (b i.succ)] (a i.succ)) (𝓝 v) → |v - u| ≤ A i) :
    1 ≤ (∫ x, ρ x) + ∑ i, A i := by
  choose g hg heq hleft hright using fun i =>
    exists_absolutelyContinuous_extension_of_integrable_derivative (hab i) (hd i) (hi i)
  have hgderiv (i : Fin (n + 1)) (x : ℝ) (hx : x ∈ Ioo (a i) (b i)) :
      deriv (g i) x = d x := by
    have hevent : g i =ᶠ[𝓝 x] f := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with z hz
      exact heq i hz
    exact ((hd i x hx).congr_of_eventuallyEq hevent).deriv
  have hfirst : g 0 (a 0) = 0 := by
    have : NeBot (𝓝[Ioo (a 0) (b 0)] (a 0)) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by simpa [closure_Ioo (hab 0).ne] using (hab 0).le)
    exact tendsto_nhds_unique (hleft 0) hzero
  have hlast : g (Fin.last n) (b (Fin.last n)) = 1 := by
    have : NeBot (𝓝[Ioo (a (Fin.last n)) (b (Fin.last n))] (b (Fin.last n))) :=
      mem_closure_iff_nhdsWithin_neBot.mp (by
        rw [closure_Ioo (hab (Fin.last n)).ne]
        exact right_mem_Icc.mpr (hab (Fin.last n)).le)
    exact tendsto_nhds_unique (hright (Fin.last n)) hone
  have hline := line_payment_across_finite_gaps n a b g A (fun i => (hab i).le)
    hg hfirst hlast (fun i => hjump i _ _ (hright i.castSucc) (hleft i.succ))
  have hbound (i : Fin (n + 1)) :
      (∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x in Ioo (a i) (b i), ρ x := by
    rw [intervalIntegral.integral_of_le (hab i).le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_mono_on ?_ hρ.integrableOn measurableSet_Ioo ?_
    · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hab i).le).mp
        (hg i).intervalIntegrable_deriv.abs
    · intro x hx
      rw [hgderiv i x hx]
      exact hdom i x hx
  have hsum : (∑ i, ∫ x in a i..b i, |deriv (g i) x|) ≤ ∫ x, ρ x := by
    calc
      _ ≤ ∑ i, ∫ x in Ioo (a i) (b i), ρ x := Finset.sum_le_sum (fun i _ => hbound i)
      _ = ∫ x in ⋃ i, Ioo (a i) (b i), ρ x :=
        (integral_iUnion_fintype (fun _ => measurableSet_Ioo) hdisj
          (fun _ => hρ.integrableOn)).symm
      _ ≤ _ := setIntegral_le_integral hρ (Eventually.of_forall hpos)
  exact hline.trans (add_le_add hsum le_rfl)

end CircleDomainRigidity

end OAI
