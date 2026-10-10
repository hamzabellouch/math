import OAI.Probability.DilutedSpin.FunctionalStability
import OAI.Probability.DilutedSpin.SameInsertionAverage

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (μ : Measure (FullRootState Y X I M)) [IsProbabilityMeasure μ]
    (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (q : Fin (L+2) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

include hb in
/-- The actual finite-root logarithmic comparison, with an explicit uniform
 geometric remainder and the Q-averaged physical shape defect. -/
lemma integral_root_log_comparison (hm : Monotone q) (hpos : ∀ j, 0 ≤ q j)
    (hnz : ∀ j : Fin (L+1), q j.succ≠0) (hroot : q 0=0) (hend : q (Fin.last (L+1))=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q (fun j => q j.succ) base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i))
    (a : ℕ) (F : (Fin a → Spin) → ℝ) {C : ℝ} (hC : 0≤C) (hF : ∀ s, |F s|≤C) (K : ℕ) :
    |(∫ z, sameInsertionAverage T Q (fun j => q j.succ) base old V a F z ∂μ)-
      (∫ z, independentInsertion T Q (fun j => q j.succ) base old V a F z
        ∂Measure.pi (fun _ : Fin a => μ.prod (siteLaw N)))| ≤
      2*(∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1))+
      ∑ k∈Finset.range K, |insertionRadius C|^(k+1)/(k+1)*((a:ℝ)*
        qExpect q (fun S => shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
          (rootTower T Q (fun j => q j.succ) base old)
          (rootVector (fun y i => spin (V y i)))) k (single (L+1))) := by
  let m := fun i : Fin (L+1) => q i.succ
  let f := fun s => normalizedInsertion C (F s)
  let ν := Measure.pi (fun _ : Fin a => μ.prod (siteLaw N))
  have hmp : ∀ i, 0 < m i := fun i => lt_of_le_of_ne (hpos i.succ) (hnz i).symm
  have hme : m (Fin.last L)=1 := hend
  have hf : ∀ s, |f s|≤1 := fun s => normalizedInsertion_bound hC (hF s)
  let u := fun z k => qExpect q (fun S => sameTreeCoefficient S T Q m base old V a f z) k (single (L+1))
  let v := fun z k => qExpect q (fun S => independentTreeCoefficient S T Q m base old V a f z) k (single (L+1))
  have hui (S : PrescribedTree (L+1)) : Integrable (sameTreeCoefficient S T Q m base old V a f) μ :=
    Pattern.bounded_integrable (measurable_sameTreeCoefficient S T Q m base old V hb a f)
      (sameTreeCoefficient_bound S T Q m base old V a f hf)
  have hvi (S : PrescribedTree (L+1)) : Integrable (independentTreeCoefficient S T Q m base old V a f) ν :=
    Pattern.bounded_integrable (measurable_independentTreeCoefficient S T Q m base old V hb a f)
      (independentTreeCoefficient_bound S T Q m base old V a f hf)
  have hu (k : ℕ) : Integrable (fun z => u z k) μ :=
    integrable_qExpect μ q _ hui k _
  have hv (k : ℕ) : Integrable (fun z => v z k) ν :=
    integrable_qExpect ν q _ hvi k _
  have hAi : Integrable (sameInsertionAverage T Q m base old V a F) μ :=
    Pattern.bounded_integrable (measurable_sameInsertionAverage T Q m base old V hb a F)
      (sameInsertionAverage_bound T Q m base old V hmp a F hF)
  have hBi : Integrable (independentInsertion T Q m base old V a F) ν :=
    Pattern.bounded_integrable (measurable_independentInsertion T Q m base old V hb a F hmp hme hV)
      (independentInsertion_bound T Q m base old V hmp a F hF)
  have hAt := integral_expansion_tail μ _ u K
    (fun k => (-1:ℝ)^k/(k+1)*insertionRadius C^(k+1)) hAi hu
    (fun z => by
      simpa only [u,m,f,mul_assoc,mul_left_comm,mul_comm] using
        sameInsertionAverage_tail T Q base old V q hm hpos hnz hroot hend a F hC hF z K)
  have hBt := integral_expansion_tail ν _ v K
    (fun k => (-1:ℝ)^k/(k+1)*insertionRadius C^(k+1)) hBi hv
    (fun z => by
      simpa only [v,m,f,mul_assoc,mul_left_comm,mul_comm] using
        independentInsertion_tail T Q base old V q hm hpos hnz hroot hend a F hC hF z K)
  have hAt' : |((∫ z, sameInsertionAverage T Q m base old V a F z ∂μ)-C)-
      ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*(∫ z, u z k ∂μ)*insertionRadius C^(k+1)| ≤
        ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hAt
  have hBt' : |((∫ z, independentInsertion T Q m base old V a F z ∂ν)-C)-
      ∑ k∈Finset.range K,(-1:ℝ)^k/(k+1)*(∫ z, v z k ∂ν)*insertionRadius C^(k+1)| ≤
        ∑' k : ℕ, |insertionRadius C|^(k+K+1)/(k+K+1) := by
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hBt
  have hc (k : ℕ) : |(∫ z, u z k ∂μ)-(∫ z, v z k ∂ν)| ≤ (a:ℝ)*
      qExpect q (fun S => shapeDeviation μ (rootAlphabet (Ω := Ω) (A := A)) S
        (rootTower T Q m base old) (rootVector (fun y i => spin (V y i)))) k (single (L+1)) := by
    dsimp only [u,v]
    rw [integral_qExpect μ q _ hui,integral_qExpect ν q _ hvi]
    have hh := qExpect_difference_bound q hm hpos _ _ _
      (fun S => integral_treeCoefficient_comparison μ S T Q m base old V hb a f hf) k (single (L+1))
    simpa only [mul_comm (a:ℝ),qExpect_mul_const] using hh
  have hh := logExpansion_comparison K hAt' hBt'
  simp only [sub_sub_sub_cancel_right] at hh
  apply hh.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  exact mul_le_mul_of_nonneg_left (hc k) (by positivity)
end DilutedSpinGlass.HeterogeneousMarks

end

end OAI
