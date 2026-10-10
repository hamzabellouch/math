import OAI.Probability.DilutedSpin.GlobalSelectedError
import OAI.Probability.DilutedSpin.LabeledColorHistory
import OAI.Probability.DilutedSpin.MatrixHistory
import OAI.Probability.DilutedSpin.SplitDepthContinuity
import OAI.Probability.DilutedSpin.TreeMarkLaw

namespace OAI

section
section
namespace DilutedSpinGlass.PrescribedTree
open scoped BigOperators
noncomputable local instance pairObservableHistoryDecidable (proposition : Prop) :
    Decidable proposition := Classical.propDecidable proposition
variable {Ω : Type} [Fintype Ω] {n : ℕ}

/-- Actual one-new-path history for an arbitrary two-path observable (in
particular the empirical spin overlap). All unused old replicas are retained. -/
noncomputable def pairObservableHistory (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (S : PrescribedTree n) (a : S.Leaf) (d : ℕ)
    (R : FinitePath Ω n → FinitePath Ω n → ℝ) (f : Sample Ω S → ℝ) : ℝ :=
  (∑ b ∈ Finset.univ.erase a,
    if splitDepth S a b = d then (S.sampleLaw T).expect
      (fun x => f x * R (S.pathAt a x) (S.pathAt b x)) else 0) +
    ∑ v : S.Internal, if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
      gamma S m v * ((grow S v).sampleLaw T).expect
        (fun x => f (oldSample S v x) *
          R ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0

lemma pairObservableHistory_product {L : ℕ} (T : KernelTower Ω (L+1))
    (m : Fin (L+2) → ℝ) (S : PrescribedTree (L+1)) (a : S.Leaf) (d : ℕ)
    (E D : FinitePath Ω (L+1) → ℝ) (f : Sample Ω S → ℝ) :
    pairObservableHistory T m S a d (fun x y => E x*D y) f = pairHistory T m S a d E D f := rfl

lemma pair_univ_erase (S : PrescribedTree n) (a : S.Leaf) (d : ℕ) (hd : d < n) :
    (∑ b ∈ Finset.univ.erase a, if splitDepth S a b = d then (1:ℝ) else 0) =
      ∑ b : S.Leaf, if splitDepth S a b = d then (1:ℝ) else 0 := by
  classical
  have he := Finset.sum_erase_add (Finset.univ : Finset S.Leaf)
    (fun b => if splitDepth S a b = d then (1:ℝ) else 0) (Finset.mem_univ a)
  simpa only [splitDepth_self,ite_eq_right (Ne.symm (Nat.ne_of_lt hd)),add_zero] using he

/-- Exact, old-tree-independent singleton-anchor coefficient at a fixed split. -/
theorem pairObservableHistory_const (T : KernelTower Ω n) (m : Fin (n+1) → ℝ)
    (hend : m (Fin.last n) = 1) (S : PrescribedTree n) (a : S.Leaf)
    (d : ℕ) (hd : d < n) (R : FinitePath Ω n → FinitePath Ω n → ℝ) :
    pairObservableHistory T m S a d R (fun _ => 1) =
      (m ⟨d,by omega⟩ - m ⟨d+1,by omega⟩) * KernelTower.pairExpect n T d R := by
  classical
  unfold pairObservableHistory
  simp only [one_mul]
  have ho (b : S.Leaf) :
      (if splitDepth S a b = d then
        (S.sampleLaw T).expect (fun x => R (S.pathAt a x) (S.pathAt b x)) else 0) =
      (if splitDepth S a b = d then (1:ℝ) else 0)*KernelTower.pairExpect n T d R := by
    split_ifs with hb
    · rw [pair_marginal,hb,one_mul]
    · simp
  have hv (v : S.Internal) :
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then
        gamma S m v*((grow S v).sampleLaw T).expect (fun x => R
          ((grow S v).pathAt (oldLeaf S v a) x) ((grow S v).pathAt (newLeaf S v) x)) else 0) =
      (if splitDepth (grow S v) (oldLeaf S v a) (newLeaf S v) = d then gamma S m v else 0)*
        KernelTower.pairExpect n T d R := by
    split_ifs with hv
    · rw [pair_marginal,hv]
    · simp
  simp_rw [ho,hv]
  rw [← Finset.sum_mul,← Finset.sum_mul,← add_mul,pair_univ_erase S a d hd,
    pair_choice_total S a d hd m hend]

lemma erase_eq_of_two (S : PrescribedTree n) (a b : S.Leaf) (hab : a ≠ b)
    (htwo : ∀ c : S.Leaf, c = a ∨ c = b) : (Finset.univ : Finset S.Leaf).erase a = {b} := by
  classical
  ext c
  simp only [Finset.mem_erase,Finset.mem_univ,and_true,Finset.mem_singleton]
  constructor
  · intro hc; exact (htwo c).resolve_left hc
  · rintro rfl; exact Ne.symm hab

end DilutedSpinGlass.PrescribedTree
end

end

section
section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M : ℕ}

/-- The actual complete score error, split into its thermal and disorder parts.
The only bounds used are the perturbation factors and positive exponents. -/
theorem full_selected_error_split_average
    (ξ : Fin M → Measure Y) [∀ j, IsProbabilityMeasure (ξ j)]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure I) [IsProbabilityMeasure ν] (r s : ℝ≥0)
    (T : KernelTower Ω L) (Q : (i : I) → Fin L → FiniteLaw (A i)) (m : Fin L → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω L → ℝ)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))
    (sel : I → Bool) (fixed D E : (i : I) → FinitePath Ω L → FinitePath (A i) L → ℝ)
    (hD : ∀ i x y, |D i x y| ≤ 1) (hE : ∀ i x y, |E i x y| ≤ 1)
    {t a b c : ℝ} (ht : |t| ≤ 1/4) (hab : a < b) (hc : 0 < c)
    (hm : ∀ j, c ≤ m j) (hI : Icc a b ⊆ Icc (-(1:ℝ)/4) (1/4)) :
    (∫ u in a..b, fullSelectedError ξ μ ν r s T Q m base sel fixed D E t u) ≤
      Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ))+
        ∫ u in a..b, rootDeviation (fullRootLaw ξ μ ν r s)
          (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u) := by
  let P := fullRootLaw ξ μ ν r s
  let F := fullSelectedError ξ μ ν r s T Q m base sel fixed D E t
  let U := fun u => ∫ z, fullSelectedThermal T Q m base sel fixed D E t z u ∂P
  let V := fun u => rootDeviation P (fun z => fullSelectedRawScore T Q m base sel fixed D E t z u)
  have hu (u : ℝ) (h : u ∈ Icc a b) : |u| ≤ 1/4 :=
    abs_le.mpr ⟨by linarith [(hI h).1],(hI h).2⟩
  have hci := (fullRoot_count_memLp ξ μ ν r s).integrable (by norm_num)
  have hUn (u : ℝ) : 0 ≤ U u :=
    integral_nonneg (fun z => fullSelectedThermal_nonneg T Q m base sel fixed D E t z u)
  have hUb (u : ℝ) (h : u ∈ Icc a b) : U u ≤ 4*(s:ℝ) := by
    have hh := integral_mono_of_nonneg
      (ae_of_all P (fun z => fullSelectedThermal_nonneg T Q m base sel fixed D E t z u))
      (hci.const_mul 4)
      (ae_of_all P (fun z => fullSelectedThermal_bound T Q m base sel fixed D E t hD hE ht (hu u h) z))
    simpa only [P, U, integral_const_mul,fullRoot_count_mean] using hh
  have hUi : IntervalIntegrable U volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measurable_fullSelectedThermal T Q m base sel fixed D E t hb).stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u h
    rw [Real.norm_eq_abs,abs_of_nonneg (hUn u)]
    exact hUb u ⟨h.1.le,h.2⟩
  have hFi : IntervalIntegrable F volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    apply Measure.integrableOn_of_bounded (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
      (measurable_fullSelectedError ξ μ ν r s T Q m base sel fixed D E t hb).aestronglyMeasurable
    apply ae_restrict_of_forall_mem measurableSet_Ioc
    intro u h
    rw [Real.norm_eq_abs,abs_of_nonneg (fullSelectedError_nonneg ξ μ ν r s T Q m base sel fixed D E t u)]
    exact fullSelectedError_bound ξ μ ν r s T Q m base sel fixed D E t hb hD hE ht (hu u ⟨h.1.le,h.2⟩)
  have hVi : IntervalIntegrable V volume a b :=
    intervalIntegrable_rootDeviation P (measurable_fullSelectedRawScore T Q m base sel fixed D E t hb)
      (hci.const_mul 2) hab.le
      (fun z u h => fullSelectedRawScore_bound T Q m base sel fixed D E t hD hE ht (hu u h) z)
  have hh := intervalIntegral.integral_mono_on hab.le hFi (hUi.add hVi)
    (fun u h => fullSelectedError_split ξ μ ν r s T Q m base sel fixed D E t hb hD hE ht (hu u h))
  rw [intervalIntegral.integral_add hUi hVi] at hh
  have hsq := full_selected_thermal_average ξ μ ν r s T Q m base hb sel fixed D E hD hE ht hab hc hm hI
  have hle : (∫ u in a..b, U u) ≤ Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ)) := by
    have hK : 0 ≤ (b-a)*(4+4*(b-a))/c*(s:ℝ) := by positivity
    have hsq' : (∫ u in a..b, U u)^2 ≤ (Real.sqrt ((b-a)*(4+4*(b-a))/c*(s:ℝ)))^2 := by
      rw [Real.sq_sqrt hK]
      exact hsq
    nlinarith [Real.sqrt_nonneg ((b-a)*(4+4*(b-a))/c*(s:ℝ))]
  exact hh.trans (add_le_add hle le_rfl)

end DilutedSpinGlass.HeterogeneousMarks
end

end

end OAI
