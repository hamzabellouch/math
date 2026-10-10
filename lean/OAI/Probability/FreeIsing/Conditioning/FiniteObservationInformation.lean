import OAI.Probability.FreeIsing.Conditioning.DiscreteConditioning
import OAI.Probability.FreeIsing.Gaussian.FiniteSignalInformation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

theorem iIndep_observationFields_cond_spin
    {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)]
    {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (a : IsingSpin) :
    iIndep (fun i => (mA i).comap (X i)) (cond rho {x | S x = a}) := by
  have hne : rho (S ⁻¹' {a}) ≠ 0 := by
    change rho {x | S x = a} ≠ 0
    rw [hfair]
    norm_num
  exact (iIndepFun_cond_fiber_of_iCondIndepFun hS hX hCI a hne).iIndep

section Observations

variable {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)] [Fintype ι]
  {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
  (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hstrict : ∀ i, ∀ᵐ x ∂rho,
    |rho[fun y => spinSign (S y) | (mA i).comap (X i)] x| < 1)
  (hsym : ∀ i, Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho)

include hS hX hCI hfair hstrict hsym

theorem condExp_finite_observation_secondMoment_le_sum [Nonempty ι] :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)] x) ^ 2 ∂rho) ≤
      ∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho := by
  have h := spinInformation_finiteSignalField_le_sum (fun i => (hX i).comap_le)
    hS hstrict hfair (iIndep_observationFields_cond_spin hS hX hCI hfair) hsym
    Finset.univ Finset.univ_nonempty
  have hf : finiteSignalField (fun i => (mA i).comap (X i)) Finset.univ =
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x) := by
    simp [finiteSignalField, MeasurableSpace.comap_process_pi]
  rw [hf] at h
  simpa only [spinInformation] using h

theorem condExp_finite_observation_secondMoment_le_sum_sub_loss
    {a b : ι} (hab : a ≠ b) {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
    (htheta : theta < 1) :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)] x) ^ 2 ∂rho) ≤
      (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho) := by
  have h := spinInformation_finiteSignalField_le_sum_sub_loss (fun i => (hX i).comap_le)
    hS hstrict hfair (iIndep_observationFields_cond_spin hS hX hCI hfair) hsym
    Finset.univ hab (Finset.mem_univ a) (Finset.mem_univ b) haTheta hbTheta htheta
  have hf : finiteSignalField (fun i => (mA i).comap (X i)) Finset.univ =
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x) := by
    simp [finiteSignalField, MeasurableSpace.comap_process_pi]
  rw [hf] at h
  simpa only [spinInformation] using h

theorem condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
    {B : Type*} [mB : MeasurableSpace B] {Y : Ω → B} (hY : Measurable Y)
    (hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun x i => X i x) rho)
    (hOwnStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1)
    (hOwnSym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho)
    {a b : ι} (hab : a ≠ b) {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
    (htheta : theta < 1) :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (B × (∀ i, A i))).comap
        (fun x => (Y x, fun i => X i x))] x) ^ 2 ∂rho) ≤
      (∫ x, (rho[fun y => spinSign (S y) | mB.comap Y] x) ^ 2 ∂rho) +
      (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho) := by
  let mAll : MeasurableSpace Ω :=
    (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)
  let : MeasurableSpace Ω := mΩ
  have hAll : Measurable (fun x i => X i x) := Measurable.of_eval hX
  have hFields := iIndep_observationFields_cond_spin hS hX hCI hfair
  have hf : finiteSignalField (fun i => (mA i).comap (X i)) Finset.univ = mAll := by
    simp [mAll, finiteSignalField, MeasurableSpace.comap_process_pi]
  have hAllStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mAll] x| < 1 := by
    rw [← hf]
    exact abs_condExp_spin_finiteSignalField_lt_one (fun i => (hX i).comap_le)
      hS hstrict hfair hFields Finset.univ ⟨a, Finset.mem_univ a⟩
  have hPairInd (s : IsingSpin) : Indep mAll (mB.comap Y) (cond rho {x | S x = s}) := by
    exact (indepFun_cond_fiber_of_condIndepFun hS hY hAll hOwn s).symm
  have hPair := spinInformation_sup_le_add hAll.comap_le hY.comap_le hS
    hAllStrict hOwnStrict hfair hPairInd hOwnSym
  have hFamily := condExp_finite_observation_secondMoment_le_sum_sub_loss
    hS hX hCI hfair hstrict hsym hab haTheta hbTheta htheta
  change spinInformation rho S
    ((mB.prod MeasurableSpace.pi).comap (fun x => (Y x, fun i => X i x))) ≤ _
  rw [MeasurableSpace.comap_prodMk, sup_comm]
  change spinInformation rho S (mAll ⊔ mB.comap Y) ≤ _
  unfold spinInformation at hPair ⊢
  linarith

end Observations

end Problem367

end

end OAI
