import OAI.Probability.FreeIsing.Conditioning.FiniteObservationInformation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

theorem tanh_add_eq_binaryFusion (x y : ℝ) :
    Real.tanh (x + y) = binaryFusion (Real.tanh x) (Real.tanh y) := by
  unfold binaryFusion
  simp only [Real.tanh_eq_sinh_div_cosh, Real.sinh_add, Real.cosh_add]
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  field_simp

theorem artanh_binaryFusion {u v : ℝ} (hu : |u| < 1) (hv : |v| < 1) :
    Real.artanh (binaryFusion u v) = Real.artanh u + Real.artanh v := by
  have h := tanh_add_eq_binaryFusion (Real.artanh u) (Real.artanh v)
  rw [Real.tanh_artanh (abs_lt.mp hu), Real.tanh_artanh (abs_lt.mp hv)] at h
  rw [← h, Real.artanh_tanh]

theorem artanh_condExp_spin_sup
    {Ω : Type*} {m₁ m₂ mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {S : Ω → IsingSpin} (hS : Measurable S)
    (h₁ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₁] x| < 1)
    (h₂ : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m₂] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, Indep m₁ m₂ (cond rho {x | S x = a})) :
    (fun x => Real.artanh (rho[fun y => spinSign (S y) | m₁ ⊔ m₂] x)) =ᵐ[rho]
      fun x => Real.artanh (rho[fun y => spinSign (S y) | m₁] x) +
        Real.artanh (rho[fun y => spinSign (S y) | m₂] x) := by
  filter_upwards [condExp_spin_sup_eq_binaryFusion hm₁ hm₂ hS h₁ h₂ hfair hInd,
    h₁, h₂] with x hx hx₁ hx₂
  rw [hx, artanh_binaryFusion hx₁ hx₂]

theorem artanh_condExp_spin_finiteSignalField
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} {rho : Measure Ω}
    [IsProbabilityMeasure rho] {m : ι → MeasurableSpace Ω}
    (hm : ∀ i, m i ≤ mΩ) {S : Ω → IsingSpin} (hS : Measurable S)
    (hstrict : ∀ i, ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | m i] x| < 1)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hInd : ∀ a : IsingSpin, iIndep m (cond rho {x | S x = a}))
    (I : Finset ι) (hI : I.Nonempty) :
    (fun x => Real.artanh
      (rho[fun y => spinSign (S y) | finiteSignalField m I] x)) =ᵐ[rho]
      fun x => ∑ i ∈ I, Real.artanh (rho[fun y => spinSign (S y) | m i] x) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp at hI
  | @insert a I ha ih =>
      by_cases hIn : I.Nonempty
      · have hi := ih hIn
        have hf := artanh_condExp_spin_sup (finiteSignalField_le hm I) (hm a) hS
          (abs_condExp_spin_finiteSignalField_lt_one hm hS hstrict hfair hInd I hIn)
          (hstrict a) hfair
          (fun s => indep_finiteSignalField_of_not_mem hm (hInd s) ha)
        rw [finiteSignalField_insert, sup_comm]
        filter_upwards [hi, hf] with x hx hfx
        rw [hfx, hx, Finset.sum_insert ha]
        exact add_comm _ _
      · have hIe : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIn
        subst I
        simp

theorem artanh_condExp_finite_observation
    {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)] [Fintype ι] [Nonempty ι]
    {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hstrict : ∀ i, ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA i).comap (X i)] x| < 1) :
    (fun x => Real.artanh (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (∀ i, A i)).comap (fun x i => X i x)] x)) =ᵐ[rho]
      fun x => ∑ i, Real.artanh
        (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) := by
  have h := artanh_condExp_spin_finiteSignalField (fun i => (hX i).comap_le)
    hS hstrict hfair (iIndep_observationFields_cond_spin hS hX hCI hfair)
    Finset.univ Finset.univ_nonempty
  simpa only [finiteSignalField, Finset.mem_univ, iSup_pos,
    MeasurableSpace.comap_process_pi] using h

theorem artanh_condExp_own_and_finite_observation
    {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)] [Fintype ι] [Nonempty ι]
    {rho : Measure Ω} [IsProbabilityMeasure rho]
    {S : Ω → IsingSpin} (hS : Measurable S)
    {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
    (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
    (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
    (hstrict : ∀ i, ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA i).comap (X i)] x| < 1)
    {B : Type*} [mB : MeasurableSpace B] {Y : Ω → B} (hY : Measurable Y)
    (hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun x i => X i x) rho)
    (hOwnStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1) :
    (fun x => Real.artanh (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (B × (∀ i, A i))).comap
        (fun x => (Y x, fun i => X i x))] x)) =ᵐ[rho]
      fun x => Real.artanh (rho[fun y => spinSign (S y) | mB.comap Y] x) +
        ∑ i, Real.artanh (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) := by
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
      hS hstrict hfair hFields Finset.univ Finset.univ_nonempty
  have hPairInd (s : IsingSpin) : Indep (mB.comap Y) mAll (cond rho {x | S x = s}) :=
    indepFun_cond_fiber_of_condIndepFun hS hY hAll hOwn s
  have hPair := artanh_condExp_spin_sup hY.comap_le hAll.comap_le hS
    hOwnStrict hAllStrict hfair hPairInd
  have hFamily := artanh_condExp_finite_observation hS hX hCI hfair hstrict
  change (fun x => Real.artanh (rho[fun y => spinSign (S y) |
    (mB.prod MeasurableSpace.pi).comap (fun x => (Y x, fun i => X i x))] x)) =ᵐ[rho] _
  rw [MeasurableSpace.comap_prodMk]
  filter_upwards [hPair, hFamily] with x hp hfam
  exact hp.trans (congrArg (fun z =>
    Real.artanh (rho[fun y => spinSign (S y) | mB.comap Y] x) + z) hfam)

end Problem367

end

end OAI
