import OAI.Probability.DilutedSpin.FunctionalContinuity
import OAI.Probability.DilutedSpin.PatternComparison
import OAI.Probability.DilutedSpin.QSubsetDeviation
import OAI.Probability.DilutedSpin.QTopologyBound
import OAI.Probability.DilutedSpin.RootEncoding
import OAI.Probability.DilutedSpin.SpinLogContinuous

namespace OAI

section
namespace DilutedSpinGlass.HeterogeneousMarks
open _root_.MeasureTheory _root_.OAI.MeasureTheory PrescribedTree KernelTower ConcreteReservoir
open scoped BigOperators
local instance rootInsertionMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance rootInsertionBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩
variable {Ω I X Y : Type} [Fintype Ω] {A : I → Type} [∀ i, Fintype (A i)]
    [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
    [MeasurableSpace X] [MeasurableSpace Y] {L M N : ℕ}
variable (T : KernelTower Ω (L+1)) (Q : (i : I) → Fin (L+1) → FiniteLaw (A i))
    (m : Fin (L+1) → ℝ)
    (base : RootPath Y M → (k : ℕ) → RootPath X k → FinitePath Ω (L+1) → ℝ)
    (old : (i : I) → FinitePath Ω (L+1) → FinitePath (A i) (L+1) → ℝ)
    (V : FinitePath Ω (L+1) → Site N → Spin)
    (hb : ∀ k y, Measurable (fun z : RootPath Y M × RootPath X k => base z.1 k z.2 y))

noncomputable def rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : FullRootState Y X I M × (Fin a → Site N)) : ℝ :=
  backwardLog (L+1) (rootTower T Q m base old z.1) m
    (fun y => F (fun i => V (physical (rootArray z.1.2.2.1 z.1.2.2.2) (L+1) y) (z.2 i)))

include hb in
lemma measurable_rootInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ) :
    Measurable (rootInsertion T Q m base old V a F) := by
  apply measurable_from_prod_countable_left
  intro v
  apply measurable_packRoot_into (F := fun h k x n y =>
    backwardLog (L+1) (tilt (L+1) (tower (rootArray n y) (L+1) T Q) m
      (logWeight (base h k x) (rootArray n y) old)) m
      (fun w => F (fun i => V (physical (rootArray n y) (L+1) w) (v i))))
  intro k n
  apply measurable_from_prod_countable_left
  intro y
  dsimp only
  simp_rw [← insertion]
  apply Measurable.sub
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact ((hb k _).add measurable_const).add measurable_const
  · apply measurable_backwardLog (L+1) (tower (rootArray n y) (L+1) T Q) m
    intro w
    exact (hb k _).add measurable_const

noncomputable def independentInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (z : Fin a → FullRootState Y X I M × Site N) : ℝ :=
  backwardLog (L+1) (KernelTower.pi (L+1) (fun i => rootTower T Q m base old (z i).1)) m
    (fun y => F (fun i => V
      (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) (FinitePath.proj (L+1) y i)) (z i).2))

omit [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Y] in
lemma independentInsertion_encode (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i))
    (z : Fin a → FullRootState Y X I M × Site N) :
    independentInsertion T Q m base old V a F z =
      DilutedSpinGlass.logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc)
        (fun i => rootEncoding T Q m base old (fun w j => spin (V w j)) (z i).1 (z i).2) :=
  backwardLog_encode (α := fun i : Fin a => rootAlphabet (Ω := Ω) (A := A) (z i).1) L
    (fun i => rootTower T Q m base old (z i).1)
    (fun i y => V (physical (rootArray (z i).1.2.2.1 (z i).1.2.2.2) (L+1) y) (z i).2)
    F m hm (fun i => hV (z i).1 (z i).2)

include hb in
lemma measurable_independentInsertion (a : ℕ) (F : (Fin a → Spin) → ℝ)
    (hm : ∀ i, 0 < m i) (hend : m (Fin.last L)=1)
    (hV : ∀ z i, TerminalInterior L (rootTower T Q m base old z)
      (fun y => rootVector (fun w j => spin (V w j)) z y i)) :
    Measurable (independentInsertion T Q m base old V a F) := by
  have hf : ∀ s, |F s|≤∑ t, |F t| := fun s => Finset.single_le_sum (fun t _ => abs_nonneg (F t)) (Finset.mem_univ s)
  have hc := (logMean_continuous_bound L _ (FiniteLaw.spinLog_continuous F)
    (FiniteLaw.spinLog_bound F hf) (fun i => m i.castSucc) (fun i => hm i.castSucc)).1
  simp_rw [show independentInsertion T Q m base old V a F = fun z =>
      DilutedSpinGlass.logMean L (FiniteLaw.spinLog F) (fun i => m i.castSucc)
        (fun i => rootEncoding T Q m base old (fun w j => spin (V w j)) (z i).1 (z i).2) from
    funext (independentInsertion_encode T Q m base old V a F hend hV)]
  exact hc.measurable.comp (Measurable.of_eval (fun index =>
    (measurable_rootEncoding_joint T Q m base old (fun w j => spin (V w j)) hb).comp (measurable_pi_apply index)))
end DilutedSpinGlass.HeterogeneousMarks

end

section
namespace DilutedSpinGlass.Pattern
open _root_.MeasureTheory _root_.OAI.MeasureTheory
open scoped BigOperators
noncomputable local instance mixedPatternsDecidableEq (type : Type) :
    DecidableEq type := Classical.decEq type
variable {Z : Type} [MeasurableSpace Z] (μ : Measure Z) [IsProbabilityMeasure μ]
    (Ω : Z → Type) [∀ z, Fintype (Ω z)] (P : (z : Z) → FiniteLaw (Ω z))
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (mass : (z : Z) → Ω z → (ι → Bool) → ℝ)
    (hmass : ∀ z w e, 0 ≤ mass z w e) (htotal : ∀ z w, ∑ e, mass z w e=1)
    (hmean : ∀ e, Measurable (fun z => (P z).expect (fun w => mass z w e)))

noncomputable def mixedMass (e : ι → Bool) : ℝ := ∫ z, (P z).expect (fun w => mass z w e) ∂μ

omit [IsProbabilityMeasure μ] [Fintype ι] [DecidableEq ι] in
include hmass in
lemma mixedMass_nonneg (e : ι → Bool) : 0 ≤ mixedMass μ Ω P mass e :=
  integral_nonneg (fun z => (P z).expect_nonneg (fun w => hmass z w e))

include hmass htotal hmean in
lemma mixedMass_total : ∑ e, mixedMass μ Ω P mass e=1 := by
  have hi (e : ι → Bool) : Integrable (fun z => (P z).expect (fun w => mass z w e)) μ :=
    bounded_integrable (hmean e) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_of_nonneg (hmass z w e)]
      exact mass_le_one _ (hmass z w) (htotal z w) e))
  unfold mixedMass
  rw [← integral_finsetSum _ (fun e _ => hi e)]
  simp_rw [← FiniteLaw.expect_fintype_sum,htotal,FiniteLaw.expect_const]
  simp

include hmass htotal hmean in
lemma mixedMass_moment (S : Finset ι) :
    moment (mixedMass μ Ω P mass) S=∫ z, (P z).expect (fun w => moment (mass z w) S) ∂μ := by
  have hi (e : ι → Bool) : Integrable (fun z => (P z).expect (fun w => mass z w e)) μ :=
    bounded_integrable (hmean e) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_of_nonneg (hmass z w e)]
      exact mass_le_one _ (hmass z w) (htotal z w) e))
  simp only [moment,mixedMass,← integral_mul_const,FiniteLaw.expect_fintype_sum,
    FiniteLaw.expect_mul_right]
  exact (integral_finsetSum _ (fun e _ => (hi e).mul_const _)).symm

include hmass htotal hmean in
 
lemma mixed_pattern_replacement (a : ℕ) (f : (Fin a → (ι → Bool)) → ℝ)
    (hf : ∀ x, |f x|≤1)
    (hA : Measurable (fun z => (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x)))
    (hD : ∀ S : Finset ι, Measurable (fun z => (P z).expect (fun w =>
      |moment (mass z w) S-moment (mixedMass μ Ω P mass) S|))) :
    |(∫ z, (P z).expect (fun w => ∑ x, (∏ i, mass z w (x i))*f x) ∂μ)-
      (∑ x, (∏ i, mixedMass μ Ω P mass (x i))*f x)| ≤
      (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
        FiniteLaw.mixedDeviation μ Ω P (fun z w => moment (mass z w) S) := by
  let Q := mixedMass μ Ω P mass
  let A (z : Z) (w : Ω z) := ∑ x, (∏ i, mass z w (x i))*f x
  let B := ∑ x, (∏ i, Q (x i))*f x
  have hQ := mixedMass_nonneg μ Ω P mass hmass
  have htQ := mixedMass_total μ Ω P mass hmass htotal hmean
  have hAb (z : Z) (w : Ω z) : |A z w|≤1 := by
    apply mass_abs_average _ f (fun x => Finset.prod_nonneg (fun i _ => hmass z w (x i))) _ hf
    rw [← Fintype.prod_sum]
    simp only [htotal,Finset.prod_const_one]
  have hAi : Integrable (fun z => (P z).expect (A z)) μ :=
    bounded_integrable hA (fun z => (P z).abs_expect_le (hAb z))
  have hDb (S : Finset ι) (z : Z) (w : Ω z) :
      |moment (mass z w) S-moment Q S|≤2 := by
    apply (abs_sub _ _).trans
    have h1 := mass_abs_average _ _ (hmass z w) (htotal z w) (fun x => (abs_character S x).le)
    have h2 := mass_abs_average _ _ hQ htQ (fun x => (abs_character S x).le)
    change |moment (mass z w) S|≤1 at h1
    change |moment Q S|≤1 at h2
    linarith
  have hDi (S : Finset ι) : Integrable (fun z => (P z).expect
      (fun w => |moment (mass z w) S-moment Q S|)) μ :=
    bounded_integrable (hD S) (fun z => (P z).abs_expect_le (fun w => by
      rw [abs_abs]; exact hDb S z w))
  change |(∫ z, (P z).expect (A z) ∂μ)-B|≤_
  have hBc : (∫ _ : Z, B ∂μ)=B := by simp
  rw [← hBc,← integral_sub hAi (integrable_const B)]
  calc
    _ ≤ ∫ z, |(P z).expect (A z)-B| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
        (P z).expect (fun w => |moment (mass z w) S-moment Q S|) ∂μ := by
      apply integral_mono (hAi.sub (integrable_const B)).abs
        ((integrable_finsetSum _ (fun S _ => hDi S)).const_mul _) 
      intro z
      dsimp only [Pi.sub_apply]
      rw [← (P z).expect_const B,← FiniteLaw.expect_sub]
      calc
        _ ≤ (P z).expect (fun w => |A z w-B|) := FiniteLaw.abs_expect_le_expect_abs _ _
        _ ≤ (P z).expect (fun w => (a:ℝ)*∑ S∈(Finset.univ : Finset (Finset ι)).erase ∅,
            |moment (mass z w) S-moment Q S|) :=
          (P z).expect_mono (fun w => pattern_replacement _ _ (hmass z w) hQ (htotal z w) htQ a f hf)
        _ = _ := by rw [FiniteLaw.expect_mul_left,FiniteLaw.expect_sum]
    _ = _ := by
      rw [integral_const_mul,integral_finsetSum _ (fun S _ => hDi S)]
      congr 1
      apply Finset.sum_congr rfl
      intro S _
      rw [mixedMass_moment μ Ω P mass hmass htotal hmean]
      rfl

end DilutedSpinGlass.Pattern

end

section
namespace DilutedSpinGlass
open KernelTower _root_.MeasureTheory _root_.OAI.MeasureTheory
local instance exponentsExistMeasurableSpace (space : TopCat) : MeasurableSpace space := borel space
local instance exponentsExistBorelSpace (space : TopCat) : BorelSpace space := ⟨rfl⟩

lemma exponents_nonempty (r : ℕ) : ∃ m : Fin r → ℝ,Exponents m := by
  refine ⟨fun i => ((i:ℕ)+1:ℝ)/(r+1),?_,?_⟩
  · intro i j hij
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<r+1)).mpr
    simpa only [add_comm] using
      (add_lt_add_right (Nat.cast_lt.mpr hij : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)) 1)
  · intro i
    constructor
    · positivity
    · rw [div_lt_one (by positivity : (0:ℝ)<r+1)]
      simpa only [add_comm] using
        (add_lt_add_right (Nat.cast_lt.mpr i.isLt : ((i : ℕ) : ℝ) < (r : ℝ)) 1)

noncomputable def zeroHierarchy : (r : ℕ) → Hierarchy r
  | 0 => (show Hierarchy 0 from (0 : ℝ))
  | r+1 => (show ProbabilityMeasure (Hierarchy r) from
      ⟨Measure.dirac (zeroHierarchy r),Measure.dirac.isProbabilityMeasure⟩)

end DilutedSpinGlass

end

end OAI
