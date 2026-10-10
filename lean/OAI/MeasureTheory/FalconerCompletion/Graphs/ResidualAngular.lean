import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.ResidualSourceSymbol
import OAI.MeasureTheory.FalconerCompletion.Graphs.FarPairDirectionMeasurable

namespace OAI

/-! Graph energies and pair estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Filter
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {n : ℕ}

noncomputable def actualResidualAngular
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))) :=
  actualAngularProduct (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i x

lemma uniform_actualResidualAngular_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      ∀ (x : EuclideanSpace ℝ (Fin (n+1))), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualResidualAngular A N q a t r L ρ m sig C J i x).1 w‖ ≤
        D^total*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives (ι:=PolicyDescriptor) W M B total 3
    hW 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,Filter.eventually_ge_atTop 1] with N hDb hN
  intro A q a t r hq L ρ m C J i hL htotal x j hj w hw
  have hsub : unreachedDescriptorList A N q a t r ⊆ policyDescriptorList A N q a t := Finset.filter_subset _ _
  have hcard : ((unreachedDescriptorList A N q a t r).card:ℝ) ≤ 8*(N:ℝ)^3 :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (actualPolicy_card_bound A hN hq)
  have hsum : ∑ b∈unreachedDescriptorList A N q a t r, (L b).length≤total :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans htotal
  exact hDb (unreachedDescriptorList A N q a t r) id L ρ m C J i _
    hcard (fun b hb => hL b (hsub hb)) hsum (fun b hb => Finset.le_sup hb) x j hj w hw

lemma uniform_actualResidualAngular_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (k : ℕ) (x w : EuclideanSpace ℝ (Fin (n+1))), ‖w‖=1 →
      w ∈ tsupport (iteratedFDeriv ℝ k (actualResidualAngular A N q a t r L ρ m sig C J i x).1) →
      ∀ b ∈ unreachedDescriptorList A N q a t r, (x,w) ∈ endpointGood ρ m N sig C J (i+1) b := by
  obtain ⟨N₀,h₀⟩ := uniform_actualAngularProduct_support (d:=n+1) (ι:=PolicyDescriptor) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t r hq ht m C i L k x w hw hs b hb
  exact h₀ N hN ρ hf m C i (unreachedDescriptorList A N q a t r) id
    (fun e he => policyDescriptor_valid A hq ht (Finset.mem_filter.mp he).1) L k x w hw hs b hb

lemma actualResidualSourceSymbol_support
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))) :
    tsupport (iteratedFDeriv ℝ k (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q x).1) ⊆
      tsupport (actualResidualAngular A N q a t r L ρ m sig C J i x).1 :=
  (tsupport_iteratedFDeriv_subset k).trans (tsupport_mul_subset_right.trans tsupport_mul_subset_right)

noncomputable def actualResidualAmbientGood
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) : Set (EuclideanSpace ℝ (Fin (n+1))) :=
  {w | ‖w‖≠1 ∨ ∀ b∈unreachedDescriptorList A N q a t r, (x,w)∈endpointGood ρ m N sig C J i b}

lemma actualResidualAmbientGood_even
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin (n+1))) {w : EuclideanSpace ℝ (Fin (n+1))}
    (hw : w∈actualResidualAmbientGood A N q a t r ρ m sig C J i x) :
    -w∈actualResidualAmbientGood A N q a t r ρ m sig C J i x := by
  rcases hw with hn | hg
  · exact Or.inl (by simpa only [norm_neg] using hn)
  · right
    intro b hb P hP hx
    exact descriptorGood_neg ρ m N sig C J i P b (hg b hb P hP hx)

lemma actualResidualAmbientGood_measurable
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1)) |
      z.2∈actualResidualAmbientGood A N q a t r ρ m sig C J i z.1} := by
  change MeasurableSet ({z | ‖z.2‖≠1} ∪ {z | ∀ b∈unreachedDescriptorList A N q a t r,
    z∈endpointGood ρ m N sig C J i b})
  refine ((measurable_snd.norm (measurableSet_singleton 1)).compl).union ?_
  simp only [ofPred_forall]
  exact Finset.measurableSet_biInter _ (fun b hb => measurable_endpointGood ρ m N sig C J i b)

lemma uniform_actualResidualSourceSymbol_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (k : ℕ) (x : EuclideanSpace ℝ (Fin (n+1))),
      tsupport (iteratedFDeriv ℝ k (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q x).1) ⊆
        actualResidualAmbientGood A N q a t r ρ m sig C J (i+1) x := by
  obtain ⟨N₀,h₀⟩ := uniform_actualResidualAngular_support (n:=n) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t r hq ht m C i L f Q k x w hw
  by_cases hn : ‖w‖=1
  · right
    have hs := actualResidualSourceSymbol_support A N q a t r L ρ m sig C J i f Q k x hw
    have hts : tsupport (iteratedFDeriv ℝ 0 (actualResidualAngular A N q a t r L ρ m sig C J i x).1)=
        tsupport (actualResidualAngular A N q a t r L ρ m sig C J i x).1 := by
      apply congrArg closure
      ext z
      simp only [Function.mem_support]
      rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    apply h₀ N hN ρ hf A q a t r hq ht m C i L 0 x w hn
    rwa [hts]
  · exact Or.inl hn

lemma uniform_actualResidualSourceSymbol_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      (∀ x, ‖f x‖≤1) → (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      ∀ (x : EuclideanSpace ℝ (Fin (n+1))), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q x).1 w‖ ≤
        E*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualResidualAngular_derivatives W M B total hW sig hsig
  refine ⟨Cq*D^total*2^M,by positivity,?_⟩
  filter_upwards [hDb] with N hDb
  intro A q a t r hq L ρ m C J i f Q hL htotal hf hQ x j hj w hw
  let Z := actualResidualAngular A N q a t r L ρ m sig C J i x
  let scale := ((2:ℝ)^N)^sig*sourceMaskScaleND
    ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig
  have hscale : 1 ≤ scale := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hsig.le)
    (sourceMaskScaleND_one_le _ _ _)
  have hb := symbol_mul_derivative_boundND Q Z j hCq (pow_nonneg (zero_le_one.trans hD) total)
    (zero_le_one.trans hscale) w (fun k hk =>
      (hQ k (hk.trans hj) w hw).trans (le_mul_of_one_le_right hCq (one_le_pow₀ hscale)))
    (fun k hk => hDb A q a t r hq L ρ m C J i hL htotal x k (hk.trans hj) w hw)
  have hh := symbol_const_mul_derivative_boundND (smoothMulND Q Z) (f x) (hf x) j w
  apply hh.trans (hb.trans ?_)
  rw [mul_pow]
  change Cq*D^total*(2^j*scale^j) ≤ Cq*D^total*2^M*scale^j
  rw [mul_assoc (Cq*D^total) (2^M)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj)
      (pow_nonneg (zero_le_one.trans hscale) j)) (mul_nonneg hCq (pow_nonneg (zero_le_one.trans hD) total))

noncomputable def actualResidualPairSourceSymbol
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :=
  pairSmoothSymbolsND (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q)
    (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q)

lemma actualResidualPairSourceSymbol_measurable
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
    Measurable (fun z : (EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1)) =>
      (actualResidualPairSourceSymbol A N q a t r L ρ m sig C J i f Q z.1).1 z.2) :=
  pairSmoothSymbolsND_measurable _ _ (actualResidualSourceSymbol_measurable A N q a t r L ρ m sig C J i f hf Q)
    (actualResidualSourceSymbol_measurable A N q a t r L ρ m sig C J i f hf Q)

noncomputable def actualResidualPairAmbientGood
    (A : ℕ → ℝ) (N q a t r : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1))) :=
  actualResidualAmbientGood A N q a t r ρ m sig C J i z.1 ∩
    actualResidualAmbientGood A N q a t r ρ m sig C J i z.2

lemma actualResidualPairAmbientGood_even
    (A : ℕ → ℝ) (N q a t r : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin (n+1))))
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)))
    {w : EuclideanSpace ℝ (Fin (n+1))} (hw : w∈actualResidualPairAmbientGood A N q a t r ρ m sig C J i z) :
    -w∈actualResidualPairAmbientGood A N q a t r ρ m sig C J i z :=
  ⟨actualResidualAmbientGood_even A N q a t r ρ m sig C J i z.1 hw.1,
   actualResidualAmbientGood_even A N q a t r ρ m sig C J i z.2 hw.2⟩

lemma actualResidualPairAmbientGood_measurable
    (A : ℕ → ℝ) (N q a t r : ℕ) (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z : (EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1)) |
      z.2∈actualResidualPairAmbientGood A N q a t r ρ m sig C J i z.1} := by
  have hh := actualResidualAmbientGood_measurable A N q a t r ρ m sig C J i
  let p₁ : ((EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))) →
      EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)) := fun z => (z.1.1,z.2)
  let p₂ : ((EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)))×EuclideanSpace ℝ (Fin (n+1))) →
      EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1)) := fun z => (z.1.2,z.2)
  have hp₁ : Measurable p₁ := measurable_fst.fst.prodMk measurable_snd
  have hp₂ : Measurable p₂ := measurable_fst.snd.prodMk measurable_snd
  change MeasurableSet (p₁ ⁻¹' {z | z.2∈actualResidualAmbientGood A N q a t r ρ m sig C J i z.1} ∩
    p₂ ⁻¹' {z | z.2∈actualResidualAmbientGood A N q a t r ρ m sig C J i z.1})
  exact (hh.preimage hp₁).inter (hh.preimage hp₂)

lemma uniform_actualResidualPairSourceSymbol_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1))))
        (k : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1))),
      tsupport (iteratedFDeriv ℝ k (actualResidualPairSourceSymbol A N q a t r L ρ m sig C J i f Q z).1) ⊆
        actualResidualPairAmbientGood A N q a t r ρ m sig C J (i+1) z := by
  obtain ⟨N₀,h₀⟩ := uniform_actualResidualSourceSymbol_support (n:=n) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t r hq ht m C i L f Q k z w hw
  have hh := pairSmoothSymbolsND_support
    (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q)
    (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q) z k hw
  have hbase (x : EuclideanSpace ℝ (Fin (n+1))) := h₀ N hN ρ hf A q a t r hq ht m C i L f Q 0 x
  have hts (b : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
      tsupport (iteratedFDeriv ℝ 0 b.1)=tsupport b.1 := by
    apply congrArg closure
    ext w
    simp only [Function.mem_support]
    rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
  simp only [hts] at hbase
  exact ⟨hbase z.1 hh.1,hbase z.2 hh.2⟩

lemma uniform_actualResidualPairSourceSymbol_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      (∀ x, ‖f x‖≤1) → (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      ∀ (z : EuclideanSpace ℝ (Fin (n+1))×EuclideanSpace ℝ (Fin (n+1))), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualResidualPairSourceSymbol A N q a t r L ρ m sig C J i f Q z).1 w‖ ≤
        E*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨E,hE,hEb⟩ := uniform_actualResidualSourceSymbol_derivatives W M B total hW sig hsig Cq hCq
  refine ⟨E*E*2^M,by positivity,?_⟩
  filter_upwards [hEb] with N hEb
  intro A q a t r hq L ρ m C J i f Q hL htotal hf hQ z j hj w hw
  let scale := ((2:ℝ)^N)^sig*sourceMaskScaleND
    ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig
  have hscale : 0 ≤ scale := by dsimp [scale]; exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sourceMaskScaleND_pos _ _ _).le
  have hb := pairSmoothSymbolsND_derivatives
    (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q)
    (actualResidualSourceSymbol A N q a t r L ρ m sig C J i f Q) z j hE hE hscale w
    (fun k hk => hEb A q a t r hq L ρ m C J i f Q hL htotal hf hQ z.1 k (hk.trans hj) w hw)
    (fun k hk => hEb A q a t r hq L ρ m C J i f Q hL htotal hf hQ z.2 k (hk.trans hj) w hw)
  apply hb.trans
  rw [mul_pow]
  change E*E*(2^j*scale^j) ≤ E*E*2^M*scale^j
  rw [mul_assoc (E*E) (2^M)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj) (pow_nonneg hscale j))
    (mul_nonneg hE hE)

lemma actualResidualPairAmbientGood_radial_measurable
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z | Attempt4FullFar.euclideanPairDirectionND z∈
      actualResidualPairAmbientGood A N q a t r ρ m sig C J i z} := by
  let F : (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) →
      (EuclideanSpace ℝ (Fin (n+1)) × EuclideanSpace ℝ (Fin (n+1))) × EuclideanSpace ℝ (Fin (n+1)) :=
    fun z => (z,Attempt4FullFar.euclideanPairDirectionND z)
  have hF : Measurable F := measurable_id.prodMk actualFar_pairDirection_measurable
  have hh := actualResidualPairAmbientGood_measurable A N q a t r ρ m sig C J i
  change MeasurableSet (F ⁻¹' {z | z.2∈actualResidualPairAmbientGood A N q a t r ρ m sig C J i z.1})
  exact hh.preimage hF

theorem actual_residualFar_symbol_package
    (W : Finset (List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))))
    (M B total : ℕ) (hW : ∀ L∈W, L.length≤B)
    {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (ρ : Measure (EuclideanSpace ℝ (Fin (n+1)))) [IsFiniteMeasure ρ],
      ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q → t≤N →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1))))
        (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (f : EuclideanSpace ℝ (Fin (n+1)) → ℂ)
        (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))),
      Measurable f → (∀ x, ‖f x‖≤1) →
      (∀ b∈policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length≤total) →
      (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      let b := fun z => (actualResidualPairSourceSymbol A N q a t r L ρ m sig C J i f Q z).1
      let U := actualResidualPairAmbientGood A N q a t r ρ m sig C J (i+1)
      Measurable (Function.uncurry b) ∧
      MeasurableSet {z | Attempt4FullFar.euclideanPairDirectionND z∈U z} ∧
      ∀ z, ContDiff ℝ ∞ (b z) ∧ (∀ w∈U z, -w∈U z) ∧ tsupport (b z) ⊆ U z ∧
        (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j (b z) w‖≤
          E*(Attempt4FullFar.shellEffectiveScaleND
            ((unreachedDescriptorList A N q a t r).sup descriptorLength) ((2:ℝ)^N) sig)^j) := by
  obtain ⟨E,hE,hder⟩ := uniform_actualResidualPairSourceSymbol_derivatives W M B total hW sig hsig Cq hCq
  obtain ⟨N₀,hsup⟩ := uniform_actualResidualPairSourceSymbol_support (n:=n) hsig hJ
  refine ⟨E,hE,?_⟩
  filter_upwards [hder,eventually_ge_atTop N₀] with N hder hN
  intro ρ hρ A q a t r hq ht L m C i f Q hfm hf hL htotal hQ
  refine ⟨actualResidualPairSourceSymbol_measurable A N q a t r L ρ m sig C J i f hfm Q,
    actualResidualPairAmbientGood_radial_measurable A N q a t r ρ m sig C J (i+1),?_⟩
  intro z
  refine ⟨smoothFunctionND_contDiff _,fun w hw => actualResidualPairAmbientGood_even A N q a t r ρ m sig C J (i+1) z hw,?_,?_⟩
  · have hh := hsup N hN ρ hρ A q a t r hq ht m C i L f Q 0 z
    have hz (v : SmoothFunctionND (EuclideanSpace ℝ (Fin (n+1)))) :
        tsupport (iteratedFDeriv ℝ 0 v.1)=tsupport v.1 := by
      apply congrArg closure
      ext w
      simp only [Function.mem_support]
      rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    rwa [hz] at hh
  · intro j hj w hw
    simpa only [actualFar_scale_eq] using hder A q a t r hq L ρ m C J i f Q hL htotal hf hQ z j hj w hw

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
