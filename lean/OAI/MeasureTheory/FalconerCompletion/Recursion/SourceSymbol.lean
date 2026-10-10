import Mathlib
import OAI.MeasureTheory.Falconer.Model
import OAI.MeasureTheory.Falconer.Recursion.PolicyDescriptors
import OAI.MeasureTheory.FalconerCompletion.Angular.SymbolMulDerivativeBound
import OAI.MeasureTheory.FalconerCompletion.Recursion.PolicyAngular

namespace OAI

/-! Recursive policies and quantitative depth estimates. -/

open _root_.OAI.PlanarFalconer

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer Filter
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {d : ℕ}

noncomputable def actualSourceSymbol
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d)))
    (x : EuclideanSpace ℝ (Fin d)) : SmoothFunctionND (EuclideanSpace ℝ (Fin d)) :=
  ⟨fun w => f x*(Q.1 w*(actualPolicyAngular A N q a t L ρ m sig C J i x).1 w),
    contDiff_const.mul ((show ContDiff ℝ ∞ Q.1 from Q.2).mul (show ContDiff ℝ ∞ (actualPolicyAngular A N q a t L ρ m sig C J i x).1 from (actualPolicyAngular A N q a t L ρ m sig C J i x).2))⟩

lemma actualSourceSymbol_measurable
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hf : Measurable f)
    (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))) :
    Measurable (fun z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      (actualSourceSymbol A N q a t L ρ m sig C J i f Q z.1).1 z.2) := by
  exact (hf.comp measurable_fst).mul (((show ContDiff ℝ ∞ Q.1 from Q.2).continuous.measurable.comp measurable_snd).mul
    (actualPolicyAngular_measurable A N q a t L ρ m sig C J i))

lemma actualSourceSymbol_support
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d)))
    (k : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    tsupport (iteratedFDeriv ℝ k (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1) ⊆
      tsupport (actualPolicyAngular A N q a t L ρ m sig C J i x).1 :=
  (tsupport_iteratedFDeriv_subset k).trans (tsupport_mul_subset_right.trans tsupport_mul_subset_right)

noncomputable def actualPolicyAmbientGood
    (A : ℕ → ℝ) (N q a t : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {w | ‖w‖≠1 ∨ ∀ b∈policyDescriptorList A N q a t, (x,w)∈endpointGood ρ m N sig C J i b}

lemma actualPolicyAmbientGood_even
    (A : ℕ → ℝ) (N q a t : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) {w : EuclideanSpace ℝ (Fin d)}
    (hw : w∈actualPolicyAmbientGood A N q a t ρ m sig C J i x) :
    -w∈actualPolicyAmbientGood A N q a t ρ m sig C J i x := by
  rcases hw with hn | hg
  · exact Or.inl (by simpa only [norm_neg] using hn)
  · right
    intro b hb P hP hx
    exact descriptorGood_neg ρ m N sig C J i P b (hg b hb P hP hx)

lemma actualPolicyAmbientGood_measurable
    (A : ℕ → ℝ) (N q a t : ℕ)
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ) :
    MeasurableSet {z : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) |
      z.2∈actualPolicyAmbientGood A N q a t ρ m sig C J i z.1} := by
  change MeasurableSet ({z | ‖z.2‖≠1} ∪ {z | ∀ b∈policyDescriptorList A N q a t,
    z∈endpointGood ρ m N sig C J i b})
  refine ((measurable_snd.norm (measurableSet_singleton 1)).compl).union ?_
  simp only [ofPred_forall]
  exact Finset.measurableSet_biInter _ (fun b hb => measurable_endpointGood ρ m N sig C J i b)

lemma uniform_actualSourceSymbol_support {sig : ℝ} (hsig : 0<sig) {J : ℕ} (hJ : 0<J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (ρ : Measure (EuclideanSpace ℝ (Fin d))), IsFiniteMeasure ρ →
      ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q → t≤N →
      ∀ (m : ℝ → ℝ) (C : ℝ) (i : ℕ)
        (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d)))
        (k : ℕ) (x : EuclideanSpace ℝ (Fin d)),
      tsupport (iteratedFDeriv ℝ k (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1) ⊆
        actualPolicyAmbientGood A N q a t ρ m sig C J (i+1) x := by
  obtain ⟨N₀,h₀⟩ := uniform_actualPolicyAngular_support (d:=d) hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ρ hf A q a t hq ht m C i L f Q k x w hw
  by_cases hn : ‖w‖=1
  · right
    have hs := actualSourceSymbol_support A N q a t L ρ m sig C J i f Q k x hw
    have hts : tsupport (iteratedFDeriv ℝ 0 (actualPolicyAngular A N q a t L ρ m sig C J i x).1)=
        tsupport (actualPolicyAngular A N q a t L ρ m sig C J i x).1 := by
      apply congrArg closure
      ext z
      simp only [Function.mem_support]
      rw [← norm_ne_zero_iff,norm_iteratedFDeriv_zero,norm_ne_zero_iff]
    apply h₀ N hN ρ hf A q a t hq ht m C i L 0 x w hn
    rwa [hts]
  · exact Or.inl hn

lemma uniform_actualSourceSymbol_derivatives
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (M B total : ℕ) (hW : ∀ L ∈ W, L.length ≤ B) (sig : ℝ) (hsig : 0<sig)
    (Cq : ℝ) (hCq : 0≤Cq) :
    ∃ E : ℝ, 0≤E ∧ ∀ᶠ N : ℕ in atTop, ∀ (A : ℕ → ℝ) (q a t : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ)
        (f : EuclideanSpace ℝ (Fin d) → ℂ) (Q : SmoothFunctionND (EuclideanSpace ℝ (Fin d))),
      (∀ b ∈ policyDescriptorList A N q a t, L b ∈ W) →
      (∑ b ∈ policyDescriptorList A N q a t, (L b).length ≤ total) →
      (∀ x, ‖f x‖≤1) → (∀ j≤M, ∀ w, ‖w‖=1 → ‖iteratedFDeriv ℝ j Q.1 w‖≤Cq) →
      ∀ (x : EuclideanSpace ℝ (Fin d)), ∀ j ≤ M, ∀ w, ‖w‖=1 →
      ‖iteratedFDeriv ℝ j (actualSourceSymbol A N q a t L ρ m sig C J i f Q x).1 w‖ ≤
        E*(((2:ℝ)^N)^sig*
          sourceMaskScaleND ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig)^j := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualPolicyAngular_derivatives W M B total hW sig hsig
  refine ⟨Cq*D^total*2^M,by positivity,?_⟩
  filter_upwards [hDb] with N hDb
  intro A q a t hq L ρ m C J i f Q hL htotal hf hQ x j hj w hw
  let Z := actualPolicyAngular A N q a t L ρ m sig C J i x
  let scale := ((2:ℝ)^N)^sig*sourceMaskScaleND
    ((policyDescriptorList A N q a t).sup descriptorLength) ((2:ℝ)^N) sig
  have hscale : 1 ≤ scale := one_le_mul_of_one_le_of_one_le
    (Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hsig.le)
    (sourceMaskScaleND_one_le _ _ _)
  have hb := symbol_mul_derivative_boundND Q Z j hCq (pow_nonneg (zero_le_one.trans hD) total)
    (zero_le_one.trans hscale) w (fun k hk =>
      (hQ k (hk.trans hj) w hw).trans (le_mul_of_one_le_right hCq (one_le_pow₀ hscale)))
    (fun k hk => hDb A q a t hq L ρ m C J i hL htotal x k (hk.trans hj) w hw)
  have hh := symbol_const_mul_derivative_boundND (smoothMulND Q Z) (f x) (hf x) j w
  apply hh.trans (hb.trans ?_)
  rw [mul_pow]
  change Cq*D^total*(2^j*scale^j) ≤ Cq*D^total*2^M*scale^j
  rw [mul_assoc (Cq*D^total) (2^M)]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj)
      (pow_nonneg (zero_le_one.trans hscale) j)) (mul_nonneg hCq (pow_nonneg (zero_le_one.trans hD) total))

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace CurrentFalconer.TreeND
open Set Metric MeasureTheory PlanarFalconer
open scoped ENNReal RealInnerProductSpace ContDiff Topology Classical
variable {d : ℕ}

lemma actualEndpointSmooth_reached (ρ : Measure (EuclideanSpace ℝ (Fin d)))
    (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ) (J i : ℕ) (b : PolicyDescriptor)
    {P : CellPath d} (ha : descriptorAnchor b ≤ P.length)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈treeCell P) (hy : y∈treeCell P) :
    actualEndpointSmooth ρ m N sig C J i b x = actualEndpointSmooth ρ m N sig C J i b y := by
  have hP : P.take (descriptorAnchor b) ∈ dyadicPaths (descriptorAnchor b) := by
    simp only [mem_dyadicPaths,List.length_take,Nat.min_eq_left ha]
  rw [actualEndpointSmooth_of_mem ρ m N sig C J i b hP (treeCell_subset_take P _ hx),
    actualEndpointSmooth_of_mem ρ m N sig C J i b hP (treeCell_subset_take P _ hy)]

lemma actualEndpointAngular_reached
    (L : List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ)
    (J i : ℕ) (b : PolicyDescriptor) {P : CellPath d} (ha : descriptorAnchor b ≤ P.length)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈treeCell P) (hy : y∈treeCell P) :
    actualEndpointAngular L ρ m N sig C J i b x = actualEndpointAngular L ρ m N sig C J i b y := by
  unfold actualEndpointAngular
  rw [actualEndpointSmooth_reached ρ m N sig C J i b ha hx hy]

lemma actualAngularProduct_reached {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor)
    (L : ι → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (N : ℕ) (sig C : ℝ)
    (J i : ℕ) {P : CellPath d} (ha : ∀ e∈S, descriptorAnchor (b e) ≤ P.length)
    {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈treeCell P) (hy : y∈treeCell P) :
    actualAngularProduct S b L ρ m N sig C J i x = actualAngularProduct S b L ρ m N sig C J i y := by
  apply Subtype.ext
  funext w
  apply Finset.prod_congr rfl
  intro e he
  exact congrArg (fun f : SmoothFunctionND (EuclideanSpace ℝ (Fin d)) => f.1 w)
    (actualEndpointAngular_reached (L e) ρ m N sig C J i (b e) (ha e he) hx hy)

noncomputable def reachedDescriptorList (A : ℕ → ℝ) (N q a t r : ℕ) : Finset PolicyDescriptor :=
  (policyDescriptorList A N q a t).filter (fun b => descriptorAnchor b≤r)

noncomputable def unreachedDescriptorList (A : ℕ → ℝ) (N q a t r : ℕ) : Finset PolicyDescriptor :=
  (policyDescriptorList A N q a t).filter (fun b => r<descriptorAnchor b)

lemma actualPolicyAngular_reached_factorization
    (A : ℕ → ℝ) (N q a t r : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    (x : EuclideanSpace ℝ (Fin d)) :
    actualPolicyAngular A N q a t L ρ m sig C J i x =
      smoothMulND
        (actualAngularProduct (reachedDescriptorList A N q a t r) id L ρ m N sig C J i x)
        (actualAngularProduct (unreachedDescriptorList A N q a t r) id L ρ m N sig C J i x) := by
  apply Subtype.ext
  funext w
  change (∏ b∈policyDescriptorList A N q a t, (actualEndpointAngular (L b) ρ m N sig C J i b x).1 w) = _
  simpa only [reachedDescriptorList,unreachedDescriptorList,actualAngularProduct,smoothMulND,smoothFinsetProductND,
    id_eq, not_le] using (Finset.prod_filter_mul_prod_filter_not
      (policyDescriptorList A N q a t) (fun b => descriptorAnchor b≤r)
      (fun b => (actualEndpointAngular (L b) ρ m N sig C J i b x).1 w)).symm

lemma reachedSymbol_constant_on_cell
    (A : ℕ → ℝ) (N q a t : ℕ)
    (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
    (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (sig C : ℝ) (J i : ℕ)
    {P : CellPath d} {x y : EuclideanSpace ℝ (Fin d)} (hx : x∈treeCell P) (hy : y∈treeCell P) :
    actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i x =
      actualAngularProduct (reachedDescriptorList A N q a t P.length) id L ρ m N sig C J i y :=
  actualAngularProduct_reached _ _ _ _ _ _ _ _ _ _
    (fun _ hb => (Finset.mem_filter.mp hb).2) hx hy

lemma uniform_reachedSymbol_bound
    (W : Finset (List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))))
    (B total : ℕ) (hW : ∀ L∈W, L.length≤B) (sig : ℝ) (hsig : 0<sig) :
    ∃ D : ℝ, 1≤D ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ (A : ℕ → ℝ) (q a t r : ℕ), 0<q →
      ∀ (L : PolicyDescriptor → List (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)))
        (ρ : Measure (EuclideanSpace ℝ (Fin d))) (m : ℝ → ℝ) (C : ℝ) (J i : ℕ),
      (∀ b ∈ policyDescriptorList A N q a t, L b∈W) →
      (∑ b∈policyDescriptorList A N q a t, (L b).length ≤ total) →
      ∀ (x w : EuclideanSpace ℝ (Fin d)), ‖w‖=1 →
      ‖(actualAngularProduct (reachedDescriptorList A N q a t r) id L ρ m N sig C J i x).1 w‖ ≤ D^total := by
  obtain ⟨D,hD,hDb⟩ := uniform_actualAngularProduct_derivatives
    (ι:=PolicyDescriptor) W 0 B total 3 hW 8 sig hsig
  refine ⟨D,hD,?_⟩
  filter_upwards [hDb,Filter.eventually_ge_atTop 1] with N hDb hN
  intro A q a t r hq L ρ m C J i hL htotal x w hw
  have hsub : reachedDescriptorList A N q a t r ⊆ policyDescriptorList A N q a t := Finset.filter_subset _ _
  have hcard : ((reachedDescriptorList A N q a t r).card:ℝ)≤8*(N:ℝ)^3 := by
    calc
      _ ≤ ((policyDescriptorList A N q a t).card:ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ ≤ _ := actualPolicy_card_bound A hN hq
  have hsum : ∑ b∈reachedDescriptorList A N q a t r, (L b).length ≤ total :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; exact Nat.zero_le _)).trans htotal
  have hh := hDb (reachedDescriptorList A N q a t r) id L ρ m C J i
    ((policyDescriptorList A N q a t).sup descriptorLength) hcard
    (fun b hb => hL b (hsub hb)) hsum (fun b hb => Finset.le_sup (f:=descriptorLength) (hsub hb)) x 0 le_rfl w hw
  simpa only [norm_iteratedFDeriv_zero,pow_zero,mul_one] using hh

end CurrentFalconer.TreeND
end GraphLiteralSupport
end
end

end OAI
