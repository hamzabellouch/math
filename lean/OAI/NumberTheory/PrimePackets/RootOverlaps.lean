import Mathlib
import OAI.NumberTheory.PrimePackets.KernelScaling

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module
universe u
open scoped TensorProduct
open Set Module
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
namespace PrimeDegreePackets.RootBox

variable {n : ℕ} {i j k : Fin n} {hij : i ≠ j}

def overlapBox (B : RootBox hij k) (a : ℝ) : RootBox hij k :=
  B.shrink B.transverse (B.time ∩ (fun t : ℝ => t+a) ⁻¹' B.time)
    B.transverse_open (B.time_open.inter (B.time_open.preimage (by fun_prop)))
    subset_rfl inter_subset_left

lemma overlapBox_domain_subset (B : RootBox hij k) (a : ℝ) :
    (B.overlapBox a).domain ⊆ B.domain := fun _ h => ⟨h.1,h.2.1⟩

lemma overlapBox_translate_domain_subset (B : RootBox hij k) (a : ℝ) :
    timeTranslation a '' (B.overlapBox a).domain ⊆ B.domain := by
  rintro _ ⟨z,hz,rfl⟩
  exact ⟨hz.1,hz.2.2⟩

 

theorem mass_translate_on_overlap (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    {S : Set (X n)} (hS : MeasurableSet S) (hSC : S ⊆ (B.overlapBox a).range) :
    μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S := by
  let C := B.overlapBox a
  let T := (rootQuotientParametrization hij) ⁻¹' S ∩ C.domain
  have hT : MeasurableSet T :=
    ((rootQuotientParametrization_localHomeomorph hij).continuous.measurable hS).inter
      (C.transverse_open.prod C.time_open).measurableSet
  have hTC : T ⊆ C.domain := inter_subset_right
  have hTB : T ⊆ B.domain := hTC.trans (B.overlapBox_domain_subset a)
  have hshift : timeTranslation a '' T ⊆ B.domain :=
    (Set.image_mono hTC).trans (B.overlapBox_translate_domain_subset a)
  have hfT : rootQuotientParametrization hij '' T = S := by
    ext x
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact hz.1
    · intro hx
      obtain ⟨z,hz⟩ := hSC hx
      refine ⟨z.val,⟨?_,z.prop⟩,hz⟩
      change rootQuotientParametrization hij z.val ∈ S
      change rootQuotientParametrization hij z.val = x at hz
      rwa [hz]
  have hfshift : rootQuotientParametrization hij '' (timeTranslation a '' T) =
      (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S := by
    rw [Set.image_image,←hfT,Set.image_image]
    congr 1
    funext z
    exact rootQuotientParametrization_add hij z.1 z.2 a
  have H := B.coordinateMeasure_translate_of_haar μ hhaar a hT hTB hshift
  rw [B.coordinateMeasure_apply μ
      ((timeTranslation a).measurableEmbedding.measurableSet_image.mpr hT),
    B.coordinateMeasure_apply μ hT,
    Set.inter_eq_left.mpr hshift,Set.inter_eq_left.mpr hTB,hfshift,hfT] at H
  exact H

 

theorem local_mass_translate_of_endpoints (B : RootBox hij k) (μ : Measure (X n))
    [IsFiniteMeasure μ] (hhaar : B.HasHaarConditionals μ) (a : ℝ)
    (s : RootSlice i j k) (t : ℝ) (hs : s ∈ B.transverse)
    (ht : t ∈ B.time) (hta : t+a ∈ B.time) :
    ∃ U : Set (X n), IsOpen U ∧ rootQuotientParametrization hij (s,t) ∈ U ∧
      ∀ S : Set (X n), MeasurableSet S → S ⊆ U →
        μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S := by
  refine ⟨(B.overlapBox a).range,(B.overlapBox a).range_open,?_,?_⟩
  · exact ⟨⟨(s,t),⟨hs,ht,hta⟩⟩,rfl⟩
  · exact fun S hS hSU => B.mass_translate_on_overlap μ hhaar a hS hSU

end PrimeDegreePackets.RootBox


namespace PrimeDegreePackets

 

theorem root_invariant_of_haar_conditionals (d : ℕ) (μ : Measure (X (d+1)))
    [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (i j : Fin (d+1)) (hij : i ≠ j)
    (hhaar : ∀ (k : Fin (d+1)) (B : RootBox hij k), B.HasHaarConditionals μ)
    (a : ℝ) :
    Measure.map (fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) μ = μ := by
  apply (homeomorph_measurePreserving_of_ae_local μ
    (rightActionHomeomorph (Matrix.SpecialLinearGroup.transvection hij a)) ?_).map_eq
  filter_upwards [ae_rootBox_arbitrary_length d μ hA] with x hx
  obtain ⟨k,B,s,t,hs,hI,hx⟩ := hx i j hij (|a|+1)
  have ht : t ∈ B.time := hI ⟨by linarith [abs_nonneg a],by linarith [abs_nonneg a]⟩
  have hta : t+a ∈ B.time := hI ⟨by linarith [neg_abs_le a],by linarith [le_abs_self a]⟩
  change ∃ U : Set (X (d+1)), IsOpen U ∧ x ∈ U ∧
    ∀ S : Set (X (d+1)), MeasurableSet S → S ⊆ U →
      μ ((fun x => rightAction x (Matrix.SpecialLinearGroup.transvection hij a)) '' S) = μ S
  simpa only [hx] using B.local_mass_translate_of_endpoints μ (hhaar k B) a s t hs ht hta

end PrimeDegreePackets

open MeasureTheory
namespace PrimeDegreePackets

theorem full_invariance_of_haar_conditionals (d : ℕ) (hd : 1 ≤ d)
    (μ : Measure (X (d+1))) [IsFiniteMeasure μ]
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (hhaar : ∀ (i j : Fin (d+1)) (hij : i ≠ j) (k : Fin (d+1))
      (B : RootBox hij k), B.HasHaarConditionals μ) :
    ∀ g : G (d+1), Measure.map (fun x => rightAction x g) μ = μ := by
  apply right_invariant_of_all_roots (by omega)
  intro i j hij a
  exact root_invariant_of_haar_conditionals d μ hA i j hij (hhaar i j hij) a

theorem measure_eq_haar_of_haar_conditionals (d : ℕ) (hd : 1 ≤ d)
    (μ : Measure (X (d+1))) [IsProbabilityMeasure μ]
    (m : Measure (X (d+1))) (hm : IsHaarProbability m)
    (hA : ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) μ = μ)
    (hhaar : ∀ (i j : Fin (d+1)) (hij : i ≠ j) (k : Fin (d+1))
      (B : RootBox hij k), B.HasHaarConditionals μ) : μ = m := by
  exact isHaarProbability_unique
    ⟨inferInstance,full_invariance_of_haar_conditionals d hd μ hA hhaar⟩ hm

end PrimeDegreePackets

open scoped BigOperators ENNReal
namespace PrimeDegreePackets
universe v

lemma complex_summable_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    Summable (fun k : ∀ i, κ i => ‖∏ i, f i (k i)‖) := by
  classical
  apply tsum_enorm_ne_top_iff_summable_norm.mp
  simp only [enorm_eq_nnnorm, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
  rw [ennreal_tsum_fintype_prod κ (fun i a => (‖f i a‖₊ : ℝ≥0∞))]
  exact ENNReal.prod_ne_top (fun i _ => tsum_enorm_ne_top_iff_summable_norm.mpr (hf i))

lemma complex_tsum_fintype_prod {ι : Type*} [Fintype ι]
    (κ : ι → Type v) (f : ∀ i, κ i → ℂ)
    (hf : ∀ i, Summable (fun a => ‖f i a‖)) :
    (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x := by
  classical
  revert κ f
  refine Fintype.induction_empty_option (P := fun ι [Fintype ι] =>
    ∀ (κ : ι → Type v) (f : ∀ i, κ i → ℂ),
      (∀ i, Summable (fun a => ‖f i a‖)) →
      (∑' k : ∀ i, κ i, ∏ i, f i (k i)) = ∏ i, ∑' x : κ i, f i x)
    ?_ ?_ ?_ ι
  · intro α β _ e ih κ f hf
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (fun i => κ (e i)) (fun i => f (e i)) (fun i => hf (e i))
    rw [← (Equiv.piCongrLeft κ e).tsum_eq]
    convert h using 1
    · apply tsum_congr
      intro k
      exact (Fintype.prod_equiv e _ _ (by intro i; simp)).symm
    · exact (Fintype.prod_equiv e _ _ (by intro i; rfl)).symm
  · intro κ f _
    simp
  · intro α _ ih κ f hf
    rw [← Equiv.piOptionEquivProd.symm.tsum_eq]
    simp only [Fintype.prod_option]
    change (∑' c : κ none × (∀ i, κ (some i)),
      f none c.1 * ∏ i, f (some i) (c.2 i)) = _
    rw [←tsum_mul_tsum_of_summable_norm (hf none)
      (complex_summable_fintype_prod _ _ (fun i => hf (some i))), ih _ _ (fun i => hf (some i))]

lemma complex_tsum_multiset_prod {α : Type*} [Fintype α]
    (f : α → ℂ) (hf : ∀ a, ‖f a‖ < 1) :
    Summable (fun m : Multiset α => ‖(m.map f).prod‖) ∧
    (∑' m : Multiset α, (m.map f).prod) = ∏ a, (1-f a)⁻¹ := by
  classical
  let e : (α → ℕ) ≃ Multiset α :=
    Finsupp.equivFunOnFinite.symm.trans Multiset.toFinsupp.symm.toEquiv
  have hm (m : Multiset α) : (m.map f).prod = ∏ a, f a ^ m.count a := by
    rw [Finset.prod_multiset_map_count]
    apply Finset.prod_subset (Finset.subset_univ _)
    intro a _ ha
    rw [Multiset.count_eq_zero.mpr (by simpa using ha),pow_zero]
  have he (k : α → ℕ) (a : α) : (e k).count a = k a := by simp [e]
  have hfS (a : α) : Summable (fun k : ℕ => ‖f a ^ k‖) := by
    simpa only [norm_pow] using summable_geometric_of_norm_lt_one
      (show ‖‖f a‖‖ < 1 by simpa using hf a)
  have hS := complex_summable_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  have hT := complex_tsum_fintype_prod (fun _ : α => ℕ) (fun a k => f a ^ k) hfS
  constructor
  · rw [←e.summable_iff]
    simpa only [Function.comp_def,hm,he] using hS
  · rw [←e.tsum_eq]
    simp only [hm,he]
    rw [hT]
    apply Finset.prod_congr rfl
    intro a _
    exact tsum_geometric_of_norm_lt_one (hf a)

end PrimeDegreePackets

open NumberField Finset
namespace PrimeDegreePackets
variable (K : Type*) [Field K] [NumberField K]

lemma zetaSummand_norm_lt_one {s : ℂ} (hs : 1 < s.re) {m : ℕ} (hm : 2 ≤ m) :
    ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) m‖ < 1 := by
  change ‖(m : ℂ)^(-s)‖ < 1
  rw [←Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg m)
      (Complex.re_neg_ne_zero_of_one_lt_re hs),Complex.neg_re]
  apply Real.rpow_lt_one_of_one_lt_of_neg
  · exact_mod_cast hm
  · linarith

lemma primary_ideal_complex_series {s : ℂ} (hs : 1 < s.re) {p : ℕ} :
    Summable (fun I : PrimaryIdeal K p =>
      ‖riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)‖) ∧
    (∑' I : PrimaryIdeal K p,
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm I.1)) =
      ∏ P : idealsOverPrime K p,
        (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  have HM (m : Multiset (idealsOverPrime K p)) :
      H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1) =
        (m.map (fun P => H (Ideal.absNorm P.1))).prod := by
    rw [primaryIdealMultisetEquiv_val]
    induction m using Multiset.induction_on with
    | empty => simp
    | @cons P m ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,map_mul]
      exact congrArg (fun z => H (Ideal.absNorm P.1)*z) ih
  obtain ⟨hS,hT⟩ := complex_tsum_multiset_prod
    (fun P : idealsOverPrime K p => H (Ideal.absNorm P.1))
    (fun P => zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2))
  constructor
  · rw [←(primaryIdealMultisetEquiv K p).summable_iff]
    change Summable (fun m => ‖H (Ideal.absNorm (primaryIdealMultisetEquiv K p m).1)‖)
    simpa only [HM] using hS
  · rw [←(primaryIdealMultisetEquiv K p).tsum_eq]
    exact (tsum_congr HM).trans hT

lemma norm_fiber_complex_tsum (m : ℕ) (hm : m ≠ 0) (F : ℕ → ℂ) :
    (∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m}, F (Ideal.absNorm I.1)) =
      (idealCoefficient K m : ℂ) * F m := by
  classical
  have : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = m} :=
    (Ideal.finite_setOfPred_absNorm_eq _).to_subtype
  let : Fintype {I : Ideal (𝓞 K) // Ideal.absNorm I = m} := Fintype.ofFinite _
  have he : (fun I : {I : Ideal (𝓞 K) // Ideal.absNorm I = m} => F (Ideal.absNorm I.1)) =
      (fun _ => F m) := funext (fun I => congrArg F I.2)
  rw [he,tsum_fintype,sum_const,idealCoefficient_pos K m hm,Nat.card_eq_fintype_card,
    nsmul_eq_mul,Finset.card_univ]

lemma primary_ideal_tsum_by_norm {p : ℕ} (hp : p.Prime) (H : ℕ → ℂ)
    (HS : Summable (fun I : PrimaryIdeal K p => H (Ideal.absNorm I.1))) :
    (∑' I : PrimaryIdeal K p, H (Ideal.absNorm I.1)) =
      ∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) * H (p^e) := by
  have HE : Summable (fun I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e} =>
      H (Ideal.absNorm I.2.1)) :=
    (primaryIdealNormEquiv K p hp).summable_iff.mpr HS
  calc
    _ = ∑' I : Σe : ℕ, {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.2.1) :=
      ((primaryIdealNormEquiv K p hp).tsum_eq (fun I => H (Ideal.absNorm I.1))).symm
    _ = ∑' e : ℕ, ∑' I : {I : Ideal (𝓞 K) // Ideal.absNorm I = p^e},
          H (Ideal.absNorm I.1) := HE.tsum_sigma
    _ = _ := tsum_congr (fun e => norm_fiber_complex_tsum K _ (pow_ne_zero _ hp.ne_zero) H)

lemma ideal_local_complex_euler {s : ℂ} (hs : 1 < s.re) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, (idealCoefficient K (p^e) : ℂ) *
      riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (p^e)) =
        ∏ P : idealsOverPrime K p,
          (1-riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs) (Ideal.absNorm P.1))⁻¹ := by
  have HD := primary_ideal_complex_series K hs (p := p)
  exact (primary_ideal_tsum_by_norm K hp _ HD.1.of_norm).symm.trans HD.2

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma primePower_succ_injective : Function.Injective
    (fun a : Nat.Primes × ℕ => (a.1 : ℕ) ^ (a.2+1)) := by
  rintro ⟨p,k⟩ ⟨q,l⟩ h
  obtain ⟨hp,hk⟩ := p.property.pow_inj q.property h
  exact Prod.ext (Subtype.ext hp) hk

 

theorem complex_multiplicative_tsum_ne_zero
    (f : ℕ → ℂ) (hzero : f 0 = 0) (hone : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → f (m*n) = f m * f n)
    (hs : Summable (fun m => ‖f m‖))
    (hlocal : ∀ p : Nat.Primes, (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0) :
    (∑' m : ℕ, f m) ≠ 0 := by
  let E (p : Nat.Primes) : ℂ := ∑' k : ℕ, f ((p:ℕ)^k)
  have hpS (p : Nat.Primes) : Summable (fun k : ℕ => f ((p:ℕ)^k)) :=
    hs.of_norm.comp_injective (Nat.pow_right_injective p.property.two_le)
  have hspp : Summable (fun a : Nat.Primes × ℕ => f ((a.1:ℕ)^(a.2+1))) :=
    hs.of_norm.comp_injective primePower_succ_injective
  have he (p : Nat.Primes) : E p = 1 + ∑' k : ℕ, f ((p:ℕ)^(k+1)) := by
    change (∑' k : ℕ, f ((p:ℕ)^k)) = _
    rw [(hpS p).tsum_eq_zero_add]
    simp only [pow_zero,hone]
  have hdev : Summable (fun p : Nat.Primes => 1-E p) := by
    have H := hspp.prod.neg
    exact H.congr (fun p => by dsimp; rw [he]; ring)
  have hl : Summable (fun p : Nat.Primes => Complex.log (E p)) := by
    simpa only [sub_sub_cancel] using hdev.clog_one_sub
  have hP := hl.hasSum.cexp
  have hexp (p : Nat.Primes) : Complex.exp (Complex.log (E p)) = E p :=
    Complex.exp_log (hlocal p)
  simp only [Function.comp_def,hexp] at hP
  have hE : HasProd E (∑' m : ℕ, f m) :=
    EulerProduct.eulerProduct_hasProd hone hmul hs hzero
  rw [hE.unique hP]
  exact Complex.exp_ne_zero _

end PrimeDegreePackets


namespace PrimeDegreePackets

lemma dedekindZeta_ne_zero_of_one_lt_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : NumberField.dedekindZeta K s ≠ 0 := by
  classical
  let H := riemannZetaSummandHom (Complex.ne_zero_of_one_lt_re hs)
  let f (m : ℕ) : ℂ := (idealCoefficient K m : ℂ) * H m
  have hf (m : ℕ) : f m = LSeries.term (fun k => (idealCoefficientReal K k : ℂ)) s m := by
    by_cases hm : m = 0
    · subst m
      simp [f]
    · simp only [f,H,riemannZetaSummandHom,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,
        LSeries.term_of_ne_zero hm,idealCoefficientReal,ArithmeticFunction.coe_mk,
        Complex.ofReal_natCast,Complex.cpow_neg,div_eq_mul_inv]
  have hS : Summable (fun m => ‖f m‖) := by
    simpa only [hf] using (idealCoefficient_LSeriesSummable K hs).norm
  have h0 : f 0 = 0 := by simp [f]
  have h1 : f 1 = 1 := by simp [f,idealCoefficient_one]
  have hm {m n : ℕ} (h : m.Coprime n) : f (m*n) = f m * f n := by
    simp only [f,(idealCoefficient_multiplicative K).map_mul_of_coprime h,
      Nat.cast_mul,map_mul]
    ring
  have hE (p : Nat.Primes) : (∑' k : ℕ, f ((p:ℕ)^k)) ≠ 0 := by
    change (∑' k : ℕ, (idealCoefficient K ((p:ℕ)^k) : ℂ) * H ((p:ℕ)^k)) ≠ 0
    rw [ideal_local_complex_euler K hs p.property]
    apply Finset.prod_ne_zero_iff.mpr
    intro P _
    apply inv_ne_zero
    intro he
    have hn := zetaSummand_norm_lt_one hs (idealsOverPrime_norm_two_le K P.2)
    rw [←sub_eq_zero.mp he,norm_one] at hn
    exact (lt_irrefl _ hn)
  have HN := complex_multiplicative_tsum_ne_zero f h0 h1 (fun h => hm h) hS hE
  have he : (∑' m : ℕ, f m) = NumberField.dedekindZeta K s := by
    calc
      _ = LSeries (fun k => (idealCoefficientReal K k : ℂ)) s := tsum_congr hf
      _ = _ := idealCoefficient_LSeries_eq K s
  rwa [he] at HN

lemma dedekindZeta_analyticAt_of_one_lt_re (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (NumberField.dedekindZeta K) s := by
  let D : Set ℂ := {z | 1 < z.re}
  have hD : IsOpen D := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hd : DifferentiableOn ℂ (NumberField.dedekindZeta K) D := by
    intro z hz
    exact (dedekindZeta_differentiableAt K hz).differentiableWithinAt
  exact hd.analyticOnNhd hD s hs

lemma dedekindZeta_logDeriv_analyticAt_of_one_lt_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ} (hs : 1 < s.re) :
    AnalyticAt ℂ (fun z => deriv (NumberField.dedekindZeta K) z /
      NumberField.dedekindZeta K z) s := by
  have ha := dedekindZeta_analyticAt_of_one_lt_re K hs
  exact ha.deriv.div ha (dedekindZeta_ne_zero_of_one_lt_re K hs)

end PrimeDegreePackets


namespace PrimeDegreePackets

 
def completionExponential (n : ℕ) (D : ℝ) (s : ℂ) : ℂ :=
  Complex.exp (s * (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ)) / 2)

 
def totallyRealCompletedXi (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  s * (s-1) * completionExponential (Module.finrank ℚ K)
    |(NumberField.discr K : ℝ)| s *
    Complex.Gamma (s/2) ^ Module.finrank ℚ K * NumberField.dedekindZeta K s

lemma half_ne_nonpositive_integer {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s/2 ≠ -(m:ℂ) := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.div_ofNat_re,Complex.neg_re,Complex.natCast_re] at hr
  have hm : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma completionExponential_ne_zero (n : ℕ) (D : ℝ) (s : ℂ) :
    completionExponential n D s ≠ 0 := Complex.exp_ne_zero _

lemma completionExponential_hasDerivAt (n : ℕ) (D : ℝ) (s : ℂ) :
    HasDerivAt (completionExponential n D)
      (completionExponential n D s *
        (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))/2) s := by
  have h := (((hasDerivAt_id s).mul_const
    (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))).div_const 2).cexp
  change HasDerivAt (fun z : ℂ => Complex.exp
    (z * ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2))
    (Complex.exp (s*((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2)*
      ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2) s
  simpa only [one_mul,mul_div_assoc,id_eq] using h

lemma completionExponential_logDeriv (n : ℕ) (D : ℝ) (s : ℂ) :
    logDeriv (completionExponential n D) s =
      (((Real.log D : ℝ) : ℂ) - n * (Real.log Real.pi : ℂ))/2 := by
  rw [logDeriv,Pi.div_apply, (completionExponential_hasDerivAt n D s).deriv]
  field_simp [completionExponential_ne_zero]

lemma gammaHalf_hasDerivAt {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (fun z : ℂ => Complex.Gamma (z/2))
      (deriv Complex.Gamma (s/2) / 2) s := by
  have h := (Complex.differentiableAt_Gamma (s/2)
    (half_ne_nonpositive_integer hs)).hasDerivAt.comp s
      ((hasDerivAt_id s).div_const 2)
  simpa only [Function.comp_def,div_eq_mul_inv,id_eq,one_mul] using h

lemma gammaHalf_logDeriv {s : ℂ} (hs : 0 < s.re) :
    logDeriv (fun z : ℂ => Complex.Gamma (z/2)) s =
      Complex.digamma (s/2) / 2 := by
  rw [logDeriv,Pi.div_apply, (gammaHalf_hasDerivAt hs).deriv,Complex.digamma_def,logDeriv,Pi.div_apply]
  ring

lemma totallyRealCompletedXi_ne_zero (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : totallyRealCompletedXi K s ≠ 0 := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hs1 : s-1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [hr] at hs
  unfold totallyRealCompletedXi
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1)
    (completionExponential_ne_zero _ _ _))
    (pow_ne_zero _ (Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith)))))
    (dedekindZeta_ne_zero_of_one_lt_re K hs)

lemma totallyRealCompletedXi_differentiableAt (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : DifferentiableAt ℂ (totallyRealCompletedXi K) s := by
  exact (((differentiableAt_id.mul (differentiableAt_id.sub_const (1:ℂ))).mul
    ((completionExponential_hasDerivAt _ _ _).differentiableAt)).mul
      ((gammaHalf_hasDerivAt (by linarith : 0 < s.re)).differentiableAt.pow _)).mul
        (dedekindZeta_differentiableAt K hs)

lemma totallyRealCompletedXi_logDeriv (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    logDeriv (totallyRealCompletedXi K) s =
      1/s + 1/(s-1) + (Real.log |(NumberField.discr K : ℝ)| : ℂ)/2 +
        logDeriv (NumberField.dedekindZeta K) s +
        (Module.finrank ℚ K : ℂ)/2 *
          (Complex.digamma (s/2) - (Real.log Real.pi : ℂ)) := by
  let n := Module.finrank ℚ K
  let D := |(NumberField.discr K : ℝ)|
  have h0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have h1 : s-1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re (sub_eq_zero.mp he)
    simp [hr] at hs
  have hG : Complex.Gamma (s/2) ≠ 0 :=
    Complex.Gamma_ne_zero (half_ne_nonpositive_integer (by linarith))
  have hE := completionExponential_ne_zero n D s
  have dG := (gammaHalf_hasDerivAt (by linarith : 0 < s.re)).differentiableAt
  have dE := (completionExponential_hasDerivAt n D s).differentiableAt
  have dZ := dedekindZeta_differentiableAt K hs
  have dS : DifferentiableAt ℂ (fun z : ℂ => z*(z-1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  change logDeriv (fun z : ℂ => z*(z-1)*completionExponential n D z*
    Complex.Gamma (z/2)^n*NumberField.dedekindZeta K z) s = _
  have H1 := logDeriv_fun_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z-1) s
    h0 h1 differentiableAt_id (differentiableAt_id.sub_const 1)
  have H2 := logDeriv_fun_mul (f := fun z : ℂ => z*(z-1))
    (g := completionExponential n D) s (mul_ne_zero h0 h1) hE dS dE
  have H3 := logDeriv_fun_mul (f := fun z : ℂ => z*(z-1)*completionExponential n D z)
    (g := fun z : ℂ => Complex.Gamma (z/2)^n) s
    (mul_ne_zero (mul_ne_zero h0 h1) hE) (pow_ne_zero n hG)
    (dS.mul dE) (dG.pow n)
  have H4 := logDeriv_fun_mul
    (f := fun z : ℂ => z*(z-1)*completionExponential n D z*Complex.Gamma (z/2)^n)
    (g := NumberField.dedekindZeta K) s
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) hE) (pow_ne_zero n hG))
    (dedekindZeta_ne_zero_of_one_lt_re K hs) ((dS.mul dE).mul (dG.pow n)) dZ
  rw [H4,H3,H2,H1,completionExponential_logDeriv]
  have hslog : logDeriv (fun z : ℂ => z-1) s = 1/(s-1) := by
    have h : HasDerivAt (fun z : ℂ => z-1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    rw [logDeriv,Pi.div_apply,h.deriv]
  rw [hslog,logDeriv_fun_pow dG n,gammaHalf_logDeriv (by linarith),show logDeriv (fun z : ℂ => z) s = 1/s from logDeriv_id s]
  change (1/s + 1/(s-1) + ((Real.log D : ℂ)-n*(Real.log Real.pi : ℂ))/2 +
    n*(Complex.digamma (s/2)/2)) + logDeriv (NumberField.dedekindZeta K) s = _
  dsimp only [n,D]
  ring

lemma completionExponential_eq_cpow (n : ℕ) {D : ℝ} (hD : 0 < D) (s : ℂ) :
    completionExponential n D s =
      (D:ℂ)^(s/2) * ((Real.pi:ℂ)^(-s/2))^n := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ←Complex.exp_nat_mul,←Complex.exp_add,
    ←Complex.ofReal_log hD.le,←Complex.ofReal_log Real.pi_pos.le]
  unfold completionExponential
  congr 1
  ring

 

lemma totallyRealCompletedXi_eq_GammaReal (K : Type*) [Field K] [NumberField K]
    (s : ℂ) : totallyRealCompletedXi K s =
    s*(s-1) * ((|(NumberField.discr K : ℝ)|:ℝ):ℂ)^(s/2) *
      Complex.Gammaℝ s ^ Module.finrank ℚ K * NumberField.dedekindZeta K s := by
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  rw [totallyRealCompletedXi, completionExponential_eq_cpow _ hD,
    Complex.Gammaℝ_def,mul_pow]
  ring

lemma totallyRealCompletedXi_analyticAt (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : AnalyticAt ℂ (totallyRealCompletedXi K) s := by
  let U : Set ℂ := {z | 1 < z.re}
  have hU : IsOpen U := Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
  have hd : DifferentiableOn ℂ (totallyRealCompletedXi K) U := by
    intro z hz
    exact (totallyRealCompletedXi_differentiableAt K hz).differentiableWithinAt
  exact hd.analyticOnNhd hU s hs

lemma dedekindZeta_ofReal (K : Type*) [Field K] [NumberField K] (s : ℝ) :
    NumberField.dedekindZeta K (s:ℂ) = (realDedekindZeta K s : ℂ) := by
  rw [realDedekindZeta,←idealDirichlet_eq_dedekindZeta K]
  simp

lemma dedekindZeta_logDeriv_re (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (NumberField.dedekindZeta K) (s:ℂ)).re =
      deriv (realDedekindZeta K) s / realDedekindZeta K s := by
  have h := (dedekindZeta_differentiableAt K (s := (s:ℂ))
    (by simpa using hs)).hasDerivAt.real_of_complex
  have hd : deriv (realDedekindZeta K) s =
      (deriv (NumberField.dedekindZeta K) (s:ℂ)).re := h.deriv
  rw [logDeriv_apply,dedekindZeta_ofReal,Complex.div_ofReal_re,hd]

 

lemma totallyRealCompletedXi_logDeriv_re (K : Type*) [Field K] [NumberField K]
    {s : ℝ} (hs : 1 < s) :
    (logDeriv (totallyRealCompletedXi K) (s:ℂ)).re =
      1/s + 1/(s-1) + Real.log |(NumberField.discr K : ℝ)|/2 +
        deriv (realDedekindZeta K) s / realDedekindZeta K s +
          archimedeanZetaTerm (Module.finrank ℚ K) s := by
  rw [totallyRealCompletedXi_logDeriv K (by simpa using hs)]
  simp only [Complex.add_re,Complex.div_ofNat_re,Complex.sub_re,Complex.mul_re,
    Complex.natCast_re,Complex.ofReal_re,Complex.natCast_im,
    Complex.div_ofNat_im,zero_div,zero_mul,sub_zero,Complex.div_ofReal_re,
    Complex.one_re,dedekindZeta_logDeriv_re K hs,archimedeanZetaTerm]
  congr 3
  norm_cast

end PrimeDegreePackets
end
end

end OAI
