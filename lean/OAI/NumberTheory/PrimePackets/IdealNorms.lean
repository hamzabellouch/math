import Mathlib
import OAI.NumberTheory.PrimePackets.CuspMass

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
namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma finite_nonzeroIdeals_norm_le (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    {I : {J : Ideal (𝓞 K) // J ≠ ⊥} | (Ideal.absNorm I.1:ℝ) ≤ X}.Finite := by
  have H := Set.Finite.preimage (f := fun I : {J : Ideal (𝓞 K) // J ≠ ⊥} => I.1)
    Subtype.val_injective.injOn (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) ⌈X⌉₊)
  apply H.subset
  intro I hI
  exact_mod_cast hI.trans (Nat.le_ceil X)

 
def normBoundedIdeals (K : Type*) [Field K] [NumberField K] (X : ℝ) :
    Finset {J : Ideal (𝓞 K) // J ≠ ⊥} := (finite_nonzeroIdeals_norm_le K X).toFinset

@[simp] lemma mem_normBoundedIdeals (K : Type*) [Field K] [NumberField K]
    (X : ℝ) (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) :
    I ∈ normBoundedIdeals K X ↔ (Ideal.absNorm I.1:ℝ) ≤ X :=
  Set.Finite.mem_toFinset _

lemma nonzeroIdeal_absNorm_one_le {K : Type*} [Field K] [NumberField K]
    (I : {J : Ideal (𝓞 K) // J ≠ ⊥}) : (1:ℝ) ≤ Ideal.absNorm I.1 := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp I.2)

lemma normBoundedIdeals_weight_sum_le {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (X t : ℝ) :
    (∑ I ∈ (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t),
      globalIdealWeight M (nonzeroIntegralIdealUnit I)) ≤ weightedIdealRealInterval M t t := by
  calc
    _ = ∑ I ∈ (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t),
        if t-t < (Ideal.absNorm I.1:ℝ) ∧ (Ideal.absNorm I.1:ℝ) ≤ t
        then globalIdealWeight M (nonzeroIntegralIdealUnit I) else 0 := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [ite_eq_left ⟨by linarith [nonzeroIdeal_absNorm_one_le I],(Finset.mem_filter.mp hI).2⟩]
    _ ≤ _ := ENNReal.sum_le_tsum _

 

theorem packetMeasure_cube_moment_le_log_sum {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) {θ : ℝ} (hθ : 0 < θ) :
    let X := θ^(d+1)*packetScale M
    (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
      (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) *
        ENNReal.ofReal (NumberField.dedekindZeta_residue K))⁻¹ *
      (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
      ENNReal.ofReal (∑ I ∈ normBoundedIdeals K X,
        (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
          (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) := by
  dsimp only
  let X := θ^(d+1)*packetScale M
  have hQ := packetScale_pos M
  have hX : 0 < X := mul_pos (pow_pos hθ _) hQ
  rw [packetMeasure_siegel_unfolding M σ hn hodd _ (measurable_boxIndicator _ θ),mul_assoc]
  apply _root_.mul_le_mul_right _ _
  have hfinite : (∑' I : {J : Ideal (𝓞 K) // J ≠ ⊥}, nonzeroIdealWeight M I *
      productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ)
        ((Ideal.absNorm I.1:ℝ)/packetScale M)) =
      ∑ I ∈ normBoundedIdeals K X, nonzeroIdealWeight M I *
        productFiberIntegral (boxIndicator (fun _ : Fin (d+1) => 0) θ)
          ((Ideal.absNorm I.1:ℝ)/packetScale M) := by
    apply tsum_eq_sum
    intro I hI
    have hN := nonzeroIdeal_absNorm_one_le I
    have hout : θ^(d+1) < (Ideal.absNorm I.1:ℝ)/packetScale M :=
      (lt_div_iff₀ hQ).mpr (lt_of_not_ge (fun H => hI ((mem_normBoundedIdeals K X I).mpr H)))
    rw [productFiberIntegral_cube_eq_zero (by positivity) hout,mul_zero]
  rw [hfinite]
  calc
    _ ≤ ∑ I ∈ normBoundedIdeals K X,
        (Fintype.card (Fin (d+1) → SignTypeˣ) : ℝ≥0∞) *
          ENNReal.ofReal ((globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
            (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) := by
      apply Finset.sum_le_sum
      intro I hI
      have hN : (0:ℝ) < Ideal.absNorm I.1 := lt_of_lt_of_le zero_lt_one (nonzeroIdeal_absNorm_one_le I)
      have hNI : (Ideal.absNorm I.1:ℝ)/packetScale M ≤ θ^(d+1) :=
        (div_le_iff₀ hQ).mpr ((mem_normBoundedIdeals K X I).mp hI)
      have H := productFiberIntegral_cube_le hθ (div_pos hN hQ) hNI
      have hlog : θ^(d+1)/((Ideal.absNorm I.1:ℝ)/packetScale M) = X/(Ideal.absNorm I.1:ℝ) := by
        dsimp [X]
        rw [div_div_eq_mul_div]
      rw [hlog] at H
      calc
        _ ≤ nonzeroIdealWeight M I * _ := mul_le_mul_right H _
        _ = _ := by
          rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _)),
            nonzeroIdealWeight_eq_global]
          ring
    _ = _ := by
      rw [← Finset.mul_sum,← ENNReal.ofReal_sum_of_nonneg]
      intro I hI
      apply mul_nonneg ENNReal.toReal_nonneg
      apply pow_nonneg
      apply Real.log_nonneg
      exact (one_le_div (lt_of_lt_of_le zero_lt_one (nonzeroIdeal_absNorm_one_le I))).mpr
        ((mem_normBoundedIdeals K X I).mp hI)

 

theorem weightedIdeal_log_sum_cutoff {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (d : ℕ) (X U Q A : ℝ) (hX : 0 < X) (hU : 0 ≤ U)
    (hA : 0 ≤ A) (hQ : 1 ≤ Q) (hXQ : X ≤ Q) (hUQ : U ≤ Q)
    (hcount : ∀ t : ℝ, U ≤ t → t ≤ Q → weightedIdealRealInterval M t t ≤ ENNReal.ofReal (A*t)) :
    (∑ I ∈ normBoundedIdeals K X,
      (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal *
        (Real.log (X/(Ideal.absNorm I.1:ℝ)))^d) ≤
      A*U*(Real.log Q)^d + A*X*logMomentConstant d := by
  apply log_weighted_sum_cutoff _ (fun I => (Ideal.absNorm I.1:ℝ))
    (fun I => (globalIdealWeight M (nonzeroIntegralIdealUnit I)).toReal) d X U Q A hX hA hQ hXQ
  · exact fun _ _ => ENNReal.toReal_nonneg
  · intro I hI
    exact ⟨nonzeroIdeal_absNorm_one_le I,(mem_normBoundedIdeals K X I).mp hI⟩
  · intro t ht
    have he : (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ t) =
        (normBoundedIdeals K X).filter (fun I => (Ideal.absNorm I.1:ℝ) ≤ min t Q) := by
      ext I
      simp only [Finset.mem_filter,le_min_iff]
      constructor
      · rintro ⟨hI,hIt⟩
        exact ⟨hI,hIt,((mem_normBoundedIdeals K X I).mp hI).trans hXQ⟩
      · exact fun h => ⟨h.1,h.2.1⟩
    have H := (normBoundedIdeals_weight_sum_le M X (min t Q)).trans
      ((hcount (min t Q) (le_min ht hUQ) (min_le_right _ _)).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (min_le_left _ _) hA)))
    rw [he]
    apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA (hU.trans ht))).mp
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    simpa only [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (globalIdealWeight_le_one M _))] using H

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

lemma cutoff_ratio_rpow {Q : ℝ} (hQ : 0 < Q) :
    Q^(3/4:ℝ)/Q = (Q^(1/4:ℝ))⁻¹ := by
  calc
    _ = Q^((3/4:ℝ)-1) := by rw [Real.rpow_sub hQ,Real.rpow_one]
    _ = Q^(-(1/4:ℝ)) := by congr 1; norm_num
    _ = _ := Real.rpow_neg hQ.le _

 

theorem packetMeasure_cube_moment_of_count {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1)) {θ C : ℝ}
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hC : 0 ≤ C) (hQ : 1 ≤ packetScale M)
    (hcount : ∀ t : ℝ, (packetScale M)^(3/4:ℝ) ≤ t → t ≤ packetScale M →
      weightedIdealRealInterval M t t ≤ (saturationIndex M : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal (C*t*NumberField.dedekindZeta_residue K)) :
    (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
      ENNReal.ofReal ((Fintype.card (Fin (d+1) → SignTypeˣ):ℝ)*C*
        ((Real.log (packetScale M))^d/(packetScale M)^(1/4:ℝ) +
          θ^(d+1)*logMomentConstant d)) := by
  let Q := packetScale M
  let q : ℝ := saturationIndex M
  let κ := NumberField.dedekindZeta_residue K
  let U := Q^(3/4:ℝ)
  let X := θ^(d+1)*Q
  let A := C*κ/q
  let B := C*(U/Q*(Real.log Q)^d+θ^(d+1)*logMomentConstant d)
  have hQ0 : 0 < Q := packetScale_pos M
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Nat.pos_of_ne_zero (saturationIndex_ne_zero M)
  have hk : 0 < κ := NumberField.dedekindZeta_residue_pos K
  have hU : 0 ≤ U := Real.rpow_nonneg hQ0.le _
  have hX : 0 < X := mul_pos (pow_pos hθ _) hQ0
  have hXQ : X ≤ Q := mul_le_of_le_one_left hQ0.le (pow_le_one₀ hθ.le hθ1)
  have hUQ : U ≤ Q := Real.rpow_le_self_of_one_le hQ (by norm_num)
  have hA : 0 ≤ A := div_nonneg (mul_nonneg hC hk.le) hq.le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC (add_nonneg (mul_nonneg (div_nonneg hU hQ0.le)
      (pow_nonneg (Real.log_nonneg hQ) _)) (mul_nonneg (pow_nonneg hθ.le _)
        (logMomentConstant_nonneg d)))
  have hcount' (t : ℝ) (ht : U ≤ t) (htQ : t ≤ Q) :
      weightedIdealRealInterval M t t ≤ ENNReal.ofReal (A*t) := by
    apply (hcount t ht htQ).trans_eq
    have he : A*t = (C*t*κ)/q := by dsimp [A]; ring
    rw [he,ENNReal.ofReal_div_of_pos hq,div_eq_mul_inv]
    simp only [q,κ,ENNReal.ofReal_natCast]
    exact mul_comm _ _
  have H := weightedIdeal_log_sum_cutoff M d X U Q A hX hU hA hQ hXQ hUQ hcount'
  have Hm := packetMeasure_cube_moment_le_log_sum M σ hn hodd hθ
  dsimp only at Hm
  apply Hm.trans
  calc
    _ ≤ (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) * ENNReal.ofReal κ)⁻¹ *
        (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞) *
          ENNReal.ofReal (A*U*(Real.log Q)^d+A*X*logMomentConstant d) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal H) _
    _ = (ENNReal.ofReal (Real.sqrt |(NumberField.discr K : ℝ)|) * ENNReal.ofReal κ)⁻¹ *
        (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞) * (saturationIndex M:ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (B*Q*κ) := by
      have he : A*U*(Real.log Q)^d+A*X*logMomentConstant d = (B*Q*κ)/q := by
        dsimp [A,B,X]
        field_simp
      rw [he,ENNReal.ofReal_div_of_pos hq,div_eq_mul_inv]
      simp only [q,ENNReal.ofReal_natCast]
      ring
    _ = (Fintype.card (Fin (d+1) → SignTypeˣ):ℝ≥0∞)*ENNReal.ofReal B :=
      packet_moment_normalization M _ B hB
    _ = _ := by
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      dsimp only [B,U]
      rw [cutoff_ratio_rpow hQ0]
      dsimp only [Q]
      ring

 

theorem packet_cube_moment_bounded_discr (d : ℕ) (hodd : Odd (d+1)) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, ∀ᶠ Q : ℝ in atTop,
      ∀ (K : Type*) [Field K] [NumberField K] [NumberField.IsTotallyReal K]
        (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K),
        Module.finrank ℚ K = d+1 → |NumberField.discr K| ≤ N → packetScale M = Q →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
          (∫⁻ x, siegelTransform (boxIndicator (fun _ : Fin (d+1) => 0) θ) x ∂packetMeasure M σ) ≤
            ENNReal.ofReal (B*(θ^(d+1)+(Real.log Q)^d/Q^(1/4:ℝ))) := by
  obtain ⟨C,hC,Hcount⟩ := weightedIdeal_realInterval_bounded_discr (d+1) (by omega)
  let s : ℝ := Fintype.card (Fin (d+1) → SignTypeˣ)
  let B := s*C*(logMomentConstant d+1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hL := logMomentConstant_nonneg d
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro N
  filter_upwards [Hcount N 1 le_rfl 1 zero_lt_one,eventually_ge_atTop (1:ℝ)] with Q hcount hQ
  intro K _ _ _ M σ hn hD hMQ θ hθ hθ1
  have hQ' : 1 ≤ packetScale M := hMQ ▸ hQ
  have H := packetMeasure_cube_moment_of_count M σ hn hodd hθ hθ1 hC.le hQ' (by
    intro t ht htQ
    apply hcount K M (σ 0) hD hn (by rw [← hMQ]; exact saturationIndex_le_packetScale M) t t
    · simpa only [hMQ] using ht
    · simpa only [one_mul,hMQ] using htQ
    · simp
    · rfl)
  apply H.trans
  apply ENNReal.ofReal_le_ofReal
  rw [hMQ]
  have he : 0 ≤ (Real.log Q)^d/Q^(1/4:ℝ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg hQ) _) (Real.rpow_nonneg (by linarith) _)
  have hθn := pow_nonneg hθ.le (d+1)
  dsimp only [B,s]
  nlinarith [mul_nonneg (mul_nonneg hs.le hC.le) (mul_nonneg hL he)]

end PrimeDegreePackets


namespace PrimeDegreePackets
open MeasureTheory Filter Set Topology
open scoped ENNReal NumberField BigOperators Classical

 

theorem packet_tight_bounded_discr (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (N : ℕ) (hN : ∀ i, |NumberField.discr (K i)| ≤ N)
    (hQ : Tendsto (fun i => packetScale (M i)) atTop atTop) :
    IsTightMeasureSet (Set.range (fun i => packetMeasure (M i) (σ i))) := by
  obtain ⟨B,hB,Hcube⟩ := packet_cube_moment_bounded_discr d hodd
  apply isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mpr
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact ⟨∅,isCompact_empty,fun _ _ => by simp [hεtop]⟩
  let e := ε.toReal
  have he : 0 < e := ENNReal.toReal_pos hε.ne' hεtop
  let θ := min (1/2:ℝ) (e/(4*B))
  have hθ : 0 < θ := lt_min (by norm_num) (div_pos he (by positivity))
  have hθ1 : θ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hθe : B*θ^(d+1) ≤ e/4 := by
    have hpow : θ^(d+1) ≤ θ := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hθ.le (pow_le_one₀ hθ.le hθ1)
    have he' := (le_div_iff₀ (show 0 < 4*B by positivity)).mp (min_le_right (1/2:ℝ) (e/(4*B)))
    dsimp only [θ] at hpow ⊢
    nlinarith
  have Herror := ((cusp_log_error_vanishes d).comp hQ).eventually_lt_const
    (show (0:ℝ) < e/(4*B) by positivity)
  have Hmass : ∀ᶠ i in atTop,
      packetMeasure (M i) (σ i) (thickLattices (d+1) θ)ᶜ ≤ ε := by
    filter_upwards [hQ.eventually (Hcube N),Herror] with i hi herror
    apply (cusp_mass_le_cube_moment (packetMeasure (M i) (σ i)) θ).trans
    apply (hi (K i) (M i) (σ i) (hn i) (hN i) rfl θ hθ hθ1).trans
    rw [← ENNReal.ofReal_toReal hεtop]
    apply ENNReal.ofReal_le_ofReal
    have H := (lt_div_iff₀ (show 0 < 4*B by positivity)).mp herror
    dsimp only [Function.comp_apply] at H
    change B*(θ^(d+1)+(Real.log (packetScale (M i)))^d/(packetScale (M i))^(1/4:ℝ)) ≤ e
    nlinarith
  obtain ⟨i₀,Hi⟩ := eventually_atTop.mp Hmass
  let F : Set (X (d+1)) := ⋃ i : Fin i₀, packetSupport (M i) (σ i)
  have hF : IsCompact F := isCompact_iUnion fun i : Fin i₀ =>
    packetSupport_isCompact (M i) (σ i) (hn i) hodd
  refine ⟨thickLattices (d+1) θ ∪ F,(mahler_compact d θ hθ).union hF,?_⟩
  rintro μ ⟨i,rfl⟩
  by_cases hi : i₀ ≤ i
  · exact (measure_mono (Set.compl_subset_compl.mpr Set.subset_union_left)).trans (Hi i hi)
  · have hs : packetSupport (M i) (σ i) ⊆ thickLattices (d+1) θ ∪ F := by
      intro x hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i,Nat.lt_of_not_ge hi⟩,hx⟩)
    apply (measure_mono (Set.compl_subset_compl.mpr hs)).trans
    rw [packetMeasure_compl_support (M i) (σ i) (hn i) hodd]
    exact bot_le

 

theorem packet_limit_diagonal_invariant (d : ℕ) (hodd : Odd (d+1))
    (K : ℕ → Type*) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, FullLattice (d+1) (K i)) (σ : ∀ i, OrderedEmbeddings (d+1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d+1)
    (ν : ProbabilityMeasure (X (d+1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd) atTop (𝓝 ν))
    (u : LogCoordinates d) :
    Measure.map (fun x => rightAction x (diagonalFlow u)) (ν : Measure (X (d+1))) = ν := by
  apply right_invariance_of_tendsto _ ν hlim
  intro i
  exact packetMeasure_invariant (M i) (σ i) u

end PrimeDegreePackets

open MeasureTheory Filter Set Module TopologicalSpace
namespace PrimeDegreePackets

def diagonalOneParameter {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (t : ℝ) : G n :=
  ⟨Matrix.diagonal (fun i => Real.exp (ell i * t)), by
    rw [Matrix.det_diagonal, ← Real.exp_sum, ← Finset.sum_mul, hell, zero_mul,
      Real.exp_zero]⟩

 

def twoSidedTube {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (b t : ℝ) : Set (G n) :=
  {h | diagonalOneParameter ell hell (-t) * h * diagonalOneParameter ell hell t ∈ matrixBall n b ∧
       diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t) ∈ matrixBall n b}

lemma conjugation_entry {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    (h : G n) (t : ℝ) (i j : Fin n) :
    (diagonalOneParameter ell hell t * h * diagonalOneParameter ell hell (-t)).1 i j =
      Real.exp ((ell i - ell j) * t) * h.1 i j := by
  change (Matrix.diagonal (fun i => Real.exp (ell i * t)) * h.1 *
    Matrix.diagonal (fun i => Real.exp (ell i * (-t)))) i j = _
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [mul_assoc, mul_comm (h.1 i j), ← mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma tube_entries {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    {b t : ℝ} {h : G n} (hh : h ∈ twoSidedTube ell hell b t) :
    (∀ i, |h.1 i i - 1| < b) ∧
      ∀ i j, i ≠ j → |h.1 i j| < b * Real.exp (-|(ell i - ell j) * t|) := by
  constructor
  · intro i
    have H := hh.2 i i
    simpa only [conjugation_entry,sub_self,zero_mul,Real.exp_zero,one_mul,
      Matrix.one_apply_eq] using H
  · intro i j hij
    have Hplus := hh.2 i j
    have Hminus := hh.1 i j
    have he := conjugation_entry ell hell h (-t) i j
    simp only [neg_neg] at he
    rw [he] at Hminus
    simp only [conjugation_entry,Matrix.one_apply_ne hij,sub_zero,abs_mul,
      abs_of_pos (Real.exp_pos _)] at Hplus Hminus
    by_cases hd : 0 ≤ (ell i - ell j) * t
    · rw [abs_of_nonneg hd]
      have H : |h.1 i j| < b / Real.exp ((ell i - ell j)*t) :=
        (lt_div_iff₀ (Real.exp_pos ((ell i - ell j)*t))).mpr (by
          simpa only [mul_comm] using Hplus)
      simpa only [Real.exp_neg,div_eq_mul_inv] using H
    · rw [abs_of_nonpos (le_of_not_ge hd),neg_neg]
      have H : |h.1 i j| < b / Real.exp ((ell i - ell j)*(-t)) :=
        (lt_div_iff₀ (Real.exp_pos ((ell i - ell j)*(-t)))).mpr (by
          simpa only [mul_comm] using Hminus)
      simpa only [mul_neg,Real.exp_neg,inv_inv,div_eq_mul_inv] using H

lemma tube_entries_uniform {n : ℕ} (ell : Fin n → ℝ) (hell : ∑ i, ell i = 0)
    {b t δ : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t)
    (hδ : ∀ i j, i ≠ j → δ ≤ |ell i - ell j|)
    {h : G n} (hh : h ∈ twoSidedTube ell hell b t) :
    (∀ i, |h.1 i i - 1| < b) ∧
      ∀ i j, i ≠ j → |h.1 i j| < b * Real.exp (-δ*t) := by
  refine ⟨(tube_entries ell hell hh).1, ?_⟩
  intro i j hij
  apply ((tube_entries ell hell hh).2 i j hij).trans_le
  apply mul_le_mul_of_nonneg_left _ hb
  apply Real.exp_le_exp.mpr
  rw [abs_mul,abs_of_nonneg ht]
  nlinarith [mul_le_mul_of_nonneg_right (hδ i j hij) ht]

 

lemma exists_two_moved {α : Type*} (σ : Equiv.Perm α) (hσ : σ ≠ 1) :
    ∃ i j, i ≠ j ∧ σ i ≠ i ∧ σ j ≠ j := by
  obtain ⟨i,hi⟩ : ∃ i, σ i ≠ i := by
    by_contra! H
    apply hσ
    exact Equiv.ext H
  refine ⟨i,σ i,Ne.symm hi,hi,?_⟩
  intro he
  exact hi (σ.injective he)

 

lemma product_two_small {α : Type*} [Fintype α] [DecidableEq α]
    (f : α → ℝ) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ i, |f i| ≤ 2)
    {i j : α} (hij : i ≠ j) (hi : |f i| ≤ r) (hj : |f j| ≤ r) :
    |∏ k, f k| ≤ r^2 * 2^(Fintype.card α) := by
  classical
  have hi' : i ∈ (Finset.univ : Finset α) := Finset.mem_univ i
  have hj' : j ∈ (Finset.univ.erase i : Finset α) := by simp [hij.symm]
  rw [←Finset.mul_prod_erase _ _ hi', ←Finset.mul_prod_erase _ _ hj',
    abs_mul,abs_mul]
  have HT : |∏ k ∈ (Finset.univ.erase i).erase j, f k| ≤
      2^((Finset.univ.erase i).erase j).card := by
    rw [Finset.abs_prod]
    simpa only [Finset.prod_const] using Finset.prod_le_prod₀
      (fun k _ => abs_nonneg (f k)) (fun k _ => hf k)
  have HC : ((Finset.univ.erase i).erase j).card ≤ Fintype.card α := by
    exact Finset.card_le_card (by simp)
  have HP : (2:ℝ)^((Finset.univ.erase i).erase j).card ≤ 2^(Fintype.card α) :=
    pow_le_pow_right₀ (by norm_num) HC
  calc
    _ ≤ r * (r * 2^((Finset.univ.erase i).erase j).card) :=
      mul_le_mul hi (mul_le_mul hj HT (abs_nonneg _) hr) (by positivity) hr
    _ ≤ r^2 * 2^(Fintype.card α) := by
      nlinarith [mul_le_mul_of_nonneg_left HP (sq_nonneg r)]

 

lemma determinant_diagonal_error {n : ℕ} {h : G n} {r : ℝ}
    (hr : 0 ≤ r)
    (hall : ∀ i j, |h.1 i j| ≤ 2)
    (hoff : ∀ i j, i ≠ j → |h.1 i j| ≤ r) :
    |(∏i, h.1 i i) - 1| ≤ (Nat.factorial n : ℝ) * 2^n * r^2 := by
  classical
  have Hterm (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) :
      |Equiv.Perm.sign σ * ∏i, h.1 (σ i) i| ≤ r^2 * 2^n := by
    obtain ⟨i,j,hij,hi,hj⟩ := exists_two_moved σ hσ
    rw [abs_mul]
    have hs : |(Equiv.Perm.sign σ : ℝ)| = 1 := by
      rw [←Int.cast_abs, Int.abs_eq_natAbs, Int.units_natAbs]
      norm_num
    rw [hs,one_mul]
    simpa using product_two_small (fun k => h.1 (σ k) k) hr
      (fun k => hall (σ k) k) hij (hoff _ _ hi) (hoff _ _ hj)
  have Hdet : (1:ℝ) = (∏ i, h.1 i i) +
      ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        Equiv.Perm.sign σ * ∏i, h.1 (σ i) i := by
    calc
      1 = Matrix.det h.1 := h.2.symm
      _ = _ := by
        rw [Matrix.det_apply']
        rw [←Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
        simp
  have HE : (∏i, h.1 i i) - 1 =
      -(∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        Equiv.Perm.sign σ * ∏i, h.1 (σ i) i) := by linarith
  rw [HE,abs_neg]
  calc
    _ ≤ ∑ σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)),
        |Equiv.Perm.sign σ * ∏i, h.1 (σ i) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), r^2 * 2^n := by
      exact Finset.sum_le_sum (fun σ hσ => Hterm σ (Finset.ne_of_mem_erase hσ))
    _ ≤ (Nat.factorial n : ℝ) * 2^n * r^2 := by
      rw [Finset.sum_const,nsmul_eq_mul]
      have HC : (Finset.univ.erase (1 : Equiv.Perm (Fin n))).card ≤ Nat.factorial n := by
        calc
          _ ≤ (Finset.univ : Finset (Equiv.Perm (Fin n))).card :=
            Finset.card_le_card (Finset.erase_subset _ _)
          _ = _ := by rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
      have HC' : ((Finset.univ.erase (1 : Equiv.Perm (Fin n))).card : ℝ) ≤ Nat.factorial n :=
        Nat.cast_le.mpr HC
      nlinarith [mul_le_mul_of_nonneg_right HC' (by positivity : 0 ≤ r^2 * (2:ℝ)^n)]

 

lemma diagonalFlow_neg_log_val {d : ℕ} (h : G (d+1))
    (hd : ∀ i, 0 < h.1 i i) :
    (diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc))).1 =
      Matrix.diagonal (Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
        (∏ i : Fin d, h.1 i.castSucc i.castSucc)) := by
  change Matrix.diagonal _ = Matrix.diagonal _
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last, Finset.sum_neg_distrib,neg_neg,Real.exp_sum]
    exact Finset.prod_congr rfl (fun i _ => Real.exp_log (hd i.castSucc))
  · simp only [Fin.snoc_castSucc,Real.exp_neg,Real.exp_log (hd j.castSucc)]

lemma normalizing_scalars_le {d : ℕ} (h : G (d+1))
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) (i : Fin (d+1)) :
    (0:ℝ) < Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
      (∏ i : Fin d, h.1 i.castSucc i.castSucc) i ∧
    Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
      (∏ i : Fin d, h.1 i.castSucc i.castSucc) i ≤ (2:ℝ) + 2^d := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    constructor
    · exact Finset.prod_pos (fun j _ => lt_of_lt_of_le (by norm_num) (hd j.castSucc).1)
    · have H : (∏j : Fin d, h.1 j.castSucc j.castSucc) ≤ (2:ℝ)^d := by
        simpa using Finset.prod_le_prod₀ (s := Finset.univ)
          (fun (j : Fin d) _ => (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) (hd j.castSucc).1).le)
          (fun (j : Fin d) _ => (hd j.castSucc).2)
      linarith
  · simp only [Fin.snoc_castSucc]
    have hp : 0 < h.1 j.castSucc j.castSucc := lt_of_lt_of_le (by norm_num) (hd j.castSucc).1
    refine ⟨inv_pos.mpr hp, ?_⟩
    have H : (h.1 j.castSucc j.castSucc)⁻¹ ≤ 2 := by
      exact (inv_le_comm₀ hp (by norm_num)).mpr (by simpa using (hd j.castSucc).1)
    linarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d]

 

lemma normalized_matrix_entry_bound {d : ℕ} (h : G (d+1)) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2)
    (hoff : ∀ i j, i ≠ j → |h.1 i j| ≤ r) (i j : Fin (d+1)) :
    |(diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc)) * h).1 i j -
      (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤
      (((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d) * r := by
  have hp : ∀ i, 0 < h.1 i i := fun i => lt_of_lt_of_le (by norm_num) (hd i).1
  have he : (diagonalFlow (fun i : Fin d => -Real.log (h.1 i.castSucc i.castSucc)) * h).1 =
      Matrix.diagonal (Fin.snoc (α := fun _ => ℝ) (fun i : Fin d => (h.1 i.castSucc i.castSucc)⁻¹)
        (∏ i : Fin d, h.1 i.castSucc i.castSucc)) * h.1 := by
    change (diagonalFlow _).1 * h.1 = _
    rw [diagonalFlow_neg_log_val h hp]
  rw [he,Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply_eq]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      have hall : ∀ i j, |h.1 i j| ≤ 2 := by
        intro i j
        by_cases he : i=j
        · subst j; rw [abs_of_pos (hp i)]; exact (hd i).2
        · exact (hoff i j he).trans (by linarith)
      have HD := determinant_diagonal_error hr hall hoff
      rw [Fin.prod_univ_castSucc] at HD
      have hrr : r^2 ≤ r := by nlinarith
      have HC : (0:ℝ) ≤ ((d+1).factorial : ℝ) * 2^(d+1) := by positivity
      have HE : ((d+1).factorial : ℝ) * 2^(d+1) * r^2 ≤
          (((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d)*r := by
        nlinarith [mul_le_mul_of_nonneg_left hrr HC,
          mul_nonneg hr (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) d)]
      exact HD.trans HE
    · simp only [Fin.snoc_castSucc,inv_mul_cancel₀ (hp j.castSucc).ne',sub_self,abs_zero]
      positivity
  · rw [Matrix.one_apply_ne hij,sub_zero,abs_mul,abs_of_pos (normalizing_scalars_le h hd i).1]
    have H := mul_le_mul (normalizing_scalars_le h hd i).2 (hoff i j hij)
      (abs_nonneg _) (by positivity : (0:ℝ) ≤ 2+2^d)
    have HC : (0:ℝ) ≤ ((d+1).factorial : ℝ) * 2^(d+1)*r := by positivity
    nlinarith

 

lemma diagonal_log_mem_compact_box {d : ℕ} (h : G (d+1))
    (hd : ∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) :
    (fun i : Fin d => Real.log (h.1 i.castSucc i.castSucc)) ∈
      Set.pi Set.univ (fun _ => Set.Icc (-Real.log 2) (Real.log 2)) := by
  intro i _
  have hp : 0 < h.1 i.castSucc i.castSucc := lt_of_lt_of_le (by norm_num) (hd i.castSucc).1
  constructor
  · have H := Real.log_le_log (by norm_num : (0:ℝ)<1/2) (hd i.castSucc).1
    simpa only [one_div,Real.log_inv] using H
  · exact Real.log_le_log hp (hd i.castSucc).2

 

theorem cube_grid_cover (d : ℕ) {R r : ℝ} (hR : 0 ≤ R) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ s : Finset (Fin d → ℝ),
      (∀ u ∈ s, ∀ i, |u i| ≤ R+1) ∧
      (s.card : ℝ) ≤ (2*R+2)^d / r^d ∧
      ∀ x : Fin d → ℝ, (∀ i, |x i| ≤ R) →
        ∃ u ∈ s, ∀ i, |x i-u i| < r := by
  classical
  let N : ℕ := ⌈2*R/r⌉₊
  let g (k : Fin d → Fin (N+1)) : Fin d → ℝ := fun i => -R + (k i : ℕ)*r
  let s : Finset (Fin d → ℝ) := Finset.univ.image g
  have hN : (N:ℝ) < 2*R/r+1 := by
    exact Nat.ceil_lt_add_one (div_nonneg (by positivity) hr.le)
  have hNr : (N:ℝ)*r < 2*R+r := by
    have := (mul_lt_mul_iff_left₀ hr).mpr hN
    field_simp at this
    nlinarith
  refine ⟨s, ?_, ?_, ?_⟩
  · intro u hu i
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
    dsimp [g]
    rw [abs_le]
    constructor
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) (k i).val) hr.le]
    · have hki : ((k i).val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (k i).isLt)
      nlinarith [mul_le_mul_of_nonneg_right hki hr.le]
  · have hcard : s.card ≤ (N+1)^d := by
      calc
        _ ≤ (Finset.univ : Finset (Fin d → Fin (N+1))).card := Finset.card_image_le
        _ = _ := by simp
    have hN1 : ((N+1:ℕ):ℝ) ≤ (2*R+2)/r := by
      apply (le_div_iff₀ hr).mpr
      push_cast
      nlinarith
    calc
      (s.card:ℝ) ≤ (((N+1)^d:ℕ):ℝ) := Nat.cast_le.mpr hcard
      _ = (((N+1:ℕ):ℝ))^d := Nat.cast_pow _ _
      _ ≤ ((2*R+2)/r)^d := pow_le_pow_left₀ (Nat.cast_nonneg _) hN1 d
      _ = _ := div_pow _ _ _
  · intro x hx
    have hx0 (i : Fin d) : 0 ≤ (x i+R)/r := by
      apply div_nonneg _ hr.le
      have := (abs_le.mp (hx i)).1
      linarith
    let k (i : Fin d) : Fin (N+1) := ⟨⌊(x i+R)/r⌋₊, by
      apply Nat.lt_succ_of_le
      apply (Nat.floor_mono ?_).trans (Nat.floor_le_ceil _)
      apply div_le_div_of_nonneg_right _ hr.le
      have := (abs_le.mp (hx i)).2
      linarith⟩
    refine ⟨g k, Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
    intro i
    have hlo := Nat.floor_le (hx0 i)
    have hhi := Nat.lt_floor_add_one ((x i+R)/r)
    have Hlo : (⌊(x i+R)/r⌋₊ : ℝ)*r ≤ x i+R := (le_div_iff₀ hr).mp hlo
    have Hhi : x i+R < ((⌊(x i+R)/r⌋₊ : ℝ)+1)*r := (div_lt_iff₀ hr).mp hhi
    dsimp [g,k]
    rw [abs_of_nonneg (by linarith)]
    linarith

lemma exp_sub_one_abs_le {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - 1| ≤ 2 * |x| := by
  have H := Real.norm_exp_sub_one_sub_id_le (show ‖x‖ ≤ 1 by simpa using hx)
  simp only [Real.norm_eq_abs] at H
  have He := abs_le.mp H
  have Ha := abs_le.mp (le_refl |x|)
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg x]

lemma diagonalFlow_small_entries {d : ℕ} {u : Fin d → ℝ} {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hu : ∀ i, |u i| ≤ r / (d+1)) (i j : Fin (d+1)) :
    |(diagonalFlow u).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ 2*r := by
  have hd : (0:ℝ) < d+1 := by positivity
  have hsmall (i : Fin d) : |u i| ≤ r := by
    exact (hu i).trans (div_le_self hr (by linarith [Nat.cast_nonneg (α := ℝ) d]))
  have hsum : |∑ i, u i| ≤ r := by
    calc
      _ ≤ ∑ i, |u i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, r/(d+1) := Finset.sum_le_sum (fun i _ => hu i)
      _ = (d:ℝ)*(r/(d+1)) := by simp
      _ ≤ r := by
        have H : (d:ℝ) ≤ d+1 := by linarith
        have := mul_le_mul_of_nonneg_right H (div_nonneg hr hd.le)
        rwa [mul_div_cancel₀ _ hd.ne'] at this
  change |(Matrix.diagonal _ : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j - _| ≤ _
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simp only [Fin.snoc_last]
      exact (exp_sub_one_abs_le (by simpa only [abs_neg] using hsum.trans hr1)).trans
        (by simpa only [abs_neg] using mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2))
    · simp only [Fin.snoc_castSucc]
      exact (exp_sub_one_abs_le ((hsmall k).trans hr1)).trans
        (mul_le_mul_of_nonneg_left (hsmall k) (by norm_num))
  · simp only [Matrix.diagonal_apply_ne _ hij,Matrix.one_apply_ne hij,sub_self,abs_zero]
    positivity

 

lemma matrix_product_entry_error {n : ℕ} {g h : G n} {a b : ℝ}
    (ha : 0 ≤ a)
    (hg : ∀ i j, |g.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ a)
    (hh : ∀ i j, |h.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ b)
    (i j : Fin n) :
    |(g*h).1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| ≤ a+b+n*a*b := by
  let I : Matrix (Fin n) (Fin n) ℝ := 1
  have He : (g*h).1 - I = (g.1-I)*(h.1-I)+(g.1-I)+(h.1-I) := by
    change g.1*h.1-I = _
    simp only [I,mul_sub,sub_mul,Matrix.one_mul,Matrix.mul_one]
    abel
  have Hij := congrFun (congrFun He i) j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.mul_apply] at Hij
  rw [Hij]
  calc
    _ ≤ |∑ k, (g.1 i k-I i k)*(h.1 k j-I k j)| + |g.1 i j-I i j| + |h.1 i j-I i j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (∑ _k : Fin n, a*b)+a+b := by
      apply add_le_add (add_le_add ?_ (hg i j)) (hh i j)
      exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k _ => by
        rw [abs_mul]
        exact mul_le_mul (hg i k) (hh k j) (abs_nonneg _) ha))
    _ = _ := by simp; ring

 

theorem near_diagonal_cover (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∃ s : Finset (Fin d → ℝ),
        (∀ u ∈ s, ∀ i, |u i| ≤ Real.log 2+1) ∧
        (s.card : ℝ) ≤ C / r^d ∧
        ∀ h : G (d+1),
          (∀ i, (1:ℝ)/2 ≤ h.1 i i ∧ h.1 i i ≤ 2) →
          (∀ i j, i ≠ j → |h.1 i j| ≤ r) →
          ∃ u ∈ s, h ∈ (fun k => diagonalFlow u * k) '' matrixBall (d+1) (C*r) := by
  classical
  let A : ℝ := ((d+1).factorial : ℝ)*2^(d+1) + 2 + 2^d
  let B : ℝ := 2+A+2*(d+1)*A
  let E : ℝ := ((2*Real.log 2+2)*(d+1))^d
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨B+E+1, by positivity, ?_⟩
  intro r hr hr1
  have hd : (0:ℝ) < d+1 := by positivity
  have hρ : 0 < r/(d+1) := div_pos hr hd
  have hρ1 : r/(d+1) ≤ 1 := (div_le_self hr.le (by linarith [Nat.cast_nonneg (α := ℝ) d])).trans hr1
  obtain ⟨s,hs,hcard,hcover⟩ := cube_grid_cover d
    (Real.log_nonneg (by norm_num : (1:ℝ)≤2)) hρ hρ1
  refine ⟨s,hs,?_,?_⟩
  · have hcard' : (s.card:ℝ) ≤ E/r^d := by
      convert hcard using 1
      dsimp [E]
      rw [div_pow,mul_pow]
      field_simp
    exact hcard'.trans (div_le_div_of_nonneg_right (by linarith) (pow_nonneg hr.le d))
  · intro h hdiag hoff
    let x : Fin d → ℝ := fun i => Real.log (h.1 i.castSucc i.castSucc)
    have hx : ∀ i, |x i| ≤ Real.log 2 := by
      intro i
      exact abs_le.mpr (diagonal_log_mem_compact_box h hdiag i (Set.mem_univ _))
    obtain ⟨u,hu,hxu⟩ := hcover x hx
    have hw : ∀ i, |(x-u) i| ≤ r/(d+1) := fun i => (hxu i).le
    have HD := diagonalFlow_small_entries hr.le hr1 hw
    have HN : ∀ i j,
        |(diagonalFlow (-x) * h).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ A*r :=
      normalized_matrix_entry_bound h hr.le hr1 hdiag hoff
    have Hmul := matrix_product_entry_error (show 0 ≤ 2*r by positivity)
      HD HN
    have He : diagonalFlow (x-u) * (diagonalFlow (-x) * h) = diagonalFlow (-u)*h := by
      rw [←mul_assoc,←diagonalFlow_add]
      congr 2
      abel
    have Herror (i j : Fin (d+1)) :
        |(diagonalFlow (-u)*h).1 i j - (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℝ) i j| ≤ B*r := by
      have H := Hmul i j
      rw [He] at H
      apply H.trans
      have Hr : r*r ≤ r := by nlinarith
      have HC : 0 ≤ 2*(d+1)*A := by positivity
      have := mul_le_mul_of_nonneg_left Hr HC
      dsimp [B]
      push_cast
      nlinarith
    refine ⟨u,hu,diagonalFlow (-u)*h,?_,?_⟩
    · intro i j
      exact (Herror i j).trans_lt (by nlinarith)
    · change diagonalFlow u * (diagonalFlow (-u) * h) = h
      rw [←mul_assoc,←diagonalFlow_add,add_neg_cancel,diagonalFlow_zero,one_mul]

 

theorem tube_cover (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : Fin (d+1) → ℝ) (hell : ∑i, ell i = 0)
      (δ b t : ℝ), 0 ≤ δ → 0 ≤ b → b < 1/4 → 0 ≤ t →
      (∀ i j, i ≠ j → δ ≤ |ell i-ell j|) →
      ∃ s : Finset (Fin d → ℝ),
        (∀ u ∈ s, ∀ i, |u i| ≤ Real.log 2+1) ∧
        (s.card : ℝ) ≤ C / (Real.exp (-δ*t))^d ∧
        ∀ h ∈ twoSidedTube ell hell b t,
          ∃ u ∈ s, h ∈ (fun k => diagonalFlow u*k) ''
            matrixBall (d+1) (C*Real.exp (-δ*t)) := by
  obtain ⟨C,hC,H⟩ := near_diagonal_cover d
  refine ⟨C,hC,?_⟩
  intro ell hell δ b t hδ hb hb1 ht hgap
  have hr1 : Real.exp (-δ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  obtain ⟨s,hs,hcard,hcover⟩ := H (Real.exp (-δ*t)) (Real.exp_pos _) hr1
  refine ⟨s,hs,hcard,?_⟩
  intro h hh
  obtain ⟨hdiag,hoff⟩ := tube_entries_uniform ell hell hb ht hgap hh
  apply hcover h
  · intro i
    have Hi := abs_lt.mp (hdiag i)
    constructor <;> linarith
  · intro i j hij
    exact (hoff i j hij).le.trans (mul_le_of_le_one_left (Real.exp_pos _).le (by linarith))

 

lemma continuous_rightAction_uncurry (n : ℕ) :
    Continuous (fun p : X n × G n => rightAction p.1 p.2) := by
  have hq : IsOpenQuotientMap (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) :=
    ⟨Quotient.mk_surjective, continuous_quotient_mk', (quotient_covering n).isOpenMap⟩
  apply (hq.prodMap IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  exact continuous_quotient_mk'.comp (continuous_fst.mul continuous_snd)

 

def diagonalLogBox (d : ℕ) : Set (LogCoordinates d) :=
  {u | ∀ i, |u i| ≤ Real.log 2+1}

lemma diagonalLogBox_isCompact (d : ℕ) : IsCompact (diagonalLogBox d) := by
  simpa only [diagonalLogBox,abs_le,Set.mem_Icc] using
    (isCompact_pi_infinite (fun _i : Fin d =>
      show IsCompact (Set.Icc (-(Real.log 2+1)) (Real.log 2+1)) from isCompact_Icc))

lemma compact_diagonal_thickening {d : ℕ} {Ω : Set (X (d+1))} (hΩ : IsCompact Ω) :
    IsCompact ((fun p : X (d+1) × LogCoordinates d => rightAction p.1 (diagonalFlow p.2)) ''
      (Ω ×ˢ diagonalLogBox d)) := by
  refine (hΩ.prod (diagonalLogBox_isCompact d)).image ?_
  exact (continuous_rightAction_uncurry (d+1)).comp
    (continuous_fst.prodMk ((continuous_diagonalFlow d).comp continuous_snd))

 

def OrdinaryBallBound (n : ℕ) (μ : Measure (X n)) : Prop :=
  ∀ Ω : Set (X n), IsCompact Ω → ∃ C r₀ : ℝ, 0 < C ∧ 0 < r₀ ∧
    ∀ x ∈ Ω, ∀ r : ℝ, 0 < r → r < r₀ →
      μ ((fun h => rightAction x h) '' matrixBall n r) ≤ ENNReal.ofReal (C*r^n)

lemma ordinaryBallBound_of_le {n : ℕ} {μ ξ : Measure (X n)}
    (hμ : OrdinaryBallBound n μ) {c : ℝ} (hc : 0 < c)
    (hξ : ξ ≤ ENNReal.ofReal c • μ) : OrdinaryBallBound n ξ := by
  intro Ω hΩ
  obtain ⟨C,r₀,hC,hr₀,H⟩ := hμ Ω hΩ
  refine ⟨c*C,r₀,mul_pos hc hC,hr₀,?_⟩
  intro x hx r hr hrr
  calc
    ξ _ ≤ (ENNReal.ofReal c • μ) _ := hξ _
    _ = ENNReal.ofReal c * μ _ := Measure.smul_apply _ _ _
    _ ≤ ENNReal.ofReal c * ENNReal.ofReal (C*r^n) := mul_le_mul_right (H x hx r hr hrr) _
    _ = ENNReal.ofReal ((c*C)*r^n) := by rw [← ENNReal.ofReal_mul hc.le]; congr 1; ring

 

theorem tube_mass_of_ordinary_balls {d : ℕ} {ξ : Measure (X (d+1))}
    (hξ : OrdinaryBallBound (d+1) ξ) (Ω : Set (X (d+1))) (hΩ : IsCompact Ω)
    (ell : Fin (d+1) → ℝ) (hell : ∑ i, ell i = 0)
    {δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) (hb1 : b < 1/4)
    (hgap : ∀ i j, i ≠ j → δ ≤ |ell i-ell j|) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop,
      ∀ x ∈ Ω, ξ ((fun h => rightAction x h) '' twoSidedTube ell hell b t) ≤
        ENNReal.ofReal (K*Real.exp (-δ*t)) := by
  classical
  obtain ⟨C,hC,Hcover⟩ := tube_cover d
  let Ω' : Set (X (d+1)) :=
    (fun p : X (d+1) × LogCoordinates d => rightAction p.1 (diagonalFlow p.2)) ''
      (Ω ×ˢ diagonalLogBox d)
  obtain ⟨A,r₀,hA,hr₀,Hball⟩ := hξ Ω' (compact_diagonal_thickening hΩ)
  have hexp : Tendsto (fun t : ℝ => Real.exp (-δ*t)) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hδ)).mpr tendsto_id)
  have hsmall : ∀ᶠ t : ℝ in atTop, C*Real.exp (-δ*t) < r₀ := by
    have H : Tendsto (fun t : ℝ => C*Real.exp (-δ*t)) atTop (𝓝 (C*0)) :=
      tendsto_const_nhds.mul hexp
    simpa only [mul_zero] using H.eventually (eventually_lt_nhds (by simpa using hr₀))
  refine ⟨A*C^(d+2),by positivity,?_⟩
  filter_upwards [hsmall,eventually_ge_atTop (0:ℝ)] with t htr ht
  obtain ⟨s,hs,hcard,Hs⟩ := Hcover ell hell δ b t hδ.le hb hb1 ht hgap
  intro x hx
  let r : ℝ := Real.exp (-δ*t)
  have hr : 0 < r := Real.exp_pos _
  have Hsub : (fun h => rightAction x h) '' twoSidedTube ell hell b t ⊆
      ⋃ u ∈ s, (fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r) := by
    rintro z ⟨h,hh,rfl⟩
    obtain ⟨u,hu,k,hk,rfl⟩ := Hs h hh
    refine Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,?_⟩⟩
    exact ⟨k,hk,rightAction_mul x _ _⟩
  have Hcenter (u : LogCoordinates d) (hu : u ∈ s) : rightAction x (diagonalFlow u) ∈ Ω' :=
    ⟨(x,u),⟨hx,hs u hu⟩,rfl⟩
  calc
    ξ _ ≤ ξ (⋃ u ∈ s, (fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r)) := measure_mono Hsub
    _ ≤ ∑ u ∈ s, ξ ((fun k => rightAction (rightAction x (diagonalFlow u)) k) ''
        matrixBall (d+1) (C*r)) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ s, ENNReal.ofReal (A*(C*r)^(d+1)) :=
      Finset.sum_le_sum (fun u hu => Hball _ (Hcenter u hu) _ (mul_pos hC hr) htr)
    _ = ENNReal.ofReal ((s.card:ℝ)*(A*(C*r)^(d+1))) := by
      rw [Finset.sum_const,nsmul_eq_mul]
      simp only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((C/r^d)*(A*(C*r)^(d+1))) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcard (by positivity))
    _ = ENNReal.ofReal ((A*C^(d+2))*r) := by
      congr 1
      rw [mul_pow,pow_succ r,pow_succ C,show d+2=(d+1)+1 from rfl,pow_succ C]
      field_simp
      ring

end PrimeDegreePackets
end
end

end OAI
