import OAI.Combinatorics.SparsestCut.InterfaceStep

namespace OAI

universe u1 u2 u3 u4 u5

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SliceCoefficients
open MeasureTheory Set
open scoped BigOperators Topology
variable {X : Type u1} {Z : Type u2} {I : Type u3} {K : Type u4} {A : Type u5} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [MeasurableSpace Z] [BorelSpace Z] [Fintype I] [Fintype K] [Fintype A]
  [DecidableEq I] [DecidableEq K]

lemma affine_hyperplane_null (L : Z →L[ℝ] ℝ) (hL : L ≠ 0) (t : ℝ)
    (ν : Measure Z) [ν.IsAddHaarMeasure] : ν {z | L z=t}=0 := by
  let H : AffineSubspace ℝ Z :=
    { carrier := {z | L z=t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change L x=t at hx
        change L y=t at hy
        change L z=t at hz
        change L (c • (x-y)+z)=t
        simp only [map_add,map_smul,map_sub,smul_eq_mul,hx,hy,hz]
        ring }
  have ht : H ≠ ⊤ := by
    intro he
    have hzero : (0:Z) ∈ H := by rw [he]; trivial
    change L 0=t at hzero
    rw [map_zero] at hzero
    apply hL
    ext x
    have hx : x ∈ H := by rw [he]; trivial
    change L x=t at hx
    simpa [← hzero] using hx
  exact Measure.addHaar_affineSubspace ν H ht

lemma thresholds_injective_ae (L : I → X →L[ℝ] ℝ) (B : I → Z →L[ℝ] ℝ)
    (q : I → K → ℝ) (hq : ∀ i, Function.Injective (q i))
    (hB : Function.Injective B) (ν : Measure Z) [ν.IsAddHaarMeasure]
    (μ : Measure Z) (hμ : μ ≪ ν) (y : X) :
    ∀ᵐ z ∂μ, Function.Injective (fun p : I × K => L p.1 y+B p.1 z+q p.1 p.2) := by
  have hp (p r : I × K) (hpr : p ≠ r) :
      ∀ᵐ z ∂μ, L p.1 y+B p.1 z+q p.1 p.2 ≠ L r.1 y+B r.1 z+q r.1 r.2 := by
    by_cases hi : p.1=r.1
    · filter_upwards with z hz
      have hk : p.2=r.2 := hq p.1 (by rw [← hi] at hz; linarith)
      exact hpr (Prod.ext hi hk)
    · have hn : B p.1-B r.1 ≠ 0 := sub_ne_zero.mpr (fun he => hi (hB he))
      have hnul := affine_hyperplane_null (B p.1-B r.1) hn
        (L r.1 y+q r.1 r.2-(L p.1 y+q p.1 p.2)) ν
      have hae : ∀ᵐ z ∂ν, (B p.1-B r.1) z ≠ L r.1 y+q r.1 r.2-(L p.1 y+q p.1 p.2) := by
        rw [ae_iff]; simpa only [not_not] using hnul
      filter_upwards [hμ.ae_le hae] with z hz he
      apply hz
      simp only [_root_.sub_apply]
      linarith
  have ha (p r : I × K) : ∀ᵐ z ∂μ,
      L p.1 y+B p.1 z+q p.1 p.2 = L r.1 y+B r.1 z+q r.1 r.2 → p=r := by
    by_cases hpr : p=r
    · exact ae_of_all _ (fun _ _ => hpr)
    · filter_upwards [hp p r hpr] with z hz he using (hz he).elim
  exact ae_all_iff.mpr (fun p => ae_all_iff.mpr (ha p))

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] in

lemma family_derivative (L : I → X →L[ℝ] ℝ) (b : I × K → Z → ℝ)
    (hb : ∀ p, Measurable (b p)) (F : Finset (I × K) → ℝ)
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hc : Continuous φ)
    {M C : ℝ} (hM0 : 0 ≤ M) (hC : 0 ≤ C)
    (hM : ∀ a, |F a| ≤ M) (hφC : ∀ x, |φ x| ≤ C)
    (μ : Measure Z) [IsFiniteMeasure μ] (y : X)
    (hi : ∀ᵐ z ∂μ, Function.Injective (fun p : I × K => L p.1 y+b p z)) :
    HasFDerivAt (fun y => ∫ z, (∫ x, φ x*F (Finset.univ.filter (fun p => L p.1 y+b p z<x))) ∂μ)
      (∑ i, (∑ k, ∫ z, -(φ (L i y+b (i,k) z)*
        (F (Finset.univ.filter (fun p => L p.1 y+b p z ≤ L i y+b (i,k) z))-
          F (Finset.univ.filter (fun p => L p.1 y+b p z < L i y+b (i,k) z)))) ∂μ) • L i) y := by
  have hd := InterfaceStep.averaged_threshold_derivative Finset.univ (fun p : I × K => L p.1)
    b hb F hφ hc hM0 hC hM hφC μ y (hi.mono (fun z hz => hz.injOn))
  rw [Fintype.sum_prod_type] at hd
  simp only [← Finset.sum_smul] at hd
  exact hd

omit [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] [BorelSpace Z] [DecidableEq K] in

lemma coefficient_budget (μ : Measure Z) [IsProbabilityMeasure μ]
    (w : K → Z → ℝ) (Δ : K → Z → A → ℝ) {J B : ℝ}
    (hJ : 0 ≤ J) (hw : ∀ k z, 0 ≤ w k z)
    (_hiw : ∀ k, Integrable (w k) μ)
    (hid : ∀ k a, Integrable (fun z => w k z*Δ k z a) μ)
    (hj : ∀ᵐ z ∂μ, ∀ k, w k z ≠ 0 → ∑ a, |Δ k z a| ≤ J)
    (hs : ∀ᵐ z ∂μ, ∑ k, w k z ≤ B) :
    (∑ a, |∑ k, ∫ z, -(w k z*Δ k z a) ∂μ|) ≤ J*B := by
  have hle (a : A) : |∑ k, ∫ z, -(w k z*Δ k z a) ∂μ| ≤
      ∑ k, ∫ z, w k z*|Δ k z a| ∂μ := by
    calc
      _ ≤ ∑ k, |∫ z, -(w k z*Δ k z a) ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := Finset.sum_le_sum (fun k _ => by
        simpa only [Real.norm_eq_abs,abs_neg,abs_mul,abs_of_nonneg (hw k _)] using
          norm_integral_le_integral_norm (fun z => -(w k z*Δ k z a)))
  have hia (k : K) (a : A) : Integrable (fun z => w k z*|Δ k z a|) μ := by
    simpa only [abs_mul,abs_of_nonneg (hw k _)] using (hid k a).abs
  have hisum : Integrable (fun z => ∑ k, w k z*(∑ a, |Δ k z a|)) μ := by
    simp_rw [Finset.mul_sum]
    exact integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => hia k a))
  calc
    _ ≤ ∑ a, ∑ k, ∫ z, w k z*|Δ k z a| ∂μ := Finset.sum_le_sum (fun a _ => hle a)
    _ = ∫ z, ∑ k, w k z*(∑ a, |Δ k z a|) ∂μ := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun a _ => hia k a))]
      apply Finset.sum_congr rfl
      intro k _
      exact (integral_finsetSum _ (fun a _ => hia k a)).symm
    _ ≤ ∫ z, J*B ∂μ := by
      apply integral_mono_ae hisum (integrable_const _)
      filter_upwards [hj,hs] with z hz hzB
      calc
        _ ≤ ∑ k, w k z*J := Finset.sum_le_sum (fun k _ => by
          by_cases hk : w k z=0
          · simp [hk]
          · exact mul_le_mul_of_nonneg_left (hz k hk) (hw k z))
        _ = J*∑ k, w k z := by rw [← Finset.sum_mul]; ring
        _ ≤ J*B := mul_le_mul_of_nonneg_left hzB hJ
    _ = J*B := by simp

end UniformSparsestCut.SliceCoefficients

end

end OAI
