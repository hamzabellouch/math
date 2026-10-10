import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.CovarianceLimit
import OAI.GroupTheory.SimpleAmenable.RandomFields.CompactSignalEnergy
import OAI.GroupTheory.SimpleAmenable.RandomFields.FiniteLawDistance

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section SourceFieldHS
open Classical Filter Matrix
open scoped Topology

theorem sourceFlagMatrix_HS_tendsto {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (χ : (ℝ×ℝ) → ℝ)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1) {K L ρ η κ : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hL : 0≤L) (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ)
    (hLip : ∀x y,|χ x-χ y| ≤ L*(|x.1-y.1|+|x.2-y.2|))
    (T : ℕ → Finset (FlagSite a m D v)) :
    Tendsto (fun n => matrixHSNorm (Matrix.of (fun (z w : T n) =>
      sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z.val) (flagSiteAction hD g⁻¹ w.val)-
        sourceFlagMatrix χ ρ η κ n z.val w.val))) atTop (nhds 0) := by
  have hh := (sourceFlagMatrix_covariance hD g⁻¹ χ hχ hK hcompact hL hρ hη hκ hLip
    (fun n => (T n).product (T n))).sqrt
  rw [Real.sqrt_zero] at hh
  convert hh using 1
  funext n
  unfold matrixHSNorm
  congr 1
  change (∑z : T n,∑w : T n,(sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z.val)
    (flagSiteAction hD g⁻¹ w.val)-sourceFlagMatrix χ ρ η κ n z.val w.val)^2)=_
  let f : FlagSite a m D v × FlagSite a m D v → ℝ := fun p =>
    (sourceFlagMatrix χ ρ η κ n p.1 p.2-sourceFlagMatrix χ ρ η κ n
      (flagSiteAction hD g⁻¹ p.1) (flagSiteAction hD g⁻¹ p.2))^2
  symm
  calc
    _ = ∑z∈T n,∑w∈T n,f (z,w) := by
      convert! Finset.sum_product (T n) (T n) f using 1
    _ = ∑z : T n,∑w : T n,f (z.val,w.val) := by
      rw [← Finset.sum_coe_sort (T n)]
      apply Finset.sum_congr rfl
      intro z _
      exact (Finset.sum_coe_sort (T n) _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro w _
      exact sub_sq_comm _ _

end SourceFieldHS

section SmallTransportParameters
open Classical

theorem smallTransportParameters {M C₁ C₂ ε : ℝ} (hM : 0<M)
    (hC₁ : 0≤C₁) (hC₂ : 0≤C₂) (hε : 0<ε) :
    ∃η κ δ d : ℝ,0<η ∧ η≤1 ∧ 0<κ ∧ 0<δ ∧ 0<d ∧
      ∀x y : ℝ,0≤x → x≤d → 0≤y → y≤C₁*η+C₂*Real.sqrt κ+δ →
        M*(x+(1+x)*y)<ε := by
  let t := ε/(8*M*(C₁+C₂+1))
  let d := min 1 (ε/(4*M))
  have ht : 0<t := by dsimp [t]; positivity
  have hd : 0<d := lt_min zero_lt_one (by positivity)
  refine ⟨min 1 t,t^2,t,d,lt_min zero_lt_one ht,min_le_left _ _,sq_pos_of_pos ht,ht,hd,?_⟩
  intro x y hx hxd hy hybound
  have hdx : x≤1 := hxd.trans (min_le_left _ _)
  have hdx' : x≤ε/(4*M) := hxd.trans (min_le_right _ _)
  have hmx : M*x≤ε/4 := by
    have hh := (le_div_iff₀ (show 0<4*M by positivity)).mp hdx'
    linarith
  have ht' : (C₁+C₂+1)*t=ε/(8*M) := by
    dsimp [t]
    field_simp
  have hy' : y≤ε/(8*M) := by
    rw [Real.sqrt_sq ht.le] at hybound
    calc
      y ≤ C₁*min 1 t+C₂*t+t := hybound
      _ ≤ C₁*t+C₂*t+t := by
        have hh := mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) t) hC₁
        linarith
      _ = ε/(8*M) := by rw [← ht']; ring
  have hmy : M*y≤ε/8 := by
    have hh := (le_div_iff₀ (show 0<8*M by positivity)).mp hy'
    linarith
  have hprod : (1+x)*y≤2*y := mul_le_mul_of_nonneg_right (by linarith) hy
  have hf := mul_le_mul_of_nonneg_left hprod hM.le
  nlinarith

end SmallTransportParameters

section FiniteFieldCovariance
open Classical Matrix MeasureTheory

noncomputable def fieldReindex {ι : Type*} (e : ι ≃ ι) (x : ι → ℝ) : ι → ℝ :=
  fun z => x (e.symm z)

theorem fieldReindex_measurable {ι : Type*} (e : ι ≃ ι) : Measurable (fieldReindex e) :=
  Measurable.of_eval (fun z => measurable_pi_apply (e.symm z))

theorem independentSmoothNoiseLaw_reindex {ι : Type*} (e : ι ≃ ι) :
    (independentSmoothNoiseLaw ι).map (fieldReindex e)=independentSmoothNoiseLaw ι := by
  convert! Measure.infinitePi_map_piCongrLeft (fun _ : ι => smoothNoiseLaw) e using 1
  congr 1
  funext x z
  simpa only [Equiv.apply_symm_apply,fieldReindex] using
    (MeasurableEquiv.piCongrLeft_apply_apply (β:=fun _ : ι => ℝ) e x (e.symm z)).symm

theorem finiteCoefficientField_enlarge {ι : Type*} (J T : Finset ι) (hJT : J⊆T)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (hcol : ∀z w,w∉J → B z w=0) :
    finiteCoefficientField T a B=finiteCoefficientField J a B := by
  ext x z
  unfold finiteCoefficientField
  congr 1
  exact (Finset.sum_subset hJT (fun w _ hw => by rw [hcol z w hw,zero_mul])).symm

theorem finiteCoefficientField_covariance {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) (e : ι ≃ ι) :
    ((independentSmoothNoiseLaw ι).map (finiteCoefficientField J a B)).map (fieldReindex e)=
      (independentSmoothNoiseLaw ι).map
        (finiteCoefficientField (J.image e) (fun z => a (e.symm z))
          (fun z w => B (e.symm z) (e.symm w))) := by
  rw [Measure.map_map (fieldReindex_measurable e) (finiteCoefficientField_measurable J a B)]
  have he : fieldReindex e ∘ finiteCoefficientField J a B=
      finiteCoefficientField (J.image e) (fun z => a (e.symm z))
        (fun z w => B (e.symm z) (e.symm w)) ∘ fieldReindex e := by
    ext x z
    simp only [Function.comp_apply,fieldReindex,finiteCoefficientField]
    rw [Finset.sum_image]
    · simp only [Equiv.symm_apply_apply]
    · intro i _ j _ hh
      exact e.injective hh
  rw [he]
  have hh := Measure.map_map
    (finiteCoefficientField_measurable (J.image e) (fun z => a (e.symm z))
      (fun z w => B (e.symm z) (e.symm w))) (fieldReindex_measurable e)
      (μ:=independentSmoothNoiseLaw ι)
  rw [independentSmoothNoiseLaw_reindex] at hh
  exact hh.symm

end FiniteFieldCovariance

section SourceFieldLaw
open Classical Matrix MeasureTheory Filter
open scoped Topology

theorem sourceFlagMatrix_posSemidef {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) {ρ η κ : ℝ} (hρ : 0<ρ) (hκ : 0<κ) (n : ℕ) :
    (Matrix.of (sourceFlagMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ η κ n)).PosSemidef := by
  have hh := (Matrix.posSemidef_sum (sourceDyadicIndices n) (fun i _ =>
    flagAveragingMatrix_posSemidef (a:=a) (m:=m) (D:=D) (v:=v) (η:=η) χ hρ
      (sourceDyadicN_pos n) (show 0<(2:ℝ)^i by positivity) hκ)).smul (sourceDyadicWeight_nonneg n)
  convert! hh using 1
  ext z w
  simp only [Matrix.of_apply,sourceFlagMatrix,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]

theorem sourceFlagMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (hχc : ∀x,L≤‖x‖ → χ x=0)
    (ρ η κ : ℝ) (n : ℕ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL) ∨
      w∉flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)) :
    sourceFlagMatrix χ ρ η κ n z w=0 := by
  unfold sourceFlagMatrix
  suffices (∑i∈sourceDyadicIndices n,flagAveragingMatrix χ ρ (sourceDyadicN n) ((2:ℝ)^i) η κ z w)=0 by rw [this,mul_zero]
  apply Finset.sum_eq_zero
  intro i _
  exact flagAveragingMatrix_box_support hD χ hL (sourceDyadicN_pos n) hχc _ _ _ _ z w hz

noncomputable def sourceSmoothFieldLaw {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    Measure (FlagSite a m D v → ℝ) :=
  (independentSmoothNoiseLaw (FlagSite a m D v)).map
    (finiteCoefficientField (flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL))
      (flagMeanSignal θ (sourceDyadicN n)) (Matrix.of (sourceFlagMatrix χ ρ η κ n)))

instance sourceSmoothFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceSmoothFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceSmoothFieldLaw
  infer_instance

noncomputable def sourceCommonSites {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {L : ℝ} (hL : 0<L) (n : ℕ) : Finset (FlagSite a m D v) :=
  let J := flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)
  J ∪ J.image (flagSitePermutation hD g)

theorem sourceSmoothFieldLaw_as_common {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ) :
    sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n=
      (independentSmoothNoiseLaw (FlagSite a m D v)).map
        (finiteCoefficientField (sourceCommonSites hD g hL n)
          (flagMeanSignal θ (sourceDyadicN n)) (Matrix.of (sourceFlagMatrix χ ρ η κ n))) := by
  unfold sourceSmoothFieldLaw
  congr 1
  symm
  apply finiteCoefficientField_enlarge
  · exact Finset.subset_union_left
  · intro z w hw
    exact sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n z w (Or.inr hw)

theorem sourceSmoothFieldLaw_transported {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L)
    (hχc : ∀x,L≤‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ) :
    (sourceSmoothFieldLaw (v:=v) hD θ χ hL ρ η κ n).map (fieldReindex (flagSitePermutation hD g))=
      (independentSmoothNoiseLaw (FlagSite a m D v)).map
        (finiteCoefficientField (sourceCommonSites hD g hL n)
          (fun z => flagMeanSignal θ (sourceDyadicN n) (flagSiteAction hD g⁻¹ z))
          (Matrix.of (fun z w => sourceFlagMatrix χ ρ η κ n (flagSiteAction hD g⁻¹ z) (flagSiteAction hD g⁻¹ w)))) := by
  unfold sourceSmoothFieldLaw
  rw [finiteCoefficientField_covariance]
  congr 1
  symm
  apply finiteCoefficientField_enlarge
  · exact Finset.subset_union_right
  · intro z w hw
    apply sourceFlagMatrix_box_support hD χ hL hχc ρ η κ n _ _
    right
    intro hm
    apply hw
    exact Finset.mem_image.mpr ⟨(flagSitePermutation hD g).symm w,hm,
      (flagSitePermutation hD g).apply_symm_apply w⟩

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
