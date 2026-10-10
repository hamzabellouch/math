import Mathlib
import OAI.Geometry.Cannon.Conformal.SphereMeasure
import OAI.Geometry.Cannon.Conformal.WeakQSPartialsLocally

namespace OAI

section
section
section
section
section
section
section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter
open scoped Topology

noncomputable section
noncomputable section
noncomputable section
noncomputable section
open Set Metric MeasureTheory Filter Complex
open scoped Topology

noncomputable section
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

namespace CannonBeltrami
open MeasureTheory Set Metric Filter
open scoped Topology ENNReal

lemma ae_eq_on_of_schwartz_mul {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hh : ∀ φ : SchwartzMap ℂ ℂ, HasCompactSupport (φ : ℂ → ℂ) →
      tsupport (φ : ℂ → ℂ) ⊆ U → (∫ z, f z*φ z)=(∫ z, g z*φ z)) :
    ∀ᵐ z : ℂ, z ∈ U → f z=g z := by
  have hz : ∀ᵐ z : ℂ, z ∈ U → f z-g z=0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hf.sub hg).locallyIntegrableOn U)
    intro φ hφ hc hs
    let ψ : ℂ → ℂ := fun z => (φ z : ℂ)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hφ
    have hcψ : HasCompactSupport ψ := hc.comp_left Complex.ofReal_zero
    let t : SchwartzMap ℂ ℂ := hcψ.toSchwartzMap hψ
    have htU : tsupport (t : ℂ → ℂ) ⊆ U :=
      (tsupport_comp_subset Complex.ofReal_zero φ).trans hs
    have he := hh t hcψ htU
    have hfφ : Integrable (fun z => f z*t z) := by
      simpa only [smul_eq_mul] using hf.integrable_smul_right_of_hasCompactSupport t.continuous hcψ
    have hgφ : Integrable (fun z => g z*t z) := by
      simpa only [smul_eq_mul] using hg.integrable_smul_right_of_hasCompactSupport t.continuous hcψ
    have hid : (fun z => φ z • (f z-g z))=(fun z => f z*t z-g z*t z) := by
      funext z
      change (φ z : ℂ)*(f z-g z)=f z*(φ z : ℂ)-g z*(φ z : ℂ)
      ring
    change (∫ z, φ z • (f z-g z))=0
    rw [hid,integral_sub hfφ hgφ,he,sub_self]
  filter_upwards [hz] with z hz hzu
  exact sub_eq_zero.mp (hz hzu)

theorem metric_weak_beltrami_classical (F : ℂ ≃ₜ ℂ) {H : ℝ}
    (hH : 0 < H) (hF : CannonMetricQC.WeakQS F H)
    (μ : ℂ → ℂ) (hm : AEStronglyMeasurable μ volume) {k : ℝ} (hk : 0 ≤ k)
    (hb : ∀ z, ‖μ z‖ ≤ k)
    (hw : ∀ S : Set ℂ, IsCompact S → ∃ a : Lp ℂ 2 (volume.restrict S),
      ∀ φ : SchwartzMap ℂ ℂ, tsupport (φ : ℂ → ℂ) ⊆ S →
        (∫ z, F z*partialZ φ z)=-(∫ z in S, a z*φ z) ∧
        (∫ z, F z*partialBar φ z)=-(∫ z in S, a z*(μ z*φ z))) :
    ∀ᵐ z : ℂ, partialBar F z=μ z*partialZ F z := by
  have hl := CannonMetricQC.weakQS_partials_locallyIntegrable F hH hF
  have he (R : ℝ) : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R →
      partialBar F z=μ z*partialZ F z := by
    let S := closedBall (0:ℂ) R
    have hS : IsCompact S := isCompact_closedBall _ _
    let : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hS.measure_lt_top (μ:=volume)⟩
    obtain ⟨a,ha⟩ := hw S hS
    let A : ℂ → ℂ := S.indicator (fun z => a z)
    have hia : Integrable A := (integrable_indicator_iff hS.measurableSet).mpr
      (MemLp.integrable (by norm_num) (Lp.memLp a))
    have him : Integrable (fun z => μ z*A z) :=
      hia.bdd_mul (c := ‖k‖) hm (.of_forall fun point => by
        simpa only [Real.norm_of_nonneg hk] using hb point)
    have hid (φ : SchwartzMap ℂ ℂ) : (∫ z, A z*φ z)=(∫ z in S, a z*φ z) := by
      have heq : (fun z => A z*φ z)=S.indicator (fun z => a z*φ z) := by
        funext z; by_cases hz : z ∈ S <;> simp [A,hz]
      rw [heq,integral_indicator hS.measurableSet]
    have hidm (φ : SchwartzMap ℂ ℂ) :
        (∫ z, (μ z*A z)*φ z)=(∫ z in S, a z*(μ z*φ z)) := by
      calc
        _ = ∫ z, A z*(μ z*φ z) := by congr 1; funext z; ring
        _ = _ := by
          have heq : (fun z => A z*(μ z*φ z))=S.indicator (fun z => a z*(μ z*φ z)) := by
            funext z; by_cases hz : z ∈ S <;> simp [A,hz]
          rw [heq,integral_indicator hS.measurableSet]
    have hza : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R → partialZ F z=A z := by
      apply ae_eq_on_of_schwartz_mul isOpen_ball hl.1 hia.locallyIntegrable
      intro φ hc ht
      have hh := ha φ (ht.trans ball_subset_closedBall)
      rw [← hid φ] at hh
      have hparts := CannonMetricQC.weakQS_partial_integration_by_parts F hH hF φ hc
      exact neg_injective (hparts.1.symm.trans hh.1)
    have hba : ∀ᵐ z : ℂ, z ∈ ball (0:ℂ) R → partialBar F z=μ z*A z := by
      apply ae_eq_on_of_schwartz_mul isOpen_ball hl.2 him.locallyIntegrable
      intro φ hc ht
      have hh := ha φ (ht.trans ball_subset_closedBall)
      rw [← hidm φ] at hh
      have hparts := CannonMetricQC.weakQS_partial_integration_by_parts F hH hF φ hc
      exact neg_injective (hparts.2.symm.trans hh.2)
    filter_upwards [hza,hba] with z hz hbz hzR
    rw [hbz hzR,hz hzR]
  have hall : ∀ᵐ z : ℂ, ∀ n : ℕ, z ∈ ball (0:ℂ) (n+1) →
      partialBar F z=μ z*partialZ F z := ae_all_iff.mpr (fun n => he (n+1))
  filter_upwards [hall] with z hz
  obtain ⟨n,hn⟩ := exists_nat_gt ‖z‖
  exact hz n (by simpa only [mem_ball,dist_zero_right] using (show ‖z‖ < (n:ℝ)+1 by linarith))
end CannonBeltrami

end
end
end
end
end
end
end
end
end
end
section
noncomputable section
namespace CannonConformal
open Set Topology Metric

def beltrami (q : Form) : ℂ :=
  (⟨q 0-q 2,2*q 1⟩ : ℂ) / ((q 0+q 2+2*Real.sqrt (determinant q) : ℝ) : ℂ)

lemma measurable_beltrami : Measurable beltrami := by
  have hd : Continuous determinant := by unfold determinant; fun_prop
  have hn : Continuous (fun q : Form => (⟨q 0-q 2,2*q 1⟩ : ℂ)) := by
    have H : Continuous (fun q : Form => ((q 0-q 2 : ℝ) : ℂ)+((2*q 1 : ℝ) : ℂ)*Complex.I) := by
      fun_prop
    convert H using 1
    ext q
    apply Complex.ext <;> simp
  have hh : Continuous (fun q : Form => ((q 0+q 2+2*Real.sqrt (determinant q) : ℝ) : ℂ)) := by
    fun_prop
  exact hn.measurable.div hh.measurable

lemma beltrami_uniform_bound {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    {q : Form} (hl : LowerBound ε q) (hu : UpperBound K q) :
    ‖beltrami q‖ ≤ Real.sqrt (1-ε/K) ∧ Real.sqrt (1-ε/K) < 1 := by
  have h0l : ε ≤ q 0 := by simpa [evaluate] using hl 1 0
  have h2l : ε ≤ q 2 := by simpa [evaluate] using hl 0 1
  have h0u : q 0 ≤ K := by simpa [evaluate] using hu 1 0
  have h2u : q 2 ≤ K := by simpa [evaluate] using hu 0 1
  have hεK : ε ≤ K := h0l.trans h0u
  have hd := determinant_ge_sq_lower hε.le hl
  have hd0 : 0 ≤ determinant q := (sq_nonneg ε).trans hd
  have hs : 0 ≤ Real.sqrt (determinant q) := Real.sqrt_nonneg _
  have hss : (Real.sqrt (determinant q))^2=determinant q := Real.sq_sqrt hd0
  have hsl : ε ≤ Real.sqrt (determinant q) := by nlinarith
  have hdu : determinant q ≤ K^2 := by
    have hm := mul_le_mul h0u h2u (hε.le.trans h2l) hK.le
    dsimp [determinant] at *
    nlinarith [sq_nonneg (q 1)]
  have hsu : Real.sqrt (determinant q) ≤ K := by nlinarith
  let d := q 0+q 2+2*Real.sqrt (determinant q)
  have hdp : 0 < d := by dsimp [d]; linarith
  have hdu' : d ≤ 4*K := by dsimp [d]; linarith
  have hnid : (q 0-q 2)^2+(2*q 1)^2=d^2-4*Real.sqrt (determinant q)*d := by
    dsimp [d]
    have hss' : (Real.sqrt (determinant q))^2=q 0*q 2-(q 1)^2 := hss
    nlinarith only [hss']
  have hnorm : ‖beltrami q‖^2=((q 0-q 2)^2+(2*q 1)^2)/d^2 := by
    rw [beltrami,norm_div,div_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,d,pow_two]
  have hratio : ε/K ≤ 4*Real.sqrt (determinant q)/d := by
    apply (div_le_div_iff₀ hK hdp).mpr
    nlinarith [mul_le_mul_of_nonneg_left hdu' hε.le]
  have hnormle : ‖beltrami q‖^2 ≤ 1-ε/K := by
    rw [hnorm,hnid]
    have he : (d^2-4*Real.sqrt (determinant q)*d)/d^2=
        1-4*Real.sqrt (determinant q)/d := by field_simp
    rw [he]
    linarith
  have hr0 : 0 ≤ 1-ε/K := by rw [sub_nonneg]; exact (div_le_one hK).mpr hεK
  constructor
  · have hh := Real.sq_sqrt hr0
    have hs' := Real.sqrt_nonneg (1-ε/K)
    nlinarith [norm_nonneg (beltrami q)]
  · have hr : 1-ε/K < 1 := by linarith [div_pos hε hK]
    have hh := Real.sq_sqrt hr0
    have hs' := Real.sqrt_nonneg (1-ε/K)
    nlinarith

def coefficientForm (μ : ℂ) : Form :=
  ![(1+μ.re)^2+μ.im^2,2*μ.im,(1-μ.re)^2+μ.im^2]

lemma evaluate_coefficientForm (μ : ℂ) (x y : ℝ) :
    evaluate (coefficientForm μ) x y=
      Complex.normSq ((⟨x,y⟩ : ℂ)+μ*star (⟨x,y⟩ : ℂ)) := by
  simp [evaluate,coefficientForm,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

lemma coefficient_reconstruction {q : Form} (hq : Positive q) :
    q=((q 0+q 2+2*Real.sqrt (determinant q))/4) • coefficientForm (beltrami q) := by
  have hc : 0 < q 2 := by
    have h := hq.2
    have ha := hq.1
    dsimp [determinant] at h
    nlinarith [sq_nonneg (q 1)]
  have hd : 0 < q 0+q 2+2*Real.sqrt (determinant q) := by
    linarith [Real.sqrt_nonneg (determinant q),hq.1]
  have hs : Real.sqrt (determinant q)^2=q 0*q 2-(q 1)^2 := Real.sq_sqrt hq.2.le
  have hr : (beltrami q).re=(q 0-q 2)/(q 0+q 2+2*Real.sqrt (determinant q)) := by
    simp only [beltrami,Complex.div_ofReal_re]
  have hi : (beltrami q).im=2*q 1/(q 0+q 2+2*Real.sqrt (determinant q)) := by
    simp only [beltrami,Complex.div_ofReal_im]
  ext i
  fin_cases i
  · change q 0=((q 0+q 2+2*Real.sqrt (determinant q))/4)*
      ((1+(beltrami q).re)^2+(beltrami q).im^2)
    rw [hr,hi]
    field_simp
    nlinarith only [hs]
  · change q 1=((q 0+q 2+2*Real.sqrt (determinant q))/4)*(2*(beltrami q).im)
    rw [hi]
    field_simp
    ring
  · change q 2=((q 0+q 2+2*Real.sqrt (determinant q))/4)*
      ((1-(beltrami q).re)^2+(beltrami q).im^2)
    rw [hr,hi]
    field_simp
    nlinarith only [hs]

end CannonConformal

end
end
end
end
end
end
end
end

end OAI
