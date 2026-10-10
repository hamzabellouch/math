import Mathlib
import OAI.Analysis.FreeWords.UltraTrace

namespace OAI

noncomputable section

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

attribute [local instance] KKUltraTrace.seqOrder

attribute [local instance] KKUltraTrace.seqSOR

open scoped InnerProductSpace

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def clipFunction (b u : ℝ) : ℝ := b / max b u

def spectralClip (b : ℝ) (x : A) : A :=
  x * cfc (clipFunction b) (CFC.sqrt (star x * x))

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

theorem clipFunction_zero {b : ℝ} (hb : 0 < b) : clipFunction b 0 = 1 := by
  simp [clipFunction, max_eq_left hb.le, ne_of_gt hb]

theorem clipFunction_pos {b u : ℝ} (hb : 0 < b) (hu : 0 < u) :
    clipFunction b u = min 1 (b/u) := by
  by_cases h : u ≤ b
  · rw [clipFunction, max_eq_left h, div_self (ne_of_gt hb), min_eq_left]
    exact (le_div_iff₀ hu).mpr (by simpa using h)
  · have h' : b ≤ u := le_of_lt (lt_of_not_ge h)
    rw [clipFunction, max_eq_right h', min_eq_right]
    exact (div_le_one hu).mpr h'

theorem continuous_clipFunction {b : ℝ} (hb : 0 < b) : Continuous (clipFunction b) := by
  unfold clipFunction
  exact continuous_const.div (continuous_const.max continuous_id)
    (fun u => ne_of_gt (lt_of_lt_of_le hb (le_max_left b u)))

def clipWeight (b t : ℝ) : ℝ := clipFunction b (Real.sqrt t)

theorem continuous_clipWeight {b : ℝ} (hb : 0 < b) : Continuous (clipWeight b) :=
  (continuous_clipFunction hb).comp Real.continuous_sqrt

theorem clipWeight_bounds {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    0 ≤ clipWeight b t ∧ clipWeight b t ≤ 1 ∧
    t * (clipWeight b t)^2 ≤ b^2 ∧ t * (clipWeight b t)^2 ≤ t ∧
    t * (1-clipWeight b t)^2 ≤ t := by
  have hmax : 0 < max b (Real.sqrt t) := lt_of_lt_of_le hb (le_max_left _ _)
  have hw0 : 0 ≤ clipWeight b t := div_nonneg hb.le hmax.le
  have hw1 : clipWeight b t ≤ 1 := (div_le_one hmax).mpr (le_max_left _ _)
  have hu := Real.sqrt_nonneg t
  have hu2 := Real.sq_sqrt ht
  have hprod : Real.sqrt t * clipWeight b t ≤ b := by
    dsimp [clipWeight,clipFunction]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hmax).mpr
    nlinarith [mul_le_mul_of_nonneg_left (le_max_right b (Real.sqrt t)) hb.le]
  have hsq : (Real.sqrt t * clipWeight b t)^2 ≤ b^2 :=
    pow_le_pow_left₀ (mul_nonneg hu hw0) hprod 2
  rw [mul_pow,hu2] at hsq
  have hw2 : (clipWeight b t)^2 ≤ 1 := by nlinarith
  have he2 : (1-clipWeight b t)^2 ≤ 1 := by nlinarith
  exact ⟨hw0,hw1,hsq,by simpa using mul_le_mul_of_nonneg_left hw2 ht,
    by simpa using mul_le_mul_of_nonneg_left he2 ht⟩

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem spectralClip_eq {b : ℝ} (hb : 0 < b) (x : A) :
    spectralClip b x = x*cfc (clipWeight b) (star x*x) := by
  unfold spectralClip
  rw [CFC.sqrt_eq_real_sqrt _ (star_mul_self_nonneg _),cfcₙ_eq_cfc]
  congr 1
  exact (cfc_comp (clipFunction b) Real.sqrt (star x*x)
    (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _))
    (continuous_clipFunction hb).continuousOn Real.continuous_sqrt.continuousOn).symm

theorem weighted_square (x : A) (w : ℝ → ℝ) (hw : Continuous w) :
    star (x*cfc w (star x*x)) * (x*cfc w (star x*x)) =
      cfc (fun t => t*(w t)^2) (star x*x) := by
  have hs : IsSelfAdjoint (star x*x) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have hc : Commute (cfc w (star x*x)) (star x*x) :=
    (Commute.refl _).cfc (by simpa only [hs.star_eq] using Commute.refl (star x*x)) w
  rw [star_mul, IsSelfAdjoint.cfc.star_eq]
  calc
    (cfc w (star x*x)*star x)*(x*cfc w (star x*x)) =
      (star x*x)*(cfc w (star x*x)*cfc w (star x*x)) := by
      calc
        _ = (cfc w (star x*x)*(star x*x))*cfc w (star x*x) := by noncomm_ring
        _ = _ := by rw [hc.eq,mul_assoc]
    _ = cfc (fun t => t*(w t)^2) (star x*x) := by
      rw [cfc_mul (fun t : ℝ => t) (fun t => (w t)^2) _ continuousOn_id
        (hw.pow 2).continuousOn,cfc_id' ℝ _ hs,cfc_pow w 2 _ hw.continuousOn,pow_two]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem spectralClip_square {b : ℝ} (hb : 0 < b) (x : A) :
    star (spectralClip b x)*spectralClip b x =
      cfc (fun t => t*(clipWeight b t)^2) (star x*x) := by
  rw [spectralClip_eq hb, weighted_square x _ (continuous_clipWeight hb)]

theorem spectralClip_error_square {b : ℝ} (hb : 0 < b) (x : A) :
    star (x-spectralClip b x)*(x-spectralClip b x) =
      cfc (fun t => t*(1-clipWeight b t)^2) (star x*x) := by
  have hs : IsSelfAdjoint (star x*x) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have he : x-spectralClip b x = x*cfc (fun t => 1-clipWeight b t) (star x*x) := by
    rw [spectralClip_eq hb,cfc_sub (fun _ : ℝ => 1) (clipWeight b) _ continuousOn_const
      (continuous_clipWeight hb).continuousOn,cfc_const (1:ℝ) _ hs,map_one,mul_sub,mul_one]
  rw [he]
  exact weighted_square x (fun t => 1-clipWeight b t) (continuous_const.sub (continuous_clipWeight hb))

theorem norm_spectralClip_le {b : ℝ} (hb : 0 < b) (x : A) : ‖spectralClip b x‖ ≤ b := by
  have h : ‖star (spectralClip b x)*spectralClip b x‖ ≤ b^2 := by
    rw [spectralClip_square hb]
    apply norm_cfc_le (sq_nonneg b)
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg ht0 (sq_nonneg _))]
    exact (clipWeight_bounds hb ht0).2.2.1
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg (spectralClip b x)]

theorem spectralClip_square_le {b : ℝ} (hb : 0 < b) (x : A) :
    star (spectralClip b x)*spectralClip b x ≤ star x*x := by
  rw [spectralClip_square hb]
  conv_rhs => rw [← cfc_id' ℝ (star x*x) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _))]
  apply (cfc_le_iff _ _ _ ((continuous_id.mul ((continuous_clipWeight hb).pow 2)).continuousOn)
    continuousOn_id).mpr
  intro t ht
  exact (clipWeight_bounds hb (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)).2.2.2.1

theorem spectralClip_error_square_le {b : ℝ} (hb : 0 < b) (x : A) :
    star (x-spectralClip b x)*(x-spectralClip b x) ≤ star x*x := by
  rw [spectralClip_error_square hb]
  conv_rhs => rw [← cfc_id' ℝ (star x*x) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _))]
  apply (cfc_le_iff (fun t => t*(1-clipWeight b t)^2) (fun t => t) (star x*x) ((continuous_id.mul ((continuous_const.sub (continuous_clipWeight hb)).pow 2)).continuousOn)
    continuousOn_id).mpr
  intro t ht
  exact (clipWeight_bounds hb (spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht)).2.2.2.2

theorem spectralClip_right_support {b : ℝ} (hb : 0 < b) (x p : A)
    (hp : IsStarProjection p) (hxp : x*p=x) : spectralClip b x*p = spectralClip b x := by
  have hs : IsSelfAdjoint (star x*x) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have hsp : (star x*x)*p = star x*x := by rw [mul_assoc,hxp]
  have hps : p*(star x*x) = star x*x := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq,hs.star_eq] using congrArg star hsp
  have hc : Commute (cfc (clipWeight b) (star x*x)) p :=
    (show Commute (star x*x) p from hsp.trans hps.symm).cfc
      (by simpa only [hs.star_eq] using (show Commute (star x*x) p from hsp.trans hps.symm))
      (clipWeight b)
  rw [spectralClip_eq hb,mul_assoc,hc.eq,← mul_assoc,hxp]

theorem spectralClip_eq_self {b : ℝ} (hb : 0 < b) (x : A) (hx : ‖x‖ ≤ b) :
    spectralClip b x = x := by
  nontriviality A
  have hs : IsSelfAdjoint (star x*x) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have hw : (spectrum ℝ (star x*x)).EqOn (clipWeight b) (fun _ => 1) := by
    intro t ht
    have ht0 := spectrum_nonneg_of_nonneg (star_mul_self_nonneg x) ht
    have htn : t ≤ ‖x‖^2 := by
      have hn := spectrum.norm_le_norm_of_mem ht
      simpa only [Real.norm_eq_abs,abs_of_nonneg ht0,CStarRing.norm_star_mul_self,pow_two] using hn
    have hsqrt : Real.sqrt t ≤ b :=
      ((Real.sqrt_le_iff).mpr ⟨norm_nonneg x,htn⟩).trans hx
    simp only [clipWeight,clipFunction,max_eq_left hsqrt,div_self (ne_of_gt hb)]
  rw [spectralClip_eq hb,cfc_congr hw,cfc_const (1:ℝ) _ hs,map_one,mul_one]

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem map_spectralClip (φ : A →⋆ₐ[ℂ] B) {b : ℝ} (hb : 0 < b) (x : A) :
    φ (spectralClip b x) = spectralClip b (φ x) := by
  have hs : IsSelfAdjoint (star x*x) := IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _)
  have hm := φ.map_cfc (clipWeight b) (star x*x) (continuous_clipWeight hb).continuousOn
    (by fun_prop) hs (hs.map φ)
  rw [spectralClip_eq hb,spectralClip_eq hb,map_mul,hm,map_mul,map_star]

end

end KKUltraTrace

namespace KKUltraTrace

open scoped ComplexOrder BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

@[instance_reducible] def _seqOrder : PartialOrder (ℕ →ᵇ A) := CStarAlgebra.spectralOrder _

attribute [local instance] KKUltraTrace._seqOrder

omit [PartialOrder A] [StarOrderedRing A] in
theorem _seqSOR : StarOrderedRing (ℕ →ᵇ A) := CStarAlgebra.spectralOrderedRing _

attribute [local instance] KKUltraTrace._seqSOR

def sequenceEval (j : ℕ) : (ℕ →ᵇ A) →⋆ₐ[ℂ] A where
  toFun x := x j
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem sequenceEval_apply (j : ℕ) (x : ℕ →ᵇ A) : sequenceEval j x = x j := rfl

@[simp] theorem spectralClip_apply {b : ℝ} (hb : 0 < b) (x : ℕ →ᵇ A) (j : ℕ) :
    spectralClip b x j = spectralClip b (x j) :=
  map_spectralClip (sequenceEval j) hb x

theorem spectral_clipping_transfer (τ : A →ₚ[ℂ] ℂ) (_ : τ 1 = 1)
    (htr : ∀ x y : A, τ (x*y) = τ (y*x)) (ω : Ultrafilter ℕ)
    (x : ℕ →ᵇ A) {b : ℝ} (hb : 0 < b)
    (hn : ‖(ultraTrace τ ω).gnsStarAlgHom x‖ ≤ b) :
    (∀ j, ‖spectralClip b (x j)‖ ≤ b ∧
      star (spectralClip b (x j)) * spectralClip b (x j) ≤ star (x j) * x j ∧
      star (x j-spectralClip b (x j)) * (x j-spectralClip b (x j)) ≤ star (x j)*x j) ∧
    (∀ j (p : A), IsStarProjection p → x j * p = x j →
      spectralClip b (x j) * p = spectralClip b (x j)) ∧
    Tendsto (fun j => Real.sqrt (τ (star (x j-spectralClip b (x j)) *
        (x j-spectralClip b (x j)))).re) (ω : Filter ℕ) (𝓝 0) := by
  refine ⟨fun j => ⟨norm_spectralClip_le hb _, spectralClip_square_le hb _,
    spectralClip_error_square_le hb _⟩, ?_, ?_⟩
  · exact fun j p hp hxp => spectralClip_right_support hb _ _ hp hxp
  · let e : ℕ →ᵇ A := x - spectralClip b x
    have hz : (ultraTrace τ ω).gnsStarAlgHom e = 0 := by
      dsimp [e]
      rw [map_sub, map_spectralClip _ hb, spectralClip_eq_self hb _ hn, sub_self]
    have ht : ultraTrace τ ω (star e * e) = 0 :=
      (tracial_gns_zero _ (ultraTrace_tracial τ ω htr) e).mp hz
    have hl := Complex.continuous_re.continuousAt.tendsto.comp (tendsto_ultraTraceValue τ ω (star e * e))
    change Tendsto (fun j => (τ ((star e * e) j)).re) (ω : Filter ℕ)
      (𝓝 (ultraTrace τ ω (star e * e)).re) at hl
    rw [ht, Complex.zero_re] at hl
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hl
    simpa [e, spectralClip_apply hb, Function.comp_def] using hs

end

end KKUltraTrace
end

end OAI
