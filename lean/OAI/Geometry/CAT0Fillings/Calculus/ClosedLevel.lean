import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Gradient.Multiplier
import OAI.Geometry.CAT0Fillings.Calculus.ClosedChain

namespace OAI

section

open Set Filter
open scoped Topology NNReal

namespace CAT0Fillings.ClosedCalculus

noncomputable def levelApprox (a ε t : ℝ) := ε*Real.arctan ((t-a)/ε)
noncomputable def levelApproxDeriv (a ε t : ℝ) := ε^2/(ε^2+(t-a)^2)

lemma levelApprox_hasDerivAt {ε : ℝ} (hε : 0 < ε) (a t : ℝ) :
    HasDerivAt (levelApprox a ε) (levelApproxDeriv a ε t) t := by
  have hd := ((((hasDerivAt_id t).sub_const a).div_const ε).arctan).const_mul ε
  convert hd using 1 <;> try rfl
  dsimp [levelApproxDeriv]
  field_simp [hε.ne']

lemma levelApproxDeriv_bound {ε : ℝ} (hε : 0 < ε) (a t : ℝ) : |levelApproxDeriv a ε t| ≤ 1 := by
  have hp := add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg (t-a))
  dsimp [levelApproxDeriv]
  rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hp.le)]
  exact (div_le_one hp).mpr (le_add_of_nonneg_right (sq_nonneg _))

lemma levelApprox_lipschitz {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    LipschitzWith 1 (levelApprox a ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun t => (levelApprox_hasDerivAt hε a t).differentiableAt)
  intro t
  rw [←NNReal.coe_le_coe,coe_nnnorm,NNReal.coe_one,(levelApprox_hasDerivAt hε a t).deriv,Real.norm_eq_abs]
  exact levelApproxDeriv_bound hε a t

lemma continuous_levelApproxDeriv {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Continuous (levelApproxDeriv a ε) := by
  change Continuous (fun t : ℝ => ε^2/(ε^2+(t-a)^2))
  exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
    (fun t => (add_pos_of_pos_of_nonneg (sq_pos_of_pos hε) (sq_nonneg (t-a))).ne')

lemma levelApprox_error {ε : ℝ} (hε : 0 ≤ ε) (a t : ℝ) :
    |levelApprox a ε t| ≤ ε*(Real.pi/2) := by
  dsimp [levelApprox]
  rw [abs_mul,abs_of_nonneg hε]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr
    ⟨(Real.neg_pi_div_two_lt_arctan _).le,(Real.arctan_lt_pi_div_two _).le⟩) hε

lemma levelApproxDeriv_tendsto {e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (hep : ∀ j, 0 < e j) (a t : ℝ) :
    Tendsto (fun j => levelApproxDeriv a (e j) t) atTop (𝓝 (if t = a then 1 else 0)) := by
  by_cases ht : t = a
  · subst t
    simp only [levelApproxDeriv,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero,
      div_self (pow_ne_zero 2 (hep _).ne'),ite_true]
    exact tendsto_const_nhds
  · rw [ite_eq_right ht]
    have hta : t-a ≠ 0 := sub_ne_zero.mpr ht
    have hh := (he.pow 2).div ((he.pow 2).add_const ((t-a)^2))
      (by simpa using pow_ne_zero 2 hta)
    convert hh using 1 <;> simp only [levelApproxDeriv,zero_pow (by decide : 2 ≠ 0),zero_add,zero_div]
    rfl

end CAT0Fillings.ClosedCalculus
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closed_chain_uniform {F D : ℝ → ℝ} {J : ℝ≥0} (hF : LipschitzWith J F)
    (hD : Measurable D) {C : ℝ} (hC : 0 ≤ C) (hbD : ∀ t, |D t| ≤ C)
    (Fj Dj : ℕ → ℝ → ℝ) (K : ℕ → ℝ≥0)
    (hFj : ∀ j, LipschitzWith (K j) (Fj j))
    (hdj : ∀ j t, HasDerivAt (Fj j) (Dj j t) t)
    (hcj : ∀ j, Continuous (Dj j)) (hbj : ∀ j t, |Dj j t| ≤ C)
    (hdlim : ∀ t, Tendsto (fun j => Dj j t) atTop (𝓝 (D t)))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (he : ∀ j t, |Fj j t-F t| ≤ a j) (P : q.Sobolev) :
    ∃ Q : q.Sobolev,
      (q.inclusion Q : X → ℝ) =ᵐ[MassMeasure.currentMassMeasure hT]
        (fun x => F ((q.inclusion P) x)) ∧
      (q.closedGradient Q : (ℕ × Euc (k+1)) → Euc (k+1)) =ᵐ[q.atlasMeasure]
        (fun w => D ((q.inclusion P) (q.atlasParam w)) • (q.closedGradient P) w) := by
  choose Q hQ hG using (fun j => q.closed_chain (hFj j) (hdj j) (hcj j) hC (hbj j) P)
  let b (j : ℕ) (w : ℕ × Euc (k+1)) := Dj j ((q.inclusion P) (q.atlasParam w))
  let c (w : ℕ × Euc (k+1)) := D ((q.inclusion P) (q.atlasParam w))
  have hpm := (Lp.aestronglyMeasurable (q.inclusion P)).comp_measurePreserving q.atlas_preserving
  have hb (j : ℕ) : AEStronglyMeasurable (b j) q.atlasMeasure := (hcj j).comp_aestronglyMeasurable hpm
  have hc : AEStronglyMeasurable c q.atlasMeasure := (hD.comp_aemeasurable hpm.aemeasurable).aestronglyMeasurable
  have hbC (j : ℕ) : ∀ᵐ w ∂q.atlasMeasure, |b j w| ≤ C := Eventually.of_forall fun _ => hbj j _
  have hcC : ∀ᵐ w ∂q.atlasMeasure, |c w| ≤ C := Eventually.of_forall fun _ => hbD _
  have hgl := ClosedCalculus.mulLp_tendsto hb hc hC hbC hcC
    (Eventually.of_forall fun point => hdlim ((q.inclusion P) (q.atlasParam point)))
    (tendsto_const_nhds (x := q.closedGradient P))
  have heG (j : ℕ) : ClosedCalculus.mulLp (hb j) (hbC j) (q.closedGradient P) = q.closedGradient (Q j) := by
    apply Lp.ext
    exact (ClosedCalculus.mulLp_ae (hb j) (hbC j) _).trans (hG j).symm
  simp only [heG] at hgl
  let V := q.composeValue hF (q.inclusion P)
  have hv : Tendsto (fun j => q.inclusion (Q j)) atTop (𝓝 V) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (g := fun j => a j*‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖)
    · intro j
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (q.inclusion (Q j)) V,hQ j,q.composeValue_ae hF (q.inclusion P),
        ((Foundations.boundedLip_of_lipschitz (LipschitzWith.const (1:ℝ))).memLp
          (μ := MassMeasure.currentMassMeasure hT) 2).coeFn_toLp] with x hs hq hv h1
      change (value (hT := hT) (LipschitzWith.const (1:ℝ)) : X → ℝ) x = 1 at h1
      rw [hs,Pi.sub_apply,hq,hv,h1,Real.norm_eq_abs,norm_one,mul_one]
      exact he j _
    · simpa only [zero_mul] using ha.mul_const ‖value (hT := hT) (LipschitzWith.const (1:ℝ))‖
  obtain ⟨R,hR,hRG⟩ := q.closedGradient_closed V (ClosedCalculus.mulLp hc hcC (q.closedGradient P)) Q hv hgl
  refine ⟨R,?_,?_⟩
  · rw [hR]
    exact q.composeValue_ae hF (q.inclusion P)
  · rw [hRG]
    exact ClosedCalculus.mulLp_ae hc hcC _

end CAT0Fillings.ChartGeometry
end

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
open ClosedCalculus

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma closedGradient_level_zero (hz : IsCycle T) (P : q.Sobolev) (a : ℝ) :
    ∀ᵐ w ∂q.atlasMeasure, (q.inclusion P) (q.atlasParam w) = a →
      (q.closedGradient P) w = 0 := by
  let e (j : ℕ) : ℝ := 1/((j:ℝ)+1)
  have hep (j : ℕ) : 0 < e j := by dsimp [e]; positivity
  have he : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hD : Measurable (fun t : ℝ => if t = a then (1:ℝ) else 0) := by
    convert (show Measurable (({a} : Set ℝ).indicator (fun _ : ℝ => (1:ℝ))) from
      measurable_const.indicator (measurableSet_singleton a)) using 1
    funext t
    simp only [Set.indicator_apply,Set.mem_singleton_iff]

  have hb (t : ℝ) : |if t = a then (1:ℝ) else 0| ≤ 1 := by split_ifs <;> norm_num
  obtain ⟨R,hR,hG⟩ := q.closed_chain_uniform (F := fun _ => (0:ℝ))
    (D := fun t => if t = a then (1:ℝ) else 0) (LipschitzWith.const (0:ℝ))
    hD (by norm_num : (0:ℝ) ≤ 1) hb
    (fun j => levelApprox a (e j)) (fun j => levelApproxDeriv a (e j)) (fun _ => 1)
    (fun j => levelApprox_lipschitz (hep j) a) (fun j => levelApprox_hasDerivAt (hep j) a)
    (fun j => continuous_levelApproxDeriv (hep j) a) (fun j => levelApproxDeriv_bound (hep j) a)
    (levelApproxDeriv_tendsto he hep a) (fun j => e j*(Real.pi/2))
    (by simpa only [zero_mul] using he.mul_const (Real.pi/2))
    (fun j t => by simpa only [sub_zero] using levelApprox_error (hep j).le a t) P
  have hR0 : q.inclusion R = 0 := Lp.ext (hR.trans (Lp.coeFn_zero ℝ 2 (MassMeasure.currentMassMeasure hT)).symm)
  have hRz : R = 0 := q.inclusion_injective hz (hR0.trans (map_zero q.inclusion).symm)
  rw [hRz,map_zero] at hG
  filter_upwards [hG,(Lp.coeFn_zero (Euc (k+1)) 2 q.atlasMeasure)] with w hw hz
  intro ha
  simpa only [hz,ha,ite_true,one_smul,Pi.zero_apply] using hw.symm

end CAT0Fillings.ChartGeometry
end

end OAI
