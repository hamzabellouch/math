import Mathlib

namespace OAI
noncomputable section
open Set MeasureTheory Metric
namespace ParabolicAverage
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def box (p : V × ℝ) (q : ℝ) : Set (V × ℝ) :=
  ball p.1 q ×ˢ Ioc (p.2-q^4) p.2
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma measurable_box (p : V × ℝ) (q : ℝ) : MeasurableSet (box p q) :=
  measurableSet_ball.prod measurableSet_Ioc
lemma volume_box (p : V × ℝ) (q : ℝ) (hq : 0<q) :
    (volume.prod volume) (box p q)=
      volume (ball (0:V) 1)*ENNReal.ofReal (q^(Module.finrank ℝ V+4)) := by
  rw [box,Measure.prod_prod,Measure.addHaar_ball_of_pos volume p.1 hq,Real.volume_Ioc]
  have ht : p.2-(p.2-q^4)=q^4 := by ring
  rw [ht,pow_add,ENNReal.ofReal_mul (pow_nonneg hq.le _)]
  ring

lemma exists_averaging_constant : ∃ A : ℝ, 0<A ∧ ∀ (p : V × ℝ) (q : ℝ),
    0<q → q≤1 → ∀ (Ω : Set (V × ℝ)), box p q⊆Ω →
    ∀ (u : V × ℝ → ℂ) (N E : ℝ), 0≤N → 0≤E →
    eLpNorm u 2 ((volume.prod volume).restrict Ω)≤ENNReal.ofReal N →
    (∀ z∈box p q, ‖u p-u z‖≤E) →
    ‖u p‖≤E+(A/q^(Module.finrank ℝ V+4))*N := by
  let B : ENNReal := (volume (ball (0:V) 1))^((1:ℝ)/2)
  have hB : 0<B := ENNReal.rpow_pos (measure_ball_pos volume 0 (by norm_num)) measure_ball_lt_top.ne
  have hBt : B≠⊤ := by dsimp [B]; finiteness
  have hBr : 0<B.toReal := ENNReal.toReal_pos hB.ne' hBt
  refine ⟨1/B.toReal,by positivity,?_⟩
  intro p q hq hq1 Ω hsub u N E hN hE hLp hosc
  let d := Module.finrank ℝ V+4
  let c := max 0 (‖u p‖-E)
  have hc : 0≤c := le_max_left _ _
  have hlow : ∀ z∈box p q, ‖(c:ℝ)‖≤‖u z‖ := by
    intro z hz
    rw [Real.norm_of_nonneg hc]
    apply max_le (norm_nonneg _)
    have := norm_le_insert' (u p) (u z)
    linarith [hosc z hz]
  have hmono : eLpNorm (fun _ : V × ℝ => c) 2 ((volume.prod volume).restrict (box p q))≤ENNReal.ofReal N :=
    (eLpNorm_mono_ae aestronglyMeasurable_const
      ((ae_restrict_mem (measurable_box p q)).mono hlow)).trans
      ((eLpNorm_mono_measure u (Measure.restrict_mono hsub le_rfl)).trans hLp)
  rw [eLpNorm_const' c (by norm_num) (by norm_num),Measure.restrict_apply_univ,volume_box p q hq] at hmono
  simp only [ENNReal.toReal_ofNat] at hmono
  have hcp : ‖c‖ₑ=ENNReal.ofReal c := by exact Real.enorm_of_nonneg hc
  rw [hcp,ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hmono
  change ENNReal.ofReal c*(B*(ENNReal.ofReal (q^d))^((1:ℝ)/2))≤ENNReal.ofReal N at hmono
  have hv1 : ENNReal.ofReal (q^d)≤1 := by
    rw [←ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (pow_le_one₀ hq.le hq1)
  have hvl : ENNReal.ofReal (q^d)≤(ENNReal.ofReal (q^d))^((1:ℝ)/2) := by
    simpa only [ENNReal.rpow_one] using ENNReal.rpow_le_rpow_of_exponent_ge hv1 (by norm_num : (1:ℝ)/2≤1)
  have hlo : ENNReal.ofReal c*(B*ENNReal.ofReal (q^d))≤ENNReal.ofReal N :=
    (by gcongr : ENNReal.ofReal c*(B*ENNReal.ofReal (q^d))≤ENNReal.ofReal c*(B*(ENNReal.ofReal (q^d))^((1:ℝ)/2))).trans hmono
  have hreal := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlo
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal hc,ENNReal.toReal_ofReal (pow_nonneg hq.le d),ENNReal.toReal_ofReal hN] at hreal
  have hden : 0<B.toReal*q^d := mul_pos hBr (pow_pos hq _)
  have hcN : c≤N/(B.toReal*q^d) := (le_div_iff₀ hden).mpr hreal
  have hcUp : ‖u p‖-E≤c := le_max_right _ _
  calc
    ‖u p‖≤E+N/(B.toReal*q^d) := by linarith
    _=E+((1/B.toReal)/q^d)*N := by ring
end ParabolicAverage

end

end OAI
