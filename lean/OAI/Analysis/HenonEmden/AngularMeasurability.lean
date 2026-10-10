import OAI.Analysis.HenonEmden.AngularBounds

namespace OAI

section AngularMeasurability

open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace HenonLaneEmden
open Cutoff AdaptiveCap SpatialComponents LayerTonelli

lemma measurable_cap_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (fun e : sphere (0:Space n) 1 => weightedEnergyN (weight volume κ e) u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × Space n =>
      ENNReal.ofReal (weight volume κ z.1 z.2*source u q B z.2*u z.2)) :=
    (((measurable_weight volume hκ hκ1).mul ((measurable_source hu q B).comp measurable_snd)).mul
      (hu.measurable.comp measurable_snd)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_d_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    Measurable (fun e : sphere (0:Space n) 1 => weightedEnergyN (fun x => d x*weight volume κ e x) u q B) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × Space n =>
      ENNReal.ofReal ((d z.2*weight volume κ z.1 z.2)*source u q B z.2*u z.2)) :=
    (((((continuous_d (E := Space n)).measurable.comp measurable_snd).mul (measurable_weight volume hκ hκ1)).mul
      ((measurable_source hu q B).comp measurable_snd)).mul (hu.measurable.comp measurable_snd)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_pressure {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (f g : Space n → ℝ) :
    Measurable (capPressureIntegral f g κ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) =>
      ENNReal.ofReal (((n:ℝ)-2)*weight volume κ z.1 z.2.1*directionalFactor z.1 z.2)) := by
    have hw : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) => weight volume κ z.1 z.2.1) :=
      (measurable_weight (volume : Measure (Space n)) hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)
    unfold directionalFactor
    fun_prop
  exact hm.lintegral_prod_right

lemma measurable_cap_mismatch {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (f g : Space n → ℝ) :
    Measurable (capMismatchIntegral f g κ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hw := measurable_weight (volume : Measure (Space n)) hκ hκ1
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × Space n) =>
      ENNReal.ofReal (|weight volume κ z.1 z.2.1-weight volume κ z.1 z.2.2|)) :=
    ((hw.comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (hw.comp (measurable_fst.prodMk measurable_snd.snd))).abs.ennreal_ofReal
  exact hm.lintegral_prod_right

lemma measurable_cap_loss {n : ℕ} (hn : 1 ≤ n) {κ δ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) {f u : Space n → ℝ}
    (hu : Measurable u) (hfo : IsOpen {z : Space n × ℝ | 0 < z.2 ∧ z.2 < f z.1}) :
    Measurable (lossIntegral u f κ δ) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hm : Measurable (fun z : sphere (0:Space n) 1 × (Space n × ℝ) =>
      ENNReal.ofReal ((weight volume κ z.1 z.2.1-lineWeight volume f κ δ z)*u z.2.1)) :=
    ((((measurable_weight volume hκ hκ1).comp (measurable_fst.prodMk measurable_snd.fst)).sub
      (measurable_lineWeight volume hfo hκ hκ1 δ)).mul (hu.comp measurable_snd.fst)).ennreal_ofReal
  exact hm.lintegral_prod_right

lemma lintegral_angular_d_energy {n : ℕ} (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    {u : Space n → ℝ} (hu : Continuous u) (q B : ℝ) :
    (∫⁻ e : sphere (0:Space n) 1, weightedEnergyN (fun x => d x*weight volume κ e x) u q B ∂volume.toSphere) =
      weightedEnergyN (fun x => d x*w n x) u q B := by
  unfold weightedEnergyN
  have h1 (e : sphere (0:Space n) 1) (x : Space n) :
      (d x*weight volume κ e x)*source u q B x*u x=weight volume κ e x*(d x*source u q B x*u x) := by ring
  have h2 (x : Space n) : (d x*w n x)*source u q B x*u x=w n x*(d x*source u q B x*u x) := by ring
  simp_rw [h1,h2,ENNReal.ofReal_mul (weight_nonneg volume κ _ _),ENNReal.ofReal_mul (w_nonneg n _)]
  exact lintegral_angular_weight hn hκ hκ1
    (((continuous_d (E := Space n)).measurable.mul (measurable_source hu q B)).mul hu.measurable)

def sphereMass (n : ℕ) : ℝ := (volume : Measure (Space n)).toSphere.real univ
lemma sphereMass_nonneg (n : ℕ) : 0 ≤ sphereMass n := ENNReal.toReal_nonneg

lemma angular_constant_bound {n : ℕ} (hn : 1 ≤ n) {F : sphere (0:Space n) 1 → ℝ≥0∞} {C : ℝ}
    (_hC : 0 ≤ C) (hF : ∀ e, F e ≤ ENNReal.ofReal C) :
    (∫⁻ e, F e ∂volume.toSphere) ≤ ENNReal.ofReal (sphereMass n*C) := by
  have : Nontrivial (Space n) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  apply (lintegral_mono hF).trans_eq
  rw [lintegral_const,ENNReal.ofReal_mul (sphereMass_nonneg n)]
  exact (mul_comm _ _).trans (congrArg (fun a => a*ENNReal.ofReal C) (ENNReal.ofReal_toReal (measure_ne_top _ _) |>.symm))

lemma IsSolution.angular_mismatch_bound {n : ℕ} (hn : 2 ≤ n) {p q A B κ δ : ℝ}
    {u v : Space n → ℝ} (h : IsSolution n p q A B u v) (hp : 0 < p) (hq : 0 < q)
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) :
    (∫⁻ e : sphere (0:Space n) 1, capMismatchIntegral (source u q B) (source v p A) κ e ∂volume.toSphere) ≤ ENNReal.ofReal
      (sphereMass n*(oscillationConstant (volume : Measure (Space n)) κ*δ*(weightedEnergy (eta n) u q B+weightedEnergy (eta n) v p A)+
      boundConstant (volume : Measure (Space n)) κ*(farConstant n p q A B δ+farConstant n q p B A δ))) := by
  have hC := oscillationConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hB := boundConstant_nonneg (volume : Measure (Space n)) hκ.le
  have hfE := weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_u x).le) (q:=q) (B:=B)
  have hgE := weightedEnergyN_nonneg (eta_nonneg n) (fun x => (h.positive_v x).le) (q:=p) (B:=A)
  apply angular_constant_bound (by omega) (add_nonneg (mul_nonneg (mul_nonneg hC hδ.le) (add_nonneg hfE hgE))
    (mul_nonneg hB (add_nonneg (farConstant_nonneg _ _ _ _ hδ.le) (farConstant_nonneg _ _ _ _ hδ.le))))
  exact h.capMismatch_bound hn hp hq hκ hκ1 hδ hδ1

end HenonLaneEmden
end
end AngularMeasurability

end OAI
