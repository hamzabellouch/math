import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.SelectedData

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology
noncomputable section
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis

lemma selected_data_profile_subsequence {Z s l τ : ℕ → ℝ} {N : ℕ → ℕ} {B C R Q : ℝ}
    (d : ∀ n, SelectedQuantumData (Z n) (N n) (s n) (l n) (τ n) B C R)
    (hZ : ∀ n, 0 ≤ Z n) (hs : ∀ n, 0 < s n) (hl : ∀ n, 1 ≤ l n)
    (hs0 : Tendsto s atTop (𝓝 0)) (hl0 : Tendsto l atTop atTop)
    (hτ0 : Tendsto τ atTop (𝓝 0)) (hB : 0 < B) (hC : 0 ≤ C) (hR : 0 < R)
    (hQ : 0 ≤ Q) (hq : ∀ n, |(s n)^3*(Z n-(N n:ℝ))| ≤ Q) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => (s (φ n))^3*(Z (φ n)-(N (φ n):ℝ))) atTop (𝓝 tfResidualCharge) := by
  let ρ : ℕ → TFSpace → ℝ := fun n => tfDilation (s n) (d n).density
  have hmass (n) : (∫ x, ρ n x) = (s n)^3*(N n:ℝ) := by
    rw [show ρ n = tfDilation (s n) (d n).density from rfl,tfDilation_mass (hs n),(d n).mass_density]
  have hq' (n) : |(s n)^3*Z n-∫ x, ρ n x| ≤ Q := by rw [hmass,←mul_sub]; exact hq n
  have hb := selected_data_local_bounds d hZ hs hl hl0
  obtain ⟨U,hUc,φ,hφ,hconv⟩ := screened_field_normal_family
    (fun n => tfDilation_measurable (d n).measurable_density)
    (fun n => tfDilation_integrable (hs n) (d n).integrable_density)
    (fun n => tfDilation_nonneg (d n).nonneg_density)
    (fun n => (d n).scaled_bounded (hs n)) hQ hq' hb.1 hb.2
  obtain ⟨q,hqI,ψ,hψ,hqlim⟩ := (isCompact_Icc : IsCompact (Icc (-Q) Q)).tendsto_subseq
    (fun n => abs_le.mp (hq (φ n)))
  let κ := φ ∘ ψ
  have hκ : StrictMono κ := hφ.comp hψ
  have hκt : Tendsto κ atTop atTop := hκ.tendsto_atTop
  have hrlim : Tendsto (fun n => (d (κ n)).radius/s (κ n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (div_pos (d (κ n)).radius_pos (hs (κ n))).le)
      (fun n => (d (κ n)).radius_upper) (tendsto_inv_atTop_zero.comp (hl0.comp hκt))
  have htail : Tendsto (fun n => ∫ x in {x : TFSpace | R < ‖x‖}, ρ (κ n) x) atTop (𝓝 0) :=
    squeeze_zero (fun n => integral_nonneg (fun x => tfDilation_nonneg (d (κ n)).nonneg_density x))
      (fun n => (d (κ n)).tail) (hτ0.comp hκt)
  have hcap : 0 ≤ actualInverseCap := by
    have := tfPatchCapConstant_pos
    unfold actualInverseCap
    positivity
  have hprof := selected_screened_profile (s := s ∘ κ) (r := fun n => (d (κ n)).radius)
    (l := l ∘ κ) (Z := Z ∘ κ) (a := fun n => (d (κ n)).offset)
    (μ := fun n => (d (κ n)).density) (p := fun n => (d (κ n)).error)
    (B := B) (C := C) (Ccap := actualInverseCap) (R := R) (q := q) (F_lim := U)
    (fun n => hs (κ n)) (fun n => (d (κ n)).radius_pos) (hs0.comp hκt) hrlim
    (fun n => zero_lt_one.trans_le (hl (κ n))) (hl0.comp hκt)
    (fun n => (d (κ n)).radius_lower) hB hC hcap hR
    (fun n => (d (κ n)).continuous_offset) (fun n => (d (κ n)).measurable_density)
    (fun n => (d (κ n)).integrable_density) (fun n => (d (κ n)).nonneg_density)
    (fun n => (d (κ n)).bounded_density) (fun n => (d (κ n)).measurable_error)
    (fun n => (d (κ n)).integrable_error) (fun n => (d (κ n)).nonneg_error)
    (fun n => (d (κ n)).bounded_error) (fun n => (d (κ n)).support_error)
    (fun n => (d (κ n)).mass_error) (fun n => (d (κ n)).weak)
    (fun n => (d (κ n)).lower) (fun n => (d (κ n)).upper)
    (fun n => (d (κ n)).TF) hUc
    (fun K hK hK0 u hu => hψ.tendsto_atTop.eventually (hconv K hK hK0 u hu))
    (Eventually.of_forall (fun n => (d (κ n)).cap))
    (by simpa only [Function.comp_def,κ,(d _).mass_density] using hqlim) htail
  exact ⟨κ,hκ,hprof.2 ▸ hqlim⟩

end CoulombBarrier

end

end OAI
