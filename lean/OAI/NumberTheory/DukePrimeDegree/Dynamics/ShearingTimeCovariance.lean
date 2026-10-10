import OAI.NumberTheory.DukePrimeDegree.Dynamics.LeafFlowCovariance
import OAI.NumberTheory.DukePrimeDegree.Dynamics.ShearingTimeSelection

namespace OAI

/-!
# Choosing recurrence times with leaf covariance

Finitely many affine pullbacks of a Lebesgue null exceptional set are
null. Thus the two-point, two-scale recurrence selection can enforce
the actual leaf covariance identities at every selected time.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma ae_affine_precompose {P : ℝ → Prop} (hP : ∀ᵐ t ∂volume, P t)
    (a b : ℝ) (ha : a ≠ 0) : ∀ᵐ t ∂volume, P (b + a * t) := by
  apply ae_iff.mpr
  have he : {t | ¬ P (b + a * t)} =
      (fun t => a * t) ⁻¹' ((fun t => b + t) ⁻¹' {t | ¬ P t}) := rfl
  rw [he, Real.volume_preimage_mul_left ha, measure_preimage_add, ae_iff.mp hP, mul_zero]

theorem exists_common_two_scale_time_ae
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 36 * ε < 1)
    (θ η : Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (P : ℝ → Prop) (hP : ∀ᵐ τ ∂volume, P τ) :
    ∃ τ ∈ Ioc 0 T, P τ ∧ (∀ k, Φ τ (z k) ∈ G) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H := by
  let Ψ : ℝ → Y × ℝ → Y × ℝ := fun t y => (Φ t y.1, t)
  let G' : Set (Y × ℝ) := {y | y.1 ∈ G ∧ P y.2}
  let H' : Set (Y × ℝ) := {y | y.1 ∈ H}
  have hG' (k : Fin 2) :
      volume.real (Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'}) ≤ ε * T := by
    have he : (Ioc 0 T ∩ {τ | Ψ τ (z k, 0) ∉ G'}) =ᵐ[volume]
        (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) := by
      filter_upwards [hP] with τ hτ
      simp only [mem_inter_iff, mem_ofPred_eq, Ψ, G', hτ, and_true]
    have hm := measure_congr he
    simpa only [measureReal_def, hm] using hG k
  obtain ⟨τ, hτ, hg, hh⟩ := exists_common_two_scale_time Ψ G' H'
    (fun k => (z k, 0)) T ε hT hε θ η hθlo hθhi hη hG' hH
  exact ⟨τ, hτ, (hg 0).2, fun k => (hg k).1, hh⟩

theorem exists_common_two_scale_time_with_covariance
    {Y : Type*} (Φ : ℝ → Y → Y) (G H : Set Y) (z : Fin 2 → Y)
    (T ε : ℝ) (hT : 0 < T) (hε : 36 * ε < 1)
    (θ η : Fin 2 → ℝ)
    (hθlo : ∀ q, 4 * T ≤ θ q) (hθhi : ∀ q, θ q ≤ 6 * T)
    (hη : ∀ q, η q = 0 ∨ η q = 1)
    (hG : ∀ k, volume.real (Ioc 0 T ∩ {τ | Φ τ (z k) ∉ G}) ≤ ε * T)
    (hH : ∀ k, volume.real (Ioc 0 (4 * T) ∩ {τ | Φ τ (z k) ∉ H}) ≤ ε * (4 * T))
    (Q : Y → ℝ → Prop) (hQ : ∀ k, ∀ᵐ t ∂volume, Q (z k) t) :
    ∃ τ ∈ Ioc 0 T,
      (∀ k, Φ τ (z k) ∈ G ∧ Q (z k) τ) ∧
      ∀ k q, Φ ((θ q + (2 - η q) * τ) / 2) (z k) ∈ H ∧
        Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
  have hfirst : ∀ᵐ τ ∂volume, ∀ k, Q (z k) τ := ae_all_iff.mpr hQ
  have hsecond : ∀ᵐ τ ∂volume, ∀ k q,
      Q (z k) ((θ q + (2 - η q) * τ) / 2) := by
    apply ae_all_iff.mpr
    intro k
    apply ae_all_iff.mpr
    intro q
    have ha : (2 - η q) / 2 ≠ 0 := by
      rcases hη q with h | h <;> rw [h] <;> norm_num
    have he (τ : ℝ) : (θ q + (2 - η q) * τ) / 2 =
        θ q / 2 + ((2 - η q) / 2) * τ := by ring
    simp_rw [he]
    exact ae_affine_precompose (hQ k) _ _ ha
  obtain ⟨τ, hτ, hq, hg, hh⟩ := exists_common_two_scale_time_ae
    Φ G H z T ε hT hε θ η hθlo hθhi hη hG hH
    (fun τ => (∀ k, Q (z k) τ) ∧
      ∀ k q, Q (z k) ((θ q + (2 - η q) * τ) / 2)) (hfirst.and hsecond)
  exact ⟨τ, hτ, fun k => ⟨hg k, hq.1 k⟩, fun k q => ⟨hh k q, hq.2 k q⟩⟩

end DukePrimeDegree

end

end OAI
