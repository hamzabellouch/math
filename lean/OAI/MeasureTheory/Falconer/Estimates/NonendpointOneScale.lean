import OAI.MeasureTheory.Falconer.Recursion.NonendpointContactGain
import OAI.MeasureTheory.Falconer.Estimates.SourceRelativeRegularization
import OAI.MeasureTheory.Falconer.Estimates.OneScaleParameters
import OAI.MeasureTheory.Falconer.Radial.WeakRadialTotalCost

namespace OAI

/-! # Uniform nonendpoint one-scale radial improvement

This is one orientation of the preparation lemma. The input reverse caps are
measured using the original probability laws and incoming pair relation.
-/

namespace Falconer.Regularization
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem nonendpoint_one_scale_gain (hpublished : PublishedPlanarFurstenberg)
    {h : ℕ} {α t q C D s : ℝ}
    (hq : (h:ℝ) < q) (hq' : q-(h:ℝ) ≤ 1/2) (hqt : q < t)
    (ht : t-(h:ℝ) < 1) (htα : t < α) (hC : 0 ≤ C)
    (Q : DyadicCube (h+2)) (hQ : Q.side = 1)
    (hD : 1 ≤ D) (hDdim : Real.sqrt (h+2:ℕ) ≤ D) (hs : 0 < s) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ (μ ν : Measure (Space (h+2))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
        μ Q.carrierᶜ = 0 →
        (∀ y : Space (h+2), ∀ r > 0, μ (Metric.ball y r) ≤ ENNReal.ofReal (C*r^α)) →
      ∀ A P : Set (Space (h+2)), MeasurableSet A → MeasurableSet P →
        μ Aᶜ = 0 → ν Pᶜ = 0 →
        (∀ z ∈ A, ∀ x ∈ P, s ≤ ‖z-x‖) →
        (∀ y ∈ Q.carrier, ∀ x ∈ P, ‖y-x‖ ≤ D) →
      ∀ G : Set (Space (h+2) × Space (h+2)), MeasurableSet G →
        (∀ᵐ z ∂μ, ∀ r : ℝ, 1/(2:ℝ)^N ≤ r → r ≤ 1 →
          ∀ u : Space (h+2), ‖u‖ = 1 →
            ν {x | (z,x) ∈ G ∧ dist (normalize (x-z)) u < r} ≤
              ENNReal.ofReal (((2:ℝ)^N)^ε*r^q)) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧ G' ⊆ G ∧
        (μ.prod ν) (G \ G') ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c)) ∧
        ∀ x u : Space (h+2), μ {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-q-c)) := by
  obtain ⟨ε₁,gain,hε₁,hgain,hclass⟩ := nonendpoint_contact_gain hpublished hq hq' hqt ht
    Q hQ hD hDdim hs
  obtain ⟨τ,hτ,hτε,hτgain,hτgain'⟩ := one_scale_loss_choice (h+2) hε₁ hgain
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hα : 0 ≤ α := by
    have hh := Nat.cast_nonneg (α := ℝ) h
    linarith only [hh,hq,hqt,htα]
  obtain ⟨lam,γ,hlam,hγ,hlamτ,H,Nc,hH,hcontrols,hcontact⟩ :=
    source_classes_uniform_contact (by omega : 0 < h+2) Q hside hα hqt htα hτ hC
  obtain ⟨Ng,hNg⟩ := hclass τ γ hτ hγ hτε hτgain hτgain'
  obtain ⟨c₀,hc₀,Nd,hNd⟩ := weak_radial_total_cost 0 (4*H+2)
    (A := 0) (by norm_num) hlam (by norm_num : (0:ℝ) < 1)
    (by norm_num : (0:ℝ) < 1) (by positivity : 0 < τ*γ/2)
  let c := min c₀ (gain*γ/8)
  have hc : 0 < c := lt_min hc₀ (by positivity)
  refine ⟨τ*γ,c,mul_pos hτ hγ,hc,max H (max (h+2+3) (max Nc (max Ng Nd))),?_⟩
  intro N hN μ ν _ _ hroot hfrost A P hA hP hAfull hPfull hsep hpin G hG hcap
  simp only [max_le_iff] at hN
  obtain ⟨hHN,hdN,hNc,hNg',hNd'⟩ := hN
  obtain ⟨hNp,hNB,_,hblock,hblock'⟩ := hcontrols N hNc
  have hlocal : ∀ p ∈ regularizationLeaves Q μ N,
      regularizationLabel Q μ N (N/H) p ∈ regularizationIndex Q μ N (N/H)
        (ENNReal.ofReal (((2:ℝ)^N)^(-lam))) →
      ∃ G' : Set (Space (h+2) × Space (h+2)), MeasurableSet G' ∧
        ((sourceClass Q μ N (N/H) p).prod ν) (G \ G') ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ∧
        ∀ x u : Space (h+2), sourceClass Q μ N (N/H) p
          {z | (z,x) ∈ G' ∧ ‖normalize (z-x)-u‖ ≤ 1/(2:ℝ)^N} ≤
            ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8)) := by
    intro p hp hret
    obtain ⟨G',hG',_,hdel,hbound⟩ := hNg N hNg' μ ν (N/H) hNB lam hlam.le hlamτ
      hblock hblock' p hp (hcontact N hNc μ hfrost p hp hret)
      A P hA hP hAfull hPfull hsep hpin G hG hcap
    exact ⟨G',hG',hdel,hbound⟩
  obtain ⟨G',hG',hsub,hdel,hbound⟩ := source_relative_regularization_gain Q hside μ ν G hG
    hroot hH hHN hdN (by positivity : 0 < ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
    (ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))))
    (ENNReal.ofReal (((2:ℝ)^N)^(-q-gain*γ/8))) (1/(2:ℝ)^N) hlocal
  refine ⟨G',hG',hsub,?_,?_⟩
  · apply hdel.trans
    have hd : ((2:ℝ≥0∞)^(2*N))⁻¹+(N^(4*H+2):ℕ)*ENNReal.ofReal (((2:ℝ)^N)^(-lam))+
        ENNReal.ofReal (((2:ℝ)^N)^(-(τ*γ/2))) ≤ ENNReal.ofReal (((2:ℝ)^N)^(-c₀)) := by
      simpa only [Nat.cast_zero,zero_mul,zero_add,add_zero,Nat.cast_one,one_mul] using hNd N hNd'
    exact hd.trans (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le
      (one_le_pow₀ (by norm_num)) (neg_le_neg (min_le_left _ _))))
  · intro x u
    apply (hbound x u).trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) ?_))
    have hh : c ≤ gain*γ/8 := min_le_right _ _
    linarith only [hh]

end Falconer.Regularization

end OAI
