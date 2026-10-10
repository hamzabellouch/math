import Mathlib
import OAI.Probability.LogConcave.Numerics.ChainTaylor
import OAI.Probability.LogConcave.Sampling.TensorVector

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set
open scoped Classical BigOperators NNReal
open TensorEnergy Quadrature

lemma stationary_tensorVector_rms {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : Continuous H) (ht : HasGaussianLowerTail H)
    (F : (S → Fin d) → Point d → ℝ) (hF : ∀c,PolySmooth (F c))
    (f : Point d → Point d) (hf : Measurable f) (hlaw : (gibbs H).map f=gibbs H) :
    Integrable (fun y => ‖tensorVector F (f y)‖^2) (gibbs H) ∧
      (∫y,‖tensorVector F (f y)‖^2 ∂gibbs H)=spatialEnergy F 0 (gibbs H) := by
  have he (y : Point d) : ‖tensorVector F y‖^2=spatialSquared F 0 y := by
    rw [tensorVector_norm_sq,spatialSquared_zero]
  simp_rw [he]
  have hm := (spatialSquared_polySmooth F hF 0).smooth.continuous.aestronglyMeasurable
    (μ:=(gibbs H).map f)
  refine ⟨?_,?_⟩
  · apply (integrable_map_measure hm hf.aemeasurable).mp
    rw [hlaw]
    exact (spatialSquared_polySmooth F hF 0).integrable hH ht
  · exact (integral_map hf.aemeasurable hm).symm.trans (by rw [hlaw]; rfl)

theorem stationary_lie_taylor_rms {S : Type} [Fintype S] {d : ℕ}
    {H : Point d → ℝ} (hH : PolySmooth H) (htail : HasGaussianLowerTail H)
    [SFinite (gibbs H)] {K : ℝ≥0} (hL : LipschitzWith K (gradient H))
    (A : (Unit ⊕ Unit → Fin d) → Point d → ℝ) (F : (S → Fin d) → Point d → ℝ)
    (hA : ∀c,PolySmooth (A c)) (hF : ∀c,PolySmooth (F c))
    (hsk : ∀i z y,A (Sum.elim (fun _ => i) (fun _ => z)) y=
      -A (Sum.elim (fun _ => z) (fun _ => i)) y)
    (C D B : ℕ → ℝ) {α κ ρ : ℝ} (hκ : 0≤κ) (hρ : 1≤ρ) (hB : ∀k,0≤B k)
    (hb : ∀k y,AllSplitBound (spatialTensor A (List.finRange k) y) (C k*α*ρ^k))
    (hs : ∀k,0<k → ∀y,AllSplitBound (spatialTensor (scoreField H) (List.finRange k) y) (D k*ρ^k))
    (he : ∀k,0<k → spatialEnergy F k (gibbs H)≤κ*ρ^(2*k)*B k)
    {s : Set ℝ} (Ψ : Point d → ℝ → Point d)
    (hΨ : ∀y t,t∈s → HasDerivWithinAt (Ψ y) (skewLieField H A (Ψ y t)) s t)
    (hm : Measurable (fun p : ℝ × Point d => Ψ p.2 p.1))
    (hlaw : ∀t∈s,(gibbs H).map (fun y => Ψ y t)=gibbs H)
    {a x : ℝ} (hax : a≤x) (hsub : uIcc a x⊆s) (n : ℕ) :
    Integrable (fun y => ‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2) (gibbs H) ∧
    (∫y,‖tensorVector F (Ψ y x)-chainTaylor
      (fun k t => tensorVector (iterTensorLie H A F k) (Ψ y t)) n a x‖^2 ∂gibbs H)≤
      ((x-a)^(n+1)/(n.factorial:ℝ))^2*
        (κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0) := by
  have hpoly := iterTensorLie_polySmooth hH A F hA hF
  have hfinite (t : ℝ) (ht : t∈s) := stationary_tensorVector_rms hH.smooth.continuous htail
    (iterTensorLie H A F (n+1)) (hpoly (n+1)) (fun y => Ψ y t)
    (hm.comp (measurable_const.prodMk measurable_id)) (hlaw t ht)
  have hpos : 0≤κ*(α^2*ρ^4)^(n+1)*iterEnergyBudget K C D B (n+1) 0 :=
    mul_nonneg (mul_nonneg hκ (pow_nonneg (mul_nonneg (sq_nonneg α) (by positivity)) _))
      (iterEnergyBudget_nonneg K.2 C D hB (n+1) 0)
  have htmem (t : ℝ) (ht : t∈Ioc a x) : t∈s :=
    hsub (by rw [uIcc_of_le hax]; exact ⟨ht.1.le,ht.2⟩)
  apply chainTaylor_remainder_rms hax hpos hsub
    (fun y k _ ht => lie_vector_chain hH A F hA hF hsk (Ψ y) (hΨ y) k ht)
  · exact ((tensorVector_contDiff _ (fun c => (hpoly (n+1) c).smooth)).continuous.measurable.comp hm).aestronglyMeasurable
  · exact fun t ht => (hfinite t (htmem t ht)).1
  · intro t ht
    rw [(hfinite t (htmem t ht)).2]
    simpa only [Nat.mul_zero,pow_zero,mul_one] using
      iterTensorLie_energy hH htail hL A F hA hF C D B hκ hρ hB hb hs he (n+1) 0 (Or.inl (by omega))
end LogConcaveSampling

end

end

end

end OAI
