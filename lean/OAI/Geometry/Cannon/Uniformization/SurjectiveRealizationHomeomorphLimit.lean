import Mathlib
import OAI.Geometry.Cannon.Uniformization.EventualRelativeShrink
import OAI.Geometry.Cannon.Conformal.Distinct
import OAI.Geometry.Cannon.Conformal.QuasiMobius

namespace OAI

/-! A homeomorphism obtained as the limit of surjective finite realizations. -/

section
section
namespace CannonRealization
open Set Filter Topology Metric

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y] [PreconnectedSpace X] [Nontrivial Y]

theorem surjective_realization_homeomorph_limit
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F) :
    ∃ f : X ≃ₜ Y, RelativeShrink f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  obtain ⟨u,v,huv⟩ := exists_pair_ne Y
  obtain ⟨p,hp⟩ := hsurj 0 u
  obtain ⟨q,hq⟩ := hsurj 0 v
  have hpq : p≠q := by intro h; exact huv (hp.symm.trans ((congrArg (F 0) h).trans hq))
  obtain ⟨f,φ,hφ,ht⟩ := compact_map_subsequence F (hshrink.equicontinuous hpq)
  have hf := hshrink.limit hφ ht
  have hfs := surjective_limit hsurj ht
  obtain ⟨p',hp'⟩ := hfs u
  obtain ⟨q',hq'⟩ := hfs v
  have hn : f p'≠f q' := by rwa [hp',hq']
  let H := (Equiv.ofBijective f ⟨hf.injective hn,hfs⟩).toHomeomorphOfContinuousClosed
    f.continuous f.continuous.isClosedMap
  exact ⟨H,hf,φ,hφ,ht⟩

theorem surjective_realization_quasiMobius_limit [PreconnectedSpace Y]
    {Q : ℕ} {P : ℝ} (hpack : CannonPacking.PolynomialPacking (X:=X) Q P)
    (hP : 0 ≤ P) (hdiam : ∀ x y : X, dist x y ≤ 1)
    (F : ℕ → C(X,Y)) (hsurj : ∀ n, Function.Surjective (F n))
    (hshrink : EventualRelativeShrink F) :
    ∃ f : X ≃ₜ Y, CannonQM.QuasiMobius f ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (F ∘ φ) atTop (𝓝 (⟨f,f.continuous⟩ : C(X,Y))) := by
  obtain ⟨f,hf,φ,hφ,ht⟩ := surjective_realization_homeomorph_limit F hsurj hshrink
  exact ⟨f,hf.quasiMobius f hpack hP hdiam,φ,hφ,ht⟩
end CannonRealization

end
end

end OAI
