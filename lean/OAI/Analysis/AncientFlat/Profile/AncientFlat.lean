import OAI.Analysis.AncientFlat.Profile.FlatMainCore
import OAI.Analysis.AncientFlat.Weighted.ExactWeightedInverse
import OAI.Analysis.AncientFlat.Profile.ProfileOperator

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian ENNReal
namespace FlatMain
open FlatWeighted FlatSimilarity
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem ancient_flat_right_inverse (e : OrthonormalBasis (Fin 24) ℝ V)
    (hm : Module.finrank ℝ V=24) (P : ProfileData) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ ∀ α a : ℝ, 0<α → α<1 → 0<a → a≤1/16 →
      ∃ C : ℝ, 0<C ∧ ∃ D : sourceSpace (V := V) α (-2+2*δ) a →ₗ[ℝ] (V × ℝ → ℂ),
        ∀ f : sourceSpace (V := V) α (-2+2*δ) a,
          InX e α (-2+2*δ) a (D f) ∧
          (∀ t : ℝ, t<0 → ∀ x : V, flatOperator P (D f) t x=f.val (x,t)) ∧
          XNorm e α (-2+2*δ) a (D f)≤C*sourceNorm α (-2+2*δ) a f := by
  obtain ⟨κ,K,hκ,hb⟩ := P.bounds
  obtain ⟨γ,hγ,hγ1,hD⟩ := exact_weighted_inverse e P.G P.H P.c κ P.c_pos hκ
    P.smooth P.compactified_smooth P.compactified_zero P.compactified_match
    (fun y hy => (hb y hy).1)
  refine ⟨2*γ,by linarith,by linarith,?_⟩
  intro α a hα hα1 ha ha1
  have hw : -2+2*(2*γ)= -2+4*γ := by ring
  rw [hw]
  obtain ⟨C,hC,D,hDC⟩ := hD α a hα hα1 ha ha1
  refine ⟨C,hC,D,?_⟩
  intro f
  obtain ⟨hs,hd,hn,hrad,hreal⟩ := hDC f
  have htEq (t : ℝ) (ht : t<0) (x : V) :
      timeDerivative (D f) t x=profileTime P.G f.val (D f) t x := (hd t ht x).deriv
  have hn' : xNorm e α (-2+4*γ) a (fun t x => D f (x,t)) (timeDerivative (D f))≤
      ENNReal.ofReal (C*sourceNorm α (-2+4*γ) a f) := by
    rw [xNorm_time_congr e α (-2+4*γ) a _ _ _ htEq]
    exact hn
  refine ⟨⟨fun t ht => hs t,fun t ht x => (hd t ht x).differentiableAt,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hn',fun t ht => hrad t,fun t ht => hreal t⟩,?_,?_⟩
  · intro t ht x
    rw [flatOperator,htEq t ht x,P.originalB_eq hm ht x]
    simp only [profileTime,ParabolicAnnular.profilePrincipal]
    ring
  · unfold XNorm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn').trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC.le (sourceNorm_nonneg _ _ _ f)))
end FlatMain

end

end OAI
