import OAI.Geometry.RCD.Coordinates.BoundedLocalCoordinates
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension

namespace OAI

/-! # Bounded global representatives of centered local harmonic frames -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem localGamma_pair_constant_shift {Ω : Set X}
    (f f' g g' : SobolevSpace μ Q) (a b : ℝ)
    (hf : (fun x => SobolevSpace.toLp μ Q f' x-SobolevSpace.toLp μ Q f x)
      =ᵐ[μ.restrict Ω] fun _ => a)
    (hg : (fun x => SobolevSpace.toLp μ Q g' x-SobolevSpace.toLp μ Q g x)
      =ᵐ[μ.restrict Ω] fun _ => b) :
    localGamma μ Q f' g' =ᵐ[μ.restrict Ω] localGamma μ Q f g := by
  filter_upwards [hf,hg,ae_restrict_of_ae (localGamma_eq_on_diff_level μ Q f' f g' a),
    ae_restrict_of_ae (localGamma_eq_on_diff_level μ Q g' g f b),
    ae_restrict_of_ae (localGamma_comm μ Q f g'),ae_restrict_of_ae (localGamma_comm μ Q g f)]
    with x hfx hgx h₁ h₂ h₃ h₄
  exact (h₁ hfx).trans (h₃.trans ((h₂ hgx).trans h₄))

theorem centered_bounded_frame {n : ℕ} (u : Fin n → SobolevSpace μ Q)
    (v : X → Euclidean n) (c : Euclidean n) (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hu : ∀ i, SobolevSpace.toLp μ Q (u i) =ᵐ[μ.restrict Ω] fun x => v x i)
    (hH : ∀ i, IsSobolevHarmonicOn μ Q Ω (u i))
    (hgram : ∀ i j, localGamma μ Q (u i) (u j) =ᵐ[μ.restrict Ω]
      fun _ => if i=j then 1 else 0)
    (η : SobolevSpace μ Q)
    (hη : SobolevSpace.toLp μ Q η =ᵐ[μ.restrict Ω] fun _ => (1:ℝ))
    (C : ℝ≥0) (hC : ∀ x∈Ω, ∀ i, |v x i-c i|≤C) :
    ∃ U : Fin n → SobolevSpace μ Q,
      (∀ i, ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (U i) x|≤C) ∧
      (∀ i, SobolevSpace.toLp μ Q (U i) =ᵐ[μ.restrict Ω] fun x => (v x-c) i) ∧
      (∀ i, IsSobolevHarmonicOn μ Q Ω (U i)) ∧
      (∀ i j, localGamma μ Q (U i) (U j) =ᵐ[μ.restrict Ω]
        fun _ => if i=j then 1 else 0) := by
  let f i := u i-c i • η
  have hf (i : Fin n) : SobolevSpace.toLp μ Q (f i) =ᵐ[μ.restrict Ω]
      fun x => v x i-c i := by
    change SobolevSpace.toLpCLM μ Q (u i-c i • η) =ᵐ[μ.restrict Ω] _
    rw [map_sub,map_smul]
    filter_upwards [hu i,hη,ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ Q (u i))
      (c i • SobolevSpace.toLp μ Q η)),ae_restrict_of_ae (Lp.coeFn_smul (c i) (SobolevSpace.toLp μ Q η))]
      with x hx hηx hsub hsm
    change (SobolevSpace.toLp μ Q (u i)-c i • SobolevSpace.toLp μ Q η) x=_
    simp only [hsub,Pi.sub_apply,hsm,Pi.smul_apply,smul_eq_mul,hx,hηx,mul_one]
  have hfbound (i : Fin n) : ∀ᵐ x ∂μ.restrict Ω, |SobolevSpace.toLp μ Q (f i) x|≤C := by
    filter_upwards [hf i,ae_restrict_mem hΩ] with x hx hxm
    rw [hx]
    exact hC x hxm i
  let U i := boundedLocalVersion μ Q (f i) C
  have hUf (i : Fin n) := boundedLocalVersion_eq μ Q (f i) C (hfbound i)
  have hconst := isSobolevHarmonicOn_of_local_constant μ Q Ω hΩ η 1 hη
  have hfh (i : Fin n) : IsSobolevHarmonicOn μ Q Ω (f i) := by
    simpa only [f,sub_eq_add_neg,neg_smul] using (hH i).add μ Q (hconst.smul μ Q (-c i))
  have hd (i : Fin n) : (fun x => SobolevSpace.toLp μ Q (f i) x-SobolevSpace.toLp μ Q (u i) x)
      =ᵐ[μ.restrict Ω] fun _ => -c i := by
    filter_upwards [hf i,hu i] with x hx hy
    simp only [hx,hy]
    ring
  refine ⟨U,fun i => boundedLocalVersion_bound μ Q (f i) C,?_,?_,?_⟩
  · intro i
    exact (hUf i).trans (hf i)
  · intro i
    exact (hfh i).congr_ae μ Q hΩ (hUf i)
  · intro i j
    exact (localGamma_pair_congr_ae μ Q (hUf i) (hUf j)).trans
      ((localGamma_pair_constant_shift μ Q (u i) (f i) (u j) (f j) (-c i) (-c j)
        (hd i) (hd j)).trans (hgram i j))

end RegularPointCoordinates

end

end OAI
