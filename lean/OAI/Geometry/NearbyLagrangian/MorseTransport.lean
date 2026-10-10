import Mathlib
import OAI.Geometry.NearbyLagrangian.TransportCutoffs
import OAI.Geometry.NearbyLagrangian.MixedGraphs

namespace OAI

/-! Smooth transport of regular Morse generating families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Filter Set
open scoped Topology ContDiff InnerProductSpace

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiffAt_baseGradient {F : E × W → ℝ} {q : E × W}
    (hF : ContDiffAt ℝ ∞ F q) :
    ContDiffAt ℝ ∞ (fun v => baseGradient F v.1 v.2) q := by
  have hd := hF.fderiv_right (m := ∞) (by simp)
  have hb : ContDiffAt ℝ ∞ (fun v => baseDifferential F v.1 v.2) q :=
    (((compL ℝ E (E × W) ℝ).flip (inl ℝ E W)).contDiff.contDiffAt.comp q hd)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contDiffAt.comp q hb

namespace StepData

variable (S : StepData (E := E) (W := W))

lemma contDiffAt_carry (hψ : ContDiff ℝ ∞ (S.ψ : E × E → E × E))
    {q : E × W} (hU : q.1 ∈ S.U) : ContDiffAt ℝ ∞ S.carry q := by
  have ha := contDiffAt_baseGradient (S.smooth_F _ hU q.2)
  have hX : ContDiffAt ℝ ∞ (fun r : E × W => (S.ψ (r.1,baseGradient S.F r.1 r.2)).1) q :=
    ((hψ.contDiffAt (x := (q.1,baseGradient S.F q.1 q.2))).comp q
      (contDiffAt_fst.prodMk ha)).fst
  exact hX.prodMk (contDiffAt_snd.prodMk ((contDiffAt_fst.sub hX).prodMk
    ((S.smooth_ζ.contDiffAt.comp q hX).smul ha)))

omit [CompleteSpace E] in
lemma contDiff_recover : ContDiff ℝ ∞ S.recover := by
  have hk : ContDiff ℝ ∞ (fun r : E × (W × (E × E)) => S.κ r.1 r.2.1 r.2.2.1) :=
    ((S.smooth_ζ.comp contDiff_fst).mul (S.smooth_β.comp contDiff_snd.snd.fst)).mul
      (S.smooth_χ.comp contDiff_snd.fst)
  exact (contDiff_fst.add (hk.smul contDiff_snd.snd.fst)).prodMk contDiff_snd.fst

omit [CompleteSpace E] in
lemma contDiffAt_totalPhase {q : E × (W × (E × E))} (hU : q.1 ∈ S.U) :
    ContDiffAt ℝ ∞ (totalPhase S.F S.σ S.κ) q := by
  have hk : ContDiffAt ℝ ∞ (fun r : E × (W × (E × E)) => S.κ r.1 r.2.1 r.2.2.1) q :=
    (((S.smooth_ζ.comp contDiff_fst).mul (S.smooth_β.comp contDiff_snd.snd.fst)).mul
      (S.smooth_χ.comp contDiff_snd.fst)).contDiffAt
  have hshift : ContDiffAt ℝ ∞ (fun r : E × (W × (E × E)) =>
      (r.1+S.κ r.1 r.2.1 r.2.2.1 • r.2.2.1,r.2.1)) q :=
    (contDiffAt_fst.add (hk.smul contDiffAt_snd.snd.fst)).prodMk contDiffAt_snd.fst
  exact (((S.smooth_F _ (S.shift_mem _ hU _ _) _).comp q hshift).add
    (S.smooth_σ.contDiffAt.comp q (contDiffAt_fst.prodMk contDiffAt_snd.snd.snd))).sub
      (contDiffAt_snd.snd.fst.inner ℝ contDiffAt_snd.snd.snd)

end StepData
end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport

open Set Filter ContinuousLinearMap
open scoped ContDiff Topology NNReal

variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem exists_hamiltonian_step_data
    {U : Set E} (hU : IsOpen U) {K : Set (E × E)} (hK : IsCompact K)
    (hKU : ∀ z ∈ K, z.1 ∈ U)
    (F : E × W → ℝ) {R c C δ : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hF : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w))
    (hbase : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → ‖baseDifferential F x w‖ ≤ C * ‖w‖^2)
    (hvert : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖verticalDifferential F x w‖)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζr : ∀ x, ζ x ∈ Icc (0:ℝ) 1)
    (hζ1 : ∀ x ∈ Prod.fst '' K, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    (φ : ℝ × (E × E) → E × E) (H : ℝ × (E × E) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H)
    (hHam : ∀ t z (w : E × E),
      inner ℝ (flowVelocity φ (t,z)).2 w.1 - inner ℝ w.2 (flowVelocity φ (t,z)).1 =
        - fderiv ℝ H (t,φ (t,z)) (0,w))
    (a b : ℝ) (hi : ∀ z, φ (a,z) = z)
    (ψ : (E × E) ≃ₜ (E × E)) (hψ : ∀ z, ψ z = φ (b,z))
    (hst : ∀ z ∉ K, ∀ t, φ (t,z) = z)
    (hHK : ∀ z ∉ K, ∀ t, H (t,z) = 0)
    (η : ℝ≥0) (hη : η < 1)
    (hsmall : ∀ z, ‖fderiv ℝ (fun x => φ (b,x)) z - ContinuousLinearMap.id ℝ (E × E)‖ ≤ η)
    (hdis : ∀ z, ‖ψ z-z‖ < δ) :
    ∃ S : StepData (E := E) (W := W), S.U = U ∧ S.F = F ∧ S.ψ = ψ ∧
      S.ζ = ζ ∧ S.δ₀ = δ ∧ HasCompactSupport S.β ∧ HasCompactSupport S.χ ∧
      HasCompactSupport S.σ ∧ ContDiff ℝ ∞ (S.ψ : E × E → E × E) ∧
      ∀ X p, Function.Surjective (ContinuousLinearMap.id ℝ E +
        (fderiv ℝ (mixedDisplacement S.σ) (X,p)).comp (inl ℝ E E)) := by
  obtain ⟨e,σ,he,hes,hjs,hσ,hσc,hd,hσ0,hσp,hg,hgo⟩ :=
    exists_controlled_mixed_generator φ H hφ hH hHam a b hi ψ hψ hK hst hHK η hη hsmall hdis
  have hψ0 : ∀ z ∉ K, ψ z = z := fun z hz => (hψ z).trans (hst z hz b)
  obtain ⟨S,hSU,hSF,hSσ,hSψ,hSζ,hSδ,hSβ,hSχ⟩ := exists_stepData_of_mixed hU
    (hK.image continuous_fst).isClosed F σ ψ hR hc hC hδ hF hσ hζ hζr hζ1 hbuf
    hσ0 hσp hbase hvert (fun x p => base_mem_iff_of_compact_support ψ.injective hKU hψ0 x p)
    (fun x p X _ => hg x p X) (fun x p _ => hgo x p)
  refine ⟨S,hSU,hSF,hSψ,hSζ,hSδ,hSβ,hSχ,?_,?_,?_⟩
  · rwa [hSσ]
  · rw [hSψ, show (ψ : E × E → E × E) = (fun z => φ (b,z)) from funext hψ]
    exact hφ.comp (contDiff_const.prodMk contDiff_id)
  · intro X p
    rw [hSσ]
    exact mixed_twist_surjective e he hes hjs hd (X,p)

namespace StepData

variable (S : StepData (E := E) (W := W))

omit [FiniteDimensional ℝ W] in

theorem transported_morse_family
    (hold : ∀ x ∈ S.U, ∀ w, verticalDifferential S.F x w = 0 →
      Function.Surjective (fderiv ℝ (fun v : E × W => verticalDifferential S.F v.1 v.2) (x,w)))
    (htwist : ∀ X p, Function.Surjective (ContinuousLinearMap.id ℝ E +
      (fderiv ℝ (mixedDisplacement S.σ) (X,p)).comp (inl ℝ E E)))
    (q : E × (W × (E × E))) (hU : q.1 ∈ S.U)
    (hq : fiberDifferential (totalPhase S.F S.σ S.κ) q = 0) :
    Function.Surjective (fderiv ℝ (fiberDifferential (totalPhase S.F S.σ S.κ)) q) := by
  have hd := ((S.contDiffAt_totalPhase hU).differentiableAt (by simp)).hasFDerivAt.comp q.2
    (f := fun v => (q.1,v)) (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2)
  have hc : IsShiftedCritical S.F S.σ S.κ q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    change fderiv ℝ (fun v => totalPhase S.F S.σ S.κ (q.1,v)) q.2 = 0
    simpa only [Function.comp_def] using hd.fderiv.trans hq
  exact S.regular_at_newCritical_of_twist hold (fun X _ p => htwist X p) ⟨q,hU,hc⟩

end StepData
end NearbyLagrangian.Transport

end

end OAI
