import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolBilinear
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemoteSymbolInverse

namespace OAI

/-! Finite remote block reduction. Every iteration gains two powers, with
uniform bounds for all fixed logarithmic derivatives. -/

open Set Filter Topology
open scoped ContDiff
namespace DefocusingNLS

abbrev SpectralRemoteSuperOperator := SpectralRemoteOperator →L[ℝ] SpectralRemoteOperator

noncomputable def spectralRemoteReductionData
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator) :
    ℕ → (ℕ → ℝ → SpectralRemoteOperator) × (ℕ → ℝ → SpectralRemoteOperator)
  | 0 => (fun _ _ => 0, B)
  | m+1 =>
    let d := spectralRemoteReductionData Lambda B P K m
    let A := d.1
    let R := d.2
    let S := fun n t => K n t (R n t)
    let A' := fun n t => A n t+P (R n t)
    (A', fun n t => spectralRemoteReducedRemainder
      (Lambda n t) (A n t+R n t) (A' n t) (S n t) (deriv (S n) t))

theorem spectralRemote_finite_reduction
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (Lambda B : ℕ → ℝ → SpectralRemoteOperator)
    (P : SpectralRemoteSuperOperator) (K : ℕ → ℝ → SpectralRemoteSuperOperator)
    (hP : ∀ X, P (P X) = P X)
    (hB : HasUniformLogJetBound L 0 B)
    (hK : HasUniformLogJetBound L (-2) K)
    (hcomm : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ∀ X,
      Lambda n t*K n t X-K n t X*Lambda n t = P X-X)
    (m : ℕ) :
    let d := spectralRemoteReductionData Lambda B P K m
    HasUniformLogJetBound L 0 d.1 ∧
      HasUniformLogJetBound L (-2*(m : ℝ)) d.2 ∧
      (∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), P (d.1 n t) = d.1 n t) := by
  induction m with
  | zero =>
      refine ⟨HasUniformLogJetBound.zero 0,?_,?_⟩
      · simpa [spectralRemoteReductionData] using hB
      · exact Eventually.of_forall (fun _ _ _ => map_zero P)
  | succ m ih =>
      obtain ⟨hA,hR,hblock⟩ := ih
      let A := (spectralRemoteReductionData Lambda B P K m).1
      let R := (spectralRemoteReductionData Lambda B P K m).2
      let S := fun n t => K n t (R n t)
      let A' := fun n t => A n t+P (R n t)
      let B' := fun n t => A n t+R n t
      let R' := fun n t => spectralRemoteReducedRemainder
        (Lambda n t) (B' n t) (A' n t) (S n t) (deriv (S n) t)
      change HasUniformLogJetBound L 0 A' ∧
        HasUniformLogJetBound L (-2*(↑(m+1))) R' ∧ _
      have hneg : (-2 : ℝ)+(-2*(m : ℝ)) < 0 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have hS : HasUniformLogJetBound L (-2+(-2*(m : ℝ))) S := hK.apply hR
      have hR0 := hR.mono hL (by nlinarith [Nat.cast_nonneg (α := ℝ) m] : -2*(m : ℝ) ≤ 0)
      have hA' : HasUniformLogJetBound L 0 A' := hA.add (hR0.map P)
      have hB' : HasUniformLogJetBound L 0 B' := hA.add hR0
      have hc : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n),
          Lambda n t*S n t-S n t*Lambda n t = A' n t-B' n t := by
        filter_upwards [hcomm] with n hn
        intro t ht
        dsimp only [S,A',B']
        rw [hn t ht]
        abel
      refine ⟨hA',?_,?_⟩
      · have he : (-2 : ℝ)+(-2*(m : ℝ)) = -2*((m+1 : ℕ) : ℝ) := by
          push_cast; ring
        rw [← he]
        exact spectralRemote_uniform_reduction hL hneg Lambda B' A' S hB' hA' hS hc
      · filter_upwards [hblock] with n hn
        intro t ht
        change P (A n t+P (R n t)) = A n t+P (R n t)
        rw [map_add,hP,hn t ht]

end DefocusingNLS

end OAI
