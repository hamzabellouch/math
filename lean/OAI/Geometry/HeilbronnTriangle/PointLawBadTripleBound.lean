import OAI.Geometry.HeilbronnTriangle.IntegerPointLawTriples
import OAI.Geometry.HeilbronnTriangle.AveragedBadTripleBound

namespace OAI


noncomputable section

namespace Problem355.IntegerPointLaw

open IntegerSampling ConditionalSamples ParameterSampling
open ConditionalBadTripleBound DigitColumnLaw OrbitSampling LiftingProbability
attribute [local instance] Classical.propDecidable

def projectedDistinctTriples (N : ℕ) :
    Finset (Fin 3 → Box N 3 (samplingShift N)) := by
  classical
  exact Finset.univ.filter fun x =>
    project (x 0) ≠ project (x 1) ∧ project (x 0) ≠ project (x 2) ∧
      project (x 1) ≠ project (x 2)

theorem badDeterminantEvent_filter (N : ℕ) (τ : ℤ) :
    Finset.univ.filter (badDeterminantEvent (N := N) τ) =
      (projectedDistinctTriples N).filter
        (fun x => |(OrbitSampling.integralMatrix x).det| ≤ τ) := by
  classical
  ext x
  simp only [projectedDistinctTriples, Finset.mem_filter, Finset.mem_univ,
    true_and, badDeterminantEvent, and_assoc]

theorem ofSpecialLinear_tripleProbability_le_smallMass {Ω D : Type}
    [Fintype Ω] [Fintype D]
    (h q L s : ℕ) [NeZero h] [NeZero q]
    (hc : h.Coprime q) (hL : 0 < L) (hs : 0 < s)
    (w : Ω → ℝ) (p : D → ℝ) (c : D → Fin 3 → ZMod h)
    (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hp : ∀ d, 0 ≤ p d) (hpsum : ∑ d, p d = 1)
    (hV : ∀ ω, (V ω).card = s) {τ : ℤ} (hτ : 0 ≤ τ) :
    (ofSpecialLinear h q L s hc hL hs w p c V hw hwsum hp hpsum hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (h * q) : ℕ) : ℝ) ^ 3)) ≤
      ∑ z : Fin 3 → D, productWeight p z *
        smallMass h q L s (samplingShift (L * (h * q))) (fun j => c (z j))
          w V (projectedDistinctTriples (L * (h * q))) τ := by
  classical
  have hbound := ofSpecialLinear_tripleProbability_le_badDeterminant
    h q L s hc hL hs w p c V hw hwsum hp hpsum hV hτ
  simpa only [badDeterminantEvent_filter, smallMass] using hbound

theorem ofSpecialLinear_tripleProbability_le
    {Λ X Ω : Type} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    [Fintype X] [Nonempty X] [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) [NeZero q] (hc : (p ^ k).Coprime q) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (c : Latent Λ X k → Fin 3 → ZMod (p ^ k))
    (d : (z : Fin 3 → Latent Λ X k) →
      PrimePowerData p k (Matrix.transpose (fun j => c (z j))))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω) (hwsum : ∑ ω, w ω = 1)
    (hV : ∀ ω, (V ω).card = s)
    {τ : ℤ} (hτ : 0 ≤ τ) (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hmoment : ∀ labels : Fin 3 → Λ,
      (∑ f : Array X k, uniformWeight (Array X k) f *
        ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
    (hseparate : ∀ z : Fin 3 → Latent Λ X k,
      (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
      ∀ x ∈ projectedDistinctTriples (L * (p ^ k * q)), (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)) →
          τ < |(integralMatrix x).det|)
    (hcount : ∀ z : Fin 3 → Latent Λ X k, ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ ((projectedDistinctTriples (L * (p ^ k * q))).filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
    (ofSpecialLinear (p ^ k) q L s hc hL hs w
      (uniformWeight (Latent Λ X k)) c V hw hwsum
      (uniformWeight_nonneg _) (sum_uniformWeight _) hV).tripleProbability
      ((τ : ℝ) / (16 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3)) ≤
      6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
        (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
  classical
  apply le_trans (ofSpecialLinear_tripleProbability_le_smallMass
    (p ^ k) q L s hc hL hs w (uniformWeight (Latent Λ X k)) c V
    hw hwsum (uniformWeight_nonneg _) (sum_uniformWeight _) hV hτ)
  exact averaged_small_mass_le hp hk q L s hq hL hs
    (samplingShift (L * (p ^ k * q))) c d w V hw
    (projectedDistinctTriples (L * (p ^ k * q))) hwidth hK
    hmoment hseparate hcount

end Problem355.IntegerPointLaw

end

end OAI
