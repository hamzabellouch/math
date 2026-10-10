import OAI.Geometry.HeilbronnTriangle.ConditionalBadTripleBound
import OAI.Geometry.HeilbronnTriangle.DigitBadTripleAverage

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability DigitColumnLaw

def smallMass {Ω : Type*} [Fintype Ω]
    (h q L s : ℕ) [NeZero h] (shift : Fin 3 → ℤ)
    (C : Fin 3 → Fin 3 → ZMod h)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (S : Finset (Fin 3 → Box (L * (h * q)) 3 shift)) (τ : ℤ) : ℝ := by
  classical
  exact ∑ x ∈ S.filter (fun x => |(integralMatrix x).det| ≤ τ),
    liftedMass (fun x i => residue h (x i)) (fun x i => residue q (x i))
      (orbitFinset (MainGroup h) C) w V s (L ^ 9) x

theorem averaged_small_mass_le
    {Λ X Ω : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]
    [Fintype X] [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (shift : Fin 3 → ℤ)
    (c : Latent Λ X k → Fin 3 → ZMod (p ^ k))
    (d : (z : Fin 3 → Latent Λ X k) →
      PrimePowerData p k (Matrix.transpose (fun j => c (z j))))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω)
    (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
    {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hmoment : ∀ labels : Fin 3 → Λ,
      (∑ f : Array X k, uniformWeight (Array X k) f *
        ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ)) ≤ 2)
    (hseparate : ∀ z : Fin 3 → Latent Λ X k,
      (z 0).1 ≠ (z 1).1 → (z 0).1 ≠ (z 2).1 → (z 1).1 ≠ (z 2).1 →
      ∀ x ∈ S, (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)) →
          τ < |(integralMatrix x).det|)
    (hcount : ∀ z : Fin 3 → Latent Λ X k, ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x => (fun i => residue (p ^ k) (x i)) ∈
        orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ (d z).b : ℕ) : ℝ) ^ 2 * ((p ^ (d z).e : ℕ) : ℝ) ^ 2)) :
    (∑ z : Fin 3 → Latent Λ X k,
      ConditionalSamples.productWeight (uniformWeight (Latent Λ X k)) z *
        smallMass (p ^ k) q L s shift (fun j => c (z j)) w V S τ) ≤
      6 * (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
        (((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 * (Fintype.card Λ : ℝ)) := by
  classical
  let A : ℝ := (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) /
    ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have h := bad_triple_expectation_le
    (fun labels f => ((p ^ (d (tripleEquiv.symm (labels, f))).b : ℕ) : ℝ))
    (fun z => smallMass (p ^ k) q L s shift (fun j => c (z j)) w V S τ)
    A hA hmoment (by
      intro labels f
      have hb := conditional_small_mass_le hp hk q L s hq hL hs shift
        (fun j => c ((tripleEquiv.symm (labels, f)) j))
        (d (tripleEquiv.symm (labels, f))) w V hw S hwidth hK
        (hcount (tripleEquiv.symm (labels, f)))
      unfold smallMass
      convert hb using 1; dsimp [A]; ring)
    (by
      intro z h01 h02 h12
      unfold smallMass
      exact lifted_small_event_eq_zero
        (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
        (fun x => (integralMatrix x).det)
        (orbitFinset (MainGroup (p ^ k)) (fun j => c (z j)))
        w V s (L ^ 9) S τ (hseparate z h01 h02 h12))
  convert h using 1; dsimp [A]; ring

end Problem355.ConditionalBadTripleBound

end

end OAI
