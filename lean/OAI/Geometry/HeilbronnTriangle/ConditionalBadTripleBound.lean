import OAI.Geometry.HeilbronnTriangle.OrbitSampling
import OAI.Geometry.HeilbronnTriangle.PrimePowerData
import OAI.Geometry.HeilbronnTriangle.OrbitRowLattice
import OAI.Geometry.HeilbronnTriangle.LiftedBadEvent

namespace OAI


noncomputable section

namespace Problem355.ConditionalBadTripleBound

open OrbitSampling IntegerSampling LiftingProbability

def orbitTransposeEquiv (h : ℕ) (C : Fin 3 → Fin 3 → ZMod h) :
    MulAction.orbit (MainGroup h) C ≃ Section04Orbit.slOrbit (Matrix.transpose C) where
  toFun A := ⟨Matrix.transpose A.val, by
    obtain ⟨G, hG⟩ := A.property
    exact ⟨G, by rw [← hG, sl_action_transpose]⟩⟩
  invFun A := ⟨Matrix.transpose A.val, by
    obtain ⟨G, hG⟩ := A.property
    refine ⟨G, ?_⟩
    have ht := (sl_action_transpose h G C).trans hG
    exact funext fun i => funext fun j => congrFun (congrFun ht j) i⟩
  left_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _
  right_inv A := by apply Subtype.ext; exact Matrix.transpose_transpose _

theorem card_sampling_orbit (h : ℕ) [NeZero h]
    (C : Fin 3 → Fin 3 → ZMod h) :
    (orbitFinset (MainGroup h) C).card =
      Nat.card (Section04Orbit.slOrbit (Matrix.transpose C)) := by
  rw [card_orbitFinset]
  exact Nat.card_congr (orbitTransposeEquiv h C)

theorem sampling_orbit_lower_bound {p k : ℕ} [NeZero (p ^ k)]
    (hp : p.Prime) (hk : 0 < k)
    (C : Fin 3 → Fin 3 → ZMod (p ^ k))
    (d : PrimePowerData p k (Matrix.transpose C)) :
    (21 / 64 : ℝ) * ((p ^ k : ℕ) : ℝ) ^ 8 /
      (((p ^ d.b : ℕ) : ℝ) ^ 3 * ((p ^ d.e : ℕ) : ℝ) ^ 2) ≤
        ((orbitFinset (MainGroup (p ^ k)) C).card : ℝ) := by
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [card_sampling_orbit]
  exact d.orbit_lower_bound hp hk

theorem integral_det_residue (h q L : ℕ) [NeZero h]
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod h)
    (x : Fin 3 → Box (L * (h * q)) 3 shift)
    (hx : (fun i => residue h (x i)) ∈ orbitFinset (MainGroup h) C) :
    ((integralMatrix x).det : ZMod h) = (Matrix.transpose C).det := by
  obtain ⟨G, hG⟩ := integralMatrix_reduction_of_mem_orbit h q L shift C x hx
  apply OrbitRowLattice.det_cast_eq_of_reduction_mem_slOrbit h (Matrix.transpose C)
    (integralMatrix x)
  exact ⟨G, hG.symm⟩

theorem conditional_small_mass_le {Ω : Type*} [Fintype Ω]
    {p k : ℕ} [NeZero (p ^ k)] (hp : p.Prime) (hk : 0 < k)
    (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (shift : Fin 3 → ℤ) (C : Fin 3 → Fin 3 → ZMod (p ^ k))
    (d : PrimePowerData p k (Matrix.transpose C))
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q))
    (hw : ∀ ω, 0 ≤ w ω)
    (S : Finset (Fin 3 → Box (L * (p ^ k * q)) 3 shift))
    {τ : ℤ} (hwidth : 2 * τ < (p ^ k : ℕ))
    {K R : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ t : ℤ, |t| ≤ τ →
      (∑ x ∈ (S.filter (fun x =>
        (fun i => residue (p ^ k) (x i)) ∈ orbitFinset (MainGroup (p ^ k)) C)).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (p ^ k * q) : ℕ) : ℝ) ^ 6 /
            (((p ^ d.b : ℕ) : ℝ) ^ 2 * ((p ^ d.e : ℕ) : ℝ) ^ 2)) :
    (∑ x ∈ S.filter (fun x => |(integralMatrix x).det| ≤ τ),
      liftedMass (fun x i => residue (p ^ k) (x i))
        (fun x i => residue q (x i)) (orbitFinset (MainGroup (p ^ k)) C)
        w V s (L ^ 9) x) ≤
      (K / (21 / 64)) * R ^ 2 * ((p ^ k : ℕ) : ℝ) * ((p ^ d.b : ℕ) : ℝ) /
        ((L * (p ^ k * q) : ℕ) : ℝ) ^ 3 := by
  classical
  let : NeZero (p ^ k) := ⟨pow_ne_zero _ hp.ne_zero⟩
  exact lifted_small_event_le (D := ((p ^ d.b : ℕ) : ℝ))
    (E := ((p ^ d.e : ℕ) : ℝ))
    (fun x i => residue (p ^ k) (x i)) (fun x i => residue q (x i))
    (fun x => (integralMatrix x).det)
    (orbitFinset (MainGroup (p ^ k)) C) (orbitFinset_nonempty C) w V
    s (p ^ k) q L hs (pow_pos hp.pos _) hq hL hw S hwidth
    (Matrix.transpose C).det
    (fun x _ hxo => integral_det_residue (p ^ k) q L shift C x hxo)
    (by exact_mod_cast pow_pos hp.pos d.b)
    (by exact_mod_cast pow_pos hp.pos d.e)
    (by norm_num) hK (sampling_orbit_lower_bound hp hk C d) hcount

end Problem355.ConditionalBadTripleBound

end

end OAI
