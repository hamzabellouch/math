import OAI.Geometry.HeilbronnTriangle.AveragedBadTripleBound
import OAI.Geometry.HeilbronnTriangle.MainDigitLaw
import OAI.Geometry.HeilbronnTriangle.MainDigitObstruction

namespace OAI


noncomputable section

attribute [local irreducible] Problem355.heilbronnT
  Problem355.heilbronnM

namespace Problem355.MainDigitLaw

open Parameters FiniteFieldLabels OrbitSampling IntegerSampling LiftingProbability
open ConditionalBadTripleBound

variable {r : ℕ} [Fact r.Prime]
variable (D : PrimeParameterData heilbronnK r)

local instance mainModulusNeZero : NeZero (D.B ^ heilbronnK) :=
  ⟨pow_ne_zero _ D.base_prime.ne_zero⟩

def sampledSmith (z : Fin 3 → Latent r) :
    PrimePowerData D.B heilbronnK (Matrix.transpose (fun j => column D (z j))) :=
  smith D (DigitColumnLaw.tripleEquiv z).1 (DigitColumnLaw.tripleEquiv z).2

theorem sampled_small_det_forces_repeated_labels
    (z : Fin 3 → Latent r) (A : Matrix (Fin 3) (Fin 3) ℤ)
    (G : MainGroup (D.B ^ heilbronnK))
    (hA : A.map (Int.castRingHom (ZMod (D.B ^ heilbronnK))) =
      G.val * Matrix.transpose (fun j => column D (z j)))
    (hsmall : |A.det| ≤ (D.tau : ℤ)) :
    ∃ i j : Fin 3, i ≠ j ∧ (z i).1 = (z j).1 := by
  have hr : 2 < r := by
    have hk := D.two_le_k
    have hl := D.large_r
    nlinarith
  exact MainDigitObstruction.finite_small_det_forces_repeated_labels hr D
    (D.B ^ heilbronnK) rfl (fun j => (z j).1)
    (fun i j v => (digit D (z j).1 i v ((z j).2 i v)).val)
    (fun i j v => digit_le D (z j).1 i v ((z j).2 i v))
    (fun i j v => digit_residue D (z j).1 i v ((z j).2 i v))
    A G hA hsmall

theorem sampled_orbit_det_gt
    (q L : ℕ) (shift : Fin 3 → ℤ) (z : Fin 3 → Latent r)
    (h01 : (z 0).1 ≠ (z 1).1) (h02 : (z 0).1 ≠ (z 2).1)
    (h12 : (z 1).1 ≠ (z 2).1)
    (x : Fin 3 → Box (L * (D.B ^ heilbronnK * q)) 3 shift)
    (hx : (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
      orbitFinset (MainGroup (D.B ^ heilbronnK)) (fun j => column D (z j))) :
    (D.tau : ℤ) < |(integralMatrix x).det| := by
  by_contra hnot
  obtain ⟨G, hG⟩ := integralMatrix_reduction_of_mem_orbit
    (D.B ^ heilbronnK) q L shift (fun j => column D (z j)) x hx
  obtain ⟨i, j, hij, heq⟩ := sampled_small_det_forces_repeated_labels D z
    (integralMatrix x) G hG (le_of_not_gt hnot)
  have hinj : Function.Injective (fun j => (z j).1) := by
    intro a b hab
    fin_cases a <;> fin_cases b
    all_goals first
      | rfl
      | exact (h01 hab).elim
      | exact (h02 hab).elim
      | exact (h12 hab).elim
      | exact (h01 hab.symm).elim
      | exact (h02 hab.symm).elim
      | exact (h12 hab.symm).elim
  exact hij (hinj heq)

theorem averaged_small_mass_le_of_weighted_fibers
    [Fintype (Label r)] {Ω : Type*} [Fintype Ω]
    (q L s : ℕ) (hq : 0 < q) (hL : 0 < L) (hs : 0 < s)
    (shift : Fin 3 → ℤ)
    (w : Ω → ℝ) (V : Ω → Finset (Fin 3 → ZMod q)) (hw : ∀ ω, 0 ≤ w ω)
    (S : Finset (Fin 3 → Box (L * (D.B ^ heilbronnK * q)) 3 shift))
    {K R : ℝ} (hK : 0 ≤ K)
    (hcount : ∀ z : Fin 3 → Latent r, ∀ t : ℤ, |t| ≤ (D.tau : ℤ) →
      (∑ x ∈ (S.filter (fun x => (fun i => residue (D.B ^ heilbronnK) (x i)) ∈
        orbitFinset (MainGroup (D.B ^ heilbronnK)) (fun j => column D (z j)))).filter
          (fun x => (integralMatrix x).det = t),
        auxiliaryWeight q s w V (fun i => residue q (x i))) ≤
          K * R ^ 2 * ((L * (D.B ^ heilbronnK * q) : ℕ) : ℝ) ^ 6 /
            (((D.B ^ (sampledSmith D z).b : ℕ) : ℝ) ^ 2 *
              ((D.B ^ (sampledSmith D z).e : ℕ) : ℝ) ^ 2)) :
    (∑ z : Fin 3 → Latent r,
      ConditionalSamples.productWeight (DigitColumnLaw.uniformWeight (Latent r)) z *
        smallMass (D.B ^ heilbronnK) q L s shift (fun j => column D (z j)) w V S D.tau) ≤
      6 * (K / (21 / 64)) * R ^ 2 * ((D.B ^ heilbronnK : ℕ) : ℝ) /
        (((L * (D.B ^ heilbronnK * q) : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 41) := by
  classical
  have hwidth : 2 * (D.tau : ℤ) < (D.B ^ heilbronnK : ℕ) := by
    exact_mod_cast D.twice_tau_lt_h
  have hm : ∀ labels : Fin 3 → Label r,
      (∑ f : Array r, DigitColumnLaw.uniformWeight (Array r) f *
        ((D.B ^ (sampledSmith D (DigitColumnLaw.tripleEquiv.symm (labels, f))).b : ℕ) : ℝ))
        ≤ 2 := by
    intro labels
    change (∑ f : Array r, DigitColumnLaw.uniformWeight (Array r) f *
      ((D.B ^ (smith D labels f).b : ℕ) : ℝ)) ≤ 2
    simpa only [Nat.cast_pow] using conditional_moment D labels
  have hb := averaged_small_mass_le D.base_prime heilbronnK_pos q L s hq hL hs shift
    (column D) (sampledSmith D) w V hw S hwidth hK hm
    (fun z h01 h02 h12 x _ hx => sampled_orbit_det_gt D q L shift z h01 h02 h12 x hx)
    hcount
  have hcard : Fintype.card (Label r) = r ^ 41 := by
    rw [← Nat.card_eq_fintype_card, card_label]
    rfl
  have hcardR : (Fintype.card (Label r) : ℝ) = (r : ℝ) ^ 41 := by
    exact_mod_cast hcard
  rw [hcardR] at hb
  exact hb

end Problem355.MainDigitLaw

end

end OAI
