import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.SelectedScreenedProfileBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierActualInitializationBarrier
import OAI.Analysis.CoulombIonization.Localization.ActualPointInverseBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierChargeBound

namespace OAI

noncomputable section

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

lemma originalQueryField_eq_nuclear_mean {N K : ℕ} (F : fermionGraph N)
    (Z lam r : ℝ) (j : ℕ) (c r₀ s : ℝ) (q) (y : Space) :
    originalQueryField F Z lam r j c r₀ s q y =
      nuclearField Z y+meanFieldOffset lam
        (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c r₀ s canonicalRealPacket q) y := by
  unfold originalQueryField nuclearField meanFieldOffset
  have he : originalQueryDensity F r j c r₀ s q =
      originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
        j c r₀ s canonicalRealPacket q := rfl
  rw [he]
  ring

def actualInverseCap : ℝ := 100000^4*(16*(tfPatchCapConstant+3))

lemma actual_finite_barrier_from_good {N K : ℕ} {Z lam r s c A Q B C M lam1 lam2 e ξ hl hh : ℝ}
    (_hZ : 0 ≤ Z) (_hlam : 0 < lam) (hr : 0 < r) (hs : 0 < s) (_hs1 : s ≤ 1)
    (hrs : r ≤ s) (hc : 0 < c) (_hcL : c < (10*(100000:ℝ))⁻¹)
    (_hN : PriceMinimizes (energy Z) lam N) {F : fermionGraph N}
    (hFn : ‖fermionGraphValue N F‖^2 = 1)
    (_hFE : formEnergy Z (graphFormVector F) ≤ energy Z N+1)
    (cal : OutwardCalibration tfDensityCoefficient B C M lam1 lam2 e ξ hl hh)
    (hCC : actualInverseCap ≤ C) (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (hm : ∀ (j : ℕ) {v : ℝ}, r ≤ v → v ≤ s → ∀ y : Space, v ≤ ‖y‖ → ‖y‖ ≤ 2*v →
      (∫ q, (originalQueryDensity F r j c r s q y)^2 ∂physicalObservationLaw (graphRawLaw F) K)
        ≤ Q*v^(-12-6*masterExponent))
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ} {η : ℝ}
    (initial : IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r 0 c r s) Z tfDensityCoefficient B C r 2 η a p)
    (hgood : ∀ j : Fin K, (2:ℝ)^j.val*r ≤ s →
      ∃ G : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
        MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] G ∧
        (physicalObservationLaw (graphRawLaw F) K).real Gᶜ ≤ A*((2:ℝ)^j.val*r)^25 ∧
        ∀ q ∈ G, ∀ y : Space, (2:ℝ)^j.val*r ≤ ‖y‖ → ‖y‖ ≤ 4*M*((2:ℝ)^j.val*r) →
          InverseComparisonAt ‖y‖ (originalQueryField F Z lam r j c r s q y)
            (originalQueryDensity F r j c r s q y) tfDensityCoefficient hl hh ξ actualInverseCap)
    (J : ℕ) (hJK : J ≤ K) (hJs : (2:ℝ)^J*r ≤ s) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r J c r s) Z tfDensityCoefficient B C ((2:ℝ)^J*r) (max 2 M)
      (η+(32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*s^barrierErrorExponent) a' p' := by
  classical
  let := graphRawLaw_probability F hFn
  have hjr (j : ℕ) : r ≤ (2:ℝ)^j*r := le_mul_of_one_le_left hr.le (one_le_pow₀ (by norm_num))
  have hjs (j : ℕ) (hj : j < J) : (2:ℝ)^j*r ≤ s :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj.le) hr.le).trans hJs
  choose G hG hp hcomp using fun j : Fin J =>
    hgood ⟨j,Nat.lt_of_lt_of_le j.isLt hJK⟩ (hjs j j.isLt)
  let good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop :=
    fun j q => if hj : j < J then q ∈ G ⟨j,hj⟩ else True
  have hg (j) (hj : j < J) : MeasurableSet {q | good j q} := by
    simp only [good,dite_eq_left hj]
    exact (observationInformation_le _ _) _ (hG ⟨j,hj⟩)
  have hcomp' (j) (hj : j < J) (q) (hq : good j q) (y : Space)
      (hy : (2:ℝ)^j*r ≤ ‖y‖) (hy' : ‖y‖ < 4*M*((2:ℝ)^j*r)) :
      InverseComparisonAt ‖y‖
        (nuclearField Z y+meanFieldOffset lam
          (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
            j c r s canonicalRealPacket q) y)
        (originalMasterField (graphRawLaw F) (fun k : Fin K => dyadicObservationWidth r k)
          j c r s canonicalRealPacket q y)
        tfDensityCoefficient hl hh ξ actualInverseCap := by
    simp only [good,dite_eq_left hj] at hq
    have h := hcomp ⟨j,hj⟩ q hq y hy hy'.le
    rw [originalQueryField_eq_nuclear_mean] at h
    exact h
  obtain ⟨a',p',hnew⟩ := original_finite_barrier_iteration (graphRawLaw F)
    (fun k : Fin K => dyadicObservationWidth r k) hc hr hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact canonicalRealPacket_normalized
    cal hA hQ good hg initial
    (fun j hj q hq y hy hy' => by
      have h := (hcomp' j hj q hq y hy hy').1.trans hCC
      exact (le_div_iff₀ (pow_pos (hr.trans_le ((hjr j).trans hy)) 4)).mpr (by simpa [mul_comm] using h))
    hcomp'
    (fun j hj => by simpa only [good,dite_eq_left hj,Set.compl_def] using hp ⟨j,hj⟩)
    (fun j hj y hy hy' => hm j (hjr j) (hjs j hj) y hy hy'.le)
  refine ⟨a',p',hnew.mono_budget ?_⟩
  exact add_le_add le_rfl (sum_dyadic_errors_le (C := 32*Real.pi/3*Real.sqrt A*Real.sqrt Q)
    hr (by positivity) J hJs)

end
open MeasureTheory Filter Set Metric Laplacian
open scoped Topology
open CoulombAtom CoulombAnalysis

structure SelectedQuantumData (Z : ℝ) (N : ℕ) (s l τ B C R : ℝ) where
  radius : ℝ
  offset : TFSpace → ℝ
  density : TFSpace → ℝ
  error : TFSpace → ℝ
  radius_pos : 0 < radius
  radius_lower : 1/(2*l) ≤ radius/s
  radius_upper : radius/s ≤ l⁻¹
  continuous_offset : Continuous offset
  measurable_density : Measurable density
  integrable_density : Integrable density
  nonneg_density : ∀ x, 0 ≤ density x
  bounded_density : ∃ M ≥ 0, ∀ x, density x ≤ M
  mass_density : (∫ x, density x) = (N:ℝ)
  measurable_error : Measurable error
  integrable_error : Integrable error
  nonneg_error : ∀ x, 0 ≤ error x
  bounded_error : ∃ P ≥ 0, ∀ x, error x ≤ P
  support_error : ∀ x, radius < ‖x‖ → error x = 0
  mass_error : (∫ x, error x) ≤ 1
  weak : WeakNuclearLowerOn univ Z (fun x => nuclearField Z x+offset x)
    (fun x => innerSource radius density error x+
      outerCoefficient radius x*reaction tfDensityCoefficient (nuclearField Z x+offset x))
  lower : ∀ x, radius ≤ ‖x‖ → outerBarrier B radius x ≤ nuclearField Z x+offset x
  upper : ∀ x, radius ≤ ‖x‖ → nuclearField Z x+offset x ≤ C/‖x‖^4
  TF : ∀ x, radius/s ≤ ‖x‖ → ‖x‖ ≤ l →
    |tfDilation s density x-tfDensityCoefficient*(max (nuclearField (s^3*Z) x-
      tfPotential (tfDilation s density) x-1) 0)^(3/2:ℝ)| ≤ l⁻¹^8/‖x‖^6
  cap : ∀ x, radius/s ≤ ‖x‖ → ‖x‖ ≤ l →
    nuclearField (s^3*Z) x-tfPotential (tfDilation s density) x ≤ 1+actualInverseCap/‖x‖^4
  tail : (∫ x in {x : TFSpace | R < ‖x‖}, tfDilation s density x) ≤ τ

lemma SelectedQuantumData.opposite_charge {Z s l τ B C R : ℝ} {N : ℕ}
    (d : SelectedQuantumData Z N s l τ B C R) (hs : 0 < s) (hl : 0 < l)
    (hB : 0 ≤ B) (hRl : R ≤ l) :
    -(s^3+volume.real (closedBall (0:TFSpace) R)*(64*l⁻¹^2)+τ) ≤ s^3*(Z-(N:ℝ)) := by
  obtain ⟨M,hM,hMb⟩ := d.bounded_density
  obtain ⟨P,hP,hPb⟩ := d.bounded_error
  have hh := barrier_charge_bound (div_pos d.radius_pos hs) hl d.radius_lower
    tfDensityCoefficient_pos.le ((d.continuous_offset.comp (continuous_id.const_smul s)).const_mul (s^4))
    (tfDilation_measurable d.measurable_density) (tfDilation_integrable hs d.integrable_density)
    (mul_nonneg (pow_nonneg hs.le 6) hM) (tfDilation_nonneg d.nonneg_density)
    (fun x => mul_le_mul_of_nonneg_left (hMb _) (pow_nonneg hs.le 6))
    (tfDilation_measurable d.measurable_error) (tfDilation_integrable hs d.integrable_error)
    (mul_nonneg (pow_nonneg hs.le 6) hP) (tfDilation_nonneg d.nonneg_error)
    (fun x => mul_le_mul_of_nonneg_left (hPb _) (pow_nonneg hs.le 6))
    (barrier_weak_dilation hs d.weak)
    (S := R) (fun x hx hxR => by
      have ht := (abs_le.mp (d.TF x hx (hxR.trans hRl))).2
      linarith only [ht])
    (fun x hx => (show 0 ≤ (7*B/8)/‖x‖^4 by positivity).trans
      ((outerBarrier_bounds hB (div_pos d.radius_pos hs) hx).1.trans
        (scaled_barrier_lower hs d.lower x hx)))
    (scaled_barrier_upper hs d.upper)
  rw [tfDilation_mass hs,tfDilation_mass hs,d.mass_density] at hh
  have he := mul_le_mul_of_nonneg_left d.mass_error (pow_nonneg hs.le 3)
  nlinarith only [hh,he,d.tail]

end CoulombBarrier

end

end OAI
