import OAI.MeasureTheory.Falconer.Estimates.PolicyPrefixLowpass
import OAI.MeasureTheory.Falconer.Fourier.PolicyJetData
import OAI.MeasureTheory.Falconer.Fourier.FourierBandBound

namespace OAI

/-! # The positive policy count from its actual Fourier bands -/

namespace Falconer
open Set MeasureTheory

namespace PolicyJetData
variable {m : ℕ}

def atFrequency (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) : PolicyJetData m :=
  { P with t := v, base_right := hv }

def positiveSuccessor (P : PolicyJetData m) (v : ℕ) (hv : v ≤ P.t₀) (i : ℕ) : PolicyJetData m :=
  { P with
    a₀ := P.a
    t₀ := v
    t := v
    i := i
    base_left := le_rfl
    base_right := le_rfl
    base_N := hv.trans P.base_N
    separated := by
      intro b hb
      apply P.separated b
      obtain ⟨hb,ha⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr
        ⟨PlanarFalconer.policyDescriptorList_mono P.policy P.base_left hv hb,ha⟩ }

theorem root_list (P : PolicyJetData m) (hleft : P.a₀ = P.a) (hright : P.t₀ = P.t) :
    P.list = PlanarFalconer.policyDescriptorList P.policy P.N P.q P.a P.t := by
  unfold list PlanarFalconer.remainingPolicyDescriptors
  rw [hleft,hright]
  apply Finset.filter_eq_self.mpr
  intro b hb
  exact PlanarFalconer.policyDescriptor_anchor_gt_left P.policy P.q_pos hb

noncomputable def positiveCount (P : PolicyJetData m) (w₀ : Sphere (m+3)) : ℝ :=
  (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
    P.N P.σ P.J P.i P.q P.a P.t P.X P.Y).toReal

noncomputable def maskedLaw (P : PolicyJetData m) (w₀ : Sphere (m+3)) : Measure ℝ :=
  maskedCellDistance w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a P.list
    P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)

end PolicyJetData

theorem exists_policy_positive_band_bound (m : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ,
      ∀ P : PolicyJetData m, P.σ = σ → P.J = J → N₀ ≤ P.N →
      P.a₀ = P.a → P.t₀ = P.t → P.a ≤ P.t →
      (∀ b ∈ P.list, ∀ w : Sphere (m+3), ∃ c ∈ P.masks b,
        dist w c ≤ descriptorMaskRadius P.N P.σ b/2) →
      125*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side ≤
        ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ →
      ‖(P.Q.descendant P.X).center-(P.Q.descendant P.Y).center‖ ≤
        2000*(((m+3:ℕ):ℝ)+1)*(P.Q.descendant P.X).side →
      ∀ (w₀ : Sphere (m+3)) (D H : ℝ), 0 ≤ D → 0 ≤ H →
      (∀ v ∈ Finset.Ioc P.a P.t, σ*P.N ≤ (P.t:ℝ)-v →
        (positiveCollisionCount w₀ P.Q P.ρ (fun u => P.profile (u/P.N)) P.policy
          P.N P.σ P.J (P.i+1) P.q P.a v P.X P.Y).toReal ≤ D) →
      (∀ v ∈ Finset.Ioc P.a P.t, (P.t:ℝ)-v < σ*P.N →
        (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^((v:ℝ)+1)),
          ‖charFun (P.maskedLaw w₀) r‖^2) ≤ H) →
      P.positiveCount w₀ ≤ C*(1+2*(P.N:ℝ))*
        (((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam)+D+H) := by
  obtain ⟨C₀,hC₀,N₀,hfourier⟩ := uniform_policy_prefix_lowpass (m+3) (by omega) hσ hJ
  let c : ℝ := 32*PlanarFalconer.binKernelConstant.toReal
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C₀*(1+c),by positivity,N₀,?_⟩
  intro P hσP hJP hN hleft hright hat hcover hlo hhi w₀ D H hD hH hlow hhigh
  let := P.regular.probability
  have htN : P.t ≤ P.N := by rw [← hright]; exact P.base_N
  have hlist := P.root_list hleft hright
  have hcover' : ∀ b ∈ PlanarFalconer.policyDescriptorList P.policy P.N P.q P.a P.t,
      ∀ w : Sphere (m+3), ∃ c ∈ P.masks b, dist w c ≤ descriptorMaskRadius P.N P.σ b/2 := by
    simpa only [← hlist] using hcover
  have hsep : ∀ᵐ z ∂(P.ρ.restrict (P.Q.descendant P.X).carrier).prod
      (P.ρ.restrict (P.Q.descendant P.Y).carrier), 1 ≤ dist z.1 z.2*(2:ℝ)^P.a := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem (P.Q.descendant P.X).measurable),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem (P.Q.descendant P.Y).measurable)] with z hx hy
    have hb := separated_cell_distance_bounds P.Q P.unit P.a P.X P.Y
      P.X_length P.Y_length hlo hhi hx hy
    exact (by have := Nat.cast_nonneg (α := ℝ) (m+3); nlinarith :
      (1:ℝ) ≤ 100*(((m+3:ℕ):ℝ)+1)).trans hb.1
  let := maskedCellDistance_finite w₀ P.Q P.ρ P.profile P.N P.σ P.J P.i P.a
    P.list P.masks hcover (by omega) (by norm_num : (0:ℝ) < 1)
    (P.Q.descendant P.X) (P.Q.descendant P.Y) hsep
  have hlaw : P.maskedLaw w₀ = policyMaskedDistance w₀ P.Q P.ρ P.profile P.policy
      P.N P.σ P.J P.i P.q P.a P.t P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y) := by
    unfold PolicyJetData.maskedLaw policyMaskedDistance
    rw [hlist]
  let : IsFiniteMeasure (P.maskedLaw w₀) := by unfold PolicyJetData.maskedLaw; infer_instance
  let : IsFiniteMeasure (policyMaskedDistance w₀ P.Q P.ρ P.profile P.policy
      P.N P.σ P.J P.i P.q P.a P.t P.masks (P.Q.descendant P.X) (P.Q.descendant P.Y)) := by
    rw [← hlaw]; infer_instance
  let F : ℝ := ((2:ℝ)^P.N)^(4*(((m+3:ℕ):ℝ)+1)*P.lam)
  let B : ℝ := F+D+H
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFB : F ≤ B := by dsimp [B]; linarith
  have hDB : D ≤ B := by dsimp [B]; linarith
  have hHB : H ≤ B := by dsimp [B]; linarith
  have hbase := policy_masked_distance_low_frequency w₀ P.Q P.ρ P.regular P.policy
    P.σ P.J P.i P.q P.a P.t (hat.trans htN) hat P.masks hcover' (by omega)
    P.X P.Y P.X_length P.Y_length hsep
  have hbase' : (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc (-((2:ℝ)^P.a)) ((2:ℝ)^P.a),
      ‖charFun (P.maskedLaw w₀) r‖^2) ≤ (1+c)*B := by
    rw [hlaw]
    have hp : (2:ℝ)^(-(P.a:ℝ)) = 1/(2:ℝ)^P.a := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    rw [hp]
    exact hbase.trans (by change c*F ≤ _; nlinarith [mul_nonneg hc (sub_nonneg.mpr hFB)])
  have hshell : ∀ v ∈ Finset.Ioc P.a P.t,
      (2:ℝ)^(-(P.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v),
        ‖charFun (P.maskedLaw w₀) r‖^2) ≤ (1+c)*B := by
    intro v hv
    by_cases hgap : σ*P.N ≤ (P.t:ℝ)-v
    · have hb := policy_masked_distance_low_band w₀ P.Q P.ρ P.profile P.policy P.N P.σ
        P.J P.i P.q P.a P.t v (Finset.mem_Ioc.mp hv).1.le (Finset.mem_Ioc.mp hv).2
        P.masks hcover' (by omega) P.X P.Y hsep
      have hsmall := mul_le_mul_of_nonneg_left (PlanarFalconer.fourier_shell_le_band (P.maskedLaw w₀) v)
        (show 0 ≤ (2:ℝ)^(-(P.a:ℝ)) by positivity)
      have hp : (2:ℝ)^(-(P.a:ℝ)) = 1/(2:ℝ)^P.a := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
      rw [hlaw,hp] at hsmall
      have hb' : _ ≤ (1+c)*B := (hsmall.trans hb).trans (by
        have hh := hlow v hv hgap
        change c*_ ≤ (1+c)*B
        nlinarith [mul_nonneg hc (sub_nonneg.mpr (hh.trans hDB))])
      simpa only [hlaw,hp] using hb'
    · exact (mul_le_mul_of_nonneg_left (PlanarFalconer.fourier_shell_le_expanded (P.maskedLaw w₀) v)
        (show 0 ≤ (2:ℝ)^(-(P.a:ℝ)) by positivity)).trans
        ((hhigh v hv (lt_of_not_ge hgap)).trans (by nlinarith [mul_nonneg hc hB]))
  have hband := PlanarFalconer.finite_fourier_band_bound (P.maskedLaw w₀) hat htN
    (mul_nonneg (by positivity) hB) hbase' hshell
  have hf := hfourier P.N hN w₀ P.Q P.unit P.ρ P.profile P.policy P.q P.i P.a P.t
    P.q_pos htN hat P.masks (by simpa only [hσP] using hcover') P.X P.Y
    P.X_length P.Y_length hlo hhi
  rw [← hσP,← hJP,← hlaw] at hf
  have hp : C₀/(2:ℝ)^P.a = C₀*(2:ℝ)^(-(P.a:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv]
  rw [hp,mul_assoc] at hf
  apply hf.trans
  convert mul_le_mul_of_nonneg_left hband hC₀.le using 1
  dsimp [B,F]
  ring

end Falconer

end OAI
