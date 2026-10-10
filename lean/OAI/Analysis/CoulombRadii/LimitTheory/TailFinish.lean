import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PacketBridge
import OAI.Analysis.CoulombRadii.RandomFields.QuantumRetainedFamily
import OAI.Analysis.CoulombRadii.ThomasFermi.QuantumProfileDatum

namespace OAI

section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NeutralAtom
theorem Admissible.charge_tendsto {Zbar : ℝ → ℕ} {s : ℕ → ℝ} {N : ℕ → ℕ}
    (h : Admissible Zbar s N) : Tendsto (fun n => N n+1) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [h.1, h.2.1.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    h.2.2.2.eventually_ge_atTop (b : ℝ)] with n hsp hs1 hb
  have hs3 : s n^3 ≤ 1 := pow_le_one₀ hsp.le hs1.le
  have hz : (b : ℝ) ≤ (N n+1 : ℝ) := hb.trans
    (mul_le_of_le_one_right (by positivity) hs3)
  exact_mod_cast hz

theorem expected_exterior_of_raw_annuli (hcount : UniformGroundStateCountControl)
    (s : ℕ → ℝ) (N : ℕ → ℕ) (ψ : ∀ n, Wavefunction (N n+1))
    (hψ : ∀ n, IsNormalizedGroundState (N n+1) (ψ n))
    (hsp : ∀ n, 0 < s n) (hs : Tendsto s atTop (𝓝 0))
    (hN : Tendsto (fun n => N n+1) atTop atTop)
    (hann : ∀ a b, 0 < a → a < b →
      Tendsto (fun n => s n^3 * ∫ x,
        rawCount (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
        atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)))
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n => s n^3 * exteriorMass (ψ n) (a*s n))
      atTop (𝓝 ((81*Real.pi^2/2)/a^3)) := by
  obtain ⟨A,B,Z₀,hA,_hB,hbound⟩ := small_shell_bounds_of_count_control hcount
  have hint : ∀ n σ, MemLp (ψ n σ) 2 volume := fun n => (hψ n).choose_spec.1.2.2.1
  have hanti : ∀ n, IsAntisymmetric (ψ n) := fun n => (hψ n).choose_spec.1.1
  apply tails_converge_of_annuli (β := fun n => B*s n^3) (D := (8/7:ℝ)*A)
    (by positivity : 0 ≤ 81*Real.pi^2/2) ha
  · simpa using (hs.pow 3).const_mul B
  · exact fun n r => mul_nonneg (pow_nonneg (hsp n).le 3) (exteriorMass_nonneg (ψ n) _)
  · intro M hM
    filter_upwards [hN.eventually_ge_atTop Z₀] with n hn
    obtain ⟨hfar,hshell⟩ := hbound (N n) (ψ n) hn (hψ n)
    exact scaled_dyadic_tail_bound hA (exteriorMass_antitone (hint n)) hfar hshell (hsp n) hM
  · intro M haM
    have heq : (fun n => s n^3 * exteriorMass (ψ n) (a*s n) -
        s n^3 * exteriorMass (ψ n) (M*s n)) =
        (fun n => s n^3 * ∫ x,
          rawCount (spatialAnnulus (a*s n) (M*s n)) x ∂rawLaw (ψ n)) := by
      funext n
      rw [← mul_sub, exteriorMass_sub (hint n)
        (mul_le_mul_of_nonneg_right haM.le (hsp n).le), integral_rawLaw (hint n),
        rawExpectation_count_eq_density (hanti n) (hint n) (measurableSet_spatialAnnulus _ _)]
    simpa only [heq] using hann a M ha haM

end NeutralAtom
end

end
section
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

theorem quantum_profile_packet_limit
    (N : ℕ → ℕ) (ψ : ∀ n,Wavefunction (N n+1))
    (hψ : ∀ n,IsNormalizedGroundState (N n+1) (ψ n))
    [∀ n,IsProbabilityMeasure (rawLaw (ψ n))]
    {ε B C L M : ℝ} (hε : 0 < ε) (hB : 0 < B) (_ : 0 ≤ M)
    (s : ℕ → ℝ) (hsp : ∀ n,0 < s n) (hs : Tendsto s atTop (𝓝 0))
    (hN : Tendsto (fun n => N n+1) atTop atTop)
    (hr₀ : Tendsto (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)/s n) atTop (𝓝 0))
    (q : ℕ → ℕ) (hq : Tendsto q atTop atTop) (Cq : ℕ → ℝ)
    (d : ∀ n,QuantumProfileDatum (ψ n) ε B C L M (s n) (q n:ℝ) (Cq n))
    (hprob : ∀ n,Cq n*s n^25 ≤ (q n:ℝ)⁻¹)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Tendsto (fun n => s n^3 * ∫ x,packetMass Coulomb.unitWindow 1
      (initialAtomicRadius ε ((N n+1:ℕ):ℝ)) (s n) (spatialAnnulus (a*s n) (b*s n)) x ∂rawLaw (ψ n))
      atTop (𝓝 ((81*Real.pi^2/2)/a^3-(81*Real.pi^2/2)/b^3)) := by
  let Ω := fun n => ObservationSample (N n+1) ((d n).j+1)
  let P := fun n => observationLaw ((d n).j+1) (rawLaw (ψ n))
  let μ := fun n => profileDensity (ψ n) ε (s n) (d n).j
  let rs := fun n (k : Fin ((d n).j+1)) => profileRadius ε (N n) k.val
  let obs := fun n => tailObservation (n:=N n+1) (rs n) (d n).j
  let r := fun n => profileRadius ε (N n) (d n).j
  have hpr (n : ℕ) : 0 < initialAtomicRadius ε ((N n+1:ℕ):ℝ) := initialAtomicRadius_pos hε (by positivity)
  have hr (n : ℕ) : 0 < r n := mul_pos (hpr n) (by positivity)
  have hμi (n : ℕ) (o : Ω n) : Integrable (μ n o) :=
    mixturePacketDensity_integrable Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) _
  have hμp (n : ℕ) (o : Ω n) (x : Position) : 0 ≤ μ n o x :=
    conditionalPacketDensity_nonneg (P n) Prod.fst (obs n) Coulomb.unitWindow
      (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) _ x
  have hwindow : HasCompactSupport (Coulomb.unitWindow : Position → ℝ) := by
    apply HasCompactSupport.intro (K:=Metric.closedBall 0 1) (isCompact_closedBall _ _)
    intro x hx
    exact Coulomb.unitWindow_support x (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hx)
  have hμb (n : ℕ) : ∃ A : ℝ,∀ o : Ω n,∀ x : Position,μ n o x ≤ A := by
    obtain ⟨A,hA,HA⟩ := conditionalPacketDensity_bounded (P n) Prod.fst (obs n)
      Coulomb.unitWindow.continuous hwindow (by norm_num : (0:ℝ)<1) (hpr n) (hsp n)
    exact ⟨A,fun o => HA (obs n o)⟩
  choose A HA using hμb
  have hmass (n : ℕ) (o : Ω n) : (∫ x,μ n o x)=(N n+1:ℕ) := by
    exact conditionalPacketDensity_mass (P n) Prod.fst (obs n)
      Coulomb.unitWindow.continuous Coulomb.unitWindow_mass (by norm_num : (0:ℝ)<1) (hpr n) (hsp n) (obs n o)
  let f := physical_family_of_data P μ (fun n => N n+1) q s r B C L physicalSpatialCap
    hB physicalSpatialCap_pos.le hsp hr hs hq
    (fun n => by
      apply (le_div_iff₀ (hsp n)).mpr
      simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using (d n).low)
    (fun n => (div_le_iff₀ (hsp n)).mpr (by simpa only [div_eq_mul_inv,mul_comm] using (d n).high))
    hμi hμp A HA hmass (fun n => (d n).datum) (fun n => (d n).G)
    (fun n => (d n).valid) (fun n => (d n).band)
  have hbad : Tendsto (fun n => (P n).real (d n).Gᶜ) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => measureReal_nonneg)
      (fun n => (d n).failure.trans (add_le_add le_rfl (hprob n)))
    simpa using ((hs.pow 9).const_mul M).add (staged_error_tendsto_zero hq)
  obtain ⟨D,Z₀,hD,Hcount,_⟩ := physical_uniform_count_control
  apply expected_packet_annulus_from_retained P
    (fun n => MeasurableSpace.comap (obs n) inferInstance)
    (fun n => measurable_iff_comap_le.mp (measurable_tailObservation (rs n) (d n).j))
    (fun n => N n+1) (fun n => rawLaw (ψ n)) (fun _ => Prod.fst)
    (fun n => observationLaw_rawProjection (rawLaw (ψ n))) s
    (fun n => initialAtomicRadius ε ((N n+1:ℕ):ℝ)) hsp hpr hs hr₀
    Coulomb.unitWindow Coulomb.unitWindow.continuous Coulomb.unitWindow_mass Coulomb.unitWindow_support
    (by norm_num : (0:ℝ)<1) hD (fun n => (d n).measurable) hbad f.toAnalytic
    (fun n o => scaledDensity (s n) (μ n o)) (fun _ _ => rfl) ?_ ?_ ha hab
  · intro n a b ha hab
    have HH := conditionalPacketDensity_annulus_eq_condExp (P n) (rawLaw (ψ n))
      (observationLaw_rawProjection (rawLaw (ψ n))) (measurable_tailObservation (rs n) (d n).j)
      Coulomb.unitWindow.continuous Coulomb.unitWindow_mass (by norm_num : (0:ℝ)<1)
      (hpr n) (hsp n) (spatialAnnulus (a*s n) (b*s n))
    filter_upwards [HH] with o ho
    rw [annularIntegral_scaledDensity (hsp n)]
    exact congrArg (fun t => s n^3*t) ho
  · intro a b ha hab
    obtain ⟨K,hK,HK⟩ := Hcount a b ha hab
    refine ⟨K,hK,?_⟩
    filter_upwards [hN.eventually_ge_atTop Z₀] with n hn
    rw [integral_rawLaw (hψ n).choose_spec.1.2.2.1]
    exact HK (N n) (ψ n) hn (hψ n) (s n) (hsp n)
end NeutralAtom
end

end

end OAI
