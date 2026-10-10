import OAI.MathematicalPhysics.Boltzmann.Approximation.CapColdBounds
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence

namespace OAI

section

/-! # Positive approximations below the cap

The cap upper bound suffices for compactness, without requiring the cap to be
attained. Zero-hot approximations therefore satisfy the same bounds. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure Approximation (s₀ η K α γ d₀ q T : ℝ) (N : ℕ) where
  amplitude : ℝ
  coefficient : ℝ
  amplitude_pos : 0 < amplitude
  coefficient_mem : coefficient ∈ Icc 0 2
  initial_bound : ∀ p, initial s₀ η K α γ d₀ q N
    (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p) p ≤ 2*amplitude
  solution : PeriodicMildState q (N+1) (damping q (N+1) amplitude) T (2*amplitude)
    (initial s₀ η K α γ d₀ q N
      (fun p => coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p))
  cap_bound : solution.hotPeak (DatumBounds.scale s₀ η (N+1)) (color s₀ η K α γ d₀ q N) ≤ 1

theorem cap_family_pairs_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun N => CollisionCompactness.pairDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap_bound)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Actual cold components of approximations below the cap -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.WeightedLocal BoltzmannNonuniqueness.WeightedLocalControl
open BoltzmannNonuniqueness.WeightedTranslation BoltzmannNonuniqueness.VelocityWeight
open BoltzmannNonuniqueness.JetLattice BoltzmannNonuniqueness.Published
namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

def Approximation.cold {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (i : Label) : ℝ × JetPrototype.Phase → ℝ :=
  rebuilt s₀ η K α γ d₀ q (N+1) (damping q (N+1) F.amplitude) T N F.solution.value i



theorem Approximation.cold_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    (∀ i, Measurable (F.cold i)) ∧ (∀ i u, 0 ≤ F.cold i u) ∧
      (∀ s : Finset JetLattice.Label, ∀ u, ∑ i ∈ s, F.cold i u ≤ F.solution.value u) ∧
      (∀ i, ColdMildAE q (N+1) (damping q (N+1) F.amplitude) T F.solution.value
        (color s₀ η K α γ d₀ q N i) (F.cold i)) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  have hi := initial_color_bounds hs₀ hsmax hη hηmax hK hd₀ α γ q N hh₀
  have hc₀ (i) (p) : 0 ≤ color s₀ η K α γ d₀ q N i p ∧
      color s₀ η K α γ d₀ q N i p ≤ 2*F.amplitude :=
    ⟨(hi.1 i p).1,(hi.1 i p).2.trans (F.initial_bound p)⟩
  have hL : 0 ≤ damping q (N+1) F.amplitude :=
    (bounds (q := q) (by positivity : 0 ≤ (N+1:ℝ)) F.amplitude_pos).1
  have hR : 0 ≤ 2*F.amplitude := mul_nonneg (by norm_num) F.amplitude_pos.le
  have hp := rebuiltColdFamily_properties hq (by positivity : 0 ≤ (N+1:ℝ)) hL hT hR le_rfl
    F.solution.measurable_value (measurable_color s₀ η K α γ d₀ q N)
    F.solution.value_bounds hc₀ hi.2 (F.solution.all_mild hT)
  exact ⟨hp.1,fun i u => (hp.2.1 i u).1,hp.2.2.1,hp.2.2.2.2⟩



def Approximation.coldTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (u : ℝ × JetPrototype.Phase) : ℝ :=
  ∑' i, F.cold i u

theorem Approximation.coldTotal_properties {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.coldTotal ∧ ∀ u, Summable (fun i => F.cold i u) ∧
      0 ≤ F.coldTotal u ∧ F.coldTotal u ≤ F.solution.value u := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  refine ⟨Measurable.tsum hc.1,fun u => ?_⟩
  exact ⟨summable_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u),
    tsum_nonneg (fun i => hc.2.1 i u),
    Real.tsum_le_of_sum_le (fun i => hc.2.1 i u) (fun s => hc.2.2.1 s u)⟩



theorem Approximation.cold_envelope {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (i : JetLattice.Label) {t : ℝ} (ht : t ∈ Ioc 0 T) (p : JetPrototype.Phase) :
    H q p.2*F.cold i (t,p) ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) t i.positive
        (shift (displacement i.lattice) p) := by
  have hδ := DatumBounds.scale_pos (η := η) hs₀ (N+1)
  have hδone : DatumBounds.scale s₀ η (N+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (N+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hh₀ (p) : 0 ≤ F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p :=
    mul_nonneg F.coefficient_mem.1 ((HotSeedProfile.normalized_bounds hδ hδone q).choose_spec.2 p).1
  exact rebuilt_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq (by positivity)
    (bounds (by positivity) F.amplitude_pos).1 hT (by linarith [F.amplitude_pos])
    (hTmax.trans (by norm_num)) le_rfl N hh₀ F.solution.measurable_value
    F.solution.value_bounds F.initial_bound i ht p



def Approximation.escapedTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ :=
  ∑' i, escaped s₀ η z.1.1 N z.1.2
    (fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) i

theorem Approximation.escapedTotal_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.escapedTotal := by
  classical
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  apply Measurable.tsum
  intro i
  have hi : MeasurableSet {z : Published.KineticPhase |
      z.1.2 ∉ JetLattice.spatialEnlargement s₀ η z.1.1 i} :=
    ((JetLattice.measurableSet_spatialEnlargement s₀ η i).preimage measurable_fst).compl
  have hm : Measurable (fun z : Published.KineticPhase =>
      F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    apply (hc i).comp
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  by_cases hN : i.annulus < N
  · change Measurable (fun z : Published.KineticPhase => if i.annulus < N ∧
        JetLatticeTail.outside η (JetGeometry.jetScale s₀ η i.annulus) z.1.1 i.positive z.1.2 i.lattice
        then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0)
    simp only [hN,true_and,outside_iff_not_mem]
    exact hm.ite hi measurable_const
  · change Measurable (fun z : Published.KineticPhase => if i.annulus < N ∧
        JetLatticeTail.outside η (JetGeometry.jetScale s₀ η i.annulus) z.1.1 i.positive z.1.2 i.lattice
        then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0)
    simp only [hN,false_and,ite_false]
    exact measurable_const

theorem Approximation.escapedTotal_nonneg {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (z : Published.KineticPhase) : 0 ≤ F.escapedTotal z := by
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2.1
  apply tsum_nonneg
  intro i
  unfold escaped
  split_ifs
  · exact hc i _
  · exact le_rfl

theorem Approximation.escapedTotal_bound {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T)
    (hx : ∀ k, |z.1.2 k| ≤ 1) :
    F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent A)*z.1.1^A := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  let f : JetLattice.Label → ℝ := fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  have hfs : Summable f :=
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2 _).1
  have henv (i : JetLattice.Label) : H q z.2*f i ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (JetSpatialBox.shifted z.1.2 i.lattice,z.2) := by
    have he : (JetSpatialBox.shifted z.1.2 i.lattice,z.2) =
        WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2) := rfl
    rw [he]
    exact F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax i ht
      (JetPeriodicDatum.spatialMap z.1.2,z.2)
  have hb := normalized_escaped_bound (γ := γ) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht.1
    (ht.2.trans hTmax) hsmall A q N f z.1.2 z.2 hx
    (fun i => hc.2.1 i _) hfs (fun i _ => henv i)
  exact hb



def Approximation.centralTotal {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N) (z : Published.KineticPhase) : ℝ := by
  classical
  exact ∑' i, if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    then F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) else 0

theorem Approximation.centralTotal_measurable {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) :
    Measurable F.centralTotal := by
  classical
  have hc := (F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).1
  apply Measurable.tsum
  intro i
  have hm : Measurable (fun z : Published.KineticPhase =>
      F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))) := by
    apply (hc i).comp
    unfold JetPeriodicDatum.spatialMap transverse axial
    fun_prop
  have hi : MeasurableSet {z : Published.KineticPhase |
      z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i} :=
    (JetLattice.measurableSet_spatialEnlargement s₀ η i).preimage measurable_fst
  by_cases hN : i.annulus < N
  · simpa only [hN,true_and] using hm.ite hi measurable_const
  · simp only [hN,false_and,ite_false]
    exact measurable_const

theorem Approximation.coldTotal_eq_central_add_escaped {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T)
    (z : Published.KineticPhase) :
    F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) =
      F.centralTotal z+F.escapedTotal z := by
  classical
  let f : JetLattice.Label → ℝ := fun i => F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  let g : JetLattice.Label → ℝ := fun i =>
    if i.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i then f i else 0
  let h : JetLattice.Label → ℝ := escaped s₀ η z.1.1 N z.1.2 f
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀ hq hT
  have hfs : Summable f := (F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀ hq hT).2 _ |>.1
  have hfn (i) : 0 ≤ f i := hc.2.1 i _
  have hgn (i) : 0 ≤ g i := by
    dsimp [g]
    split_ifs
    · exact hfn i
    · exact le_rfl
  have hgl (i) : g i ≤ f i := by dsimp [g]; split_ifs <;> simp only [le_refl,hfn]
  have hhn (i) : 0 ≤ h i := by
    dsimp [h,escaped]
    split_ifs
    · exact hfn i
    · exact le_rfl
  have hhl (i) : h i ≤ f i := by dsimp [h,escaped]; split_ifs <;> simp only [le_refl,hfn]
  have hgs := Summable.of_nonneg_of_le hgn hgl hfs
  have hhs := Summable.of_nonneg_of_le hhn hhl hfs
  change (∑' i, f i) = (∑' i, g i)+(∑' i, h i)
  rw [← hgs.tsum_add hhs]
  apply tsum_congr
  intro i
  by_cases hN : i.annulus < N
  · by_cases hi : z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i
    <;> simp [g,h,escaped,hN,hi,outside_iff_not_mem]
  · have hz : f i = 0 := congrFun
      (rebuilt_zero s₀ η K α γ d₀ q (N+1) (WeightedLocalControl.damping q (N+1) F.amplitude)
        T N (fun u => (F.solution.value_bounds u).1) i hN) _
    simp [g,h,escaped,hN,hz]

theorem Approximation.centralTotal_single {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (z : Published.KineticPhase) (ht : z.1.1 ≤ 1/32)
    (i : JetLattice.Label) (hN : i.annulus < N)
    (hi : z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 i) :
    F.centralTotal z = F.cold i (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) := by
  classical
  unfold centralTotal
  rw [tsum_eq_single i]
  · simp only [hN,hi,and_self,ite_true]
  · intro j hji
    have hj : ¬(j.annulus < N ∧ z.1.2 ∈ JetLattice.spatialEnlargement s₀ η z.1.1 j) := by
      rintro ⟨_,hj⟩
      exact hji (JetLattice.common_point_label hs₀ hsmax hη hηmax ht hj hi)
    simp only [hj,ite_false]



theorem Approximation.cold_free_majorant_at_main {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hd₀ : 0 < d₀)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (z : KineticPhase) (ht : z.1.1 ∈ Ioc 0 T) (i : Label) (hi : i.annulus < N)
    (hx : z.1.2 ∈ spatialEnlargement s₀ η z.1.1 i) :
    H q z.2*F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) ≤
      JetFreeTransport.free η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2))+
      JetSupersolution.epsilon K (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10)*
        JetBarrier.barrier η K α γ (JetGeometry.jetScale s₀ η i.annulus)
          (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
          (WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2))+
      H q z.2*F.escapedTotal z := by
  rw [F.coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀.le hq hT z,
    F.centralTotal_single hs₀ hsmax hη hηmax z (ht.2.trans hTmax) i hi hx,mul_add]
  exact add_le_add (F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax
    i ht (JetPeriodicDatum.spatialMap z.1.2,z.2)) le_rfl

theorem Approximation.coldTotal_eq_escaped_of_no_main {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hd₀ : 0 ≤ d₀) (hq : q < 2) (hT : 0 ≤ T) (z : KineticPhase)
    (hx : ∀ i : Label, i.annulus < N → z.1.2 ∉ spatialEnlargement s₀ η z.1.1 i) :
    F.coldTotal (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2)) = F.escapedTotal z := by
  classical
  rw [F.coldTotal_eq_central_add_escaped hs₀ hsmax hη hηmax hK hd₀ hq hT z]
  have hz : F.centralTotal z = 0 := by
    have hi : ∀ i : Label, ¬(i.annulus < N ∧ z.1.2 ∈ spatialEnlargement s₀ η z.1.1 i) :=
      fun i hi => hx i hi.1 hi.2
    simp only [Approximation.centralTotal,hi,ite_false,tsum_zero]
  rw [hz,zero_add]


theorem Approximation.escapedTotal_bound_global {s₀ η K α γ d₀ q T : ℝ} {N : ℕ}
    (F : Approximation s₀ η K α γ d₀ q T N)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 ≤ α) (hαmax : α ≤ 1) (hγ : 0 ≤ γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (A : ℝ) {z : Published.KineticPhase} (ht : z.1.1 ∈ Ioc 0 T) :
    F.escapedTotal z ≤ JetEscapedEnvelope.constant s₀ η α K d₀
      (JetEscapedEnvelope.exponent A)*z.1.1^A := by
  have hc := F.cold_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT
  let f : JetLattice.Label → ℝ := fun j => F.cold j (z.1.1,(JetPeriodicDatum.spatialMap z.1.2,z.2))
  have hfs : Summable f :=
    ((F.coldTotal_properties hs₀ hsmax hη hηmax hK hd₀.le hq hT).2 _).1
  have henv (i : JetLattice.Label) : H q z.2*f i ≤
      JetSupersolution.U η K α γ (JetGeometry.jetScale s₀ η i.annulus)
        (d₀*JetGeometry.jetScale s₀ η i.annulus^10) z.1.1 i.positive
        (JetSpatialBox.shifted z.1.2 i.lattice,z.2) := by
    have he : (JetSpatialBox.shifted z.1.2 i.lattice,z.2) =
        WeightedTranslation.shift (displacement i.lattice) (JetPeriodicDatum.spatialMap z.1.2,z.2) := rfl
    rw [he]
    exact F.cold_envelope hs₀ hsmax hη hηmax hK hα hγ hd₀ hsmall hq hT hTmax i ht
      (JetPeriodicDatum.spatialMap z.1.2,z.2)
  have hb := normalized_escaped_bound_global (γ := γ) hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max ht.1
    (ht.2.trans hTmax) hsmall A q N f z.1.2 z.2
    (fun i => hc.2.1 i _) hfs (fun i _ => henv i)
  exact hb


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
