import OAI.Probability.SLE.Geometry.CenteredDiskCoefficient

namespace OAI

/-! Monotonicity and convergence of the source's prescribed moments. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace SLEExactGauge.Multipoint.CanonicalMass

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ}
  {B : ℝ≥0 → Ω → ℝ} {hBm : Measurable (Function.uncurry B)}
  {γ : Ω → ℝ≥0 → ℂ} {G : Ω → ℝ≥0 → ℂ → ℂ}
  (C : CanonicalMass P κ B hBm γ G)

include C in
lemma levelCoefficient_nonneg_integrable
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (ℓ : ℝ) (hℓ : 0≤ℓ) (m : ℕ) :
    (∀ θ∈Ioo (0:ℝ) Real.pi, 0≤Target.levelCoefficient κ W ℓ m θ) ∧
      Integrable (Target.levelCoefficient κ W ℓ m) (Target.angleLaw κ) := by
  obtain ⟨M,hM,hbound⟩ := C.uniform_clippedCoefficient_bound hB hc h0 hκ hκ8 F hw hgrowth W hW m
  have hb (θ) (hθ : θ∈Ioo (0:ℝ) Real.pi) : 0≤Target.levelCoefficient κ W ℓ m θ ∧
      Target.levelCoefficient κ W ℓ m θ≤M/(Real.sin θ)^greenExponent κ := by
    have ht := C.levelCoefficient_tendsto hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m
    exact ⟨ge_of_tendsto ht (Eventually.of_forall (fun n =>
      (hbound θ hθ ℓ hℓ n (Nat.cast_nonneg n)).1)),
      le_of_tendsto ht (Eventually.of_forall (fun n =>
      (hbound θ hθ ℓ hℓ n (Nat.cast_nonneg n)).2))⟩
  refine ⟨fun θ hθ => (hb θ hθ).1,?_⟩
  have hi : Integrable (fun θ => M/(Real.sin θ)^greenExponent κ) (Target.angleLaw κ) := by
    simpa only [div_eq_mul_inv,mul_one,one_mul] using (Target.angle_inverse_sine_integrable κ).const_mul M
  apply hi.mono' (C.levelCoefficient_aestronglyMeasurable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m)
  filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
  rw [Real.norm_of_nonneg (hb θ hθ).1]
  exact (hb θ hθ).2

include C in
lemma levelCoefficient_mono
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (m : ℕ) :
    MonotoneOn (fun ℓ => Target.levelCoefficient κ W ℓ m θ) (Ici 0) := by
  intro ℓ hℓ L hL hℓL
  let v := 4*ℓ/κ
  let V := 4*L/κ
  have hv : 0≤v := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have hV : 0≤V := div_nonneg (mul_nonneg (by norm_num) hL) hκ.le
  have hvV : v≤V := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hℓL (by norm_num)) hκ.le
  let u : ℕ → ℝ := fun n => if n=0 then v else V
  have hu (n) : 0≤u n := by dsimp [u]; split_ifs <;> assumption
  have hum : Monotone u := by
    intro i j hij
    dsimp only [u]
    split_ifs with hi hj
    · exact le_rfl
    · exact hvV
    · omega
    · exact le_rfl
  obtain ⟨τ,hτ,_,heτ⟩ := exists_monotone_radiusLevel_stops hB
    (fun r => (hBm.comp (measurable_const.prodMk measurable_id) : Measurable (B r)))
    hBm hc h0 κ hκ hκ8 γ G F (Eventually.of_forall hw)
    (Target.diskMapInv θ 0) (Target.diskMapInv_maps hθ (by simp)) u hu hum
  have hs : ∀ᵐ ω ∂P, τ 0 ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) v := by
    filter_upwards [heτ] with ω hω
    simpa only [u,ite_true] using hω 0
  have ht : ∀ᵐ ω ∂P, τ 1 ω=radiusLevelTime (γ ω) (G ω) (Target.diskMapInv θ 0) V := by
    filter_upwards [heτ] with ω hω
    simpa only [u,one_ne_zero,ite_false] using hω 1
  have hmono := (C.compactWeightedMass_paths (Target.diskMassWeight κ θ hθ)
    (Target.diskSourceHalfPlane θ) (Target.diskSourceHalfPlane_compact hθ)).mono
      (fun _ h => h.1)
  have h := finiteCenteredLaw_stoppedScalar_moment_mono hB hBm hc h0 κ hκ hκ8
    γ G F (Eventually.of_forall hw) (Target.diskMapInv θ 0)
    (Target.diskMapInv_maps hθ (by simp)) v V hv hvV
    (C.diskScalar θ hθ) (C.diskScalar_progressive θ hθ) hmono (τ 0) (τ 1)
    (hτ 0) (hτ 1) hs ht m
  rw [← C.levelCoefficient_eq_centered_moment hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ ℓ hℓ m (τ 0) (hτ 0) hs,
    ← C.levelCoefficient_eq_centered_moment hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ L hL m (τ 1) (hτ 1) ht] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    ((C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW L hL m).1 θ hθ)).mp h

include C in
theorem finiteMoment_mono
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (m : ℕ) : MonotoneOn (Target.finiteMoment κ W m) (Ici 0) := by
  intro ℓ hℓ L hL hℓL
  rw [C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m,
    C.finiteMoment_eq_levelCoefficientIntegral hB hc h0 hκ hκ8 F hw hgrowth W hW L hL m]
  apply integral_mono_ae
    (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW ℓ hℓ m).2
    (C.levelCoefficient_nonneg_integrable hB hc h0 hκ hκ8 F hw hgrowth W hW L hL m).2
  filter_upwards [Target.angleLaw_ae_mem κ] with θ hθ
  exact C.levelCoefficient_mono hB hc h0 hκ hκ8 F hw hgrowth W hW θ hθ m hℓ hL hℓL

include C in
theorem finiteMoment_tendsto_moment
    (hB : IsBrownianReal B P)
    (hc : ∀ ω, Continuous (fun t => B t ω)) (h0 : ∀ ω, B 0 ω=0)
    (hκ : 0<κ) (hκ8 : κ<8) (F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ*B t ω) (γ ω) (G ω) (F ω))
    (hgrowth : PublishedDiskUnivalentGrowth) (W : Target.WienerLaw) (hW : Target.IsWiener W)
    (m : ℕ) : Tendsto (fun ℓ : ℕ => Target.finiteMoment κ W m ℓ) atTop
      (𝓝 (Target.moment κ W m)) := by
  have hm : Monotone (fun ℓ : ℕ => Target.finiteMoment κ W m ℓ) := by
    intro i j hij
    exact C.finiteMoment_mono hB hc h0 hκ hκ8 F hw hgrowth W hW m
      (by change (0:ℝ) ≤ (i:ℝ); exact Nat.cast_nonneg i)
      (by change (0:ℝ) ≤ (j:ℝ); exact Nat.cast_nonneg j) (Nat.cast_le.mpr hij)
  obtain ⟨M,_,hM⟩ := C.uniform_finiteMoment_bound hB hc h0 hκ hκ8 F hw hgrowth W hW m
  have hb : BddAbove (range (fun ℓ : ℕ => Target.finiteMoment κ W m ℓ)) := by
    refine ⟨M,?_⟩
    rintro _ ⟨ℓ,rfl⟩
    exact (hM ℓ (Nat.cast_nonneg ℓ)).2
  have ht := tendsto_atTop_ciSup hm hb
  simpa only [Target.moment,ht.limUnder_eq] using ht

end SLEExactGauge.Multipoint.CanonicalMass

end

end OAI
