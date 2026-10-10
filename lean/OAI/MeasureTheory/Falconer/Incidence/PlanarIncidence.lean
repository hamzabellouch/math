import OAI.MeasureTheory.Falconer.Estimates.PlanarSampling

namespace OAI

/-!
# Quantitative planar measure incidence obstruction

This is the measure-to-finite-set step of `ang:planar-measures`. The only
published input is the finite-set specialization of the planar
Furstenberg theorem. All losses from the two original-label sampling steps
are explicit; no geometric gain is assumed.
-/

namespace Falconer
open Set MeasureTheory Real
attribute [local instance] Classical.propDecidable

noncomputable def samplingBallLoss (K B s : ℝ) : ℝ := ((exp 1-1)*K+B)*8^s

theorem samplingBallLoss_pos {K B s : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    0 < samplingBallLoss K B s := by
  have he : 0 ≤ exp 1-1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num))
  apply mul_pos
  · exact lt_of_lt_of_le zero_lt_one (hB.trans (le_add_of_nonneg_left (mul_nonneg he hK)))
  · exact Real.rpow_pos_of_pos (by norm_num) _

theorem planar_measure_incidence_obstruction
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) :
    ∃ ε δ₀ : ℝ, 0 < ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1/2 ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
    ∀ (X W : Type) [MeasurableSpace X] [MeasurableSpace W]
      (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure W)
      (p : X → Space 2) (m : W → ℝ) (E : X → W → Prop),
      Measurable p → Measurable m → MeasurableSet {z : X × W | E z.1 z.2} →
      (∀ x, |p x 0| ≤ 1/4 ∧ |p x 1| ≤ 1/4) → (∀ w, |m w| ≤ 1/2) →
    ∀ (K B I : ℝ) (n l L H J : ℕ) (A : W → Finset ℝ),
      0 ≤ K → 1 ≤ B → 0 < I → 0 < n → 0 < l →
      δ⁻¹+1 ≤ L → δ⁻¹ ≤ H →
      1 ≤ (n : ℝ)*δ^b → (n : ℝ)*δ^b ≤ 2 →
      1 ≤ (l : ℝ)*δ^f → (l : ℝ)*δ^f ≤ 2 →
      (∀ c r, δ ≤ r → (μ : Measure X).real {x | dist (p x) c ≤ r} ≤ K*r^f) →
      (∀ a r, δ ≤ r → (ν : Measure W).real {w | |m w-a| ≤ r} ≤ K*r^b) →
      I ≤ (∫ w, ∫ x, if E x w then (1 : ℝ) else 0 ∂(μ : Measure X) ∂(ν : Measure W)) →
      (((2*L+1)^2*H : ℕ) : ℝ)*exp (-B) ≤ I/16 →
      2*(8*samplingBallLoss K B f/I)^2 ≤ δ^(-ε) →
      8*2^b*(samplingBallLoss K B b)^2/I ≤ δ^(-ε) →
      (n : ℝ) ≤ δ^(-b-ε/4) →
      (∀ w, ((A w).card * (2*J+1) : ℕ) ≤ δ^(-b-ε/4)) →
      (∀ x w, E x w → ∃ a ∈ A w, |p x 1-m w*p x 0-a| ≤ ((J : ℝ)-2)*δ) →
      False := by
  obtain ⟨ε, δ₀, hε, hδ₀, hδ₀', hFurst⟩ :=
    sampled_furstenberg_obstruction hpublished hb hb' hbf hf
  refine ⟨ε, δ₀, hε, hδ₀, hδ₀', ?_⟩
  intro δ hδ hδsmall X W _ _ μ ν p m E hp hm hE hpchart hmchart
    K B I n l L H J A hK hB hI hn hl hL hH hnsize hnsize' hlsize hlsize'
    hpball hmball hmean hfail hPloss hTloss hnc hAc hcover
  let F : X → W → ℝ := fun x w => if E x w then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    exact measurable_const.indicator hE
  have hF0 (x : X) (w : W) : 0 ≤ F x w := by simp only [F]; split <;> norm_num
  have hF1 (x : X) (w : W) : F x w ≤ 1 := by simp only [F]; split <;> norm_num
  have hmbound (w : W) (i : Fin 2) : |slopePoint (m w) i| ≤ 1 := by
    fin_cases i
    · exact (hmchart w).trans (by norm_num)
    · simp
  obtain ⟨ω, hω, hgood⟩ := exists_uniform_incidence_sample μ ν (slopePoint ∘ m)
    (continuous_slopePoint.measurable.comp hm) hmbound F hF hF0 hF1 hn hδ hb.le hK hB
    hL hH hnsize (slopePoint_ball_mass_le ν m hmball) hI hmean (hfail.trans (by linarith))
  let G := {x | I/4 ≤ iidAverage (F x) ω}
  have hG : MeasurableSet G := by
    apply measurableSet_le measurable_const
    unfold iidAverage
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact hF.comp (measurable_id.prodMk measurable_const)
  have hpbound (x : X) (i : Fin 2) : |p x i| ≤ 1 := by
    fin_cases i
    · exact (hpchart x).1.trans (by norm_num)
    · exact (hpchart x).2.trans (by norm_num)
  obtain ⟨ξ, D, P, hDn, hDG, hPn, hPD, hPsep, hPball⟩ :=
    exists_good_separated_point_sample μ p hp hpbound G hG (by positivity : 0 < I/4)
      hgood hl hδ (hb.trans hbf).le hK hB hL hH hlsize hlsize' hpball
      (by convert hfail using 1; ring)
  have hrep : ∀ x ∈ P, ∃ y : X, p y = x ∧ y ∈ G := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp (hPD hx)
    exact ⟨ξ i, hix, hDG i hi⟩
  let rep : {x // x ∈ P} → X := fun x => Classical.choose (hrep x.val x.property)
  have hrep' (x : Space 2) (hx : x ∈ P) : p (rep ⟨x,hx⟩) = x ∧ rep ⟨x,hx⟩ ∈ G :=
    Classical.choose_spec (hrep x hx)
  let S : Space 2 → Finset (Fin n) := fun x =>
    if hx : x ∈ P then incidentLabels E ω (rep ⟨x,hx⟩) else ∅
  let U : Fin n → Finset (Space 2) := fun i =>
    stripLineCandidates δ (m (ω i)) (A (ω i)) J
  have hPchart (x : Space 2) (hx : x ∈ P) : |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4 := by
    rw [← (hrep' x hx).1]
    exact hpchart _
  have hPbound : NormalizedFiniteBallBound δ f (δ^(-ε)) P := by
    have he : 2*(2*samplingBallLoss K B f/(I/4))^2 =
        2*(8*samplingBallLoss K B f/I)^2 := by ring
    change NormalizedFiniteBallBound δ f (2*(2*samplingBallLoss K B f/(I/4))^2) P at hPball
    rw [he] at hPball
    intro c r hdr hr1
    apply (hPball c r hdr hr1).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPloss
      (Real.rpow_nonneg (hδ.le.trans hdr) _)) (Nat.cast_nonneg _)
  have hcount (a r : ℝ) (hdr : δ ≤ r) :
      (((Finset.univ : Finset (Fin n)).filter (fun i => |m (ω i)-a| ≤ r)).card : ℝ) ≤
        (samplingBallLoss K B b * ((Finset.univ : Finset (Fin n)).card : ℝ))*r^b := by
    have hh := hω (slopePoint a) r hdr
    simpa only [Function.comp_apply, slopePoint_dist, iidCount_eq_card_filter,
      Finset.card_univ, Fintype.card_fin, Set.mem_ofPred_eq, samplingBallLoss] using hh
  apply hFurst δ hδ hδsmall P hPn hPchart hPsep hPbound (Fin n) Finset.univ
    (m ∘ ω) S U (samplingBallLoss K B b) (I/4)
    (samplingBallLoss_pos hK hB) (by positivity) ⟨⟨0,hn⟩, Finset.mem_univ _⟩
    (by simpa using hnsize') (fun i _ => hmchart (ω i)) hcount
  · intro x hx
    constructor
    · exact Finset.subset_univ _
    · simp only [S, dite_eq_left hx, Finset.card_univ, Fintype.card_fin]
      exact empirical_incidence_card_lower E hn ω _ (hrep' x hx).2
  · convert hTloss using 1; ring
  · simpa using hnc
  · intro i _
    exact (show ((U i).card : ℝ) ≤ ((A (ω i)).card * (2*J+1) : ℕ) by
      exact_mod_cast stripLineCandidates_card_le δ (m (ω i)) (A (ω i)) J).trans (hAc (ω i))
  · intro x hx i hi
    have hiy : E (rep ⟨x,hx⟩) (ω i) := by
      simpa only [S, dite_eq_left hx, incidentLabels, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    apply roundedIncidentLine_mem_stripLineCandidates (C := (J : ℝ)-2) hδ _ J (by linarith)
      x ((hPchart x hx).1.trans (by norm_num))
    obtain ⟨a, ha, he⟩ := hcover _ _ hiy
    rw [(hrep' x hx).1] at he
    exact ⟨a,ha,he⟩

end Falconer

end OAI
