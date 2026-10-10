import OAI.Geometry.Immersion.ClosedSurface.QuadraticCorrection
import OAI.Geometry.Immersion.ClosedSurface.ProjectionStability

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma secondQuadratic_sub_form {n : ℕ} (B C : Fin 3 → RVec n) (v : Base) :
    secondQuadratic (B-C) v = secondQuadratic B v-secondQuadratic C v := by
  simp only [secondQuadratic,Pi.sub_apply,smul_sub]
  abel

lemma norm_secondQuadratic_le {n : ℕ} (B : Fin 3 → RVec n) (v : Base) :
    ‖secondQuadratic B v‖ ≤ 4*‖B‖*‖v‖^2 := by
  have h1 : |v.1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le v
  have h2 : |v.2| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le v
  have hq1 : |v.1^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hq2 : |v.2^2| ≤ ‖v‖^2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hm : |2*v.1*v.2| ≤ 2*‖v‖^2 := by
    simp only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    nlinarith [mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg v)]
  unfold secondQuadratic
  calc
    _ ≤ (‖v.1^2 • B 0‖+‖(2*v.1*v.2) • B 1‖)+‖v.2^2 • B 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖^2*‖B‖+(2*‖v‖^2)*‖B‖)+‖v‖^2*‖B‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm B 0
      · exact norm_le_pi_norm B 1
      · exact norm_le_pi_norm B 2
    _ = _ := by ring

lemma norm_rotated_covector (ξ : Base) : ‖(-ξ.2,ξ.1)‖ = ‖ξ‖ := by
  simp only [Prod.norm_def,norm_neg]
  exact max_comm _ _




theorem second_form_direction_persists {n : ℕ} (B C : Fin 3 → RVec n) (ξ : Base)
    {κ : ℝ} (hκ : 0 < κ) (hB : κ ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖)
    (hBC : 4*‖B-C‖*‖ξ‖^2 ≤ κ/2) :
    κ/2 ≤ ‖secondQuadratic C (-ξ.2,ξ.1)‖ ∧ Good C ξ := by
  have he : ‖secondQuadratic B (-ξ.2,ξ.1)-secondQuadratic C (-ξ.2,ξ.1)‖ ≤ κ/2 := by
    rw [← secondQuadratic_sub_form]
    exact (norm_secondQuadratic_le _ _).trans (by simpa only [norm_rotated_covector] using hBC)
  have hb' : κ/2 ≤ ‖secondQuadratic C (-ξ.2,ξ.1)‖ := by
    have hh := norm_sub_norm_le (secondQuadratic B (-ξ.2,ξ.1)) (secondQuadratic C (-ξ.2,ξ.1))
    linarith
  have hn := norm_pos_iff.mp ((half_pos hκ).trans_le hb')
  refine ⟨hb',?_,hn⟩
  intro hz
  apply hn
  simp [hz,secondQuadratic]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.WeightedEstimates
open Set

lemma WeightedBound.convex_variation {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {U : Set E} (hU : IsOpen U)
    (hconv : Convex ℝ U) {s A : ℝ} {f : E → G} (hs : 0 < s)
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s 1 A f)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x-f y‖ ≤ (A/s)*‖x-y‖ := by
  apply Convex.norm_image_sub_le_of_norm_fderivWithin_le
    (hf.differentiableOn (by simp)) _ hconv hy hx
  intro p hp
  have hh := hb.deriv_le hs (show 1 ≤ 1 by rfl) hp
  simpa only [norm_iteratedFDerivWithin_one (𝕜 := ℝ) f (hU.uniqueDiffOn p hp),pow_one] using hh

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.RealModes
open SmallModes WeightedEstimates Set

lemma weighted_coordinate_second_jet {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hb : WeightedBound U z 3 A F) {v w : Base} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    WeightedBound U z 1 (A/z^2) (coordDeriv v (coordDeriv w F)) := by
  have h1 : WeightedBound U z 2 (A/z) (coordDeriv w F) := by
    have hh := hb.directional hU hz hF w
    simp only [hw,one_mul] at hh
    exact hh.congr (fun p hp => rfl)
  have h2 := h1.directional hU hz (contDiffOn_coordDeriv_vector hU hF w) v
  simp only [hv,one_mul,div_div,← pow_two] at h2
  exact h2.congr (fun p hp => rfl)

lemma coordinate_jets_variation {F : RField 4} {U : Set Base} (hU : IsOpen U)
    (hconv : Convex ℝ U) (hF : ContDiffOn ℝ ∞ F U) {z A : ℝ} (hz : 0 < z)
    (hA : 0 ≤ A) (hb : WeightedBound U z 3 A F) {x y : Base} (hx : x ∈ U) (hy : y ∈ U) :
    ‖firstJetPair F x-firstJetPair F y‖ ≤ (A/z^2)*‖x-y‖ ∧
    ‖secondJetTriple F x‖ ≤ A/z^2 ∧
    ‖secondJetTriple F x-secondJetTriple F y‖ ≤ (A/z^3)*‖x-y‖ := by
  have hdx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hdy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have h1 (v : Base) (hv : ‖v‖ = 1) :
      ‖coordDeriv v F x-coordDeriv v F y‖ ≤ (A/z^2)*‖x-y‖ := by
    have hh : WeightedBound U z 1 (A/z) (coordDeriv v F) := by
      have hh := (hb.mono_order (by omega : 2 ≤ 3)).directional hU hz hF v
      simp only [hv,one_mul] at hh
      exact hh.congr (fun p hp => rfl)
    simpa only [div_div,pow_two] using hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU hF v) hx hy
  have h2 (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖coordDeriv v (coordDeriv w F) x‖ ≤ A/z^2 ∧
      ‖coordDeriv v (coordDeriv w F) x-coordDeriv v (coordDeriv w F) y‖ ≤ (A/z^3)*‖x-y‖ := by
    have hh := weighted_coordinate_second_jet hU hF hz hb hv hw
    refine ⟨hh.norm_le hx,?_⟩
    have hvw := hh.convex_variation hU hconv hz
      (contDiffOn_coordDeriv_vector hU (contDiffOn_coordDeriv_vector hU hF w) v) hx hy
    simpa only [div_div,← pow_succ] using hvw
  refine ⟨?_,?_,?_⟩
  · change max ‖coordDeriv dx F x-coordDeriv dx F y‖ ‖coordDeriv dy F x-coordDeriv dy F y‖ ≤ _
    exact max_le (h1 dx hdx) (h1 dy hdy)
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).1
    · exact (h2 dx dy hdx hdy).1
    · exact (h2 dy dy hdy hdy).1
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    fin_cases i
    · exact (h2 dx dx hdx hdx).2
    · exact (h2 dx dy hdx hdy).2
    · exact (h2 dy dy hdy hdy).2




theorem second_form_cell_variation (R c A : ℝ) (hc : 0 < c) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℝ), 0 < z → z ≤ 1 →
      ∀ (F : RField 4) (U : Set Base), IsOpen U → Convex ℝ U → ContDiffOn ℝ ∞ F U →
      WeightedBound U z 3 A F →
      (∀ p ∈ U, ‖firstJetPair F p‖ ≤ R ∧ c ≤ NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2) →
      ∀ x ∈ U, ∀ y ∈ U, ‖realSecondTensor F x-realSecondTensor F y‖ ≤ (C/z^4)*‖x-y‖ := by
  obtain ⟨L,D,hL,hD,hb⟩ := compact_normal_projection_bounds R c hc
  refine ⟨L*A^2+D*A,by positivity,fun z hz hz1 F U hU hconv hF hFbound hmetric x hx y hy => ?_⟩
  obtain ⟨h1,h2,h3⟩ := coordinate_jets_variation hU hconv hF hz hA hFbound hx hy
  have hp4 : z^4 ≤ z^3 := pow_le_pow_of_le_one hz.le hz1 (by omega : 3 ≤ 4)
  have h43 : A/z^3 ≤ A/z^4 := div_le_div_of_nonneg_left hA (pow_pos hz 4) hp4
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simp only [Pi.sub_apply,realSecondTensor_eq_projection]
  have hh := hb (firstJetPair F x) (firstJetPair F y)
    (hmetric x hx).1 (hmetric x hx).2 (hmetric y hy).1 (hmetric y hy).2
    (secondJetTriple F x i) (secondJetTriple F y i)
  calc
    _ ≤ L*‖firstJetPair F x-firstJetPair F y‖*‖secondJetTriple F x i‖+
        D*‖secondJetTriple F x i-secondJetTriple F y i‖ := hh
    _ ≤ L*((A/z^2)*‖x-y‖)*(A/z^2)+D*((A/z^3)*‖x-y‖) := by
      gcongr
      · exact (norm_le_pi_norm _ i).trans h2
      · exact (norm_le_pi_norm _ i).trans h3
    _ ≤ L*((A/z^2)*‖x-y‖)*(A/z^2)+D*((A/z^4)*‖x-y‖) := by gcongr
    _ = _ := by field_simp [hz.ne']

end ClosedSurfaceR4.RealModes

end

end OAI
