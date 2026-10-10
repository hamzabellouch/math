import Mathlib
import OAI.Analysis.Crouzeix.BoundaryModulus

namespace OAI

/-! Exterior Riemann. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

def invertedExterior (K : Set ℂ) (a : ℂ) : Set ℂ :=
  {z | z = 0 ∨ a + z⁻¹ ∉ K}

@[simp] theorem zero_mem_invertedExterior (K : Set ℂ) (a : ℂ) :
    0 ∈ invertedExterior K a := Or.inl rfl

theorem invertedExterior_mem_nhds_zero {K : Set ℂ} (hb : Bornology.IsBounded K) (a : ℂ) :
    invertedExterior K a ∈ 𝓝 0 := by
  obtain ⟨R, hR, hsub⟩ := hb.subset_ball_lt 0 a
  apply Metric.mem_nhds_iff.mpr
  refine ⟨R⁻¹, inv_pos.mpr hR, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · exact Or.inl hz0
  · apply Or.inr
    intro hk
    have hn := mem_ball.mp (hsub hk)
    rw [dist_eq_norm, add_sub_cancel_left, norm_inv] at hn
    have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hzr : ‖z‖ < R⁻¹ := mem_ball_zero_iff.mp hz
    have hback : R < ‖z‖⁻¹ := (lt_inv_comm₀ hR hnorm).mpr hzr
    exact (hback.trans hn).false

theorem isOpen_invertedExterior {K : Set ℂ} (hK : IsCompact K) (a : ℂ) :
    IsOpen (invertedExterior K a) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    exact invertedExterior_mem_nhds_zero hK.isBounded a
  · have hzn : a + z⁻¹ ∉ K := hz.resolve_left hz0
    have hc : ContinuousAt (fun w : ℂ => a + w⁻¹) z :=
      continuousAt_const.add (continuousAt_inv₀ hz0)
    filter_upwards [hc.preimage_mem_nhds (hK.isClosed.isOpen_compl.mem_nhds hzn)] with w hw
    exact Or.inr hw

theorem isBounded_invertedExterior {K : Set ℂ} {a : ℂ} (ha : a ∈ interior K) :
    Bornology.IsBounded (invertedExterior K a) := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := ε⁻¹)).subset
  intro z hz
  apply mem_closedBall_zero_iff.mpr
  rcases hz with rfl | hzn
  · simpa only [norm_zero] using (inv_nonneg.mpr hε.le)
  · by_cases hz0 : z = 0
    · simpa only [hz0, norm_zero] using (inv_nonneg.mpr hε.le)
    · by_contra h
      have hlarge : ε⁻¹ < ‖z‖ := lt_of_not_ge h
      apply hzn
      apply hsub
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv]
      exact (inv_lt_comm₀ (norm_pos_iff.mpr hz0) hε).mpr hlarge

theorem starConvex_invertedExterior {K : Set ℂ} (hK : Convex ℝ K) {a : ℂ}
    (ha : a ∈ K) : StarConvex ℝ 0 (invertedExterior K a) := by
  intro z hz s t hs ht hst
  simp only [smul_zero, zero_add]
  by_cases ht0 : t = 0
  · simp only [ht0, zero_smul, zero_mem_invertedExterior]
  by_cases hz0 : z = 0
  · simp only [hz0, smul_zero, zero_mem_invertedExterior]
  apply Or.inr
  intro hk
  have hi := hK.add_smul_sub_mem ha hk (show t ∈ Icc 0 1 by constructor <;> linarith)
  have he : a + t • (a + (t • z)⁻¹ - a) = a + z⁻¹ := by
    simp only [Complex.real_smul, add_sub_cancel_left, mul_inv_rev]
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    field_simp
  rw [he] at hi
  exact (hz.resolve_left hz0) hi

theorem isSimplyConnected_invertedExterior {K : Set ℂ} (hK : Convex ℝ K) {a : ℂ}
    (ha : a ∈ K) : IsSimplyConnected (invertedExterior K a) := by
  let _ := (starConvex_invertedExterior hK ha).contractibleSpace
    (show (invertedExterior K a).Nonempty from ⟨0, zero_mem_invertedExterior K a⟩)
  change SimplyConnectedSpace (invertedExterior K a)
  infer_instance

theorem riemann_invertedExterior {K : Set ℂ} (hK : IsCompact K) (hconv : Convex ℝ K)
    {a : ℂ} (ha : a ∈ interior K) :
    ∃ f g : ℂ → ℂ,
      DifferentiableOn ℂ f (invertedExterior K a) ∧
      DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f (invertedExterior K a) (ball 0 1) ∧
      BijOn g (ball 0 1) (invertedExterior K a) ∧
      InvOn g f (invertedExterior K a) (ball 0 1) ∧ f 0 = 0 ∧ g 0 = 0 ∧
      (∀ z ∈ invertedExterior K a, deriv f z ≠ 0) ∧
      (∀ w ∈ ball 0 1, deriv g w ≠ 0) := by
  obtain ⟨f, g, hf, hg, hfb, hgb, hinv, hf0, hfd, hgd⟩ :=
    riemann_biholomorphic_bounded (isOpen_invertedExterior hK a)
      (isBounded_invertedExterior ha)
      (isSimplyConnected_invertedExterior hconv (interior_subset ha))
      (zero_mem_invertedExterior K a)
  have hg0 : g 0 = 0 := by
    simpa only [hf0] using hinv.1 (zero_mem_invertedExterior K a)
  exact ⟨f, g, hf, hg, hfb, hgb, hinv, hf0, hg0, hfd, hgd⟩

theorem riemann_exterior {K : Set ℂ} (hK : IsCompact K) (hconv : Convex ℝ K)
    {a : ℂ} (ha : a ∈ interior K) :
    ∃ G Φ : ℂ → ℂ,
      DifferentiableOn ℂ G {t | 1 < ‖t‖} ∧ DifferentiableOn ℂ Φ Kᶜ ∧
      BijOn G {t | 1 < ‖t‖} Kᶜ ∧ BijOn Φ Kᶜ {t | 1 < ‖t‖} ∧
      InvOn Φ G {t | 1 < ‖t‖} Kᶜ ∧
      (∀ t, 1 < ‖t‖ → deriv G t ≠ 0) ∧ (∀ z ∈ Kᶜ, deriv Φ z ≠ 0) := by
  obtain ⟨f, g, hf, hg, hfb, hgb, hinv, hf0, hg0, _, _⟩ :=
    riemann_invertedExterior hK hconv ha
  let G : ℂ → ℂ := fun t => a + (g t⁻¹)⁻¹
  let Φ : ℂ → ℂ := fun z => (f (z - a)⁻¹)⁻¹
  have ht0 : ∀ t : ℂ, 1 < ‖t‖ → t ≠ 0 := fun t ht =>
    norm_pos_iff.mp (zero_lt_one.trans ht)
  have htinv : ∀ t : ℂ, 1 < ‖t‖ → t⁻¹ ∈ ball 0 1 := fun t ht =>
    mem_ball_zero_iff.mpr (by rw [norm_inv]; exact (inv_lt_one₀ (zero_lt_one.trans ht)).mpr ht)
  have hgn : ∀ t, 1 < ‖t‖ → g t⁻¹ ≠ 0 := by
    intro t ht he
    have hi := hgb.injOn (htinv t ht) (mem_ball_self zero_lt_one) (he.trans hg0.symm)
    exact inv_ne_zero (ht0 t ht) hi
  have hGmap : MapsTo G {t | 1 < ‖t‖} Kᶜ := by
    intro t ht
    exact (hgb.mapsTo (htinv t ht)).resolve_left (hgn t ht)
  have hza : ∀ z ∈ Kᶜ, z - a ≠ 0 := by
    intro z hz he
    exact hz (sub_eq_zero.mp he ▸ interior_subset ha)
  have hzinv : ∀ z ∈ Kᶜ, (z - a)⁻¹ ∈ invertedExterior K a := by
    intro z hz
    apply Or.inr
    simpa only [inv_inv, add_sub_cancel, mem_compl_iff] using hz
  have hfn : ∀ z ∈ Kᶜ, f (z - a)⁻¹ ≠ 0 := by
    intro z hz he
    have hi := hfb.injOn (hzinv z hz) (zero_mem_invertedExterior K a) (he.trans hf0.symm)
    exact inv_ne_zero (hza z hz) hi
  have hΦmap : MapsTo Φ Kᶜ {t | 1 < ‖t‖} := by
    intro z hz
    change 1 < ‖(f (z - a)⁻¹)⁻¹‖
    rw [norm_inv, one_lt_inv₀ (norm_pos_iff.mpr (hfn z hz))]
    exact mem_ball_zero_iff.mp (hfb.mapsTo (hzinv z hz))
  have hInv : InvOn Φ G {t | 1 < ‖t‖} Kᶜ := by
    constructor
    · intro t ht
      simp only [Φ, G, add_sub_cancel_left, inv_inv, hinv.2 (htinv t ht)]
    · intro z hz
      simp only [Φ, G, inv_inv, hinv.1 (hzinv z hz), add_sub_cancel]
  have hGbij : BijOn G {t | 1 < ‖t‖} Kᶜ := by
    refine ⟨hGmap, ?_, ?_⟩
    · intro t ht s hs he
      simpa only [hInv.1 ht, hInv.1 hs] using congrArg Φ he
    · intro z hz
      exact ⟨Φ z, hΦmap hz, hInv.2 hz⟩
  have hΦbij := hGbij.symm hInv.symm
  have hGo : IsOpen {t : ℂ | 1 < ‖t‖} := isOpen_lt continuous_const continuous_norm
  have hGhol : DifferentiableOn ℂ G {t | 1 < ‖t‖} := by
    intro t ht
    have hd := ((hg _ (htinv t ht)).differentiableAt (isOpen_ball.mem_nhds (htinv t ht))).comp t
      (differentiableAt_inv (ht0 t ht))
    exact ((hd.inv (hgn t ht)).const_add a).differentiableWithinAt
  have hΦhol : DifferentiableOn ℂ Φ Kᶜ := by
    intro z hz
    have hd := ((hf _ (hzinv z hz)).differentiableAt
      ((isOpen_invertedExterior hK a).mem_nhds (hzinv z hz))).comp z
      ((differentiableAt_id.sub_const a).inv (hza z hz))
    exact (hd.inv (hfn z hz)).differentiableWithinAt
  exact ⟨G, Φ, hGhol, hΦhol, hGbij, hΦbij, hInv,
    fun t ht => deriv_ne_zero_of_injOn hGo hGhol hGbij.injOn ht,
    fun z hz => deriv_ne_zero_of_injOn hK.isClosed.isOpen_compl hΦhol hΦbij.injOn hz⟩

end CrouzeixHilbert.Conformal

end

end OAI
