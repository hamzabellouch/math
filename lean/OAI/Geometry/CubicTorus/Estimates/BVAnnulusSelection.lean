import Mathlib
import OAI.Geometry.CubicTorus.Regularity.BVOrientedGraphCost

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma torusGraphRegion_interior_symmDiff {n : Cover} (hn : ‖n‖ = 1)
    {f g : Plane → ℝ} {q H a : ℝ} (ha : 0 ≤ a) (has : a ≤ 1/4)
    (hmargin : q+H ≤ a)
    (he : ∀ y, q ≤ ‖y‖ → f y = g y)
    (hf : ∀ y, ‖y‖ < q → |f y| ≤ H)
    (hg : ∀ y, ‖y‖ < q → |g y| ≤ H) :
    torusGraphRegion cubeCenter n f ∆ torusGraphRegion cubeCenter n g ⊆
      sublevelRegion radialSquared (a^2) := by
  intro z hz
  let v := representative z-cubeCenter
  let y := normalPlaneCoordinates n v
  let t := ⟪n,v⟫
  have hz' : (t < f y ∧ ¬t < g y) ∨ (t < g y ∧ ¬t < f y) := hz
  have hy : ‖y‖ < q := by
    by_contra! hy
    have hh := he y hy
    rw [hh] at hz'
    rcases hz' with hz' | hz'
    · exact hz'.2 hz'.1
    · exact hz'.2 hz'.1
  have hf' := abs_le.mp (hf y hy)
  have hg' := abs_le.mp (hg y hy)
  have ht : |t| ≤ H := by
    rw [abs_le]
    rcases hz' with hz' | hz' <;> constructor <;> linarith
  have hv : ‖v‖ ≤ ‖y‖+|t| := by
    rw [← normalPlaneCoordinates_reconstruct hn v]
    exact (norm_add_le _ _).trans (by simp only [normalPlaneEmbedding_norm,norm_smul,
      Real.norm_eq_abs,hn,mul_one,y,t]; rfl)
  rw [sublevelRegion_radialSquared ha has]
  change dist (representative z) cubeCenter < a
  rw [dist_eq_norm]
  change ‖v‖ < a
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

lemma radial_sublevelVolume_le (E : Set Torus) {r : ℝ} (hr : 0 ≤ r) (hrs : r ≤ 1/4) :
    sublevelVolume E radialSquared (r^2) ≤ r^3*(Real.pi*4/3) := by
  unfold sublevelVolume
  rw [sublevelRegion_radialSquared hr hrs]
  apply (measureReal_mono inter_subset_right).trans_eq
  rw [Measure.real,volume_cubeBall hr (by linarith),ENNReal.toReal_ofReal (by positivity)]

lemma plane_relative_gradient_norm (f : Plane → ℝ) (y : Plane) (p : Plane →L[ℝ] ℝ) :
    ‖gradient f y-(InnerProductSpace.toDual ℝ Plane).symm p‖ = ‖fderiv ℝ f y-p‖ := by
  rw [gradient,← map_sub,(InnerProductSpace.toDual ℝ Plane).symm.norm_map]

theorem isMinimizerAt_graph_interpolation_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ η C : ℝ, 0 < η ∧ 0 ≤ C ∧ ∀ (n : Cover), ‖n‖ = 1 →
      ∀ (χ g u : Plane → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → ContDiff ℝ (⊤ : ℕ∞) g →
        ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ (p : Plane →L[ℝ] ℝ) (s q H a b D B K : ℝ),
        0 < a → a < b → b < 1/4 → b^3*(Real.pi*8/3) < η →
        0 ≤ D → (∀ y, ‖fderiv ℝ χ y‖ ≤ D) → (∀ y, χ y ∈ Icc 0 1) →
        (∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1) →
        (∀ y, q ≤ ‖y‖ → χ y = 0) →
        (∀ y, ‖y‖ < q → |g y| ≤ H) → (∀ y, ‖y‖ < q → |u y| ≤ H) →
        q+H ≤ a → (∀ t, ‖deriv Real.smoothTransition t‖ ≤ K) →
        sublevelVolume (E ∆ torusGraphRegion cubeCenter n g) radialSquared (b^2) < B →
        bundleOrientedExcess μ (graphSlopeNormal n ((InnerProductSpace.toDual ℝ Plane).symm p)) a ≤
          3/2*((∫ y in Metric.ball (0 : Plane) b \ Metric.ball 0 s, ‖fderiv ℝ g y-p‖^2)+
            (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ u y-p‖^2)+
            D^2*(∫ y in Metric.ball (0 : Plane) b, (u y-g y)^2))+
            4*K*b*B/(b^2-a^2)+C*b^3 := by
  obtain ⟨η,C,hη,hC,hcomp⟩ := isMinimizerAt_oriented_interior_low_slice hV hE hmin hμ
  refine ⟨η,C*(Real.pi*8/3),hη,by positivity,?_⟩
  intro n hn χ g u hχ hg hu p s q H a b D B K ha hab hbs hsmall hD hd hb hone hzero hgH huH hmargin hK hvol
  have hbpos : 0 < b := ha.trans hab
  let v := graphBlend χ g u
  have hv := graphBlend_contDiff hχ hg hu
  have hsupp : torusGraphRegion cubeCenter n g ∆ torusGraphRegion cubeCenter n v ⊆
      sublevelRegion radialSquared (a^2) :=
    torusGraphRegion_interior_symmDiff hn ha.le (hab.le.trans hbs.le) hmargin
      (fun y hy ↦ (graphBlend_eq_of_zero (hzero y hy)).symm) hgH
      (fun y hy ↦ graphBlend_abs_le (hb y) (hgH y hy) (huH y hy))
  have htot : sublevelVolume (E ∆ torusGraphRegion cubeCenter n v) radialSquared (b^2) <
      b^3*(Real.pi*8/3) := by
    apply (radial_sublevelVolume_le _ (ha.trans hab).le hbs.le).trans_lt
    have hbp : 0 < b^3*Real.pi := by positivity
    nlinarith
  have hh := hcomp n hn v hv ((InnerProductSpace.toDual ℝ Plane).symm p)
    (torusGraphRegion cubeCenter n g) (measurableSet_torusGraphRegion _ _ hg.continuous)
    a b B (b^3*(Real.pi*8/3)) K ha hab hbs hsmall hK hsupp hvol htot
  have he := graphBlend_relative_energy_cutoff hχ hg hu hb hD hd hone p (b := b)
  simp_rw [plane_relative_gradient_norm] at hh
  dsimp only [v] at hh
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace CubicTorus

def planeAnnulus (ρ δ : ℝ) (i : ℕ) : Set Plane :=
  Metric.ball 0 (ρ+(i+1)*δ) \ Metric.ball 0 (ρ+i*δ)

lemma planeAnnulus_pairwise {ρ δ : ℝ} (hδ : 0 ≤ δ) :
    Pairwise (fun i j ↦ Disjoint (planeAnnulus ρ δ i) (planeAnnulus ρ δ j)) := by
  intro i j hij
  wlog hle : i < j generalizing i j
  · exact (this hij.symm (lt_of_le_of_ne (Nat.le_of_not_gt hle) hij.symm)).symm
  apply disjoint_left.mpr
  intro x hxi hxj
  apply hxj.2
  apply Metric.ball_subset_ball (show ρ+(i+1)*δ ≤ ρ+j*δ from ?_) hxi.1
  have hc : (i : ℝ)+1 ≤ j := by exact_mod_cast hle
  nlinarith

lemma planeAnnulus_subset {ρ δ : ℝ} (hδ : 0 ≤ δ) {N i : ℕ} (hi : i < N) :
    planeAnnulus ρ δ i ⊆ Metric.ball (0 : Plane) (ρ+N*δ) := by
  intro x hx
  apply Metric.ball_subset_ball (show ρ+(i+1)*δ ≤ ρ+N*δ from ?_) hx.1
  have hc : (i : ℝ)+1 ≤ N := by exact_mod_cast hi
  nlinarith

lemma planeAnnulus_integral_pigeonhole {ρ δ : ℝ} (hδ : 0 ≤ δ)
    {N : ℕ} (hN : 0 < N) {f : Plane → ℝ}
    (hf : IntegrableOn f (Metric.ball (0 : Plane) (ρ+N*δ)))
    (hpos : ∀ x, 0 ≤ f x) :
    ∃ i : Fin N, (∫ x in planeAnnulus ρ δ i, f x) ≤
      (∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x)/(N : ℝ) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  have hsum : (∑ i : Fin N, ∫ x in planeAnnulus ρ δ i, f x) ≤
      ∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x := by
    rw [← integral_iUnion_fintype (s := fun i : Fin N ↦ planeAnnulus ρ δ i)
      (fun _ ↦ measurableSet_ball.diff measurableSet_ball)
      (fun i j hij ↦ planeAnnulus_pairwise hδ (Fin.val_ne_of_ne hij))
      (fun i ↦ hf.mono_set (planeAnnulus_subset hδ i.isLt))]
    exact setIntegral_mono_set hf (Eventually.of_forall hpos)
      (iUnion_subset fun i ↦ planeAnnulus_subset hδ i.isLt).eventuallyLE
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hc : (∑ _i : Fin N, (∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x)/(N : ℝ)) =
      ∫ x in Metric.ball (0 : Plane) (ρ+N*δ), f x := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  obtain ⟨i,_,hi⟩ := Finset.exists_le_of_sum_le (s := Finset.univ)
    Finset.univ_nonempty (hsum.trans_eq hc.symm)
  exact ⟨i,hi⟩

lemma finite_subsequence_constant {ι : Type*} [Finite ι] (f : ℕ → ι) :
    ∃ i : ι, ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ k, f (ψ k) = i := by
  obtain ⟨i,hi⟩ := Finite.exists_infinite_fiber f
  have hh : ∃ᶠ k in atTop, f k = i := by
    apply Nat.frequently_atTop_iff_infinite.mpr
    exact Set.infinite_coe_iff.mp hi
  obtain ⟨ψ,hψ,hf⟩ := extraction_of_frequently_atTop hh
  exact ⟨i,ψ,hψ,hf⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_fderiv_relative_integrable {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : Plane →L[ℝ] ℝ) (r : ℝ) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ g y-p‖^2) (Metric.ball (0 : Plane) r) :=
  ((((hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Plane) r)).mono_set Metric.ball_subset_closedBall

lemma exists_plane_interpolation_bump {s q : ℝ} (hs : 0 < s) (hsq : s < q) :
    ∃ (χ : Plane → ℝ) (D : ℝ), ContDiff ℝ (⊤ : ℕ∞) χ ∧ 0 ≤ D ∧
      (∀ y, ‖fderiv ℝ χ y‖ ≤ D) ∧ (∀ y, χ y ∈ Icc 0 1) ∧
      (∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1) ∧
      (∀ y, q ≤ ‖y‖ → χ y = 0) := by
  let χ : ContDiffBump (0 : Plane) := ⟨s,q,hs,hsq⟩
  obtain ⟨D,hD⟩ := (χ.hasCompactSupport.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((χ.contDiff : ContDiff ℝ (⊤ : ℕ∞) χ).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous
  refine ⟨χ,max D 0,χ.contDiff,le_max_right _ _,fun y ↦ (hD y).trans (le_max_left _ _),
    fun y ↦ ⟨χ.nonneg,χ.le_one⟩,fun y hy ↦ χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),?_⟩
  intro y hy
  exact χ.zero_of_le_dist (by simpa only [dist_zero_right] using hy)

theorem strong_L2_annulus_replacement {θ : ℝ} (hθ : 0 < θ)
    (f : ℕ → Plane → ℝ) (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (p : Plane →L[ℝ] ℝ)
    {A H : ℝ} (_hA : 0 ≤ A)
    (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
    (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
    (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s q a b D : ℝ) (χ : Plane → ℝ) (ψ : ℕ → ℕ),
      θ ≤ s ∧ s < q ∧ q < a ∧ a < b ∧ b ≤ 2*θ ∧ StrictMono ψ ∧
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ 0 ≤ D ∧ (∀ y, ‖fderiv ℝ χ y‖ ≤ D) ∧
      (∀ y, χ y ∈ Icc 0 1) ∧ (∀ y ∈ Metric.ball (0 : Plane) s, χ y = 1) ∧
      (∀ y, q ≤ ‖y‖ → χ y = 0) ∧
      ∀ᶠ i in atTop, (∫ y in Metric.ball (0 : Plane) b,
        ‖fderiv ℝ (graphBlend χ (f (ψ i)) u) y-p‖^2) ≤ 3*H+ε := by
  obtain ⟨N,hNlarge⟩ := exists_nat_gt (max 0 (6*A/ε))
  have hNr : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hNlarge
  have hN : 0 < N := by exact_mod_cast hNr
  have hsmall : A/(N : ℝ) < ε/6 := by
    have hlarge : 6*A/ε < N := (le_max_right _ _).trans_lt hNlarge
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hNr]
    nlinarith
  let δ := θ/(N : ℝ)
  have hδ : 0 < δ := div_pos hθ hNr
  have heq : θ+(N : ℝ)*δ = 2*θ := by dsimp [δ]; field_simp; ring
  have hex (i : ℕ) : ∃ j : Fin N, (∫ y in planeAnnulus θ δ j, ‖fderiv ℝ (f i) y-p‖^2) ≤ A/N := by
    obtain ⟨j,hj⟩ := planeAnnulus_integral_pigeonhole hδ.le hN
      (f := fun y ↦ ‖fderiv ℝ (f i) y-p‖^2)
      (heq ▸ plane_fderiv_relative_integrable (hf i) p (2*θ)) (fun y ↦ sq_nonneg _)
    refine ⟨j,hj.trans ?_⟩
    rw [heq]
    exact div_le_div_of_nonneg_right (henergy i) hNr.le
  choose j hj using hex
  obtain ⟨k,ψ,hψ,hconst⟩ := finite_subsequence_constant j
  let s := θ+(k : ℝ)*δ
  let b := θ+((k : ℝ)+1)*δ
  let q := (2*s+b)/3
  let a := (s+2*b)/3
  have hs : θ ≤ s := by
    have hk : 0 ≤ (k : ℝ)*δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    dsimp [s]
    linarith
  have hsb : s < b := by dsimp [s,b]; nlinarith
  have hb : b ≤ 2*θ := by
    have hk : (k : ℝ)+1 ≤ N := by exact_mod_cast k.isLt
    rw [← heq]
    dsimp [b]
    nlinarith
  have hsq : s < q := by dsimp [q]; linarith
  have hqa : q < a := by dsimp [q,a]; linarith
  have hab : a < b := by dsimp [a]; linarith
  obtain ⟨χ,D,hχ,hD,hd,hχb,hone,hzero⟩ := exists_plane_interpolation_bump (hθ.trans_le hs) hsq
  refine ⟨s,q,a,b,D,χ,ψ,hs,hsq,hqa,hab,hb,hψ,hχ,hD,hd,hχb,hone,hzero,?_⟩
  have hc : Tendsto (fun i ↦ D^2*(∫ y in Metric.ball (0 : Plane) (2*θ), (f (ψ i) y-u y)^2))
      atTop (𝓝 0) := by simpa using (hconv.comp hψ.tendsto_atTop).const_mul (D^2)
  filter_upwards [hc.eventually (gt_mem_nhds (show 0 < ε/6 by positivity))] with i hi
  have hdiff : D^2*(∫ y in Metric.ball (0 : Plane) b, (u y-f (ψ i) y)^2) ≤
      D^2*(∫ y in Metric.ball (0 : Plane) (2*θ), (f (ψ i) y-u y)^2) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg D)
    have hsq (y : Plane) : (u y-f (ψ i) y)^2 = (f (ψ i) y-u y)^2 := by ring
    simp_rw [hsq]
    exact setIntegral_mono_set
      ((((hf (ψ i)).continuous.sub hu.continuous).pow 2).continuousOn.integrableOn_compact
        (isCompact_closedBall (0 : Plane) (2*θ)) |>.mono_set Metric.ball_subset_closedBall)
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hb).eventuallyLE
  have hharm : (∫ y in Metric.ball (0 : Plane) b, ‖fderiv ℝ u y-p‖^2) ≤ H :=
    (setIntegral_mono_set (plane_fderiv_relative_integrable hu p (2*θ))
      (Eventually.of_forall fun y ↦ sq_nonneg _) (Metric.ball_subset_ball hb).eventuallyLE).trans hH
  have hring : (∫ y in Metric.ball (0 : Plane) b \ Metric.ball 0 s, ‖fderiv ℝ (f (ψ i)) y-p‖^2) ≤ A/N := by
    have hh := hj (ψ i)
    rw [hconst i] at hh
    exact hh
  have hh := graphBlend_relative_energy_cutoff hχ (hf (ψ i)) hu hχb hD hd hone p (b := b)
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_mul_of_bound_on_support {X : Type*} [PseudoMetricSpace X]
    {ζ f : X → ℝ} {K L A B : ℝ≥0}
    (hζ : LipschitzWith K ζ) (hf : LipschitzWith L f)
    (hA : ∀ x, |ζ x| ≤ A) (hB : ∀ x ∈ Function.support ζ, |f x| ≤ B) :
    LipschitzWith (A * L + B * K) (fun x ↦ ζ x * f x) := by
  have hbound (x y : X) (hy : ζ y ≠ 0) :
      |ζ x * f x - ζ y * f y| ≤ (A * L + B * K : ℝ≥0) * dist x y := by
    have he : ζ x * f x - ζ y * f y = ζ x * (f x - f y) + f y * (ζ x - ζ y) := by ring
    rw [he]
    have h₁ := hf.dist_le_mul x y
    have h₂ := hζ.dist_le_mul x y
    simp only [Real.dist_eq] at h₁ h₂
    calc
      _ ≤ |ζ x| * |f x - f y| + |f y| * |ζ x - ζ y| := by
        simpa only [abs_mul] using abs_add_le (ζ x * (f x - f y)) (f y * (ζ x - ζ y))
      _ ≤ (A : ℝ) * (L * dist x y) + (B : ℝ) * (K * dist x y) :=
        add_le_add (mul_le_mul (hA x) h₁ (abs_nonneg _) (NNReal.coe_nonneg _))
          (mul_le_mul (hB y hy) h₂ (abs_nonneg _) (NNReal.coe_nonneg _))
      _ = _ := by push_cast; ring
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  by_cases hy : ζ y = 0
  · by_cases hx : ζ x = 0
    · simp only [hx, hy, zero_mul, sub_self, abs_zero]
      positivity
    · simpa only [abs_sub_comm, dist_comm] using hbound y x hx
  · exact hbound x y hy

lemma exists_lipschitz_cutoff_mul {X : Type*} [PseudoMetricSpace X]
    {ζ f : X → ℝ} {K L : ℝ≥0} (hζ : LipschitzWith K ζ) (hf : LipschitzWith L f)
    (hs : HasCompactSupport ζ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x ↦ ζ x * f x) := by
  obtain ⟨A, hA⟩ := hs.exists_bound_of_continuous hζ.continuous
  obtain ⟨B, hB⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  refine ⟨A.toNNReal * L + B.toNNReal * K,
    lipschitz_mul_of_bound_on_support hζ hf ?_ ?_⟩
  · intro x
    have hh : |ζ x| ≤ A := by simpa only [Real.norm_eq_abs] using hA x
    exact hh.trans (le_max_left _ _)
  · intro x hx
    have hh : |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x (subset_tsupport _ hx)
    exact hh.trans (le_max_left _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem local_planar_H1_harmonic_approximation {R : ℝ} (hR : 0 < R)
    {S : Set Plane} (hS : IsCompact S) (hball : Metric.ball (0 : Plane) (4 * R) ⊆ S)
    {ζ : Plane → ℝ} {Lζ : ℝ≥0} (hζ : ContDiff ℝ 1 ζ)
    (hζLip : LipschitzWith Lζ ζ) (hζs : tsupport ζ ⊆ S)
    (hζone : ∀ x ∈ Metric.ball (0 : Plane) (4 * R), ζ x = 1)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ x, |ζ x| ≤ A) (hb : ∀ x, ‖fderiv ℝ ζ x‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : ℕ → Plane → ℝ) (L : ℕ → ℝ≥0),
        (∀ i, LipschitzWith (L i) (f i)) →
      ∀ M D : ℝ, 0 ≤ D →
        (∀ i, (∫ x in S, f i x ^ 2) ≤ M) →
        (∀ i, (∫ x in S, ‖fderiv ℝ (f i) x‖ ^ 2) ≤ D) →
        (∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Metric.ball 0 (4 * R) →
          Tendsto (fun i ↦ ∫ y, f i y * Δ φ y) atTop (𝓝 0)) →
      ∃ (ψ : ℕ → ℕ) (b : ℝ) (l : Plane →L[ℝ] ℝ), StrictMono ψ ∧
        ∀ ρ ε : ℝ, 0 ≤ ρ → ρ ≤ R → 0 < ε →
          ∀ᶠ i in atTop,
            (∫ x in Metric.ball (0 : Plane) ρ, (f (ψ i) x - b - l x) ^ 2) ≤
              C * M * ρ ^ 6 + ε := by
  obtain ⟨C₀, hC₀, happ⟩ := planar_H1_harmonic_approximation hR hS hball
  refine ⟨C₀ * (A ^ 2 + 1), by positivity, ?_⟩
  intro f L hf M D hD hM hgrad hw
  have hMnon : 0 ≤ M := (integral_nonneg (fun x ↦ sq_nonneg (f 0 x))).trans (hM 0)
  have hs : HasCompactSupport ζ := hS.of_isClosed_subset isClosed_closure hζs
  let u : ℕ → Plane → ℝ := fun i x ↦ ζ x * f i x
  have huLip (i : ℕ) := exists_lipschitz_cutoff_mul hζLip (hf i) hs
  choose K hK using huLip
  have henergy (i : ℕ) := lipschitz_cutoff_H1 (μ := volume) (hf i) hζ hs hS hζs hA hB ha hb
  have hglobalM (i : ℕ) : (∫ x, u i x ^ 2) ≤ A ^ 2 * M :=
    (henergy i).2.2.1.trans (mul_le_mul_of_nonneg_left (hM i) (sq_nonneg A))
  have hglobalD (i : ℕ) : (∫ x, ‖fderiv ℝ (u i) x‖ ^ 2) ≤
      2 * A ^ 2 * D + 2 * B ^ 2 * M := by
    exact (henergy i).2.2.2.trans (add_le_add
      (mul_le_mul_of_nonneg_left (hgrad i) (by positivity))
      (mul_le_mul_of_nonneg_left (hM i) (by positivity)))
  have hw' (φ : Plane → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφs : HasCompactSupport φ)
      (hφb : tsupport φ ⊆ Metric.ball 0 (4 * R)) :
      Tendsto (fun i ↦ ∫ y, u i y * Δ φ y) atTop (𝓝 0) := by
    have he (i : ℕ) : (fun y ↦ u i y * Δ φ y) = (fun y ↦ f i y * Δ φ y) := by
      funext y
      by_cases hy : y ∈ tsupport φ
      · simp only [u, hζone y (hφb hy), one_mul]
      · have hz : Δ φ y = 0 := image_eq_zero_of_notMem_tsupport
          (fun hh ↦ hy (laplacian_tsupport_subset hφ hh))
        simp only [hz, mul_zero]
    simpa only [he] using hw φ hφ hφs hφb
  obtain ⟨ψ, b, l, hψ, he⟩ := happ u K hK (fun i ↦ (henergy i).1)
    (fun i ↦ (henergy i).2.1) (A ^ 2 * M) (2 * A ^ 2 * D + 2 * B ^ 2 * M)
    (by positivity) hglobalM hglobalD hw'
  refine ⟨ψ, b, l, hψ, fun ρ ε hρ hρR hε ↦ ?_⟩
  filter_upwards [he ρ ε hρ hρR hε] with i hi
  have heq : (∫ x in Metric.ball (0 : Plane) ρ, (u (ψ i) x - b - l x) ^ 2) =
      ∫ x in Metric.ball (0 : Plane) ρ, (f (ψ i) x - b - l x) ^ 2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    have hx' := (Metric.ball_subset_ball (by linarith : ρ ≤ 4 * R)) hx
    simp only [u, hζone x hx', one_mul]
  rw [heq] at hi
  apply hi.trans
  have hm : C₀ * (A ^ 2 * M) * ρ ^ 6 ≤ C₀ * (A ^ 2 + 1) * M * ρ ^ 6 := by
    have ht : A ^ 2 * M ≤ (A ^ 2 + 1) * M := by nlinarith
    have ht' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht hC₀.le)
      (pow_nonneg hρ 6)
    nlinarith
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma lipschitz_centered_scale {X : Type*} [PseudoMetricSpace X]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a m : ℝ) :
    LipschitzWith (‖a‖₊ * K) (fun x ↦ a * (f x - m)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : a * (f x - m) - a * (f y - m) = a * (f x - f y) := by ring
  rw [Real.dist_eq, he, abs_mul]
  have hb := hf.dist_le_mul x y
  rw [Real.dist_eq] at hb
  simpa only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, mul_assoc] using
    mul_le_mul_of_nonneg_left hb (abs_nonneg a)

lemma lipschitz_centered_scale_gradient {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a m : ℝ) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y ↦ a * (f y - m)) x‖ ^ 2 =
      a ^ 2 * ‖fderiv ℝ f x‖ ^ 2 := by
  filter_upwards [hf.ae_differentiableAt] with x hx
  rw [fderiv_const_mul (hx.sub_const m), fderiv_sub_const m, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs]

lemma lipschitz_centered_scale_gradient_integral {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [μ.IsAddHaarMeasure]
    {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (a m : ℝ) (S : Set X) :
    (∫ x in S, ‖fderiv ℝ (fun y ↦ a * (f y - m)) x‖ ^ 2 ∂μ) =
      a ^ 2 * ∫ x in S, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_restrict_of_ae (lipschitz_centered_scale_gradient hf a m))

theorem planar_normalized_H1 {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {R e D : ℝ} (hR : 0 < R) (he : 0 < e)
    (henergy : (∫ x in planeSquare R, ‖fderiv ℝ f x‖ ^ 2) ≤ D * e ^ 2) :
    let m := (∫ y in planeSquare R, f y) / (2 * R) ^ 2
    let u := fun x ↦ e⁻¹ * (f x - m)
    (∫ x in planeSquare R, ‖fderiv ℝ u x‖ ^ 2) ≤ D ∧
    (∫ x in planeSquare R, u x ^ 2) ≤
      16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 * D := by
  dsimp only
  have hgrad := mul_le_mul_of_nonneg_left henergy (sq_nonneg e⁻¹)
  have heq : e⁻¹ ^ 2 * (D * e ^ 2) = D := by field_simp
  rw [heq] at hgrad
  refine ⟨?_, ?_⟩
  · rw [lipschitz_centered_scale_gradient_integral hf]
    exact hgrad
  · have heq' : (fun x ↦ (e⁻¹ * (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2)) ^ 2) =
        (fun x ↦ e⁻¹ ^ 2 * (f x - (∫ y in planeSquare R, f y) / (2 * R) ^ 2) ^ 2) := by
      funext x
      exact mul_pow _ _ 2
    rw [heq', integral_const_mul]
    have hp := mul_le_mul_of_nonneg_left (plane_square_poincare hf hR) (sq_nonneg e⁻¹)
    have hC : 0 ≤ 16 * R ^ 2 * ‖planeProductCoordinates.symm.toContinuousLinearMap‖ ^ 2 := by
      positivity
    have hb := mul_le_mul_of_nonneg_left hgrad hC
    nlinarith

lemma centered_scale_laplacian_pairing {f φ : Plane → ℝ} (hf : Continuous f)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hs : HasCompactSupport φ) (a m : ℝ) :
    (∫ x, (a * (f x - m)) * Δ φ x) = a * ∫ x, f x * Δ φ x := by
  have hl : Continuous (Δ φ) := compact_laplacian_continuous hφ
  have hls : HasCompactSupport (Δ φ) := hs.mono'
    ((subset_tsupport _).trans (laplacian_tsupport_subset hφ))
  have hi : Integrable (fun x ↦ f x * Δ φ x) :=
    (hf.mul hl).integrable_of_hasCompactSupport hls.mul_left
  have hli : Integrable (Δ φ) := hl.integrable_of_hasCompactSupport hls
  simp_rw [mul_assoc, sub_mul]
  rw [integral_const_mul, integral_sub hi (hli.const_mul m), integral_const_mul,
    integral_compact_laplacian_zero hφ hs, mul_zero, sub_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

def normalColumnCutoff (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : ℝ) where
  rIn := r / 3
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

lemma normalColumnCutoff_tsupport {r : ℝ} (hr : 0 < r) :
    tsupport (normalColumnCutoff r hr) ⊆ Icc (-r / 2) (r / 2) := by
  rw [(normalColumnCutoff r hr).tsupport_eq]
  intro t ht
  have hh : |t| ≤ r / 2 := by simpa [normalColumnCutoff, Real.norm_eq_abs] using ht
  exact ⟨by linarith [(abs_le.mp hh).1], (abs_le.mp hh).2⟩

lemma normalColumnCutoff_eventually_one {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    (normalColumnCutoff r hr : ℝ → ℝ) =ᶠ[𝓝 t] (fun _ ↦ (1 : ℝ)) := by
  apply (normalColumnCutoff r hr).eventuallyEq_one_of_mem_ball
  change dist t 0 < r / 3
  rw [dist_zero_right, Real.norm_eq_abs]
  linarith

lemma normalColumnCutoff_one {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    normalColumnCutoff r hr t = 1 :=
  (normalColumnCutoff_eventually_one hr ht).eq_of_nhds

lemma normalColumnCutoff_deriv_zero {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    deriv (normalColumnCutoff r hr) t = 0 := by
  rw [(normalColumnCutoff_eventually_one hr ht).deriv_eq]
  simp

lemma normalColumnCutoff_second_zero {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 4) :
    iteratedDeriv 2 (normalColumnCutoff r hr) t = 0 := by
  rw [((normalColumnCutoff_eventually_one hr ht).iteratedDeriv 2).eq_of_nhds]
  simp [iteratedDeriv_const]

lemma normalColumnTest_tsupport_ball (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    {r : ℝ} (hr : 0 < r) {φ : Plane → ℝ}
    (hφ : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    tsupport (normalScalarTest a n (normalColumnCutoff r hr) φ) ⊆ Metric.ball a r := by
  intro x hx
  have hh := normalScalarTest_tsupport a n (normalColumnCutoff r hr) φ hx
  have hv : |⟪n, x - a⟫| ≤ r / 2 := by
    have ht := normalColumnCutoff_tsupport hr hh.1
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hp : ‖normalPlaneCoordinates n (x - a)‖ ≤ r / 3 := by simpa using hφ hh.2
  have htri := norm_add_le (normalPlaneEmbedding n (normalPlaneCoordinates n (x - a)))
    (⟪n, x - a⟫ • n)
  rw [normalPlaneCoordinates_reconstruct hn, normalPlaneEmbedding_norm, norm_smul,
    Real.norm_eq_abs, hn, mul_one] at htri
  change dist x a < r
  rw [dist_eq_norm]
  linarith

lemma trapped_column_characteristic {U : Set Torus} {a n : Cover} (hn : ‖n‖ = 1)
    {r ε : ℝ} (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {y : Plane} (hy : ‖y‖ ≤ r / 3) {t : ℝ} (ht : |t| ≤ r / 2)
    (htout : r / 4 ≤ |t|) :
    characteristic U (quotientMap (normalColumnChart a n (t, y))) =
      (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t := by
  let x := normalColumnChart a n (t, y)
  have hx := normalColumnChart_ball a hn hr ht hy
  have hl : shortestLift (quotientMap x - quotientMap a) = x - a := by
    rw [← quotientMap_sub]
    exact shortestLift_quotientMap ((show ‖x - a‖ < r by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx).trans hrsmall)
  have hd : dist (quotientMap x) (quotientMap a) < r := by
    rw [dist_eq_norm, ← norm_shortestLift, hl]
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hnxt : ⟪n, shortestLift (quotientMap x - quotientMap a)⟫ = t := by
    rw [hl]
    exact normalColumnChart_height a hn t y
  have her : ε * r < r / 4 := by nlinarith
  change characteristic U (quotientMap x) = _
  by_cases htneg : t < 0
  · have hU : quotientMap x ∈ U := by
      apply htrap.2
      refine ⟨hd, ?_⟩
      rw [inner_neg_left, hnxt]
      rw [abs_of_neg htneg] at htout
      linarith
    simp [characteristic, hU, htneg]
  · have hU : quotientMap x ∉ U := by
      apply fun h ↦ htrap.1 (show quotientMap x ∈ normalCap (quotientMap a) n r (ε * r) from
        ⟨hd, by rw [hnxt]; rw [abs_of_nonneg (le_of_not_gt htneg)] at htout; linarith⟩)
        (subset_closure h)
    simp [characteristic, hU, htneg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integral_column_negative_indicator {r : ℝ} (hr : 0 < r) :
    (∫ t in Icc (-r / 4) (r / 4), (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) = r / 4 := by
  rw [setIntegral_indicator measurableSet_Iio]
  have he : Icc (-r / 4) (r / 4) ∩ Iio (0 : ℝ) = Ico (-r / 4) 0 := by
    ext t
    simp only [mem_inter_iff, mem_Icc, mem_Iio, mem_Ico]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · exact fun h ↦ ⟨⟨h.1, by linarith [h.2]⟩, h.2⟩
  rw [he, integral_const, smul_eq_mul, mul_one, measureReal_def, Measure.restrict_apply_univ,
    Real.volume_Ico, ENNReal.toReal_ofReal (by linarith : 0 ≤ 0 - -r / 4)]
  ring

lemma integrableOn_column_bounded {r : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ t, ‖f t‖ ≤ 1) : IntegrableOn f (Icc (-r / 4) (r / 4)) := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ hb)

lemma integral_column_cutoff {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : ∀ t, ‖f t‖ ≤ 1)
    (hphase : ∀ t, |t| ≤ r / 2 → r / 4 ≤ |t| →
      f t = (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) :
    (∫ t : ℝ, f t * normalColumnCutoff r hr t) =
      (∫ t in Icc (-r / 4) (r / 4), f t) - r / 4 +
        ∫ t in Iio (0 : ℝ), normalColumnCutoff r hr t := by
  let χ := normalColumnCutoff r hr
  let h : ℝ → ℝ := (Iio (0 : ℝ)).indicator (fun _ ↦ 1)
  let I := Icc (-r / 4) (r / 4)
  have hm : Measurable h := measurable_const.indicator measurableSet_Iio
  have hb' (t : ℝ) : ‖h t‖ ≤ 1 := by
    by_cases ht : t < 0 <;> simp [h, ht]
  have hfi : IntegrableOn f I := integrableOn_column_bounded hf hb
  have hhi : IntegrableOn h I := integrableOn_column_bounded hm hb'
  have hχi : Integrable (fun t ↦ h t * χ t) :=
    (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).bdd_mul
      hm.aestronglyMeasurable (ae_of_all _ hb')
  have he (t : ℝ) : f t * χ t = I.indicator (fun s ↦ f s - h s) t + h t * χ t := by
    by_cases ht : t ∈ I
    · rw [indicator_of_mem ht]
      have habs : |t| ≤ r / 4 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      rw [show χ t = 1 from normalColumnCutoff_one hr habs]
      ring
    · rw [indicator_of_notMem ht, zero_add]
      by_cases hs : t ∈ tsupport χ
      · have hs' := normalColumnCutoff_tsupport hr hs
        have hu : |t| ≤ r / 2 := abs_le.mpr ⟨by linarith [hs'.1], hs'.2⟩
        have hlo : r / 4 ≤ |t| := by
          by_contra! hn
          apply ht
          exact ⟨by linarith [(abs_lt.mp hn).1], (abs_lt.mp hn).2.le⟩
        rw [hphase t hu hlo]
      · rw [image_eq_zero_of_notMem_tsupport hs]
        simp
  change (∫ t : ℝ, f t * χ t) = _
  simp_rw [he]
  have hdiff : Integrable (I.indicator (fun s ↦ f s - h s)) := by
    exact hfi.integrable_indicator measurableSet_Icc |>.sub
      (hhi.integrable_indicator measurableSet_Icc) |>.congr (ae_of_all _ fun t ↦ by
        by_cases ht : t ∈ I <;> simp [ht])
  rw [integral_add hdiff hχi,
    integral_indicator measurableSet_Icc, integral_sub hfi hhi]
  change (∫ t in I, f t) - (∫ t in I, h t) + (∫ t, h t * χ t) = _
  rw [show (∫ t in I, h t) = r / 4 from integral_column_negative_indicator hr]
  congr 1
  simp only [h, ← indicator_mul_left, one_mul, integral_indicator measurableSet_Iio]
  rfl

lemma integral_column_cutoff_second {r : ℝ} (hr : 0 < r) {f : ℝ → ℝ}
    (hphase : ∀ t, |t| ≤ r / 2 → r / 4 ≤ |t| →
      f t = (Iio (0 : ℝ)).indicator (fun _ ↦ (1 : ℝ)) t) :
    (∫ t : ℝ, f t * iteratedDeriv 2 (normalColumnCutoff r hr) t) = 0 := by
  let χ := normalColumnCutoff r hr
  have he (t : ℝ) : f t * iteratedDeriv 2 χ t =
      (Iio (0 : ℝ)).indicator (iteratedDeriv 2 χ) t := by
    by_cases ht : |t| ≤ r / 4
    · have hz : iteratedDeriv 2 χ t = 0 := normalColumnCutoff_second_zero hr ht
      by_cases hneg : t < 0 <;> simp [hneg, hz]
    · by_cases hs : t ∈ tsupport χ
      · have hs' := normalColumnCutoff_tsupport hr hs
        have hu : |t| ≤ r / 2 := abs_le.mpr ⟨by linarith [hs'.1], hs'.2⟩
        rw [hphase t hu (le_of_not_ge ht)]
        simp only [← indicator_mul_left, one_mul]
      · have hz : iteratedDeriv 2 χ t = 0 := by
          have h0 : (χ : ℝ → ℝ) =ᶠ[𝓝 t] (fun _ ↦ 0) := notMem_tsupport_iff_eventuallyEq.mp hs
          simpa [iteratedDeriv_const] using (h0.iteratedDeriv 2).eq_of_nhds
        by_cases hneg : t < 0 <;> simp [hneg, hz]
  change (∫ t : ℝ, f t * iteratedDeriv 2 χ t) = 0
  simp_rw [he]
  rw [integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio,
    show iteratedDeriv 2 (χ : ℝ → ℝ) = deriv (deriv χ) from by
      rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]]
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) := by
    simpa using (χ.contDiff : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ)).iterate_deriv 1
  rw [χ.hasCompactSupport.deriv.integral_Iic_deriv_eq (hd.of_le (by simp))]
  exact normalColumnCutoff_deriv_zero hr (by simp; positivity)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma columnCutoff_second_contDiff {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv 2 (normalColumnCutoff r hr)) := by
  rw [iteratedDeriv_eq_iterate]
  exact (normalColumnCutoff r hr).contDiff.iterate_deriv 2

lemma columnCutoff_second_hasCompactSupport {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (iteratedDeriv 2 (normalColumnCutoff r hr)) := by
  rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  exact (normalColumnCutoff r hr).hasCompactSupport.deriv.deriv

theorem integral_column_laplacian {U : Set Torus} (hU : MeasurableSet U)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3)) :
    (∫ x : Cover, characteristic U (quotientMap x) *
      Δ (normalScalarTest a n (normalColumnCutoff r hr) φ) x) =
      ∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y := by
  let χ := normalColumnCutoff r hr
  let ψ := normalScalarTest a n χ φ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ) := χ.contDiff
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := normalScalarTest_contDiff a n hχ hφ
  have hψs : HasCompactSupport ψ := (isCompact_closedBall a r).of_isClosed_subset isClosed_closure
    ((normalColumnTest_tsupport_ball a hn hr hs).trans Metric.ball_subset_closedBall)
  have hψi : Integrable (Δ ψ) := (compact_laplacian_continuous hψ).integrable_of_hasCompactSupport
    (hψs.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hψ))
  have hbulk : Integrable (fun x : Cover ↦ characteristic U (quotientMap x) * Δ ψ x) :=
    hψi.bdd_mul ((measurable_characteristic hU).comp measurable_quotientMap).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by simpa only [Real.norm_eq_abs] using characteristic_bound U (quotientMap x))
  have hφs : HasCompactSupport φ := (isCompact_closedBall (0 : Plane) (r / 3)).of_isClosed_subset
    isClosed_closure hs
  have hφi : Integrable (Δ φ) := (compact_laplacian_continuous hφ).integrable_of_hasCompactSupport
    (hφs.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hφ))
  let C := ∫ t in Iio (0 : ℝ), χ t
  have he (y : Plane) :
      (∫ t : ℝ, characteristic U (quotientMap (normalColumnChart a n (t, y))) *
        Δ ψ (normalColumnChart a n (t, y))) =
        normalColumnHeight U (quotientMap a) n r y * Δ φ y + C * Δ φ y := by
    have hl (t : ℝ) : Δ ψ (normalColumnChart a n (t, y)) =
        iteratedDeriv 2 χ t * φ y + χ t * Δ φ y := by
      rw [laplacian_normalScalarTest a hn hχ hφ,
        normalColumnChart_height a hn, normalColumnChart_projection a hn]
    simp_rw [hl]
    by_cases hy : y ∈ tsupport φ
    · have hyn : ‖y‖ ≤ r / 3 := by simpa using hs hy
      let f : ℝ → ℝ := fun t ↦ characteristic U (quotientMap (normalColumnChart a n (t, y)))
      have hfm : Measurable f := (measurable_characteristic hU).comp
        (measurable_quotientMap.comp ((normalColumnChart a n).measurable.comp
          (measurable_id.prodMk measurable_const)))
      have hfb (t : ℝ) : ‖f t‖ ≤ 1 := by
        simpa only [f, Real.norm_eq_abs] using characteristic_bound U
          (quotientMap (normalColumnChart a n (t, y)))
      have hphase := fun t ht ho ↦ trapped_column_characteristic hn hr hrsmall hε htrap hyn
        (t := t) ht ho
      have hfχ : Integrable (fun t ↦ f t * χ t) :=
        (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport).bdd_mul
          hfm.aestronglyMeasurable (ae_of_all _ hfb)
      have hfχ2 : Integrable (fun t ↦ f t * iteratedDeriv 2 χ t) :=
        ((columnCutoff_second_contDiff hr).continuous.integrable_of_hasCompactSupport
          (columnCutoff_second_hasCompactSupport hr)).bdd_mul
            hfm.aestronglyMeasurable (ae_of_all _ hfb)
      change (∫ t : ℝ, f t * (iteratedDeriv 2 χ t * φ y + χ t * Δ φ y)) = _
      simp_rw [mul_add, ← mul_assoc]
      rw [integral_add (hfχ2.mul_const _) (hfχ.mul_const _), integral_mul_const, integral_mul_const,
        integral_column_cutoff_second hr hphase, zero_mul, zero_add,
        integral_column_cutoff hr hfm hfb hphase]
      have hfcol : (∫ t in Icc (-r / 4) (r / 4), f t) - r / 4 =
          normalColumnHeight U (quotientMap a) n r y := by
        unfold normalColumnHeight
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro t _
        exact normalColumnChart_characteristic U a hn t y
      rw [hfcol]
      ring
    · have hzφ := image_eq_zero_of_notMem_tsupport hy
      have hzΔ := image_eq_zero_of_notMem_tsupport (fun hh ↦ hy (laplacian_tsupport_subset hφ hh))
      simp [hzφ, hzΔ]
  have hheighti : Integrable (fun y : Plane ↦ normalColumnHeight U (quotientMap a) n r y * Δ φ y) :=
    hφi.bdd_mul (measurable_normalColumnHeight hU (quotientMap a) n r).aestronglyMeasurable
      (ae_of_all _ fun y ↦ by simpa only [Real.norm_eq_abs] using
        normalColumnHeight_bound hU (quotientMap a) n hr.le y)
  change (∫ x : Cover, characteristic U (quotientMap x) * Δ ψ x) = _
  rw [integral_normalColumnChart a n hbulk]
  simp_rw [he]
  rw [integral_add hheighti (hφi.const_mul C), integral_const_mul,
    integral_compact_laplacian_zero hφ hφs, mul_zero, add_zero]

theorem weakCMC_column_height_identity {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H * directionalFlux U D.coordinate D.function)
    {a n : Cover} (hn : ‖n‖ = 1) {r ε : ℝ}
    (hr : 0 < r) (hrsmall : r < 1 / 2) (hε : ε < 1 / 4)
    (htrap : normalCap (quotientMap a) n r (ε * r) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap a) (-n) r (ε * r) ⊆ U)
    {φ : Plane → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : tsupport φ ⊆ Metric.closedBall (0 : Plane) (r / 3))
    (hcell : Metric.closedBall a r ⊆ {x | ∀ i, 0 < x i ∧ x i < 1}) :
    let ψ := normalScalarTest a n (normalColumnCutoff r hr) φ
    (∫ y : Plane, normalColumnHeight U (quotientMap a) n r y * Δ φ y) +
      H * (∫ z, ψ z.1 * ⟪(z.2 : Cover), n⟫ ∂(μ : Measure NormalBundle)) =
      (1 / 2 : ℝ) * ∫ z, ‖(z.2 : Cover) - n‖ ^ 2 * fderiv ℝ ψ z.1 (z.2 : Cover)
        ∂(μ : Measure NormalBundle) := by
  dsimp only
  let χ := normalColumnCutoff r hr
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (χ : ℝ → ℝ) := χ.contDiff
  have ht := weakCMC_trapped_scalar_identity hU hμ hH hn hrsmall htrap
    (normalScalarTest_contDiff a n hχ hφ) (normalColumnTest_tsupport_ball a hn hr hs) hcell
    (fun x hx ↦ by
      rw [fderiv_normalScalarTest_normal a hn hχ hφ,
        normalColumnCutoff_deriv_zero hr (hx.trans (by nlinarith : ε * r ≤ r / 4)), zero_mul])
  simp_rw [divergence_gradient_eq_laplacian (normalScalarTest_contDiff a n hχ hφ)] at ht
  rw [integral_column_laplacian hU.measurableSet hn hr hrsmall hε htrap hφ hs] at ht
  exact ht

end CubicTorus

end
end

end

end OAI
