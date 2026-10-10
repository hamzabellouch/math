import Mathlib
import OAI.Geometry.NearbyLagrangian.HomogeneousCritical
import OAI.Geometry.NearbyLagrangian.JetTopology
import OAI.Geometry.NearbyLagrangian.JetApproximation

namespace OAI

/-! Smooth approximation and close homotopies of homogeneous families. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology
open Set Filter ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma regular_of_sphere {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x)
    (hr : ∀ x, ‖x‖ = 1 → fderiv ℝ g x ≠ 0) :
    ∀ x, x ≠ 0 → fderiv ℝ g x ≠ 0 := by
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : ‖x‖ • NormedSpace.normalize x = x := NormedSpace.norm_smul_normalize x
  have hd := MixedRadial.fderiv_smul_degree_two (hg.differentiable one_ne_zero)
    (fun r hr w => by simpa only [smul_eq_mul] using hh r hr w) hn
    (NormedSpace.normalize x)
  rw [he] at hd
  rw [hd]
  exact smul_ne_zero hn.ne' (hr _ (NormedSpace.norm_normalize hx))

lemma fderiv_blend (f : RegularHomogeneous E) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (t : ℝ) (x : E) :
    fderiv ℝ (fun w => f w + t * (g w - f w)) x =
      fderiv ℝ f x + t • (fderiv ℝ g x - fderiv ℝ f x) := by
  exact ((f.differentiable x).hasFDerivAt.add
    (((hg.differentiable one_ne_zero x).hasFDerivAt.sub
      (f.differentiable x).hasFDerivAt).const_smul t)).fderiv

def controlledBlend (f : RegularHomogeneous E) {g : E → ℝ} (hg : ContDiff ℝ 1 g)
    (hh : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x)
    {c : ℝ} (_hc : 0 < c) (hm : ∀ x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ f x‖)
    (he : ∀ x, ‖x‖ = 1 → ‖fderiv ℝ g x - fderiv ℝ f x‖ < c)
    (t : unitInterval) : RegularHomogeneous E where
  toFun w := f w + (t : ℝ) * (g w - f w)
  contDiff := f.contDiff.add ((hg.sub f.contDiff).const_smul (t : ℝ))
  homogeneity r hr w := by rw [f.homogeneity r hr w, hh r hr w]; ring
  regular := by
    apply regular_of_sphere
      (f.contDiff.add ((hg.sub f.contDiff).const_smul (t : ℝ)))
      (fun r hr w => by rw [f.homogeneity r hr w, hh r hr w]; ring)
    intro x hx hd
    change fderiv ℝ (fun w => f w + (t : ℝ) * (g w - f w)) x = 0 at hd
    rw [fderiv_blend f hg] at hd
    have ht : ‖(t : ℝ) • (fderiv ℝ g x - fderiv ℝ f x)‖ < c := by
      rw [norm_smul, Real.norm_of_nonneg t.property.1]
      exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt (he x hx)
    have hz : fderiv ℝ f x = -((t : ℝ) • (fderiv ℝ g x - fderiv ℝ f x)) :=
      eq_neg_of_add_eq_zero_left hd
    have hmx := hm x hx
    rw [hz, norm_neg] at hmx
    exact (not_lt_of_ge hmx) ht

@[simp] lemma controlledBlend_zero (f : RegularHomogeneous E) {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x)
    {c : ℝ} (hc : 0 < c) (hm : ∀ x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ f x‖)
    (he : ∀ x, ‖x‖ = 1 → ‖fderiv ℝ g x - fderiv ℝ f x‖ < c) :
    controlledBlend f hg hh hc hm he 0 = f := by ext w; simp [controlledBlend]

@[simp] lemma controlledBlend_one_apply (f : RegularHomogeneous E) {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x)
    {c : ℝ} (hc : 0 < c) (hm : ∀ x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ f x‖)
    (he : ∀ x, ‖x‖ = 1 → ‖fderiv ℝ g x - fderiv ℝ f x‖ < c) (w : E) :
    controlledBlend f hg hh hc hm he 1 w = g w := by simp [controlledBlend]

lemma continuous_controlledBlend (f : RegularHomogeneous E) {g : E → ℝ}
    (hg : ContDiff ℝ 1 g) (hh : ∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x)
    {c : ℝ} (hc : 0 < c) (hm : ∀ x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ f x‖)
    (he : ∀ x, ‖x‖ = 1 → ‖fderiv ℝ g x - fderiv ℝ f x‖ < c) :
    Continuous (controlledBlend f hg hh hc hm he) := by
  apply continuous_of_joint_jet
  · change Continuous (fun p : unitInterval × Metric.sphere (0:E) 1 =>
      f p.2 + (p.1 : ℝ) * (g p.2 - f p.2))
    exact (f.contDiff.continuous.comp (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((hg.continuous.comp (continuous_subtype_val.comp continuous_snd)).sub
          (f.contDiff.continuous.comp (continuous_subtype_val.comp continuous_snd))))
  · change Continuous (fun p : unitInterval × Metric.sphere (0:E) 1 =>
      fderiv ℝ (fun w => f w + (p.1 : ℝ) * (g w - f w)) p.2)
    simp only [fderiv_blend f hg]
    exact ((f.contDiff.continuous_fderiv one_ne_zero).comp
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((hg.continuous_fderiv one_ne_zero).comp
          (continuous_subtype_val.comp continuous_snd)).sub
          ((f.contDiff.continuous_fderiv one_ne_zero).comp
            (continuous_subtype_val.comp continuous_snd))))

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma norm_value_sub_le_jet (f g : RegularHomogeneous E) {x : E} (hx : ‖x‖ = 1) :
    ‖f x - g x‖ ≤ ‖f.jet - g.jet‖ := by
  let u : Metric.sphere (0:E) 1 := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact ((f.jet.1 - g.jet.1).norm_coe_le_norm u).trans (norm_fst_le (f.jet - g.jet))

lemma norm_derivative_sub_le_jet (f g : RegularHomogeneous E) {x : E} (hx : ‖x‖ = 1) :
    ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ ‖f.jet - g.jet‖ := by
  let u : Metric.sphere (0:E) 1 := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact ((f.jet.2 - g.jet.2).norm_coe_le_norm u).trans (norm_snd_le (f.jet - g.jet))

variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]

theorem exists_smooth_family_approx {f : B → RegularHomogeneous E} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : B → E → ℝ,
      (∀ b, ContDiff ℝ 1 (g b)) ∧
      (∀ b, g b 0 = 0) ∧
      (∀ b (r : ℝ), 0 < r → ∀ x, g b (r • x) = r^2 * g b x) ∧
      (∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (Function.uncurry g) p) ∧
      Continuous (Function.uncurry g) ∧
      Continuous (fun p : B × E => fderiv ℝ (g p.1) p.2) ∧
      ∀ b x, ‖x‖ = 1 → ‖g b x - f b x‖ ≤ ε ∧
        ‖fderiv ℝ (g b) x - fderiv ℝ (f b) x‖ ≤ ε := by
  classical
  have hδ : 0 < ε/4 := by positivity
  have hj : Continuous (fun b => (f b).jet) := continuous_induced_dom.comp hf
  let U : B → Set B := fun b => {b' | ‖(f b).jet - (f b').jet‖ < ε/4}
  have hU : ∀ b, U b ∈ 𝓝 b := by
    intro b
    change {b' : B | ‖(f b).jet - (f b').jet‖ < ε/4} ∈ 𝓝 b
    have hc : Continuous (fun b' => ‖(f b).jet - (f b').jet‖) :=
      (@continuous_norm (C(Metric.sphere (0:E) 1,ℝ) ×
        C(Metric.sphere (0:E) 1,E→L[ℝ]ℝ)) inferInstance).comp (continuous_const.sub hj)
    apply (isOpen_lt hc continuous_const).mem_nhds
    change ‖(f b).jet - (f b).jet‖ < ε/4
    rw [sub_self, @norm_zero (C(Metric.sphere (0:E) 1,ℝ) ×
      C(Metric.sphere (0:E) 1,E→L[ℝ]ℝ)) inferInstance]
    exact hδ
  obtain ⟨ι, φ, hφ⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (fun b (_ : b ∈ (univ : Set B)) => hU b)
  let : Fintype ι := φ.fintype
  let ρ := φ.toSmoothPartitionOfUnity
  have hρ : ρ.IsSubordinate (fun i => U (φ.c i)) := hφ.toSmoothPartitionOfUnity
  have happrox : ∀ i : ι, ∃ g : E → ℝ, ContDiff ℝ 1 g ∧ g 0 = 0 ∧
      (∀ r : ℝ, 0 < r → ∀ x, g (r • x) = r^2 * g x) ∧
      (∀ x ≠ 0, ContDiffAt ℝ ∞ g x) ∧
      ∀ x, ‖x‖ = 1 → ‖g x - f (φ.c i) x‖ < ε/4 ∧
        ‖fderiv ℝ g x - fderiv ℝ (f (φ.c i)) x‖ < ε/4 := by
    intro i
    exact AngularExtension.exists_smooth_homogeneous_approx
      (f (φ.c i)).contDiff (f (φ.c i)).map_zero (f (φ.c i)).homogeneity hδ
  choose g₀ hg₀ using happrox
  let g : B → E → ℝ := fun b x => ∑ i, ρ i b * g₀ i x
  have hD : ∀ b x, fderiv ℝ (g b) x = ∑ i, ρ i b • fderiv ℝ (g₀ i) x := by
    intro b x
    exact (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) =>
      ((hg₀ i).1.differentiable one_ne_zero x).hasFDerivAt.const_smul (ρ i b))).fderiv
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact ContDiff.sum (fun i (_ : i ∈ Finset.univ) => (hg₀ i).1.const_smul (ρ i b))
  · intro b
    simp only [g, (fun i => (hg₀ i).2.1), mul_zero, Finset.sum_const_zero]
  · intro b r hr x
    simp only [g, (fun i => (hg₀ i).2.2.1 r hr x), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro p hp
    apply contMDiffAt_finsetSum
    intro i _
    exact (((ρ i).contMDiff.contMDiffAt).comp p contMDiffAt_fst).mul
      (((hg₀ i).2.2.2.1 p.2 hp).contMDiffAt.comp p contMDiffAt_snd)
  · change Continuous (fun p : B × E => ∑ i, ρ i p.1 * g₀ i p.2)
    exact continuous_finsetSum _ (fun i _ => ((ρ i).contMDiff.continuous.comp
      continuous_fst).mul ((hg₀ i).1.continuous.comp continuous_snd))
  · simp only [hD]
    exact continuous_finsetSum _ (fun i _ => ((ρ i).contMDiff.continuous.comp
      continuous_fst).smul (((hg₀ i).1.continuous_fderiv one_ne_zero).comp continuous_snd))
  · intro b x hx
    have hclose : ∀ i, ρ i b ≠ 0 →
        ‖g₀ i x - f b x‖ ≤ ε/2 ∧
          ‖fderiv ℝ (g₀ i) x - fderiv ℝ (f b) x‖ ≤ ε/2 := by
      intro i hi
      have hb : ‖(f (φ.c i)).jet - (f b).jet‖ < ε/4 :=
        hρ i (subset_tsupport _ hi)
      have hi₀ := (hg₀ i).2.2.2.2 x hx
      constructor
      · have H := norm_sub_le_norm_sub_add_norm_sub (g₀ i x) (f (φ.c i) x) (f b x)
        have H' := (norm_value_sub_le_jet (f (φ.c i)) (f b) hx).trans_lt hb
        linarith [hi₀.1]
      · have H := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (g₀ i) x)
          (fderiv ℝ (f (φ.c i)) x) (fderiv ℝ (f b) x)
        have H' := (norm_derivative_sub_le_jet (f (φ.c i)) (f b) hx).trans_lt hb
        linarith [hi₀.2]
    constructor
    · have H := ρ.finsum_smul_mem_convex (Set.mem_univ b)
        (g := fun i (_ : B) => g₀ i x)
        (fun i hi => (show g₀ i x ∈ Metric.closedBall (f b x) (ε/2) from
          by simpa only [Metric.mem_closedBall, dist_eq_norm] using (hclose i hi).1))
        (convex_closedBall (f b x) (ε/2))
      have H' : ‖g b x - f b x‖ ≤ ε/2 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, finsum_eq_sum_of_fintype,
          smul_eq_mul, g] using H
      linarith
    · rw [hD]
      have H := ρ.finsum_smul_mem_convex (Set.mem_univ b)
        (g := fun i (_ : B) => fderiv ℝ (g₀ i) x)
        (fun i hi => (show fderiv ℝ (g₀ i) x ∈
            Metric.closedBall (fderiv ℝ (f b) x) (ε/2) from
          by simpa only [Metric.mem_closedBall, dist_eq_norm] using (hclose i hi).2))
        (convex_closedBall (fderiv ℝ (f b) x) (ε/2))
      have H' : ‖∑ i, ρ i b • fderiv ℝ (g₀ i) x - fderiv ℝ (f b) x‖ ≤ ε/2 := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, finsum_eq_sum_of_fintype] using H
      linarith

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B]
  [CompactSpace B] [Nonempty B]

theorem exists_smooth_homotopic (f : C(B, RegularHomogeneous E)) :
    ∃ g : C(B, RegularHomogeneous E), f.Homotopic g ∧
      ∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p => g p.1 p.2) p := by
  obtain ⟨c, C, hc, _, hb⟩ := uniform_gradient_bounds f.continuous
  have hm : ∀ b x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ (f b) x‖ := by
    intro b x hx
    have hnorm : ‖fderiv ℝ (f b) x‖ = ‖gradient (f b) x‖ := by
      rw [← toDual_gradient]
      exact (InnerProductSpace.toDual ℝ E).norm_map _
    rw [hnorm]
    simpa only [hx, mul_one] using (hb b x).1
  obtain ⟨g₀, hg₀, _, hh₀, hs₀, hv₀, hd₀, he₀⟩ :=
    exists_smooth_family_approx (I := I) f.continuous (half_pos hc)
  have he : ∀ b x, ‖x‖ = 1 → ‖fderiv ℝ (g₀ b) x - fderiv ℝ (f b) x‖ < c := by
    intro b x hx
    exact ((he₀ b x hx).2).trans_lt (half_lt_self hc)
  let K : unitInterval × B → RegularHomogeneous E := fun p =>
    controlledBlend (f p.2) (hg₀ p.2) (hh₀ p.2) hc (hm p.2) (he p.2) p.1
  have hvf : Continuous (fun p : B × E => f p.1 p.2) :=
    continuous_eval.comp (f.continuous.prodMap continuous_id)
  have hdf : Continuous (fun p : B × E => fderiv ℝ (f p.1) p.2) :=
    continuous_fderiv_eval.comp (f.continuous.prodMap continuous_id)
  have hK : Continuous K := by
    apply continuous_of_joint_jet
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        f p.1.2 p.2 + (p.1.1 : ℝ) * (g₀ p.1.2 p.2 - f p.1.2 p.2))
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hvf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
          ((hv₀.comp hcoord).sub (hvf.comp hcoord)))
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        fderiv ℝ (fun w => f p.1.2 w + (p.1.1 : ℝ) * (g₀ p.1.2 w - f p.1.2 w)) p.2)
      simp only [fderiv_blend _ (hg₀ _)]
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hdf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
          ((hd₀.comp hcoord).sub (hdf.comp hcoord)))
  let g : C(B, RegularHomogeneous E) :=
    ⟨fun b => K (1,b), hK.comp (continuous_const.prodMk continuous_id)⟩
  have hfg : f.Homotopic g := by
    refine ⟨{ toFun := K
              continuous_toFun := hK
              map_zero_left := fun _ => controlledBlend_zero _ _ _ _ _ _
              map_one_left := fun _ => rfl }⟩
  refine ⟨g, hfg, ?_⟩
  have hg : (fun p : B × E => g p.1 p.2) = Function.uncurry g₀ := by
    funext p
    exact controlledBlend_one_apply (f p.1) (hg₀ p.1) (hh₀ p.1) hc
      (hm p.1) (he p.1) p.2
  rw [hg]
  exact hs₀

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
omit [FiniteDimensional ℝ E] [Nontrivial E] in

lemma norm_jet_error_of_sphere (g f : RegularHomogeneous E) {ε : ℝ}
    (h : ∀ x, ‖x‖ = 1 → ‖g x-f x‖ ≤ ε ∧
      ‖fderiv ℝ g x-fderiv ℝ f x‖ ≤ ε) (w : E) :
    ‖g w-f w‖ ≤ ε*‖w‖^2 ∧
      ‖fderiv ℝ g w-fderiv ℝ f w‖ ≤ ε*‖w‖ := by
  by_cases hw : w = 0
  · simp [hw,g.fderiv_zero,f.fderiv_zero]
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  let u := ‖w‖⁻¹ • w
  have hu : ‖u‖ = 1 := by
    simp [u,norm_smul,hn.ne']
  have hre : ‖w‖ • u = w := by simp [u,smul_smul,hn.ne']
  obtain ⟨hv,hd⟩ := h u hu
  constructor
  · calc
      ‖g w-f w‖ = ‖‖w‖^2 * (g u-f u)‖ := by
        conv_lhs => rw [← hre,g.homogeneity _ hn,f.homogeneity _ hn]
        congr 1
        ring
      _ = ‖w‖^2 * ‖g u-f u‖ := by rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ ε*‖w‖^2 := by nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg ‖w‖)]
  · calc
      ‖fderiv ℝ g w-fderiv ℝ f w‖ = ‖‖w‖ • (fderiv ℝ g u-fderiv ℝ f u)‖ := by
        conv_lhs => rw [← hre,g.fderiv_smul hn,f.fderiv_smul hn]
        rw [smul_sub]
      _ = ‖w‖ * ‖fderiv ℝ g u-fderiv ℝ f u‖ := by rw [norm_smul,Real.norm_eq_abs,abs_norm]
      _ ≤ ε*‖w‖ := by nlinarith [mul_le_mul_of_nonneg_left hd hn.le]

variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B]
  [CompactSpace B]

omit [Nontrivial E] in

theorem exists_smooth_homotopic_close (f : C(B, RegularHomogeneous E))
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (hm : ∀ b x, ‖x‖ = 1 → c ≤ ‖fderiv ℝ (f b) x‖) :
    ∃ g : C(B, RegularHomogeneous E), f.Homotopic g ∧
      (∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (fun p => g p.1 p.2) p) ∧
      ∀ b w, ‖g b w-f b w‖ ≤ ε*‖w‖^2 ∧
        ‖fderiv ℝ (g b) w-fderiv ℝ (f b) w‖ ≤ ε*‖w‖ := by
  obtain ⟨g₀, hg₀, _, hh₀, hs₀, hv₀, hd₀, he₀⟩ :=
    exists_smooth_family_approx (I := I) f.continuous hε
  have he : ∀ b x, ‖x‖ = 1 → ‖fderiv ℝ (g₀ b) x - fderiv ℝ (f b) x‖ < c := by
    intro b x hx
    exact ((he₀ b x hx).2).trans_lt hεc
  let K : unitInterval × B → RegularHomogeneous E := fun p =>
    controlledBlend (f p.2) (hg₀ p.2) (hh₀ p.2) hc (hm p.2) (he p.2) p.1
  have hvf : Continuous (fun p : B × E => f p.1 p.2) :=
    continuous_eval.comp (f.continuous.prodMap continuous_id)
  have hdf : Continuous (fun p : B × E => fderiv ℝ (f p.1) p.2) :=
    continuous_fderiv_eval.comp (f.continuous.prodMap continuous_id)
  have hK : Continuous K := by
    apply continuous_of_joint_jet
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        f p.1.2 p.2 + (p.1.1 : ℝ) * (g₀ p.1.2 p.2 - f p.1.2 p.2))
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hvf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).mul
          ((hv₀.comp hcoord).sub (hvf.comp hcoord)))
    · change Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
        fderiv ℝ (fun w => f p.1.2 w + (p.1.1 : ℝ) * (g₀ p.1.2 w - f p.1.2 w)) p.2)
      simp only [fderiv_blend _ (hg₀ _)]
      have hcoord : Continuous (fun p : (unitInterval × B) × Metric.sphere (0:E) 1 =>
          (p.1.2, (p.2 : E))) :=
        (continuous_snd.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd)
      exact (hdf.comp hcoord).add
        ((continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).smul
          ((hd₀.comp hcoord).sub (hdf.comp hcoord)))
  let g : C(B, RegularHomogeneous E) :=
    ⟨fun b => K (1,b), hK.comp (continuous_const.prodMk continuous_id)⟩
  have hfg : f.Homotopic g := by
    refine ⟨{ toFun := K
              continuous_toFun := hK
              map_zero_left := fun _ => controlledBlend_zero _ _ _ _ _ _
              map_one_left := fun _ => rfl }⟩
  refine ⟨g, hfg, ?_, ?_⟩
  · have hg : (fun p : B × E => g p.1 p.2) = Function.uncurry g₀ := by
      funext p
      exact controlledBlend_one_apply (f p.1) (hg₀ p.1) (hh₀ p.1) hc
        (hm p.1) (he p.1) p.2
    rw [hg]
    exact hs₀
  · have heq (b : B) : (g b : E → ℝ) = g₀ b := by
      funext w
      exact controlledBlend_one_apply (f b) (hg₀ b) (hh₀ b) hc (hm b) (he b) w
    intro b w
    apply norm_jet_error_of_sphere (g b) (f b)
    intro x hx
    simpa only [heq b] using he₀ b x hx

end NearbyLagrangian.Tubes.RegularHomogeneous

end

end OAI
