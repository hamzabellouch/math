import Mathlib
import OAI.Geometry.NearbyLagrangian.FiberHomotopy

namespace OAI

/-! Relative smooth approximation of homogeneous functions and tubes. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]

theorem exists_smooth_family_approx_relative {f : B → RegularHomogeneous E}
    (hf : Continuous f) (q : RegularHomogeneous E) (hq : q.SmoothOffZero)
    {χ : B → ℝ} (hχ : ContMDiff I 𝓘(ℝ,ℝ) ∞ χ)
    (hχ01 : ∀ b, χ b ∈ Icc (0:ℝ) 1) (hfixed : ∀ b, χ b ≠ 1 → f b = q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : B → E → ℝ,
      (∀ b, ContDiff ℝ 1 (g b)) ∧
      (∀ b, g b 0 = 0) ∧
      (∀ b (r : ℝ), 0 < r → ∀ x, g b (r • x) = r^2 * g b x) ∧
      (∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (Function.uncurry g) p) ∧
      Continuous (Function.uncurry g) ∧
      Continuous (fun p : B × E => fderiv ℝ (g p.1) p.2) ∧
      (∀ b x, ‖x‖ = 1 → ‖g b x - f b x‖ ≤ ε ∧
        ‖fderiv ℝ (g b) x - fderiv ℝ (f b) x‖ ≤ ε) ∧
      ∀ b, χ b = 0 → ∀ x, g b x = q x := by
  obtain ⟨g₀, hg₀, hz₀, hh₀, hs₀, hv₀, hd₀, he₀⟩ :=
    exists_smooth_family_approx (I := I) hf hε
  let g : B → E → ℝ := fun b x => q x + χ b * (g₀ b x - q x)
  have hD : ∀ b x, fderiv ℝ (g b) x =
      fderiv ℝ q x + χ b • (fderiv ℝ (g₀ b) x - fderiv ℝ q x) :=
    fun b x => fderiv_blend q (hg₀ b) (χ b) x
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    exact q.contDiff.add (((hg₀ b).sub q.contDiff).const_smul (χ b))
  · intro b
    simp only [g, q.map_zero, hz₀, sub_self, mul_zero, add_zero]
  · intro b r hr x
    dsimp only [g]
    rw [q.homogeneity r hr x, hh₀ b r hr x]
    ring
  · intro p hp
    have hqs : ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
        (fun z : B × E => q z.2) p :=
      (hq.contDiffAt (isOpen_compl_singleton.mem_nhds hp)).contMDiffAt.comp p contMDiffAt_snd
    exact hqs.add ((hχ.contMDiffAt.comp p contMDiffAt_fst).mul
      ((hs₀ p hp).sub hqs))
  · exact (q.contDiff.continuous.comp continuous_snd).add
      ((hχ.continuous.comp continuous_fst).mul
        (hv₀.sub (q.contDiff.continuous.comp continuous_snd)))
  · simp only [hD]
    exact ((q.contDiff.continuous_fderiv one_ne_zero).comp continuous_snd).add
      ((hχ.continuous.comp continuous_fst).smul
        (hd₀.sub ((q.contDiff.continuous_fderiv one_ne_zero).comp continuous_snd)))
  · intro b x hx
    have he := he₀ b x hx
    have hv : g b x - f b x = χ b * (g₀ b x - f b x) := by
      by_cases h : χ b = 1
      · simp [g, h]
      · rw [hfixed b h]
        dsimp only [g]
        ring
    have hd : fderiv ℝ (g b) x - fderiv ℝ (f b) x =
        χ b • (fderiv ℝ (g₀ b) x - fderiv ℝ (f b) x) := by
      rw [hD]
      by_cases h : χ b = 1
      · simp [h]
      · rw [hfixed b h]
        abel
    constructor
    · rw [hv, norm_mul, Real.norm_of_nonneg (hχ01 b).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχ01 b).2).trans he.1
    · rw [hd, norm_smul, Real.norm_of_nonneg (hχ01 b).1]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hχ01 b).2).trans he.2
  · intro b hb x
    simp only [g, hb, zero_mul, add_zero]

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes.RegularHomogeneous
open Set
open scoped Topology ContDiff Manifold
variable {B V W : Type*} [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [T2Space B] [CompactSpace B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W] [Nontrivial W]

theorem exists_smooth_negative_equiv_relative (f : C(B,RegularHomogeneous W))
    (q : RegularHomogeneous W) (hq : q.SmoothOffZero)
    {χ : B → ℝ} (hχ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,ℝ) ∞ χ)
    (hχ01 : ∀ b, χ b ∈ Icc (0:ℝ) 1) (hfixed : ∀ b, χ b ≠ 1 → f b = q) :
    ∃ g : C(B,RegularHomogeneous W), f.Homotopic g ∧ SmoothFamily (E:=V) g ∧
      Nonempty (FiberwiseHomotopyEquiv
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) ∧
      ∀ b, χ b = 0 → g b = q := by
  cases isEmpty_or_nonempty B with
  | inl h => exact ⟨f,.refl f,fun p _ => isEmptyElim p.1,⟨.refl _⟩,fun b => isEmptyElim b⟩
  | inr h =>
    obtain ⟨c,C,hc,_,hb⟩ := uniform_gradient_bounds f.continuous
    have hm (b : B) (w : W) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (f b) w‖ := by
      rw [norm_fderiv_gradient]
      simpa only [hw,mul_one] using (hb b w).1
    obtain ⟨g₀,hg₀,_,hh₀,hs₀,hv₀,hd₀,he₀,hfix₀⟩ :=
      exists_smooth_family_approx_relative f.continuous q hq hχ hχ01 hfixed
        (by positivity : 0 < c/128)
    obtain ⟨g,hH,hs,hN,hg⟩ := smooth_negative_of_approx (ε:=c/128)
      f hg₀ hh₀ hs₀ hv₀ hd₀ hc (by positivity) le_rfl hm
      (fun b x hx => by simpa only [Real.norm_eq_abs] using he₀ b x hx)
    exact ⟨g,hH,hs,hN,fun b hb => RegularHomogeneous.ext
      (fun w => (hg b w).trans (hfix₀ b hb w))⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes
open Set ContinuousMap
open scoped Topology ContDiff Manifold
variable {B V : Type*} [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_smooth_tube_relative {k l : ℕ} (hkl : 0 < k+l) (a : C(B,Tube k l))
    (q : Tube k l) (hq : q.val.SmoothOffZero)
    {χ : B → ℝ} (hχ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,ℝ) ∞ χ)
    (hχ01 : ∀ b, χ b ∈ Icc (0:ℝ) 1) (hfixed : ∀ b, χ b ≠ 1 → a b = q) :
    ∃ b : C(B,Tube k l), a.Homotopic b ∧
      RegularHomogeneous.SmoothFamily (E:=V) (fun x => (b x).val) ∧
      Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) ∧
      ∀ x, χ x = 0 → b x = q := by
  let : Nonempty (Fin (k+l)) := ⟨⟨0,hkl⟩⟩
  obtain ⟨g,hag,hgs,hneg,hfix⟩ :=
    RegularHomogeneous.exists_smooth_negative_equiv_relative (tubeCoe.comp a) q.val hq
      hχ hχ01 (fun x hx => congrArg Subtype.val (hfixed x hx))
  obtain ⟨b,hab,hb⟩ := lift_tube_homotopy a g hag
  have heq : tubeCoe.comp b = g := ContinuousMap.ext hb
  refine ⟨b,hab,?_,?_,?_⟩
  · have heq' : (fun x => (b x).val) = (g : B → RegularHomogeneous (Euclidean (k+l))) :=
      funext hb
    rw [heq']
    exact hgs
  · rw [← heq] at hneg
    exact ⟨FiberwiseHomotopyEquiv.ofNegativeIn hneg.some⟩
  · intro x hx
    exact Subtype.ext ((hb x).trans (hfix x hx))

lemma contDiff_standardForm (k l : ℕ) : ContDiff ℝ ∞ (standardForm k l) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜:=ℝ) (n:=k) (m:=l)
  change ContDiff ℝ ∞ (fun w => -‖(e w).1‖^2 + ‖(e w).2‖^2)
  exact (((contDiff_fst.comp e.contDiff).norm_sq (𝕜:=ℝ)).neg).add
    ((contDiff_snd.comp e.contDiff).norm_sq (𝕜:=ℝ))

end NearbyLagrangian.Tubes

end

end OAI
