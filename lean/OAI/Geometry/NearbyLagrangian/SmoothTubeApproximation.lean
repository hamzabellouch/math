import Mathlib
import OAI.Geometry.NearbyLagrangian.SphereCollapse

namespace OAI

/-! First-jet relative approximation and smooth localized tube representatives. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes.RegularHomogeneous

open scoped ContDiff Topology Manifold
open Set Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma norm_value_sub_le_jet_C1 (f g : RegularHomogeneous E) {x : E} (hx : ‖x‖ = 1) :
    ‖f x - g x‖ ≤ ‖f.jet - g.jet‖ := by
  let u : Metric.sphere (0:E) 1 := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact ((f.jet.1 - g.jet.1).norm_coe_le_norm u).trans (norm_fst_le (f.jet - g.jet))

lemma norm_derivative_sub_le_jet_C1 (f g : RegularHomogeneous E) {x : E} (hx : ‖x‖ = 1) :
    ‖fderiv ℝ f x - fderiv ℝ g x‖ ≤ ‖f.jet - g.jet‖ := by
  let u : Metric.sphere (0:E) 1 := ⟨x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  exact ((f.jet.2 - g.jet.2).norm_coe_le_norm u).trans (norm_snd_le (f.jet - g.jet))

variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]

theorem exists_smooth_family_approx_C1 {f : B → RegularHomogeneous E} (hf : Continuous f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : B → E → ℝ,
      (∀ b, ContDiff ℝ 1 (g b)) ∧
      (∀ b, g b 0 = 0) ∧
      (∀ b (r : ℝ), 0 < r → ∀ x, g b (r • x) = r^2 * g b x) ∧
      (∀ p : B × E, p.2 ≠ 0 →
        ContMDiffAt (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (Function.uncurry g) p) ∧
      ContMDiff (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) 1 (Function.uncurry g) ∧
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
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · change ContMDiff (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) 1
        (fun p : B × E => ∑ i, ρ i p.1 * g₀ i p.2)
    apply contMDiff_finsetSum
    intro i _
    exact (((ρ i).contMDiff.of_le (by simp)).comp contMDiff_fst).mul
      ((hg₀ i).1.contMDiff.comp contMDiff_snd)
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
        have H' := (norm_value_sub_le_jet_C1 (f (φ.c i)) (f b) hx).trans_lt hb
        linarith [hi₀.1]
      · have H := norm_sub_le_norm_sub_add_norm_sub (fderiv ℝ (g₀ i) x)
          (fderiv ℝ (f (φ.c i)) x) (fderiv ℝ (f b) x)
        have H' := (norm_derivative_sub_le_jet_C1 (f (φ.c i)) (f b) hx).trans_lt hb
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
  [FiniteDimensional ℝ E]
variable {V H B : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace B] [ChartedSpace H B] [IsManifold I ∞ B] [T2Space B] [CompactSpace B]

theorem exists_smooth_family_approx_relative_C1 {f : B → RegularHomogeneous E}
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
      ContMDiff (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) 1 (Function.uncurry g) ∧
      Continuous (Function.uncurry g) ∧
      Continuous (fun p : B × E => fderiv ℝ (g p.1) p.2) ∧
      (∀ b x, ‖x‖ = 1 → ‖g b x - f b x‖ ≤ ε ∧
        ‖fderiv ℝ (g b) x - fderiv ℝ (f b) x‖ ≤ ε) ∧
      ∀ b, χ b = 0 → ∀ x, g b x = q x := by
  obtain ⟨g₀, hg₀, hz₀, hh₀, hs₀, hj₀, hv₀, hd₀, he₀⟩ :=
    exists_smooth_family_approx_C1 (I := I) hf hε
  let g : B → E → ℝ := fun b x => q x + χ b * (g₀ b x - q x)
  have hD : ∀ b x, fderiv ℝ (g b) x =
      fderiv ℝ q x + χ b • (fderiv ℝ (g₀ b) x - fderiv ℝ q x) :=
    fun b x => fderiv_blend q (hg₀ b) (χ b) x
  refine ⟨g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · change ContMDiff (I.prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) 1
        (fun p : B × E => q p.2 + χ p.1 * (g₀ p.1 p.2-q p.2))
    exact (q.contDiff.contMDiff.comp contMDiff_snd).add
      (((hχ.of_le (by simp)).comp contMDiff_fst).mul
        (hj₀.sub (q.contDiff.contMDiff.comp contMDiff_snd)))
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

theorem exists_smooth_negative_equiv_relative_C1 (f : C(B,RegularHomogeneous W))
    (q : RegularHomogeneous W) (hq : q.SmoothOffZero)
    {χ : B → ℝ} (hχ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,ℝ) ∞ χ)
    (hχ01 : ∀ b, χ b ∈ Icc (0:ℝ) 1) (hfixed : ∀ b, χ b ≠ 1 → f b = q) :
    ∃ g : C(B,RegularHomogeneous W), f.Homotopic g ∧ SmoothFamily (E:=V) g ∧
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) 1 (fun p : B × W => g p.1 p.2) ∧
      Nonempty (FiberwiseHomotopyEquiv
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => f p.1 p.2))
        (negativeInProjection {w : W | ‖w‖ = 1} (fun p : B × W => g p.1 p.2))) ∧
      ∀ b, χ b = 0 → g b = q := by
  cases isEmpty_or_nonempty B with
  | inl h => exact ⟨f,.refl f,fun p _ => isEmptyElim p.1,fun p => isEmptyElim p.1,⟨.refl _⟩,fun b => isEmptyElim b⟩
  | inr h =>
    obtain ⟨c,C,hc,_,hb⟩ := uniform_gradient_bounds f.continuous
    have hm (b : B) (w : W) (hw : ‖w‖ = 1) : c ≤ ‖fderiv ℝ (f b) w‖ := by
      rw [norm_fderiv_gradient]
      simpa only [hw,mul_one] using (hb b w).1
    obtain ⟨g₀,hg₀,_,hh₀,hs₀,hj₀,hv₀,hd₀,he₀,hfix₀⟩ :=
      exists_smooth_family_approx_relative_C1 f.continuous q hq hχ hχ01 hfixed
        (by positivity : 0 < c/128)
    obtain ⟨g,hH,hs,hN,hg⟩ := smooth_negative_of_approx (ε:=c/128)
      f hg₀ hh₀ hs₀ hv₀ hd₀ hc (by positivity) le_rfl hm
      (fun b x hx => by simpa only [Real.norm_eq_abs] using he₀ b x hx)
    have hgeq : (fun p : B × W => g p.1 p.2) = Function.uncurry g₀ :=
      funext (fun p => hg p.1 p.2)
    have hj : ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,W)) 𝓘(ℝ,ℝ) 1
        (fun p : B × W => g p.1 p.2) := by rw [hgeq]; exact hj₀
    exact ⟨g,hH,hs,hj,hN,fun b hb => RegularHomogeneous.ext
      (fun w => (hg b w).trans (hfix₀ b hb w))⟩

end NearbyLagrangian.Tubes.RegularHomogeneous

namespace NearbyLagrangian.Tubes
open Set ContinuousMap
open scoped Topology ContDiff Manifold
variable {B V : Type*} [TopologicalSpace B] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [ChartedSpace V B] [IsManifold 𝓘(ℝ,V) ∞ B]
  [T2Space B] [CompactSpace B]

theorem exists_smooth_tube_relative_C1 {k l : ℕ} (hkl : 0 < k+l) (a : C(B,Tube k l))
    (q : Tube k l) (hq : q.val.SmoothOffZero)
    {χ : B → ℝ} (hχ : ContMDiff 𝓘(ℝ,V) 𝓘(ℝ,ℝ) ∞ χ)
    (hχ01 : ∀ b, χ b ∈ Icc (0:ℝ) 1) (hfixed : ∀ b, χ b ≠ 1 → a b = q) :
    ∃ b : C(B,Tube k l), a.Homotopic b ∧
      RegularHomogeneous.SmoothFamily (E:=V) (fun x => (b x).val) ∧
      ContMDiff (𝓘(ℝ,V).prod 𝓘(ℝ,Euclidean (k+l))) 𝓘(ℝ,ℝ) 1
        (fun p : B × Euclidean (k+l) => (b p.1).val p.2) ∧
      Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) ∧
      ∀ x, χ x = 0 → b x = q := by
  let : Nonempty (Fin (k+l)) := ⟨⟨0,hkl⟩⟩
  obtain ⟨g,hag,hgs,hgc,hneg,hfix⟩ :=
    RegularHomogeneous.exists_smooth_negative_equiv_relative_C1 (tubeCoe.comp a) q.val hq
      hχ hχ01 (fun x hx => congrArg Subtype.val (hfixed x hx))
  obtain ⟨b,hab,hb⟩ := lift_tube_homotopy a g hag
  have heq : tubeCoe.comp b = g := ContinuousMap.ext hb
  refine ⟨b,hab,?_,?_,?_,?_⟩
  · have heq' : (fun x => (b x).val) = (g : B → RegularHomogeneous (Euclidean (k+l))) :=
      funext hb
    rw [heq']
    exact hgs
  · have heq' : (fun p : B × Euclidean (k+l) => (b p.1).val p.2) =
          (fun p : B × Euclidean (k+l) => g p.1 p.2) := by
        funext p; rw [hb p.1]
    rw [heq']; exact hgc
  · rw [← heq] at hneg
    exact ⟨FiberwiseHomotopyEquiv.ofNegativeIn hneg.some⟩
  · intro x hx
    exact Subtype.ext ((hb x).trans (hfix x hx))

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open Set ContinuousMap
open scoped Topology ContDiff Manifold

theorem smooth_localized_tube_C1 {k l : ℕ} (hkl : 0 < k+l)
    (a : C(UnitSphere 10,Tube k l)) (q : UnitSphere 10) :
    ∃ b : C(UnitSphere 10,Tube k l), a.Homotopic b ∧
      RegularHomogeneous.SmoothFamily (E:=Euclidean 9) (fun x => (b x).val) ∧
      ContMDiff (𝓘(ℝ,Euclidean 9).prod 𝓘(ℝ,Euclidean (k+l))) 𝓘(ℝ,ℝ) 1
        (fun p : UnitSphere 10 × Euclidean (k+l) => (b p.1).val p.2) ∧
      Nonempty (FiberwiseHomotopyEquiv (negativeProjection a) (negativeProjection b)) ∧
      ∀ x : UnitSphere 10, 3/2 ≤ ‖(x:Euclidean 10)+(q:Euclidean 10)‖^2 →
        b x = standardTube k l := by
  let : Fact (Module.finrank ℝ (Euclidean 10) = 9+1) := ⟨by simp [Euclidean]⟩
  obtain ⟨b,hab,hfixed⟩ := standard_plateau a q
  have hpres (x : UnitSphere 10) (hx : SphereCollapse.smoothPlateau q x ≠ 1) :
      b x = standardTube k l := by
    apply hfixed
    by_contra! h
    exact hx (SphereCollapse.smoothPlateau_one q x h.le)
  obtain ⟨g,hbg,hgs,hgc,hneg,hfix⟩ := exists_smooth_tube_relative_C1 (V:=Euclidean 9)
    hkl b (standardTube k l) (contDiff_standardForm k l).contDiffOn
      (SphereCollapse.contMDiff_smoothPlateau (n:=9) q)
      (SphereCollapse.smoothPlateau_mem q) hpres
  have hag := hab.trans hbg
  exact ⟨g,hag,hgs,hgc,negative_equiv_tube_of_homotopic (V:=Euclidean 9) hkl hag,
    fun x hx => hfix x (SphereCollapse.smoothPlateau_zero q x hx)⟩

theorem smooth_localized_kernel_C1 {m : ℕ} (hm : 0 < m)
    (a : C(UnitSphere 10,Tube m m)) (ha : StablyNonNull a)
    (hn : StableNegativeTrivial a) (q : UnitSphere 10) :
    ∃ b : C(UnitSphere 10,Tube m m), a.Homotopic b ∧ StablyNonNull b ∧
      StableNegativeTrivial b ∧
      RegularHomogeneous.SmoothFamily (E:=Euclidean 9) (fun x => (b x).val) ∧
      ContMDiff (𝓘(ℝ,Euclidean 9).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) 1
        (fun p : UnitSphere 10 × Euclidean (m+m) => (b p.1).val p.2) ∧
      ∀ x : UnitSphere 10, 3/2 ≤ ‖(x:Euclidean 10)+(q:Euclidean 10)‖^2 →
        b x = standardTube m m := by
  obtain ⟨b,hab,hbs,hbc,_,hfix⟩ := smooth_localized_tube_C1 (by omega) a q
  exact ⟨b,hab,ha.of_homotopic hab,hn.of_homotopic (V:=Euclidean 9) hm hab,hbs,hbc,hfix⟩

end NearbyLagrangian.Tubes

end

end OAI
