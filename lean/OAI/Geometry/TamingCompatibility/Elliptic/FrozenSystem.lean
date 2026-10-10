import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScaledLower
import OAI.Geometry.TamingCompatibility.Charts.AffineLocal

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [MeasurableSpace E] [BorelSpace E] in
lemma exists_unit_cutoff : ∃ χ : 𝓢(E,ℂ), HasCompactSupport (χ : E → ℂ) ∧
    ∀ x ∈ Metric.ball (0 : E) 1, χ x = 1 := by
  let b : ContDiffBump (0 : E) := ⟨1,2,by norm_num,by norm_num⟩
  have hs : ContDiff ℝ ∞ (fun x => (b x : ℂ)) := Complex.ofRealCLM.contDiff.comp b.contDiff
  have hc : HasCompactSupport (fun x => (b x : ℂ)) := by
    exact b.hasCompactSupport.comp_left (show (fun t : ℝ => (t : ℂ)) 0 = 0 by rfl)
  refine ⟨hc.toSchwartzMap hs,hc,fun x hx => ?_⟩
  change (b x : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx),Complex.ofReal_one]

lemma exists_small_frozen_scale
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E) :
    ∃ r : ℝ, 0 < r ∧
      ‖perturbationNegOne (F := F)
        (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r)‖ < 1 ∧
      ‖perturbation (F := F) 0
        (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r)‖ < 1 := by
  have h1 := (frozen_weak_norm_tendsto (F := F) χ hχ (fun i j x => -g i j x)
    (fun i j => (g i j).smooth ⊤ |>.neg) p).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have h2 := (frozen_perturbation_norm_tendsto (F := F) 0 χ hχ (fun i j x => -g i j x)
    (fun i j => (g i j).smooth ⊤ |>.neg) p).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp (h1.and h2)
  have hr := hεsub (show ε/2 ∈ Metric.ball (0 : ℝ) ε by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    exact half_lt_self hε)
  exact ⟨ε/2,half_pos hε,hr⟩

lemma MemSobolevLoc.real_smul {U : Set E} {n : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U n u) (r : ℝ) : MemSobolevLoc U n (r • u) := by
  intro g hg hgU
  rw [ContinuousLinearMap.map_smul_of_tower,RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact MemSobolev.smul (r : ℂ) (h g hg hgU)

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] in
lemma local_frozen_system {ι κ : Type*} [Fintype ι] [Fintype κ]
    (χ : 𝓢(E,ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ)) (p : E)
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (r : ℝ) (hr : r ≠ 0) (ψ : 𝓢(E,ℂ)) (hψ : ∀ x ∈ tsupport ψ, χ x = 1)
    (B : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (C : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) (u : 𝓢'(E,F)) :
    smulLeftCLM F ψ (perturbedHelmholtz
      (frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r) u +
      matrixLowerOrder B L v (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) u) =
    smulLeftCLM F ψ (-directionalPrincipal (stdOrthonormalBasis ℝ E)
      (fun i j => affineSchwartz p r hr (g i j)) u + matrixLowerOrder B L v C K u) := by
  rw [map_add,local_frozen_helmholtz χ hχ g p hgp r hr ψ hψ u,
    matrixLowerOrder_sub_cutoff B L v C K χ u,map_sub,local_cutoff_one χ ψ hψ u]
  simp only [map_add,map_neg]
  abel

lemma MemSobolevLoc.restrict {U V : Set E} {n : ℝ} {u : 𝓢'(E,F)}
    (h : MemSobolevLoc U n u) (hVU : V ⊆ U) : MemSobolevLoc V n u :=
  fun g hg hgV => h g hg (hgV.trans hVU)

lemma memSobolevLoc_zoom_one (p : E) (r : ℝ) (hr : r ≠ 0)
    {U : Set E} {u : 𝓢'(E,F)} (hu : MemSobolevLoc U 1 u) :
    MemSobolevLoc ((fun y => r • y+p) ⁻¹' U) 1 (zoomDistribution p r hr u) := by
  have hu' : MemSobolevLoc U (1 : ℕ) u := by simpa only [Nat.cast_one] using hu
  simpa only [Nat.cast_one] using memSobolevLoc_zoom 1 p r hr hu'

end TamingCompatibility.HilbertSobolev

end
end

section
noncomputable section
namespace TamingCompatibility.HilbertSobolev
open EuclideanSobolevOperators TemperedDistribution MeasureTheory LineDeriv Set Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem normalized_scalar_interior_regular {ι κ : Type*} [Fintype ι] [Fintype κ]
    {U : Set E} (hU : IsOpen U) (p : E) (hp : p ∈ U)
    (g : basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (hgp : ∀ i j, g i j p = if i=j then ((((2*Real.pi)^2)⁻¹ : ℝ) : ℂ) else 0)
    (b : ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F) {u : 𝓢'(E,F)}
    (hu : MemSobolevLoc U 1 u)
    (hf : ∀ n : ℕ, MemSobolevLoc U n
      (-directionalPrincipal (stdOrthonormalBasis ℝ E) g u + matrixLowerOrder b L v c K u)) :
    ∃ V : Set E, IsOpen V ∧ p ∈ V ∧ V ⊆ U ∧ ∀ n : ℕ, MemSobolevLoc V n u := by
  obtain ⟨χ,hχ,hχone⟩ := exists_unit_cutoff (E := E)
  obtain ⟨r,hr,hweak,hstrong⟩ := exists_small_frozen_scale (F := F) χ hχ g p
  have hr0 : r ≠ 0 := ne_of_gt hr
  let W : Set E := (fun y => r • y+p) ⁻¹' U ∩ Metric.ball 0 1
  have hW : IsOpen W := (hU.preimage (by fun_prop)).inter Metric.isOpen_ball
  have h0W : (0 : E) ∈ W := by simpa only [W,mem_inter_iff,mem_preimage,smul_zero,zero_add,
    Metric.mem_ball,dist_self] using And.intro hp (show (0 : ℝ) < 1 by norm_num)
  let a := frozenPrincipal χ hχ (fun i j x => -g i j x) (fun i j => (g i j).smooth ⊤ |>.neg) p r
  let B := fun i => r • affineSchwartz p r hr0 (b i)
  let C := fun i => (r*r) • affineSchwartz p r hr0 (c i)
  let z := zoomDistribution p r hr0 u
  have hz : MemSobolevLoc W 1 z := by
    exact (memSobolevLoc_zoom_one p r hr0 hu).restrict inter_subset_left
  have hsource (n : ℕ) : MemSobolevLoc W n
      (perturbedHelmholtz a z + matrixLowerOrder B L v
        (Sum.elim C (fun _ : Unit => -χ))
        (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) z) := by
    intro ψ hψ hψW
    have hpψ : ∀ x ∈ tsupport ψ, χ x = 1 := fun x hx => hχone x (hψW hx).2
    have h := (memSobolevLoc_zoom n p r hr0 (hf n)).real_smul (r*r) ψ hψ
      (fun x hx => (hψW hx).1)
    rw [rescaled_system] at h
    rw [local_frozen_system χ hχ g p hgp r hr0 ψ hpψ B L v C K z]
    exact h
  have hzall (n : ℕ) : MemSobolevLoc W n z := by
    apply (matrix_H1_interior_bootstrap n hW a hweak hstrong B L v
      (Sum.elim C (fun _ : Unit => -χ))
      (Sum.elim K (fun _ : Unit => ContinuousLinearMap.id ℂ F)) hz (hsource n)).mono
    linarith
  let V : Set E := (fun y => r⁻¹ • y + -(r⁻¹ • p)) ⁻¹' W
  have hV : IsOpen V := hW.preimage (by fun_prop)
  have hpV : p ∈ V := by
    change r⁻¹ • p + -(r⁻¹ • p) ∈ W
    simpa only [add_neg_cancel] using h0W
  have hVU : V ⊆ U := by
    intro x hx
    have h := hx.1
    change r • (r⁻¹ • x + -(r⁻¹ • p))+p ∈ U at h
    simpa only [smul_add,smul_neg,smul_smul,mul_inv_cancel₀ hr0,one_smul,neg_add_cancel_right] using h
  refine ⟨V,hV,hpV,hVU,fun n => ?_⟩
  have h := memSobolevLoc_affine n p r hr0 (hzall n)
  rw [zoomDistribution_inverse] at h
  exact h

end TamingCompatibility.HilbertSobolev

end
end

end
end
end

end OAI
