import Mathlib
import OAI.Geometry.NearbyLagrangian.TransportCutoffs
import OAI.Geometry.NearbyLagrangian.MixedGraphs
import OAI.Geometry.NearbyLagrangian.HamiltonianFlow

namespace OAI

/-! Uniform finite time meshes and prepared mixed steps. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Transport

open ContinuousLinearMap Set
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem compact_flow_step_small
    {g : (ℝ × ℝ) × E → E} (hg : ContDiff ℝ ∞ g)
    {K : Set E} (hK : IsCompact K)
    (hdiag : ∀ t x, g ((t,t),x) = x)
    (hsupp : ∀ s t x, x ∉ K → g ((s,t),x) = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist s t < δ → ∀ x,
        ‖fderiv ℝ (fun y => g ((s,t),y)) x - ContinuousLinearMap.id ℝ E‖ < ε := by
  let D : (ℝ × ℝ) × E → E →L[ℝ] E :=
    fun q => (fderiv ℝ g q).comp (inr ℝ (ℝ × ℝ) E)
  have hD : Continuous D :=
    (hg.fderiv_right (m := ∞) (by simp)).continuous.clm_comp continuous_const
  have hslice (s t : ℝ) (x : E) :
      fderiv ℝ (fun y => g ((s,t),y)) x = D ((s,t),x) := by
    exact ((hg.differentiable (by simp) ((s,t),x)).hasFDerivAt.comp x
      (hasFDerivAt_prodMk_right (s,t) x)).fderiv
  have hDi (t : ℝ) (x : E) : D ((t,t),x) = ContinuousLinearMap.id ℝ E := by
    rw [← hslice]
    have hfun : (fun y => g ((t,t),y)) = id := funext (hdiag t)
    rw [hfun, fderiv_id]
  have hcomp : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ K) :=
    (isCompact_Icc.prod isCompact_Icc).prod hK
  obtain ⟨δ,hδ,hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hcomp.uniformContinuousOn_of_continuous hD.continuousOn) ε hε
  refine ⟨δ,hδ,?_⟩
  intro s hs t ht hst x
  by_cases hx : x ∈ K
  · have hd := hunif ((s,t),x) ⟨⟨hs,ht⟩,hx⟩ ((s,s),x) ⟨⟨hs,hs⟩,hx⟩
    simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      max_eq_left dist_nonneg] at hd
    have hh := hd (by simpa only [dist_comm] using hst)
    rwa [hDi, dist_eq_norm, ← hslice] at hh
  · have hev : (fun y => g ((s,t),y)) =ᶠ[𝓝 x] id := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
      exact hsupp s t y hy
    rw [hev.fderiv_eq, fderiv_id, sub_self, norm_zero]
    exact hε

omit [NormedSpace ℝ E] in

theorem compact_flow_step_displacement
    {g : (ℝ × ℝ) × E → E} (hg : Continuous g)
    {K : Set E} (hK : IsCompact K)
    (hdiag : ∀ t x, g ((t,t),x) = x)
    (hsupp : ∀ s t x, x ∉ K → g ((s,t),x) = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist s t < δ → ∀ x, ‖g ((s,t),x)-x‖ < ε := by
  have hcomp : IsCompact ((Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) ×ˢ K) :=
    (isCompact_Icc.prod isCompact_Icc).prod hK
  obtain ⟨δ,hδ,hunif⟩ := Metric.uniformContinuousOn_iff.mp
    (hcomp.uniformContinuousOn_of_continuous hg.continuousOn) ε hε
  refine ⟨δ,hδ,?_⟩
  intro s hs t ht hst x
  by_cases hx : x ∈ K
  · have hd := hunif ((s,t),x) ⟨⟨hs,ht⟩,hx⟩ ((s,s),x) ⟨⟨hs,hs⟩,hx⟩
    simp only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg,
      max_eq_left dist_nonneg] at hd
    have hh := hd (by simpa only [dist_comm] using hst)
    simpa only [hdiag, dist_eq_norm] using hh
  · rw [hsupp s t x hx, sub_self, norm_zero]
    exact hε

theorem exists_uniform_time_subdivision
    {g : (ℝ × ℝ) × E → E} (hg : ContDiff ℝ ∞ g)
    {K : Set E} (hK : IsCompact K)
    (hdiag : ∀ t x, g ((t,t),x) = x)
    (hsupp : ∀ s t x, x ∉ K → g ((s,t),x) = x)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n → ∀ x,
      ‖fderiv ℝ (fun y => g (((i : ℝ)/n,((i+1 : ℕ) : ℝ)/n),y)) x -
        ContinuousLinearMap.id ℝ E‖ < ε := by
  obtain ⟨δ,hδ,hstep⟩ := compact_flow_step_small hg hK hdiag hsupp hε
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1 : ℝ) (δ⁻¹))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : 0 < (n : ℝ) := lt_trans zero_lt_one hn1
  have hnNat : 0 < n := by exact_mod_cast hn0
  have hnd : (n : ℝ)⁻¹ < δ := by
    apply (inv_lt_comm₀ hn0 hδ).mpr
    exact lt_of_le_of_lt (le_max_right _ _) hn
  refine ⟨n,hnNat,?_⟩
  intro i hi x
  have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg i
  have hi1 : (i+1 : ℕ) ≤ n := hi
  have hiN : (i : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt hi
  have hiN1 : ((i+1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hi1
  apply hstep ((i : ℝ)/n) ⟨div_nonneg hi0 hn0.le, (div_le_one hn0).mpr hiN⟩
    (((i+1 : ℕ) : ℝ)/n)
    ⟨div_nonneg (Nat.cast_nonneg _) hn0.le, (div_le_one hn0).mpr hiN1⟩ ?_ x
  rw [Real.dist_eq, Nat.cast_add, Nat.cast_one]
  have heq : (i : ℝ)/n-((i : ℝ)+1)/n = -(n : ℝ)⁻¹ := by ring
  rw [heq, abs_neg, abs_of_pos (inv_pos.mpr hn0)]
  exact hnd

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set ContinuousLinearMap
open scoped ContDiff Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma exists_equal_time_mesh {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n →
      (i:ℝ)/n ∈ Icc (0:ℝ) 1 ∧ ((i+1:ℕ):ℝ)/n ∈ Icc (0:ℝ) 1 ∧
        dist ((i:ℝ)/n) (((i+1:ℕ):ℝ)/n) < δ := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max (1:ℝ) (δ⁻¹))
  have hn0 : 0 < (n:ℝ) := lt_trans zero_lt_one (lt_of_le_of_lt (le_max_left _ _) hn)
  have hnd : (n:ℝ)⁻¹ < δ := (inv_lt_comm₀ hn0 hδ).mpr
    (lt_of_le_of_lt (le_max_right _ _) hn)
  refine ⟨n,by exact_mod_cast hn0,?_⟩
  intro i hi
  have hiN : (i:ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt hi
  have hiN1 : ((i+1:ℕ):ℝ) ≤ n := by exact_mod_cast hi
  refine ⟨⟨div_nonneg (Nat.cast_nonneg _) hn0.le,(div_le_one hn0).mpr hiN⟩,
    ⟨div_nonneg (Nat.cast_nonneg _) hn0.le,(div_le_one hn0).mpr hiN1⟩,?_⟩
  rw [Real.dist_eq,Nat.cast_add,Nat.cast_one]
  have heq : (i:ℝ)/n-((i:ℝ)+1)/n = -(n:ℝ)⁻¹ := by ring
  rw [heq,abs_neg,abs_of_pos (inv_pos.mpr hn0)]
  exact hnd

theorem exists_uniform_time_subdivision_both
    {g : (ℝ × ℝ) × E → E} (hg : ContDiff ℝ ∞ g)
    {K : Set E} (hK : IsCompact K)
    (hdiag : ∀ t x, g ((t,t),x) = x)
    (hsupp : ∀ s t x, x ∉ K → g ((s,t),x) = x)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ n : ℕ, 0 < n ∧ ∀ i : ℕ, i < n → ∀ x,
      ‖fderiv ℝ (fun y => g (((i:ℝ)/n,((i+1:ℕ):ℝ)/n),y)) x -
        ContinuousLinearMap.id ℝ E‖ < ε ∧
      ‖g (((i:ℝ)/n,((i+1:ℕ):ℝ)/n),x)-x‖ < η := by
  obtain ⟨δ,hδ,hstep⟩ := compact_flow_step_small hg hK hdiag hsupp hε
  obtain ⟨δ',hδ',hdisp⟩ := compact_flow_step_displacement hg.continuous hK hdiag hsupp hη
  obtain ⟨n,hn,hmesh⟩ := exists_equal_time_mesh (lt_min hδ hδ')
  refine ⟨n,hn,?_⟩
  intro i hi x
  obtain ⟨hs,ht,hd⟩ := hmesh i hi
  exact ⟨hstep _ hs _ ht (lt_of_lt_of_le hd (min_le_left _ _)) x,
    hdisp _ hs _ ht (lt_of_lt_of_le hd (min_le_right _ _)) x⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

structure PreparedMixedStep (S : Set (E × E)) (δ : ℝ) where
  ψ : (E × E) ≃ₜ (E × E)
  σ : E × E → ℝ
  smooth_ψ : ContDiff ℝ ∞ (ψ : E × E → E × E)
  smooth_σ : ContDiff ℝ ∞ σ
  compact_σ : HasCompactSupport σ
  fixed : ∀ z ∉ S, ψ z = z
  σ_zero : ∀ X ∉ Prod.fst '' S, ∀ p, σ (X,p) = 0
  σ_bound : ∀ X p, ‖fderiv ℝ (fun p => σ (X,p)) p‖ < δ
  graph : ∀ x p X, (ψ (x,p)).1 = X ↔
    fderiv ℝ (fun p => σ (X,p)) p = innerSL ℝ (x-X)
  output : ∀ x p, innerSL ℝ (ψ (x,p)).2 = innerSL ℝ p +
    fderiv ℝ (fun X => σ (X,p)) (ψ (x,p)).1
  twist : ∀ X p, Function.Surjective (ContinuousLinearMap.id ℝ E +
    (fderiv ℝ (mixedDisplacement σ) (X,p)).comp (inl ℝ E E))

variable [FiniteDimensional ℝ E]

theorem exists_finite_prepared_steps {U : Set E} (hU : IsOpen U)
    {S : Set (E × E)} (hS : IsCompact S) (hSU : ∀ z ∈ S, z.1 ∈ U)
    {H : ℝ × (E × E) → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Icc (0:ℝ) 1 ×ˢ univ))
    (hs : ∀ t ∈ Icc (0:ℝ) 1, Function.support (fun x => H (t,x)) ⊆ S) :
    ∃ (ζ : E → ℝ) (δ : ℝ) (n : ℕ) (K : ℝ≥0)
      (φ : ODE.CompleteFlow (SmoothFlow.timeLift (hamiltonianField (flatTimeField H))))
      (steps : Fin n → PreparedMixedStep S δ),
      ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧
      (∀ x, ζ x ∈ Icc (0:ℝ) 1) ∧
      (∀ x ∈ Prod.fst '' S, ζ =ᶠ[𝓝 x] fun _ => 1) ∧
      0 < δ ∧ 0 < n ∧
      (∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U) ∧
      LipschitzWith K (hamiltonianField (flatTimeField H)) ∧
      ∀ i z, (steps i).ψ z =
        SmoothFlow.evolution φ ((((i.val:ℝ)/n),z),((i.val+1:ℕ):ℝ)/n) := by
  obtain ⟨ζ,hζ,hζc,hζU,hζr,hζ1⟩ := exists_spatial_cutoff (hS.image continuous_fst) hU
    (by rintro x ⟨z,hz,rfl⟩; exact hSU z hz)
  obtain ⟨δ,hδ,hbuf⟩ := exists_shift_buffer hζc hU hζU
  obtain ⟨K,φ,hK,hφ,hsp⟩ := exists_flat_hamiltonian_evolution hH hS hs
  let G := flatTimeField H
  have hG : ContDiff ℝ ∞ G := contDiff_flatTimeField hH
  have hstation (s t : ℝ) (x : E × E) (hx : x ∉ S) :
      SmoothFlow.evolution φ ((s,x),t) = x := by
    apply sub_eq_zero.mp
    by_contra hn
    exact hx (hsp s t hn)
  have hGS (x : E × E) (hx : x ∉ S) (t : ℝ) : G (t,x) = 0 := by
    have hz : H (Real.smoothTransition t,x) = 0 := by
      by_contra hn
      exact hx (hs _ (smoothTime_mem t) hn)
    simp only [G,flatTimeField,hz,smul_zero]
  let g : (ℝ × ℝ) × (E × E) → E × E :=
    fun z => SmoothFlow.evolution φ ((z.1.1,z.2),z.1.2)
  have hg : ContDiff ℝ ∞ g := hφ.comp
    ((contDiff_fst.fst.prodMk contDiff_snd).prodMk contDiff_fst.snd)
  obtain ⟨n,hn,hstep⟩ := exists_uniform_time_subdivision_both hg hS
    (fun t x => SmoothFlow.evolution_initial φ t x) hstation (show (0:ℝ) < 1/2 by norm_num) hδ
  have hprepare (i : Fin n) : ∃ step : PreparedMixedStep S δ,
      ∀ z, step.ψ z = SmoothFlow.evolution φ ((((i.val:ℝ)/n),z),((i.val+1:ℕ):ℝ)/n) := by
    let a : ℝ := (i.val:ℝ)/n
    let b : ℝ := ((i.val+1:ℕ):ℝ)/n
    let ψ := (SmoothFlow.evolutionDiffeomorph φ (contDiff_hamiltonianField hG) hK a b).toHomeomorph
    let f := hamiltonianTrajectory φ a
    have hf : ContDiff ℝ ∞ f := contDiff_hamiltonianTrajectory φ hG hK a
    have hψ : ∀ z, ψ z = f (b,z) := fun _ => rfl
    obtain ⟨e,σ,he,hes,hjs,hσ,hσc,hd,hσ0,hσp,hgraph,hout⟩ :=
      exists_controlled_mixed_generator f G hf hG
        (fun t z w => hamiltonianTrajectory_identity φ hG hK a t z w)
        a b (hamiltonianTrajectory_initial φ a) ψ hψ hS
        (fun z hz t => hstation a t z hz) hGS (1/2:ℝ≥0) (by norm_num)
        (fun z => (hstep i.val i.isLt z).1.le) (fun z => (hstep i.val i.isLt z).2)
    refine ⟨⟨ψ, σ, hf.comp (contDiff_const.prodMk contDiff_id), hσ, hσc,
      (fun z hz => hstation a b z hz), hσ0, hσp, hgraph, hout,
      (fun X p => mixed_twist_surjective e he hes hjs hd (X,p))⟩, ?_⟩
    intro z
    rfl
  choose steps hsteps using hprepare
  exact ⟨ζ,δ,n,K,φ,steps,hζ,hζc,hζr,hζ1,hδ,hn,hbuf,hK,hsteps⟩

end NearbyLagrangian.Transport

namespace NearbyLagrangian.Transport
open Set Filter ContinuousLinearMap
open scoped ContDiff Topology
variable {E W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

theorem PreparedMixedStep.exists_stepData {S : Set (E × E)} {δ : ℝ}
    (P : PreparedMixedStep S δ) (hS : IsCompact S) {U : Set E} (hU : IsOpen U)
    (hSU : ∀ z ∈ S, z.1 ∈ U) (hδ : 0 < δ)
    {ζ : E → ℝ} (hζ : ContDiff ℝ ∞ ζ) (hζr : ∀ x, ζ x ∈ Icc (0:ℝ) 1)
    (hζ1 : ∀ x ∈ Prod.fst '' S, ζ =ᶠ[𝓝 x] fun _ => 1)
    (hbuf : ∀ x ∈ tsupport ζ, ∀ v, ‖v‖ ≤ 2*δ → x+v ∈ U)
    (F : E × W → ℝ) {R c C : ℝ} (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C)
    (hF : ∀ x ∈ U, ∀ w, ContDiffAt ℝ ∞ F (x,w))
    (hbase : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → ‖baseDifferential F x w‖ ≤ C * ‖w‖^2)
    (hvert : ∀ x ∈ U, ∀ w, R ≤ ‖w‖ → c * ‖w‖ ≤ ‖verticalDifferential F x w‖) :
    ∃ T : StepData (E := E) (W := W), T.U = U ∧ T.F = F ∧ T.σ = P.σ ∧
      T.ψ = P.ψ ∧ T.ζ = ζ ∧ T.δ₀ = δ ∧ HasCompactSupport T.β ∧
      HasCompactSupport T.χ ∧ HasCompactSupport T.σ ∧
      ContDiff ℝ ∞ (T.ψ : E × E → E × E) ∧
      ∀ X p, Function.Surjective (ContinuousLinearMap.id ℝ E +
        (fderiv ℝ (mixedDisplacement T.σ) (X,p)).comp (inl ℝ E E)) := by
  obtain ⟨T,hTU,hTF,hTσ,hTψ,hTζ,hTδ,hTβ,hTχ⟩ :=
    exists_stepData_of_mixed hU (hS.image continuous_fst).isClosed F P.σ P.ψ
      hR hc hC hδ hF P.smooth_σ hζ hζr hζ1 hbuf P.σ_zero P.σ_bound hbase hvert
      (fun x p => base_mem_iff_of_compact_support P.ψ.injective hSU P.fixed x p)
      (fun x p X _ => P.graph x p X) (fun x p _ => P.output x p)
  refine ⟨T,hTU,hTF,hTσ,hTψ,hTζ,hTδ,hTβ,hTχ,?_,?_,?_⟩
  · rw [hTσ]; exact P.compact_σ
  · rw [hTψ]; exact P.smooth_ψ
  · rw [hTσ]; exact P.twist

end NearbyLagrangian.Transport

end

end OAI
