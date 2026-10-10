import Mathlib
import OAI.Analysis.BiholderTransport.Geodesics.GeodesicBasics
import OAI.Analysis.BiholderTransport.Regularity.RiemannianMetricSegment
import OAI.Analysis.BiholderTransport.Geodesics.NoCorner

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [CompactSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma sprayFlow_minimizing_subinterval (z : TangentBundle 𝓘(ℝ,E) M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hmin : dist z.1 (sprayFlow t z).1 = t * ‖z.2‖) :
    dist (sprayFlow s z).1 (sprayFlow t z).1 = (t-s) * ‖z.2‖ := by
  have hle := dist_sprayFlow_le z s t
  rw [abs_of_nonpos (sub_nonpos.mpr hst),neg_sub] at hle
  apply le_antisymm hle
  have hlow := dist_triangle z.1 (sprayFlow s z).1 (sprayFlow t z).1
  rw [hmin,sprayFlow_minimizing_prefix z hs hst hmin] at hlow
  nlinarith

end

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma exists_local_minimizingVectors (x : M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ Metric.ball x δ,
      ∃ p ∈ minimizingVectors (n := n) x, riemannianExp x p = y := by
  obtain ⟨δ,hδ,H⟩ := exists_local_cost_gradient (E := Model n) x
  refine ⟨δ,hδ,?_⟩
  intro y hy
  obtain ⟨q,hqx,hqn,hqb,_⟩ := H y hy x (Metric.mem_ball_self hδ)
  rcases q with ⟨a,u⟩
  change a=x at hqx
  subst a
  have he : riemannianExp x (-u) = y := by
    rw [show -u = (-1:ℝ) • u by simp,riemannianExp_smul]
    exact hqb
  refine ⟨-u,?_,he⟩
  change dist x (riemannianExp x (-u)) = ‖-u‖
  rw [he,norm_neg,hqn,dist_comm]

lemma exists_minimizing_vector (x y : M) :
    ∃ p ∈ minimizingVectors (n := n) x, riemannianExp x p = y := by
  classical
  by_cases hxy : x=y
  · subst y
    exact ⟨0,by simp [minimizingVectors],riemannianExp_zero x⟩
  have hD : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨γ,hγ,hγ0,hγD⟩ := riemannian_exists_metric_segment (I := 𝓘(ℝ,Model n)) x y
  have hd (s : Icc (0:ℝ) (dist x y)) : dist x (γ s) = s.1 := by
    have hh := hγ.dist_eq (⟨0,⟨le_rfl,dist_nonneg⟩⟩ : Icc (0:ℝ) (dist x y)) s
    simpa only [hγ0,Subtype.dist_eq,Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg s.2.1] using hh
  let R : Set M := riemannianExp (n := n) x '' minimizingVectors x
  have hR : IsCompact R := (isCompact_minimizingVectors x).image (continuous_riemannianExp x)
  let U : Set (Icc (0:ℝ) (dist x y)) := γ ⁻¹' R
  have hU : IsCompact U := (hR.isClosed.preimage hγ.continuous).isCompact
  obtain ⟨δ,hδ,Hlocal⟩ := exists_local_minimizingVectors (n := n) x
  let a : ℝ := min (dist x y/2) (δ/2)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haD : a ≤ dist x y := (min_le_left _ _).trans (by linarith)
  have haδ : a < δ := (min_le_right _ _).trans_lt (by linarith)
  let s₀ : Icc (0:ℝ) (dist x y) := ⟨a,ha.le,haD⟩
  have hs₀ : s₀ ∈ U := by
    obtain ⟨p,hp,he⟩ := Hlocal (γ s₀) (by rw [Metric.mem_ball,dist_comm,hd]; exact haδ)
    exact ⟨p,hp,he⟩
  obtain ⟨s,hs,hsmax⟩ := hU.exists_isMaxOn ⟨s₀,hs₀⟩ continuous_subtype_val.continuousOn
  have hs0 : 0 < s.1 := ha.trans_le (hsmax hs₀)
  have hsD : s.1 = dist x y := by
    by_contra hsne
    have hslt : s.1 < dist x y := lt_of_le_of_ne s.2.2 hsne
    obtain ⟨p,hp,hps⟩ := hs
    have hpn : ‖p‖ = s.1 := by
      change dist x (riemannianExp x p) = ‖p‖ at hp
      rw [hps,hd] at hp
      exact hp.symm
    let z : TangentBundle 𝓘(ℝ,Model n) M := ⟨x,s.1⁻¹ • p⟩
    have hzn : ‖z.2‖ = 1 := by
      change ‖s.1⁻¹ • p‖ = 1
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs0),hpn,inv_mul_cancel₀ hs0.ne']
    have hzflow : (sprayFlow s.1 z).1 = γ s := by
      rw [←riemannianExp_smul]
      rw [smul_smul,mul_inv_cancel₀ hs0.ne',one_smul,hps]
    have hzmin : dist z.1 (sprayFlow s.1 z).1 = s.1 * ‖z.2‖ := by
      rw [hzflow,hzn,mul_one]; exact hd s
    obtain ⟨η,hη,Hext⟩ := exists_spray_local_extension (E := Model n) (γ s)
    let ε : ℝ := min (η/2) (min (s.1/2) ((dist x y-s.1)/2))
    have hε : 0 < ε := lt_min (by positivity) (lt_min (by positivity) (by linarith))
    have hεη : ε < η := (min_le_left _ _).trans_lt (by linarith)
    have hεs : ε < s.1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
    have hεD : s.1+ε < dist x y := by
      have h := (min_le_right (η/2) (min (s.1/2) ((dist x y-s.1)/2))).trans (min_le_right _ _)
      change ε ≤ (dist x y-s.1)/2 at h
      linarith
    let s' : Icc (0:ℝ) (dist x y) := ⟨s.1+ε,by linarith,hεD.le⟩
    let q := sprayFlow s.1 z
    have hqn : ‖q.2‖ = 1 := by rw [sprayFlow_speed]; exact hzn
    have hqback : sprayFlow (-ε) q = sprayFlow (s.1-ε) z := by
      rw [←sprayFlow_add]; congr 1; ring
    have hpre : dist (sprayFlow (-ε) q).1 q.1 = ε := by
      rw [hqback]
      have h := sprayFlow_minimizing_subinterval z (s := s.1-ε) (by linarith) (by linarith) hzmin
      rw [hzn,mul_one] at h
      simpa only [sub_sub_cancel] using h
    have hnext : dist q.1 (γ s') = ε := by
      change dist (sprayFlow s.1 z).1 _ = _
      rw [hzflow,hγ.dist_eq,Subtype.dist_eq,Real.dist_eq]
      change |s.1-(s.1+ε)| = ε
      rw [show s.1-(s.1+ε) = -ε by ring,abs_neg,abs_of_pos hε]
    have hlong : dist (sprayFlow (-ε) q).1 (γ s') = 2*ε := by
      apply le_antisymm
      · exact (dist_triangle _ q.1 _).trans (by rw [hpre,hnext]; linarith)
      · have h := dist_triangle x (sprayFlow (-ε) q).1 (γ s')
        rw [hd,hqback] at h
        have hpref := sprayFlow_minimizing_prefix z (s := s.1-ε) (by linarith) (by linarith) hzmin
        rw [hzn,mul_one] at hpref
        change dist x (sprayFlow (s.1-ε) z).1 = s.1-ε at hpref
        rw [hpref] at h
        change s.1+ε ≤ _ at h
        rw [hqback]
        linarith
    have hext := Hext q hzflow hqn ε hε hεη (γ s') hpre hnext hlong
    have hznext : (sprayFlow (s.1+ε) z).1 = γ s' := by
      rw [add_comm,sprayFlow_add]; exact hext
    have hs' : s' ∈ U := by
      refine ⟨(s.1+ε) • z.2,?_,?_⟩
      · change dist x (riemannianExp x ((s.1+ε) • z.2)) = ‖(s.1+ε) • z.2‖
        rw [riemannianExp_smul,hznext,hd,norm_smul,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < s.1+ε),hzn,mul_one]
      · rw [riemannianExp_smul]; exact hznext
    have hh := hsmax hs'
    change s.1+ε ≤ s.1 at hh
    linarith
  obtain ⟨p,hp,he⟩ := hs
  refine ⟨p,hp,he.trans ?_⟩
  have hsEq : s = ⟨dist x y,⟨dist_nonneg,le_rfl⟩⟩ := Subtype.ext hsD
  rw [hsEq,hγD]

end WeakMTWTransport

end

end OAI
