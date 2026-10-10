import OAI.Analysis.CircleDomains.Topology.CompactScalarCircleModelData
import OAI.Analysis.CircleDomains.Topology.FiniteCompactTests
import OAI.Analysis.CircleDomains.Topology.SphereCoreExhaustion

namespace OAI

/-! A sequence of actual finite scalar circle models has a normalized
conformal subsequential limit on the entire fixed source domain. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem scalar_models_conformal_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    {G : Set Sphere} (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) {a : ℝ} (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a)
    (T : ℕ → FiniteCompactTests G)
    (M : ∀ n, CompactScalarCircleModel G (T n).test) :
    ∃ (s : ℕ → ℕ) (F : ℂ → ℂ), StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n => (M (s n)).function) F atTop
        {z : ℂ | (z : Sphere) ∈ G} ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) := by
  let D : Set ℂ := {z : ℂ | (z : Sphere) ∈ G}
  have hD : IsOpen D := hG.preimage OnePoint.continuous_coe
  have hext : {z : ℂ | a ≤ ‖z‖} ⊆ D := by
    intro z hz
    by_contra hn
    have hb := hBa hn
    rw [mem_ball,dist_zero_right] at hb
    exact (not_lt_of_ge hz) hb
  have hDn : D.Nonempty := by
    refine ⟨(a : ℂ), hext ?_⟩
    simp only [mem_ofPred_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ha,le_refl]
  have hDc : IsConnected D := ⟨hDn,
    (finite_part_connected_unbounded hconn.isPreconnected
      (mem_interior_iff_mem_nhds.mpr (hG.mem_nhds hinf))).1⟩
  let f : ℕ → Sphere → Sphere := fun n => extendAtInfinity (M n).function
  let V : ℕ → Set Sphere := fun n => f n '' G
  have hV : ∀ n, IsOpen (V n) := fun n => (M n).circle.1
  choose fi hfi using fun n => (M n).conformal.exists_smooth_inverse hG (hV n)
  have hsource : (((↑) : ℂ → Sphere) '' ball 0 a)ᶜ ⊆ G := by
    intro p hp
    cases p using OnePoint.rec with
    | infty => exact hinf
    | coe z =>
        apply hext
        change a ≤ ‖z‖
        by_contra hz
        exact hp ⟨z, by simpa only [mem_ball,dist_zero_right] using lt_of_not_ge hz, rfl⟩
  have hclosed : (((↑) : ℂ → Sphere) '' closedBall 0 a)ᶜ ⊆ G :=
    (compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans hsource
  obtain ⟨s,F,hs,hlim,hnorm,hconf⟩ := exists_conformal_limit_of_sphere_models
    harea hmontel hhurwitz hzero f fi (fun _ => G) V hfi hV
    (fun _ => hD) (fun _ => hDc) (fun _ _ _ => Subset.rfl)
    (fun _ _ hz => hz) (fun n p hp => (M n).conformal.1 p (by
      obtain ⟨z,hz,rfl⟩ := hp
      exact hz)) ha (fun _ => hsource)
    (fun n p hp => (M n).conformal.1 p (hclosed hp)) (fun n => (M n).normalized)
    (fun z hz => hext (by
      change a ≤ ‖z‖
      change 2*a ≤ ‖z‖ at hz
      linarith))
  have hfinite : (((↑) : ℂ → Sphere) '' D ∪ {OnePoint.infty}) = G := by
    ext p
    cases p using OnePoint.rec with
    | infty => simp [hinf]
    | coe z => simp [D]
  refine ⟨s,F,hs,?_,hnorm,?_⟩
  · simpa only [iUnion_const, f, extendAtInfinity_coe, finiteCoord_coe] using hlim
  · simpa only [iUnion_const,hfinite] using hconf

end CircleDomainRigidity

end

end OAI
