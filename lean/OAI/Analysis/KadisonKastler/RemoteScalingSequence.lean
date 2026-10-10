import OAI.Analysis.KadisonKastler.RemoteProductCopy
import OAI.Analysis.KadisonKastler.ScalingCoisometryEstimates
import OAI.Analysis.KadisonKastler.TwoRatioScalingDensity
import OAI.Analysis.KadisonKastler.StrongReferenceTests

namespace OAI

/-! # Strongly central sequences of scaling coisometries

The copies commute exactly with increasingly many sites. The state-scaling
identity controls multiplication on the product vector, and its separating
property extends convergence to every vector in the represented Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace PointedMatrixSites

variable (S : PointedMatrixSites M Ω twoRatioSiteParameter)

theorem remoteCopy_commutator_tendsto (r : ℕ → ℝ) (v : ℕ → Algebra M)
    (hv : ∀ n, v n*star (v n)=1)
    (hs : ∀ n, StateScales M Ω (r n) (v n).val) (hr : ∀ n, r n ≤ 1)
    (a : Algebra M) (η : H) :
    Tendsto (fun n => (a*S.remoteCopy n (v n)-S.remoteCopy n (v n)*a).val η)
      atTop (𝓝 0) := by
  let w (n : ℕ) := S.remoteCopy n (v n)
  have hw (n : ℕ) : w n*star (w n)=1 := by
    change S.remoteCopy n (v n)*star (S.remoteCopy n (v n))=1
    rw [← map_star,← map_mul,hv,map_one]
  have hwscale (n : ℕ) : StateScales M Ω (r n) (w n).val :=
    S.remoteCopy_scales n (v n) (hs n)
  have hbound (n : ℕ) : ‖a*w n-w n*a‖ ≤ 2*‖a‖ := by
    have hn := coisometry_norm_le (w n) (hw n)
    calc
      _ ≤ ‖a*w n‖+‖w n*a‖ := norm_sub_le _ _
      _ ≤ ‖a‖*‖w n‖+‖w n‖*‖a‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ 2*‖a‖ := by nlinarith [norm_nonneg a]
  apply algebra_strong_tendsto_of_reference Ω
    (commutant_cyclic_of_separating_reference Ω S.separating)
    (fun n => a*w n-w n*a) (2*‖a‖) (by positivity) hbound ?_ η
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨⟨k,b⟩,hb⟩ := S.twoRatioMatrix_local_cyclic.exists_dist_lt (a.val Ω)
    (show 0 < ε/3 by positivity)
  let bM : Algebra M := ⟨b.val,S.twoRatioMatrix_le k b.property⟩
  have hbM : ‖(a-bM).val Ω‖ < ε/3 := by
    change dist (a.val Ω) (b.val Ω) < ε/3 at hb
    simpa only [bM,AddSubgroupClass.coe_sub,sub_apply,dist_eq_norm] using hb
  filter_upwards [eventually_ge_atTop k] with n hn
  have hcomm : Commute bM (w n) := by
    apply Subtype.ext
    exact (S.remoteCopy_commutes_stage n (v n) b.val
      (S.twoRatioMatrix_increasing hn b.property)).eq
  have hest := (hwscale n).coisometry_commutator_bound (w n) (hw n) (hr n) a bM hcomm
  have he : ‖(a*w n-w n*a).val Ω‖ < ε := hest.trans_lt (by linarith)
  simpa only [dist_zero_right] using he

include S in
theorem exists_remote_scaling_sequence {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ (s : ℕ → ℝ) (v : ℕ → Algebra M),
      Tendsto s atTop (𝓝 r) ∧
      (∀ n, 0 < s n ∧ s n < 1 ∧ v n*star (v n)=1 ∧ StateScales M Ω (s n) (v n).val) ∧
      (∀ (a : Algebra M) (η : H),
        Tendsto (fun n => (a*v n-v n*a).val η) atTop (𝓝 0)) := by
  choose s w hpos hlt hclose hco hscale using
    (fun n : ℕ => S.exists_scaling_coisometry_near hr hr1
      (show 0 < (1 : ℝ)/(n+1) by positivity))
  refine ⟨s,(fun n => S.remoteCopy n (w n)),?_,?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨k,hk⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hclose n).trans_le ((one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hn 1)).trans hk.le)
  · intro n
    refine ⟨hpos n,hlt n,?_,S.remoteCopy_scales n (w n) (hscale n)⟩
    rw [← map_star,← map_mul,hco,map_one]
  · intro a η
    exact S.remoteCopy_commutator_tendsto s w hco hscale (fun n => (hlt n).le) a η

end PointedMatrixSites

end

end KadisonKastler

end OAI
