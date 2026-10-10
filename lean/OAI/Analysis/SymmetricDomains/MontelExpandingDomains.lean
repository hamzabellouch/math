import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI


namespace Release061
open Set Filter Metric TopologicalSpace
open scoped Topology

theorem locally_uniform_subsequence_of_eventual_equicontinuity
    {X Y : Type*} [TopologicalSpace X] [SeparableSpace X]
    [MetricSpace Y] [CompleteSpace Y]
    (f : ℕ → X → Y)
    (hequi : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f j y) (f j x) < ε)
    (hcompact : ∀ x, ∃ K : Set Y, IsCompact K ∧ ∀ j, f j x ∈ K) :
    ∃ g : X → Y, Continuous g ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformly (fun j => f (φ j)) g atTop := by
  classical
  obtain ⟨D,hD,hdense⟩ := TopologicalSpace.exists_countable_dense X
  let : Countable D := hD.to_subtype
  choose K hK hmem using hcompact
  have hprod : IsCompact (Set.pi univ (fun x : D => K x.val)) :=
    isCompact_univ_pi (fun x : D => hK x.val)
  obtain ⟨gD,_,φ,hφ,hconvD⟩ := hprod.tendsto_subseq
    (fun j => (show (fun x : D => f j x.val) ∈ Set.pi univ (fun x : D => K x.val) from
      fun x _ => hmem x.val j))
  have hcD : ∀ x : D, Tendsto (fun j => f (φ j) x.val) atTop (𝓝 (gD x)) :=
    fun x => (tendsto_pi_nhds.mp hconvD) x
  have he : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f (φ j) y) (f (φ j) x) < ε := by
    intro x ε hε
    obtain ⟨W,hW,he⟩ := hequi x ε hε
    exact ⟨W,hW,hφ.tendsto_atTop he⟩
  have hcau : ∀ x, CauchySeq (fun j => f (φ j) x) := by
    intro x
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨W,hW,heW⟩ := he x (ε/3) (by positivity)
    obtain ⟨d,hdD,hdW⟩ := hdense.inter_nhds_nonempty hW
    obtain ⟨N₁,hN₁⟩ := Metric.cauchySeq_iff.mp (hcD ⟨d,hdD⟩).cauchySeq (ε/3) (by positivity)
    obtain ⟨N₂,hN₂⟩ := eventually_atTop.mp heW
    refine ⟨max N₁ N₂,?_⟩
    intro i hi j hj
    have hi₁ := le_trans (le_max_left N₁ N₂) hi
    have hi₂ := le_trans (le_max_right N₁ N₂) hi
    have hj₁ := le_trans (le_max_left N₁ N₂) hj
    have hj₂ := le_trans (le_max_right N₁ N₂) hj
    have hdi := hN₂ i hi₂ d hdW
    have hdj := hN₂ j hj₂ d hdW
    have hdij := hN₁ i hi₁ j hj₁
    calc
      dist (f (φ i) x) (f (φ j) x) ≤
          dist (f (φ i) x) (f (φ i) d) + dist (f (φ i) d) (f (φ j) d) +
            dist (f (φ j) d) (f (φ j) x) := dist_triangle4 _ _ _ _
      _ < ε := by rw [dist_comm (f (φ i) x) (f (φ i) d)]; linarith
  choose g hg using fun x => cauchySeq_tendsto_of_complete (hcau x)
  have hlimit : ∀ x ε, 0 < ε → ∃ W : Set X, W ∈ 𝓝 x ∧
      (∀ y ∈ W, dist (g y) (g x) ≤ ε) ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f (φ j) y) (f (φ j) x) < ε := by
    intro x ε hε
    obtain ⟨W,hW,heW⟩ := he x ε hε
    refine ⟨W,hW,?_,heW⟩
    intro y hy
    exact le_of_tendsto ((hg y).dist (hg x))
      (heW.mono (fun j hj => (hj y hy).le))
  have hgc : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt,Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨W,hW,hlim,_⟩ := hlimit x (ε/2) (by positivity)
    filter_upwards [hW] with y hy
    exact (hlim y hy).trans_lt (by linarith)
  refine ⟨g,hgc,φ,hφ,?_⟩
  rw [Metric.tendstoLocallyUniformly_iff]
  intro ε hε x
  obtain ⟨W,hW,hlim,heW⟩ := hlimit x (ε/3) (by positivity)
  refine ⟨W,hW,?_⟩
  have hpx : ∀ᶠ j in atTop, dist (g x) (f (φ j) x) < ε/3 := by
    simpa only [dist_comm] using (Metric.tendsto_nhds.mp (hg x) (ε/3) (by positivity))
  filter_upwards [heW,hpx] with j hj hx y hy
  calc
    dist (g y) (f (φ j) y) ≤ dist (g y) (g x) + dist (g x) (f (φ j) x) +
        dist (f (φ j) x) (f (φ j) y) := dist_triangle4 _ _ _ _
    _ < ε := by have := hlim y hy; have := hj y hy; rw [dist_comm (f (φ j) x) (f (φ j) y)]; linarith

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem bounded_fderiv_on_half_ball {f : E → F} {c x : E} {R M : ℝ}
    (hR : 0 < R) (hf : DifferentiableOn ℂ f (ball c R))
    (hb : ∀ z ∈ ball c R, ‖f z‖ ≤ M) (hx : x ∈ ball c (R/2)) :
    ‖fderiv ℂ f x‖ ≤ 4*M/R := by
  have hsub : ball x (R/2) ⊆ ball c R := by
    intro z hz
    rw [mem_ball] at hx hz ⊢
    calc
      dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ < R := by linarith
  have hxR : x ∈ ball c R := hsub (mem_ball_self (half_pos hR))
  have hm : MapsTo f (ball x (R/2)) (closedBall (f x) (2*M)) := by
    intro z hz
    rw [mem_closedBall,dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith [hb z (hsub hz),hb x hxR])
  have he := Complex.norm_fderiv_le_div_of_mapsTo_ball (hf.mono hsub) hm (half_pos hR)
  convert he using 1; ring

theorem uniformCauchySeqOn_fderiv_of_uniformCauchySeqOn
    {f : ℕ → E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (ball c R))
    (hcu : UniformCauchySeqOn f atTop (ball c R)) :
    UniformCauchySeqOn (fun j => fderiv ℂ (f j)) atTop (ball c (R/2)) := by
  rw [Metric.uniformCauchySeqOn_iff] at hcu ⊢
  intro ε hε
  obtain ⟨N,hN⟩ := hcu (ε*R/8) (by positivity)
  refine ⟨N,?_⟩
  intro j hj k hk x hx
  have hb : ∀ z ∈ ball c R, ‖f j z-f k z‖ ≤ ε*R/8 := by
    intro z hz
    exact le_of_lt (by simpa only [dist_eq_norm] using hN j hj k hk z hz)
  have hest := bounded_fderiv_on_half_ball hR ((hf j).sub (hf k)) hb hx
  have hxR : x ∈ ball c R := ball_subset_ball (by linarith) hx
  rw [fderiv_sub ((hf j).differentiableAt (isOpen_ball.mem_nhds hxR))
    ((hf k).differentiableAt (isOpen_ball.mem_nhds hxR))] at hest
  rw [dist_eq_norm]
  apply hest.trans_lt
  field_simp
  nlinarith

theorem differentiableAt_of_uniform_limit_ball [CompleteSpace F]
    {f : ℕ → E → F} {g : E → F} {c : E} {R : ℝ} (hR : 0 < R)
    (hf : ∀ j, DifferentiableOn ℂ (f j) (ball c R))
    (hfg : TendstoUniformlyOn f g atTop (ball c R)) :
    DifferentiableAt ℂ g c := by
  classical
  have hcu := uniformCauchySeqOn_fderiv_of_uniformCauchySeqOn hR hf hfg.uniformCauchySeqOn
  have hpt : ∀ x ∈ ball c (R/2), ∃ L : E →L[ℂ] F,
      Tendsto (fun j => fderiv ℂ (f j) x) atTop (𝓝 L) := by
    intro x hx
    have hcux : CauchySeq (fun j => fderiv ℂ (f j) x) := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N,hN⟩ := Metric.uniformCauchySeqOn_iff.mp hcu ε hε
      exact ⟨N,fun j hj k hk => hN j hj k hk x hx⟩
    exact cauchySeq_tendsto_of_complete hcux
  choose L hL using hpt
  let dg : E → E →L[ℂ] F := fun x => if hx : x ∈ ball c (R/2) then L x hx else 0
  have hder : TendstoUniformlyOn (fun j => fderiv ℂ (f j)) dg atTop (ball c (R/2)) := by
    apply hcu.tendstoUniformlyOn_of_tendsto
    intro x hx
    simpa only [dg,dite_eq_left hx] using hL x hx
  apply (hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hder
    (fun j x hx => ((hf j).differentiableAt
      (isOpen_ball.mem_nhds (ball_subset_ball (by linarith) hx))).hasFDerivAt)
    (fun x hx => hfg.tendsto_at (ball_subset_ball (by linarith) hx))
    (mem_ball_self (half_pos hR))).differentiableAt

theorem differentiableOn_of_locally_uniform_limit [ProperSpace E] [CompleteSpace F]
    {f : ℕ → E → F} {g : E → F} {S : Set E} (hS : IsOpen S)
    (hfg : TendstoLocallyUniformlyOn f g atTop S)
    (hf : ∀ x ∈ S, ∃ W : Set E, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, DifferentiableOn ℂ (f j) W) :
    DifferentiableOn ℂ g S := by
  intro x hx
  obtain ⟨W,hW,hhol⟩ := hf x hx
  obtain ⟨R,hR,hRW⟩ := Metric.mem_nhds_iff.mp (inter_mem hW (hS.mem_nhds hx))
  have hsub : closedBall x (R/2) ⊆ W ∩ S :=
    (closedBall_subset_ball (by linarith)).trans hRW
  have hc : TendstoUniformlyOn f g atTop (ball x (R/2)) := by
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_closedBall x (R/2))).mp (hfg.mono (fun y hy => (hsub hy).2)) |>.mono
    exact ball_subset_closedBall
  obtain ⟨N,hN⟩ := eventually_atTop.mp hhol
  have htail : TendstoUniformlyOn (fun j => f (j+N)) g atTop (ball x (R/2)) := by
    intro u hu
    exact (Filter.tendsto_add_atTop_nat N) (hc u hu)
  apply (differentiableAt_of_uniform_limit_ball (half_pos hR)
    (fun j => (hN (j+N) (Nat.le_add_left _ _)).mono
      (fun y hy => (hsub (ball_subset_closedBall hy)).1)) htail).differentiableWithinAt

omit [NormedSpace ℂ F] in

theorem compact_range_of_eventually_norm_le [ProperSpace F]
    {u : ℕ → F} {M : ℝ} (hM : 0 < M)
    (hu : ∀ᶠ j in atTop, ‖u j‖ ≤ M) :
    ∃ K : Set F, IsCompact K ∧ ∀ j, u j ∈ K := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hu
  let B := M + ∑ j ∈ Finset.range N, ‖u j‖
  refine ⟨closedBall 0 B,isCompact_closedBall _ _,?_⟩
  intro j
  rw [mem_closedBall,dist_zero_right]
  by_cases hj : j < N
  · have hb : ‖u j‖ ≤ ∑ i ∈ Finset.range N, ‖u i‖ :=
      Finset.single_le_sum (fun i _ => norm_nonneg (u i)) (Finset.mem_range.mpr hj)
    dsimp [B]
    linarith
  · exact (hN j (Nat.le_of_not_gt hj)).trans (by dsimp [B]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => norm_nonneg (u i))))

theorem montel_expanding_domains [ProperSpace E] [SecondCountableTopology E]
    [ProperSpace F] {S : Set E} (hS : IsOpen S) (f : ℕ → E → F)
    (hlocal : ∀ x ∈ S, ∃ r : ℝ, 0 < r ∧ ∃ M : ℝ, 0 < M ∧
      ball x r ⊆ S ∧ ∀ᶠ j in atTop,
        DifferentiableOn ℂ (f j) (ball x r) ∧ ∀ y ∈ ball x r, ‖f j y‖ ≤ M) :
    ∃ g : E → F, DifferentiableOn ℂ g S ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoLocallyUniformlyOn (fun j => f (φ j)) g atTop S := by
  classical
  have hequi : ∀ x : S, ∀ ε, 0 < ε → ∃ W : Set S, W ∈ 𝓝 x ∧
      ∀ᶠ j in atTop, ∀ y ∈ W, dist (f j y.val) (f j x.val) < ε := by
    intro x ε hε
    obtain ⟨r,hr,M,_,_,hF⟩ := hlocal x.val x.property
    let W : Set S := {y | y.val ∈ ball x.val r ∧ (2*M/r)*dist y.val x.val < ε}
    have hbase : ∀ᶠ y : S in 𝓝 x, y.val ∈ ball x.val r :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds (ball_mem_nhds _ hr)
    have hsmall : ∀ᶠ y : S in 𝓝 x, (2*M/r)*dist y.val x.val < ε := by
      have ht : Tendsto (fun y : S => (2*M/r)*dist y.val x.val) (𝓝 x) (𝓝 0) := by
        simpa using ((continuous_subtype_val.dist (continuous_const : Continuous (fun _ : S => x.val))).const_mul (2*M/r)).tendsto x
      exact (tendsto_order.mp ht).2 ε hε
    refine ⟨W,hbase.and hsmall,?_⟩
    filter_upwards [hF] with j hj y hy
    have hmaps : MapsTo (f j) (ball x.val r) (closedBall (f j x.val) (2*M)) := by
      intro z hz
      rw [mem_closedBall,dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hj.2 z hz,hj.2 x.val (mem_ball_self hr)])
    exact (Complex.dist_le_div_mul_dist_of_mapsTo_ball hj.1 hmaps hy.1).trans_lt hy.2
  have hcompact : ∀ x : S, ∃ K : Set F, IsCompact K ∧ ∀ j, f j x.val ∈ K := by
    intro x
    obtain ⟨r,hr,M,hM,_,hF⟩ := hlocal x.val x.property
    exact compact_range_of_eventually_norm_le hM
      (hF.mono (fun _ hj => hj.2 x.val (mem_ball_self hr)))
  obtain ⟨g,hgc,φ,hφ,hconv⟩ :=
    locally_uniform_subsequence_of_eventual_equicontinuity (fun j (x : S) => f j x.val) hequi hcompact
  let G : E → F := fun x => if hx : x ∈ S then g ⟨x,hx⟩ else 0
  have hc : TendstoLocallyUniformlyOn (fun j => f (φ j)) G atTop S := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [Function.comp_def,G,dite_eq_left (Subtype.prop _)] using hconv
  refine ⟨G,?_,φ,hφ,hc⟩
  apply differentiableOn_of_locally_uniform_limit hS hc
  intro x hx
  obtain ⟨r,hr,_,_,_,hF⟩ := hlocal x hx
  exact ⟨ball x r,ball_mem_nhds _ hr,hφ.tendsto_atTop (hF.mono (fun _ hj => hj.1))⟩

end Release061


end OAI
