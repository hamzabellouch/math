import OAI.Analysis.HotSpots.Riemann
import OAI.Analysis.HotSpots.Trace

namespace OAI

section RollingBallTaylor




noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma taylor_quadratic {f : E → ℝ} {U : Set E} {K : ℝ≥0}
    (hU : Convex ℝ U) (hd : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hL : LipschitzOnWith K (fderiv ℝ f) U) {p x : E} (hp : p ∈ U) (hx : x ∈ U) :
    ‖f x-f p-fderiv ℝ f p (x-p)‖ ≤ (K:ℝ)*‖x-p‖^2 := by
  have hs : segment ℝ p x ⊆ U := hU.segment_subset hp hx
  have H := (convex_segment p x).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => hd y (hs hy))
    (φ := fderiv ℝ f p) (C := (K:ℝ)*‖x-p‖)
    (fun y hy => (hL.norm_sub_le (hs hy) hp).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hy) K.coe_nonneg))
    (left_mem_segment ℝ p x) (right_mem_segment ℝ p x)
  simpa only [pow_two,mul_assoc] using H

lemma norm_sub_smul_sq (y n : E) (r : ℝ) :
    ‖y-r•n‖^2 = ‖y‖^2 - 2*r*inner ℝ y n + r^2*‖n‖^2 := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  ring

lemma tangent_ball_linear {p n x : E} {r : ℝ} (hn : ‖n‖ = 1) (hr : 0 < r)
    (hx : x ∈ ball (p+r•n) r) :
    ‖x-p‖^2 < 2*r*inner ℝ (x-p) n := by
  have hh : ‖(x-p)-r•n‖ < r := by
    simpa only [mem_ball,dist_eq_norm,sub_add_eq_sub_sub] using hx
  have hh2 := (sq_lt_sq₀ (norm_nonneg _) hr.le).mpr hh
  rw [norm_sub_smul_sq,hn,one_pow,mul_one] at hh2
  linarith



lemma balls_of_taylor {f : E → ℝ} {p n : E} {U : Set E} {a K r : ℝ}
    (hn : ‖n‖ = 1) (ha : 0 < a) (hr : 0 < r)
    (hsmall : 2*r*K ≤ a) (hzero : f p = 0)
    (hD : ∀ v, fderiv ℝ f p v = a*inner ℝ n v)
    (hB : ball p (2*r) ⊆ U)
    (hT : ∀ x ∈ U, ‖f x-f p-fderiv ℝ f p (x-p)‖ ≤ K*‖x-p‖^2) :
    ball (p-r•n) r ⊆ {x | f x < 0} ∧
    ball (p+r•n) r ⊆ {x | 0 < f x} := by
  have hside (N : E) (hN : ‖N‖ = 1) (x : E) (hx : x ∈ ball (p+r•N) r) :
      x ∈ U ∧ ‖x-p‖^2 < 2*r*inner ℝ (x-p) N := by
    refine ⟨hB ?_,tangent_ball_linear hN hr hx⟩
    have hd : dist (p+r•N) p = r := by
      simp [dist_eq_norm,norm_smul,hN,abs_of_pos hr]
    calc
      dist x p ≤ dist x (p+r•N)+dist (p+r•N) p := dist_triangle _ _ _
      _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
      _ = 2*r := by ring
  constructor
  · intro x hx
    have hx' : x ∈ ball (p+r•(-n)) r := by simpa [smul_neg,sub_eq_add_neg] using hx
    obtain ⟨hxU,hx2⟩ := hside (-n) (by simpa using hn) x hx'
    rw [inner_neg_right,real_inner_comm n (x-p)] at hx2
    have ht := hT x hxU
    rw [hzero,sub_zero,hD,Real.norm_eq_abs] at ht
    have he := (le_abs_self (f x-a*inner ℝ n (x-p))).trans ht
    have hk := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x-p‖)
    have hstrict := mul_lt_mul_of_pos_left hx2 ha
    have hmul := mul_le_mul_of_nonneg_left he (mul_pos (by norm_num : (0:ℝ)<2) hr).le
    change f x < 0
    nlinarith only [hmul,hstrict,hk,hr]
  · intro x hx
    obtain ⟨hxU,hx2⟩ := hside n hn x hx
    rw [real_inner_comm n (x-p)] at hx2
    have ht := hT x hxU
    rw [hzero,sub_zero,hD,Real.norm_eq_abs] at ht
    have he' : -(K*‖x-p‖^2) ≤ f x-a*inner ℝ n (x-p) := by
      have hh := neg_abs_le (f x-a*inner ℝ n (x-p))
      linarith [ht]
    have hk := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖x-p‖)
    have hstrict := mul_lt_mul_of_pos_left hx2 ha
    have hmul := mul_le_mul_of_nonneg_left he' (mul_pos (by norm_num : (0:ℝ)<2) hr).le
    change 0 < f x
    nlinarith only [hmul,hstrict,hk,hr]

end StrictHotSpots.Rolling
end
end RollingBallTaylor

section RollingBallMetric

noncomputable section
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma tangent_ball_mono {p n : E} {s r : ℝ} (hn : ‖n‖ = 1)
    (hsr : s ≤ r) : ball (p+s•n) s ⊆ ball (p+r•n) r := by
  intro x hx
  have hd : dist (p+s•n) (p+r•n) = r-s := by
    rw [dist_eq_norm,show (p+s•n)-(p+r•n) = (s-r)•n by module,norm_smul,hn,mul_one,
      Real.norm_eq_abs,abs_of_nonpos (sub_nonpos.mpr hsr)]
    ring
  calc
    dist x (p+r•n) ≤ dist x (p+s•n)+dist (p+s•n) (p+r•n) := dist_triangle _ _ _
    _ < s+(r-s) := add_lt_add_of_lt_of_le hx (le_of_eq hd)
    _ = r := by ring




lemma nearest_normal_of_balls {Ω : Set E} {x p n : E} {r : ℝ}
    (hn : ‖n‖ = 1) (hr : 0 < r) (hxp : x ≠ p)
    (hin : ball x (dist x p) ⊆ Ω)
    (hout : ball (p+r•n) r ⊆ Ωᶜ) : x = p-dist x p • n := by
  let δ := dist x p
  have hδ : 0 < δ := dist_pos.mpr hxp
  have hdisj : Disjoint (ball x δ) (ball (p+r•n) r) := by
    refine disjoint_left.mpr (fun y hy₁ hy₂ => ?_)
    exact hout hy₂ (hin hy₁)
  have hd : δ+r ≤ ‖(x-p)-r•n‖ := by
    simpa only [dist_eq_norm,sub_add_eq_sub_sub] using
      (disjoint_ball_ball_iff hδ hr).mp hdisj
  have hnorm : ‖x-p‖ = δ := (dist_eq_norm _ _).symm
  have hd2 := (sq_le_sq₀ (by positivity : 0 ≤ δ+r) (norm_nonneg _)).mpr hd
  rw [norm_sub_smul_sq,hn,one_pow,mul_one,hnorm] at hd2
  have hi : inner ℝ (x-p) n ≤ -δ := by nlinarith only [hd2,hr]
  have hi' := mul_le_mul_of_nonneg_left hi hδ.le
  have he : ‖(x-p)+δ•n‖^2 = 0 := by
    have hnn := sq_nonneg ‖(x-p)+δ•n‖
    rw [norm_add_sq_real,hnorm,real_inner_smul_right,norm_smul,
      Real.norm_eq_abs,abs_of_pos hδ,hn,mul_one] at hnn ⊢
    nlinarith only [hi',hnn]
  have hz : (x-p)+δ•n = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  dsimp [δ] at hz
  calc
    x = (x-p)+p := by abel
    _ = -(dist x p•n)+p := congrArg (fun a => a+p) (eq_neg_of_add_eq_zero_left hz)
    _ = p-dist x p•n := by abel

lemma near_interior_ball {Ω : Set E} {x p n : E} {r : ℝ}
    (hn : ‖n‖ = 1) (hr : 0 < r) (hxp : x ≠ p)
    (hin : ball x (dist x p) ⊆ Ω) (hout : ball (p+r•n) r ⊆ Ωᶜ)
    (hnear : dist x p < r) :
    dist x (p-r•n) = r-dist x p ∧ x ∈ ball (p-r•n) r := by
  have he := nearest_normal_of_balls hn hr hxp hin hout
  have heq : x-(p-r•n) = (r-dist x p) • n := by
    calc
      _ = (p-dist x p•n)-(p-r•n) := congrArg (fun a => a-(p-r•n)) he
      _ = _ := by module
  have hd : dist x (p-r•n) = r-dist x p := by
    rw [dist_eq_norm,heq,norm_smul,hn,mul_one,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hnear)]
  refine ⟨hd,?_⟩
  change dist x (p-r•n) < r
  rw [hd]
  linarith [dist_pos.mpr hxp]

end StrictHotSpots.Rolling
end
end RollingBallMetric

section RollingBallNormals

noncomputable section
open Set Metric
open scoped Topology
namespace StrictHotSpots.Rolling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]



lemma normals_bound {U : Set E} {p q n m : E} {r : ℝ} (hr : 0 < r)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hip : ball (p-r•n) r ⊆ U) (hop : ball (p+r•n) r ⊆ Uᶜ)
    (hiq : ball (q-r•m) r ⊆ U) (hoq : ball (q+r•m) r ⊆ Uᶜ) :
    r*‖n-m‖ ≤ dist p q := by
  have hd₁ : Disjoint (ball (p-r•n) r) (ball (q+r•m) r) :=
    disjoint_left.mpr (fun x h₁ h₂ => hoq h₂ (hip h₁))
  have hd₂ : Disjoint (ball (p+r•n) r) (ball (q-r•m) r) :=
    disjoint_left.mpr (fun x h₁ h₂ => hop h₁ (hiq h₂))
  have h₁ : 2*r ≤ ‖(p-q)-r•(n+m)‖ := by
    have h := (disjoint_ball_ball_iff hr hr).mp hd₁
    simpa only [dist_eq_norm,show (p-r•n)-(q+r•m)=(p-q)-r•(n+m) by module,two_mul] using h
  have h₂ : 2*r ≤ ‖(p-q)+r•(n+m)‖ := by
    have h := (disjoint_ball_ball_iff hr hr).mp hd₂
    simpa only [dist_eq_norm,show (p+r•n)-(q-r•m)=(p-q)+r•(n+m) by module,two_mul] using h
  have h₁sq := (sq_le_sq₀ (by positivity : 0 ≤ 2*r) (norm_nonneg _)).mpr h₁
  have h₂sq := (sq_le_sq₀ (by positivity : 0 ≤ 2*r) (norm_nonneg _)).mpr h₂
  have hp := parallelogram_law_with_norm ℝ (p-q) (r•(n+m))
  have hn' := parallelogram_law_with_norm ℝ n m
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr] at hp
  rw [hn,hm] at hn'
  have hsq : (r*‖n-m‖)^2 ≤ ‖p-q‖^2 := by
    nlinarith only [h₁sq,h₂sq,hp,hn',sq_nonneg r]
  rw [dist_eq_norm]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

lemma interior_centers_bound {U : Set E} {p q n m : E} {r : ℝ} (hr : 0 < r)
    (hn : ‖n‖ = 1) (hm : ‖m‖ = 1)
    (hip : ball (p-r•n) r ⊆ U) (hop : ball (p+r•n) r ⊆ Uᶜ)
    (hiq : ball (q-r•m) r ⊆ U) (hoq : ball (q+r•m) r ⊆ Uᶜ) :
    dist (p-r•n) (q-r•m) ≤ 2*dist p q := by
  have H := normals_bound hr hn hm hip hop hiq hoq
  rw [dist_eq_norm,show (p-r•n)-(q-r•m)=(p-q)-r•(n-m) by module]
  calc
    _ ≤ ‖p-q‖+‖r•(n-m)‖ := norm_sub_le _ _
    _ = dist p q+r*‖n-m‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,dist_eq_norm]
    _ ≤ 2*dist p q := by linarith
end StrictHotSpots.Rolling
end
end RollingBallNormals

section RiemannBoundaryCompatible

noncomputable section


section SmoothBoundaryGeometryCompatibleLayer

open Set Filter Metric
open scoped Topology ContDiff
namespace StrictHotSpots

lemma HasFDerivAt.eventually_lt_along_ray {f : Plane → ℝ} {D : Plane →L[ℝ] ℝ}
    {p v : Plane} (hf : HasFDerivAt f D p) (hv : D v < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (p + t • v) < f p := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hh : HasDerivAt (fun t : ℝ => f (p + t • v)) (D v) 0 := by
    exact (show HasFDerivAt f D (p + (0 : ℝ) • v) by simpa using hf).comp_hasDerivAt 0 hl
  have ht := (HasDerivAt.tendsto_slope_zero_right hh).eventually (gt_mem_nhds hv)
  filter_upwards [ht,self_mem_nhdsWithin] with t ht htp
  simp only [zero_add,zero_smul,add_zero,smul_eq_mul,inv_mul_eq_div] at ht
  have hh : f (p + t • v) - f p < 0 := by
    have := (div_lt_iff₀ htp).mp ht
    simpa only [zero_mul] using this
  exact sub_neg.mp hh

lemma regular_level_uniqueDiffWithinAt {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hρ : DifferentiableAt ℝ ρ p)
    (hD : fderiv ℝ ρ p ≠ 0) (hp : ρ p = 0)
    (hlevel : Ω ∩ U = {x | ρ x < 0} ∩ U) (hpcl : p ∈ closure Ω) :
    UniqueDiffWithinAt ℝ (closure Ω) p := by
  have hopen : IsOpen {v : Plane | fderiv ℝ ρ p v < 0} :=
    isOpen_lt (fderiv ℝ ρ p).continuous continuous_const
  have hne : {v : Plane | fderiv ℝ ρ p v < 0}.Nonempty := by
    have hn : ∃ v, fderiv ℝ ρ p v ≠ 0 := by
      by_contra hh
      apply hD
      ext v
      simpa using not_exists.mp hh v
    obtain ⟨v,hv⟩ := hn
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact ⟨v,hv⟩
    · refine ⟨-v,?_⟩
      change fderiv ℝ ρ p (-v) < 0
      rw [map_neg]
      linarith
  have hsub : {v : Plane | fderiv ℝ ρ p v < 0} ⊆ tangentConeAt ℝ Ω p := by
    intro v hv
    apply mem_tangentConeAt_of_add_smul_mem (c := fun t : ℝ => t)
      (tendsto_id'.mpr (nhdsGT_le_nhdsNE (0 : ℝ)))
    have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
      simpa using tendsto_const_nhds.add ((tendsto_id'.mpr (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
    filter_upwards [HasFDerivAt.eventually_lt_along_ray hρ.hasFDerivAt hv,ht (hU.mem_nhds hpU)] with t hneg htU
    have hh : p + t • v ∈ {x | ρ x < 0} ∩ U := ⟨by change ρ (p + t • v) < 0; simpa only [hp] using hneg,htU⟩
    rw [← hlevel] at hh
    exact hh.1
  have hspan : Submodule.span ℝ (tangentConeAt ℝ Ω p) = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    obtain ⟨v,hv⟩ := hne
    refine ⟨v,?_⟩
    exact interior_mono (hsub.trans Submodule.subset_span) (hopen.interior_eq.symm ▸ hv)
  rw [uniqueDiffWithinAt_iff,tangentConeAt_closure,hspan]
  exact ⟨by simp,subset_closure hpcl⟩

lemma SmoothBoundary.uniqueDiffOn_closure {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (hΩ : IsOpen Ω) : UniqueDiffOn ℝ (closure Ω) := by
  intro p hp
  by_cases hpi : p ∈ Ω
  · exact (hΩ.uniqueDiffOn p hpi).mono subset_closure
  · have hpf : p ∈ frontier Ω := ⟨hp,by simpa only [hΩ.interior_eq] using hpi⟩
    obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hpf
    exact regular_level_uniqueDiffWithinAt hU hpU
      ((hρ p hpU).contDiffAt (hU.mem_nhds hpU) |>.differentiableAt (by simp))
      hD hpρ hlevel hp

lemma SmoothBoundary.exterior_ball_in_neighborhood {Ω B : Set Plane}
    (hs : SmoothBoundary Ω) {p : Plane} (hp : p ∈ frontier Ω)
    (hB : IsOpen B) (hpB : p ∈ B) :
    ∃ a ∈ B, ∃ ε > 0, ball a ε ⊆ Ωᶜ := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hp
  have hdρ : DifferentiableAt ℝ ρ p :=
    ((hρ p hpU).contDiffAt (hU.mem_nhds hpU)).differentiableAt (by simp)
  obtain ⟨v,hv⟩ : ∃ v, 0 < fderiv ℝ ρ p v := by
    have hn : ∃ v, fderiv ℝ ρ p v ≠ 0 := by
      by_contra hh
      apply hD
      ext v
      simpa using not_exists.mp hh v
    obtain ⟨v,hv⟩ := hn
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact ⟨-v,by rw [map_neg]; linarith⟩
    · exact ⟨v,hv⟩
  have hray := HasFDerivAt.eventually_lt_along_ray hdρ.hasFDerivAt.neg
    (show (-fderiv ℝ ρ p) v < 0 by simpa using hv)
  have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
    simpa using tendsto_const_nhds.add ((tendsto_id'.mpr
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
  have hbt : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ B := ht (hB.mem_nhds hpB)
  have hut : ∀ᶠ t in 𝓝[>] (0 : ℝ), p+t•v ∈ U := ht (hU.mem_nhds hpU)
  obtain ⟨t,htρ,htB,htU⟩ := (hray.and (hbt.and hut)).exists
  have htpos : 0 < ρ (p+t•v) := by simpa only [Pi.neg_apply,hpρ,neg_zero,neg_lt_zero] using htρ
  have hopen : IsOpen (U ∩ {x | 0 < ρ x}) :=
    hρ.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨ε,hε,hεS⟩ := Metric.isOpen_iff.mp hopen (p+t•v) ⟨htU,htpos⟩
  refine ⟨p+t•v,htB,ε,hε,?_⟩
  intro y hy hyΩ
  have hyS := hεS hy
  have hy' : y ∈ Ω ∩ U := ⟨hyΩ,hyS.1⟩
  rw [hlevel] at hy'
  exact lt_asymm (show ρ y < 0 from hy'.1) (show 0 < ρ y from hyS.2)

end StrictHotSpots
end SmoothBoundaryGeometryCompatibleLayer


section SmoothRollingBallsCompatibleLayer

open Set Metric Filter
open scoped Topology ContDiff NNReal
namespace StrictHotSpots

lemma boundary_level_zero {Ω U : Set Plane} {ρ : Plane → ℝ} {q : Plane}
    (ho : IsOpen Ω) (hU : IsOpen U) (hq : q ∈ frontier Ω) (hqU : q ∈ U)
    (hc : ContinuousAt ρ q) (hlevel : Ω ∩ U = {x | ρ x < 0} ∩ U) : ρ q = 0 := by
  have hnonneg : 0 ≤ ρ q := by
    by_contra hh
    have hmem : q ∈ Ω ∩ U := hlevel ▸ ⟨lt_of_not_ge hh,hqU⟩
    exact hq.2 (ho.interior_eq.symm ▸ hmem.1)
  apply le_antisymm _ hnonneg
  by_contra hh
  have hp : 0 < ρ q := lt_of_not_ge hh
  have hnh : U ∩ ρ ⁻¹' Ioi 0 ∈ 𝓝 q :=
    inter_mem (hU.mem_nhds hqU) (hc.preimage_mem_nhds (Ioi_mem_nhds hp))
  obtain ⟨x,⟨hxU,hxρ⟩,hxΩ⟩ := mem_closure_iff_nhds.mp hq.1 _ hnh
  have hx : x ∈ {x | ρ x < 0} ∩ U := hlevel ▸ ⟨hxΩ,hxU⟩
  exact lt_asymm (show ρ x < 0 from hx.1) (show 0 < ρ x from hxρ)




lemma SmoothBoundary.local_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) {p : Plane} (hp : p ∈ frontier Ω) :
    ∃ (V : Set Plane), IsOpen V ∧ p ∈ V ∧ ∃ r > 0,
      ∀ q ∈ frontier Ω ∩ V, ∃ n : Plane, ‖n‖ = 1 ∧
        ball (q-r•n) r ⊆ Ω ∧ ball (q+r•n) r ⊆ Ωᶜ := by
  obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hp
  have hc : ContDiffAt ℝ ∞ ρ p := (hρ p hpU).contDiffAt (hU.mem_nhds hpU)
  have hdc : ContDiffAt ℝ 1 (fderiv ℝ ρ) p := hc.fderiv_right (by exact WithTop.coe_le_coe.mpr le_top)
  obtain ⟨K,A,hA,hL⟩ := hdc.exists_lipschitzOnWith
  let a : ℝ := ‖fderiv ℝ ρ p‖/2
  have ha : 0 < a := half_pos (norm_pos_iff.mpr hD)
  have han : a < ‖fderiv ℝ ρ p‖ := by dsimp [a]; linarith [norm_pos_iff.mpr hD]
  have hAn : {x | a < ‖fderiv ℝ ρ x‖} ∈ 𝓝 p :=
    hdc.continuousAt.norm.preimage_mem_nhds (Ioi_mem_nhds han)
  obtain ⟨R,hR,hsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hpU) (inter_mem hA hAn))
  let r : ℝ := min (R/8) (a/(4*((K:ℝ)+1)))
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : 2*r ≤ R/4 := by have := min_le_left (R/8) (a/(4*((K:ℝ)+1))); dsimp [r]; linarith
  have hrK : 2*r*(K:ℝ) ≤ a := by
    have hh : r ≤ a/(4*((K:ℝ)+1)) := min_le_right _ _
    have hc' : 0 < 4*((K:ℝ)+1) := by positivity
    have hh' := (le_div_iff₀ hc').mp hh
    nlinarith [K.coe_nonneg]
  refine ⟨ball p (R/4),isOpen_ball,mem_ball_self (by positivity),r,hr,?_⟩
  intro q hq
  have hqR : q ∈ ball p R := ball_subset_ball (by linarith : R/4 ≤ R) hq.2
  have hqU := (hsub hqR).1
  have hqρ : ρ q = 0 := boundary_level_zero ho hU hq.1 hqU
    ((hρ q hqU).contDiffAt (hU.mem_nhds hqU)).continuousAt hlevel
  let g := gradient ρ q
  have hg : ‖g‖ = ‖fderiv ℝ ρ q‖ := by simp [g,gradient]
  have hga : a < ‖g‖ := by rw [hg]; exact (hsub hqR).2.2
  have hgpos : 0 < ‖g‖ := ha.trans hga
  let n : Plane := ‖g‖⁻¹ • g
  have hn : ‖n‖ = 1 := by simp [n,norm_smul,ne_of_gt hgpos]
  have hDq (v : Plane) : fderiv ℝ ρ q v = ‖g‖*inner ℝ n v := by
    rw [show n = ‖g‖⁻¹ • g from rfl,real_inner_smul_left,
      ← mul_assoc,mul_inv_cancel₀ hgpos.ne',one_mul]
    exact inner_gradient_left.symm
  have hball : ball q (2*r) ⊆ ball p R := by
    intro x hx
    calc
      dist x p ≤ dist x q + dist q p := dist_triangle _ _ _
      _ < 2*r+R/4 := add_lt_add hx hq.2
      _ < R := by linarith
  have hT (x : Plane) (hx : x ∈ ball p R) :
      ‖ρ x-ρ q-fderiv ℝ ρ q (x-q)‖ ≤ (K:ℝ)*‖x-q‖^2 :=
    Rolling.taylor_quadratic (convex_ball p R)
      (fun y hy => ((hρ y (hsub hy).1).contDiffAt
        (hU.mem_nhds (hsub hy).1)).differentiableAt (by simp))
      (hL.mono (fun _ hy => (hsub hy).2.1)) hqR hx
  obtain ⟨hin,hout⟩ := Rolling.balls_of_taylor hn hgpos hr
    (hrK.trans hga.le) hqρ hDq hball hT
  refine ⟨n,hn,?_,?_⟩
  · intro x hx
    have hxR : x ∈ ball p R := hball (by
      have hh : dist x q < 2*r := by
        have hd : dist (q-r•n) q = r := by
          simp [norm_smul,hn,abs_of_pos hr]
        calc
          dist x q ≤ dist x (q-r•n)+dist (q-r•n) q := dist_triangle _ _ _
          _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
          _ = 2*r := by ring
      exact hh)
    have hh : x ∈ Ω ∩ U := hlevel ▸ ⟨hin hx,(hsub hxR).1⟩
    exact hh.1
  · intro x hx hxΩ
    have hxU : x ∈ U := (hsub (hball (by
      have hd : dist (q+r•n) q = r := by
        simp [dist_eq_norm,norm_smul,hn,abs_of_pos hr]
      calc
        dist x q ≤ dist x (q+r•n)+dist (q+r•n) q := dist_triangle _ _ _
        _ < r+r := add_lt_add_of_lt_of_le hx (le_of_eq hd)
        _ = 2*r := by ring))).1
    have hh : x ∈ {x | ρ x < 0} ∩ U := hlevel ▸ ⟨hxΩ,hxU⟩
    exact lt_asymm (show 0 < ρ x from hout hx) (show ρ x < 0 from hh.1)

end StrictHotSpots
end SmoothRollingBallsCompatibleLayer


section UniformRollingBallsCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots

lemma finite_positive_lower {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 < f a) : ∃ r > 0, ∀ a ∈ s, r ≤ f a := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert a s hmem ih =>
    obtain ⟨r,hr,hR⟩ := ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
    refine ⟨min r (f a),lt_min hr (hf a (Finset.mem_insert_self _ _)),?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hR b hb)




theorem SmoothBoundary.uniform_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ r > 0, ∀ p ∈ frontier Ω, ∃ n : Plane, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ Ω ∧ ball (p+r•n) r ⊆ Ωᶜ := by
  classical
  have hlocal (p : frontier Ω) := hs.local_rolling_balls ho p.property
  choose V hVo hpV r hr hballs using hlocal
  have hc : IsCompact (frontier Ω) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hcover : frontier Ω ⊆ ⋃ p : frontier Ω, V p := by
    intro p hp
    exact mem_iUnion.mpr ⟨⟨p,hp⟩,hpV ⟨p,hp⟩⟩
  obtain ⟨s,hcov⟩ := hc.elim_finite_subcover V hVo hcover
  obtain ⟨R,hR,hRs⟩ := finite_positive_lower s r (fun p _ => hr p)
  refine ⟨R,hR,?_⟩
  intro p hp
  obtain ⟨q,hq⟩ := mem_iUnion.mp (hcov hp)
  obtain ⟨hqs,hpV⟩ := mem_iUnion.mp hq
  obtain ⟨n,hn,hin,hout⟩ := hballs q p ⟨hp,hpV⟩
  refine ⟨n,hn,?_,?_⟩
  · have hmono := Rolling.tangent_ball_mono (p := p) (n := -n)
      (by simpa only [norm_neg] using hn) (hRs q hqs)
    have hmono' : ball (p-R•n) R ⊆ ball (p-r q•n) (r q) := by
      simpa only [smul_neg,← sub_eq_add_neg] using hmono
    exact hmono'.trans hin
  · exact (Rolling.tangent_ball_mono hn (hRs q hqs)).trans hout

end StrictHotSpots
end UniformRollingBallsCompatibleLayer


section RiemannBoundaryGeometryCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots


theorem SmoothBoundary.complex_rolling_balls {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) :
    ∃ r > 0, ∀ p ∈ frontier (Conformal.coordinate ⁻¹' Ω), ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ Conformal.coordinate ⁻¹' Ω ∧
      ball (p+r•n) r ⊆ (Conformal.coordinate ⁻¹' Ω)ᶜ := by
  obtain ⟨r,hr,hR⟩ := hs.uniform_rolling_balls ho hb
  refine ⟨r,hr,?_⟩
  intro p hp
  have hp' : Conformal.coordinate p ∈ frontier Ω := by
    change p ∈ Conformal.coordinate.toHomeomorph ⁻¹' frontier Ω
    rw [Conformal.coordinate.toHomeomorph.preimage_frontier]
    exact hp
  obtain ⟨n,hn,hin,hout⟩ := hR _ hp'
  refine ⟨Conformal.coordinate.symm n,by simpa using hn,?_,?_⟩
  · intro x hx
    apply hin
    simpa only [mem_ball,← Conformal.coordinate.dist_map x (p-r•Conformal.coordinate.symm n),
      map_sub,map_smul,LinearIsometryEquiv.apply_symm_apply] using hx
  · intro x hx
    apply hout
    simpa only [mem_ball,← Conformal.coordinate.dist_map x (p+r•Conformal.coordinate.symm n),
      map_add,map_smul,LinearIsometryEquiv.apply_symm_apply] using hx

namespace Riemann
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma boundary_distance_pos {U : Set E} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {x : E} (hx : x ∈ U) : 0 < infDist x Uᶜ := by
  apply (infDist_pos_iff_notMem_closure hc).mp
  rwa [ho.isClosed_compl.closure_eq,mem_compl_iff,not_not]



lemma nearest_frontier {U : Set E} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {x : E} (hx : x ∈ U) :
    ∃ p ∈ frontier U, dist x p = infDist x Uᶜ ∧ x ≠ p ∧
      ball x (dist x p) ⊆ U := by
  obtain ⟨p,hp,he⟩ := ho.isClosed_compl.exists_infDist_eq_dist hc x
  have hδ := boundary_distance_pos ho hc hx
  have hball : ball x (dist x p) ⊆ U := by
    rw [← he]
    exact ball_infDist_compl_subset
  have hpcl : p ∈ closure U := by
    have hpc : p ∈ closedBall x (dist x p) := by simp [dist_comm]
    rw [← closure_ball x (by linarith : dist x p ≠ 0)] at hpc
    exact closure_mono hball hpc
  refine ⟨p,?_,he.symm,?_,hball⟩
  · rw [frontier_eq_closure_inter_closure,ho.isClosed_compl.closure_eq]
    exact ⟨hpcl,hp⟩
  · exact dist_ne_zero.mp (by linarith)

omit [NormedSpace ℝ E] in


lemma compact_core {U : Set E} (hb : Bornology.IsBounded U) {r : ℝ} (hr : 0 < r) :
    IsCompact {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} ∧
      {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} ⊆ U := by
  have hclosed : IsClosed {x : E | r ≤ infDist x Uᶜ} :=
    isClosed_le continuous_const (continuous_infDist_pt Uᶜ)
  refine ⟨hb.isCompact_closure.inter_right hclosed,?_⟩
  intro x hx
  by_contra hnot
  have hz : infDist x Uᶜ = 0 := infDist_zero_of_mem hnot
  linarith [hx.2]

end Riemann
end StrictHotSpots
end RiemannBoundaryGeometryCompatibleLayer


section RiemannBoundaryDistanceCompatibleLayer
open Set Metric Filter
open scoped Topology
namespace StrictHotSpots.Riemann

lemma compact_disk_separation {U K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : ContinuousOn f U) (hm : MapsTo f U (ball 0 1)) :
    ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ x ∈ K, ‖f x‖ ≤ m := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0,le_rfl,by norm_num,by simp⟩
  obtain ⟨a,ha,hmax⟩ := hK.exists_isMaxOn hne (hf.norm.mono hKU)
  exact ⟨‖f a‖,norm_nonneg _,mem_ball_zero_iff.mp (hm (hKU ha)),hmax⟩

lemma core_of_ball_subset {U : Set ℂ} (hc : Uᶜ.Nonempty) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hin : ball c r ⊆ U) :
    c ∈ {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ} := by
  refine ⟨subset_closure (hin (mem_ball_self hr)),(le_infDist hc).mpr ?_⟩
  intro y hy
  by_contra h
  exact hy (hin (by simpa only [mem_ball,dist_comm] using lt_of_not_ge h))




theorem domain_distance_le_disk_distance {U : Set ℂ} (ho : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier U, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ U ∧ ball (p+r•n) r ⊆ Uᶜ)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f U) (hm : MapsTo f U (ball 0 1)) :
    ∃ C > 0, ∀ x ∈ U, infDist x Uᶜ ≤ C*(1-‖f x‖) := by
  let K : Set ℂ := {x | x ∈ closure U ∧ r ≤ infDist x Uᶜ}
  have hK := compact_core hb hr
  obtain ⟨m,hm0,hm1,hfm⟩ := compact_disk_separation hK.1 hK.2 hd.continuousOn hm
  obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (continuous_infDist_pt Uᶜ)).bddAbove
  let C := max (2*r/(1-m)^2) ((|M|+1)/(1-m))
  have hp : 0 < 1-m := sub_pos.mpr hm1
  have hpp : 0 < (1-m)^2 := sq_pos_of_pos hp
  have hC : 0 < C := lt_of_lt_of_le (by positivity : 0 < 2*r/(1-m)^2) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro x hx
  have hfx : 0 < 1-‖f x‖ := sub_pos.mpr (mem_ball_zero_iff.mp (hm hx))
  by_cases hnear : infDist x Uᶜ < r
  · obtain ⟨p,hpfr,hpd,hxp,hball⟩ := nearest_frontier ho hc hx
    obtain ⟨n,hn,hin,hout⟩ := hroll p hpfr
    obtain ⟨hdist,hxin⟩ := Rolling.near_interior_ball hn hr hxp hball hout (by rwa [hpd])
    have hcenter : p-r•n ∈ K := core_of_ball_subset hc hr hin
    have hh := disk_distance_from_interior_ball (hd.mono hin) (hm.mono_left hin)
      hxin hm1 (hfm _ hcenter)
    rw [hdist] at hh
    have hh' : infDist x Uᶜ ≤ (2*r/(1-m)^2)*(1-‖f x‖) := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hpp).mpr
      nlinarith only [hh,hpd]
    exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hfx.le)
  · have hxK : x ∈ K := ⟨subset_closure hx,le_of_not_gt hnear⟩
    have hnorm := hfm x hxK
    have hxm : infDist x Uᶜ ≤ M := hM ⟨x,subset_closure hx,rfl⟩
    have hxm' : infDist x Uᶜ ≤ |M|+1 := hxm.trans (by linarith [le_abs_self M])
    have hh : infDist x Uᶜ ≤ ((|M|+1)/(1-m))*(1-‖f x‖) := by
      calc
        _ ≤ |M|+1 := hxm'
        _ = ((|M|+1)/(1-m))*(1-m) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hfx.le)

end StrictHotSpots.Riemann
end RiemannBoundaryDistanceCompatibleLayer


section RiemannDerivativeBoundCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology
namespace StrictHotSpots.Riemann

lemma exterior_ball_distance {U : Set ℂ} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r) {b y : ℂ} (hout : ball b r ⊆ Uᶜ) (hy : y ∈ U) :
    r+infDist y Uᶜ ≤ dist y b := by
  have hδ := boundary_distance_pos ho hc hy
  have hdisj : Disjoint (ball y (infDist y Uᶜ)) (ball b r) := by
    refine disjoint_left.mpr (fun a ha ha' => ?_)
    exact hout ha' (ball_infDist_compl_subset ha)
  simpa only [add_comm] using (disjoint_ball_ball_iff hδ hr).mp hdisj


theorem schwarz_exterior_ball {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F (ball 0 1))
    {b : ℂ} {r : ℝ} (hr : 0 < r)
    (hout : ∀ z ∈ ball (0:ℂ) 1, r < dist (F z) b)
    {z : ℂ} (hz : z ∈ ball (0:ℂ) 1) :
    r*‖deriv F z‖*(1-‖z‖^2) ≤ dist (F z) b ^2-r^2 := by
  let f : ℂ → ℂ := fun w => (r:ℂ)/(F w-b)
  have hne (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) : F w-b ≠ 0 := by
    apply norm_ne_zero_iff.mp
    have hh := hout w hw
    rw [dist_eq_norm] at hh
    linarith
  have hf (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) :
      HasDerivAt f (-(r:ℂ)*deriv F w/(F w-b)^2) w := by
    simpa only [f,zero_mul,zero_sub,neg_mul] using
      (hasDerivAt_const w (r:ℂ)).fun_div
        (((hd w hw).differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt.sub_const b) (hne w hw)
  have hm : MapsTo f (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff]
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le]
    exact (div_lt_one (by simpa only [dist_eq_norm] using hr.trans (hout w hw))).mpr
      (by simpa only [dist_eq_norm] using hout w hw)
  have hh := schwarz_pick_deriv (fun w hw => (hf w hw).differentiableAt.differentiableWithinAt) hm hz
  rw [(hf z hz).deriv,norm_div,norm_mul,norm_neg,norm_real,Real.norm_of_nonneg hr.le,
    norm_pow] at hh
  have he : ‖f z‖ = r/dist (F z) b := by
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le,dist_eq_norm]
  rw [he,← dist_eq_norm,div_pow] at hh
  have hp : 0 < dist (F z) b ^2 := sq_pos_of_pos (hr.trans (hout z hz))
  have hh' := mul_le_mul_of_nonneg_right hh hp.le
  have hc₁ : (r*‖deriv F z‖/dist (F z) b ^2*(1-‖z‖^2))*dist (F z) b ^2 =
      r*‖deriv F z‖*(1-‖z‖^2) := by field_simp [(hr.trans (hout z hz)).ne']
  have hc₂ : (1-r^2/dist (F z) b ^2)*dist (F z) b ^2 = dist (F z) b ^2-r^2 := by field_simp [(hr.trans (hout z hz)).ne']
  rwa [hc₁,hc₂] at hh'



theorem bounded_deriv_of_rolling_balls (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1)
    (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hb : Bornology.IsBounded e.target)
    (hc : e.targetᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ B > 0, ∀ z ∈ ball (0:ℂ) 1, ‖deriv e z‖ ≤ B := by
  have hmi : MapsTo e.symm e.target (ball 0 1) := by simpa only [← hes] using e.mapsTo_symm
  obtain ⟨C,hC,hδ⟩ := domain_distance_le_disk_distance e.open_target hb hc hr hroll hdi hmi
  obtain ⟨M,hM⟩ := (hb.isCompact_closure.image (continuous_infDist_pt e.targetᶜ)).bddAbove
  let L := 2*r+|M|+1
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨C*L/r,by positivity,?_⟩
  intro z hz
  have hzs : z ∈ e.source := hes.symm ▸ hz
  have hx : e z ∈ e.target := e.map_source hzs
  have hδz : infDist (e z) e.targetᶜ ≤ C*(1-‖z‖) := by
    simpa only [e.left_inv hzs] using hδ (e z) hx
  have hδM : infDist (e z) e.targetᶜ ≤ M := hM ⟨e z,subset_closure hx,rfl⟩
  obtain ⟨p,hp,hpd,hxp,hball⟩ := nearest_frontier e.open_target hc hx
  obtain ⟨n,hn,hin,hout⟩ := hroll p hp
  have hnormal := Rolling.nearest_normal_of_balls hn hr hxp hball hout
  have hdist : dist (e z) (p+r•n) = r+infDist (e z) e.targetᶜ := by
    rw [dist_eq_norm,show e z-(p+r•n) = -(r+dist (e z) p)•n by
      calc
        _ = (p-dist (e z) p•n)-(p+r•n) := congrArg (fun a => a-(p+r•n)) hnormal
        _ = _ := by module,
      norm_smul,hn,mul_one,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity),hpd]
  have hbound := schwarz_exterior_ball hd hr (fun w hw =>
    lt_of_lt_of_le (by linarith [boundary_distance_pos e.open_target hc (e.map_source (hes.symm ▸ hw))] :
        r < r+infDist (e w) e.targetᶜ)
      (exterior_ball_distance e.open_target hc hr hout (e.map_source (hes.symm ▸ hw)))) hz
  rw [hdist] at hbound
  have hleft : r*‖deriv e z‖*(1-‖z‖) ≤ r*‖deriv e z‖*(1-‖z‖^2) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hz' := mem_ball_zero_iff.mp hz
    nlinarith [norm_nonneg z]
  have hright : (r+infDist (e z) e.targetᶜ)^2-r^2 ≤ L*(C*(1-‖z‖)) := by
    calc
      _ = (2*r+infDist (e z) e.targetᶜ)*infDist (e z) e.targetᶜ := by ring
      _ ≤ L*(C*(1-‖z‖)) := mul_le_mul (by dsimp [L]; linarith [le_abs_self M]) hδz
        infDist_nonneg hL.le
  have hzz : 0 < 1-‖z‖ := sub_pos.mpr (mem_ball_zero_iff.mp hz)
  have hh : r*‖deriv e z‖ ≤ L*C := (mul_le_mul_iff_left₀ hzz).mp (by
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hleft.trans (hbound.trans hright))
  apply (le_div_iff₀ hr).mpr
  nlinarith only [hh]

end StrictHotSpots.Riemann
end RiemannDerivativeBoundCompatibleLayer


section RiemannInverseBoundCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Riemann

lemma schwarz_pick_center {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (ball c r)) (hm : MapsTo f (ball c r) (ball 0 1)) :
    r*‖deriv f c‖ ≤ 1-‖f c‖^2 := by
  have hc : c ∈ ball c r := mem_ball_self hr
  have hfc : ‖f c‖ < 1 := mem_ball_zero_iff.mp (hm hc)
  let g := fun y => mobius (f c) (f y)
  have hg0 : g c = 0 := mobius_self _
  have hgd : DifferentiableOn ℂ g (ball c r) := by
    intro y hy
    exact ((hasDerivAt_mobius hfc (mem_ball_zero_iff.mp (hm hy))).differentiableAt.comp y
      ((hd y hy).differentiableAt (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hgm : MapsTo g (ball c r) (closedBall (g c) 1) := by
    intro y hy
    rw [hg0,mem_closedBall_zero_iff]
    exact (norm_mobius_lt hfc (mem_ball_zero_iff.mp (hm hy))).le
  have hle := Complex.norm_deriv_le_div_of_mapsTo_ball hgd hgm hr
  have hder := (hasDerivAt_mobius hfc hfc).comp c
    ((hd c hc).differentiableAt (isOpen_ball.mem_nhds hc)).hasDerivAt
  change HasDerivAt g (((1-conj (f c)*f c)/(1-conj (f c)*f c)^2)*deriv f c) c at hder
  rw [hder.deriv,norm_mul,norm_mobius_self_deriv hfc] at hle
  have hpos : 0 < 1-‖f c‖^2 := by nlinarith [norm_nonneg (f c)]
  have hh : ‖deriv f c‖/(1-‖f c‖^2) ≤ 1/r := by simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul] using hle
  have hh' := (div_le_div_iff₀ hpos hr).mp hh
  nlinarith only [hh']



theorem disk_distance_le_domain_distance (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hc : e.targetᶜ.Nonempty) {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ A > 0, ∀ z ∈ ball (0:ℂ) 1, 1-‖z‖ ≤ A*infDist (e z) e.targetᶜ := by
  have h0 : (0:ℂ) ∈ e.source := by rw [hes]; exact mem_ball_self (by norm_num)
  have hδ0 := boundary_distance_pos e.open_target hc (e.map_source h0)
  let m := r/(r+infDist (e 0) e.targetᶜ)
  have hm : m < 1 := (div_lt_one (by positivity)).mpr (by linarith only [hδ0])
  have hpos : 0 < (1-m)^2 := sq_pos_of_pos (sub_pos.mpr hm)
  refine ⟨2/(r*(1-m)^2),by positivity,?_⟩
  intro z hz
  have hzs : z ∈ e.source := hes.symm ▸ hz
  have hx := e.map_source hzs
  have hδ := boundary_distance_pos e.open_target hc hx
  obtain ⟨p,hp,hpd,hxp,hball⟩ := nearest_frontier e.open_target hc hx
  obtain ⟨n,hn,hin,hout⟩ := hroll p hp
  let b := p+r•n
  have hnormal := Rolling.nearest_normal_of_balls hn hr hxp hball hout
  have hdist : dist (e z) b = r+infDist (e z) e.targetᶜ := by
    rw [dist_eq_norm,show e z-b = -(r+dist (e z) p)•n by
      calc
        _ = (p-dist (e z) p•n)-(p+r•n) := congrArg (fun a => a-(p+r•n)) hnormal
        _ = _ := by module,
      norm_smul,hn,mul_one,Real.norm_eq_abs,abs_neg,abs_of_pos (by positivity),hpd]
  have hsep (w : ℂ) (hw : w ∈ ball (0:ℂ) 1) : r < dist (e w) b := by
    have hδw := boundary_distance_pos e.open_target hc (e.map_source (hes.symm ▸ hw))
    exact lt_of_lt_of_le (by linarith) (exterior_ball_distance e.open_target hc hr hout
      (e.map_source (hes.symm ▸ hw)))
  let f := fun w : ℂ => (r:ℂ)/(e w-b)
  have hf : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    apply DifferentiableWithinAt.fun_div (differentiableWithinAt_const (r:ℂ)) ((hd w hw).sub_const b)
    apply norm_ne_zero_iff.mp
    have h := hr.trans (hsep w hw)
    simpa only [dist_eq_norm] using h.ne'
  have hnorm (w : ℂ) : ‖f w‖ = r/dist (e w) b := by
    dsimp [f]
    rw [norm_div,norm_real,Real.norm_of_nonneg hr.le,dist_eq_norm]
  have hfm : MapsTo f (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [mem_ball_zero_iff,hnorm]
    exact (div_lt_one (hr.trans (hsep w hw))).mpr (hsep w hw)
  have hfc : ‖f 0‖ ≤ m := by
    rw [hnorm]
    exact div_le_div_of_nonneg_left hr.le (by positivity)
      (exterior_ball_distance e.open_target hc hr hout (e.map_source h0))
  have hh := disk_distance_from_interior_ball hf hfm hz hm hfc
  rw [dist_zero_right,hnorm,hdist] at hh
  have hright : r*(1-r/(r+infDist (e z) e.targetᶜ)) ≤ infDist (e z) e.targetᶜ := by
    have hsum : 0 < r+infDist (e z) e.targetᶜ := by positivity
    apply (mul_le_mul_iff_left₀ hsum).mp
    field_simp
    nlinarith [sq_nonneg (infDist (e z) e.targetᶜ)]
  have hh' := mul_le_mul_of_nonneg_left hh hr.le
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos hr hpos)).mpr
  nlinarith only [hh',hright]



theorem bounded_inverse_deriv_of_rolling_balls (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hc : e.targetᶜ.Nonempty) {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ B > 0, ∀ x ∈ e.target, ‖deriv e.symm x‖ ≤ B := by
  obtain ⟨A,hA,hδ⟩ := disk_distance_le_domain_distance e hes hd hc hr hroll
  refine ⟨2*A,by positivity,?_⟩
  intro x hx
  have hδx := boundary_distance_pos e.open_target hc hx
  have hin : ball x (infDist x e.targetᶜ) ⊆ e.target := ball_infDist_compl_subset
  have hmi : MapsTo e.symm e.target (ball 0 1) := by
    simpa only [← hes] using e.mapsTo_symm
  have hh := schwarz_pick_center hδx (hdi.mono hin) (hmi.mono_left hin)
  have hz : e.symm x ∈ ball (0:ℂ) 1 := hmi hx
  have H : 1-‖e.symm x‖ ≤ A*infDist x e.targetᶜ := by
    simpa only [e.right_inv hx] using hδ (e.symm x) hz
  have H' : 1-‖e.symm x‖^2 ≤ 2*(A*infDist x e.targetᶜ) := by
    have hsq := sq_nonneg (1-‖e.symm x‖)
    nlinarith only [hsq,H]
  exact (mul_le_mul_iff_right₀ hδx).mp (by
    simpa only [mul_comm,mul_left_comm,mul_assoc] using hh.trans H')

end StrictHotSpots.Riemann
end RiemannInverseBoundCompatibleLayer


section RiemannClosedExtensionCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann

lemma complex_lipschitz_extension {f : ℂ → ℂ} {U : Set ℂ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f U) :
    ∃ (F : ℂ → ℂ) (B : ℝ≥0), LipschitzWith B F ∧ EqOn f F U := by
  obtain ⟨a,ha,hea⟩ := (Complex.reCLM.lipschitzWith.comp_lipschitzOnWith hf).extend_real
  obtain ⟨b,hb,heb⟩ := (Complex.imCLM.lipschitzWith.comp_lipschitzOnWith hf).extend_real
  let F : ℂ → ℂ := fun z => (a z:ℂ)+(b z:ℂ)*I
  refine ⟨F,‖Complex.reCLM‖₊*K+‖Complex.imCLM‖₊*K,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h₁ := ha.dist_le_mul x y
    have h₂ := hb.dist_le_mul x y
    have hh := norm_le_abs_re_add_abs_im (F x-F y)
    have hre : |(F x-F y).re| = dist (a x) (a y) := by simp [F,Real.dist_eq]
    have him : |(F x-F y).im| = dist (b x) (b y) := by simp [F,Real.dist_eq]
    rw [hre,him] at hh
    simpa only [dist_eq_norm,NNReal.coe_add,NNReal.coe_mul,add_mul,mul_assoc] using
      hh.trans (add_le_add h₁ h₂)
  · intro x hx
    apply Complex.ext
    · simpa [F] using hea hx
    · simpa [F] using heb hx



theorem closed_disk_extension (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ z ∈ ball (0:ℂ) 1, ‖deriv e z‖ ≤ B) :
    ∃ (F : ℂ → ℂ) (L : ℝ≥0), LipschitzWith L F ∧ EqOn e F (ball 0 1) ∧
      F '' closedBall 0 1 = closure e.target := by
  have hLip : LipschitzOnWith ⟨B,hB⟩ e (ball 0 1) :=
    (convex_ball (0:ℂ) 1).lipschitzOnWith_of_nnnorm_deriv_le
      (fun z hz => (hd z hz).differentiableAt (isOpen_ball.mem_nhds hz)) hbound
  obtain ⟨F,L,hF,he⟩ := complex_lipschitz_extension hLip
  have him : F '' ball (0:ℂ) 1 = e.target := by
    calc
      F '' ball (0:ℂ) 1 = e '' ball (0:ℂ) 1 := image_congr he.symm
      _ = e.target := by rw [← hes,e.image_source_eq_target]
  refine ⟨F,L,hF,he,?_⟩
  apply Subset.antisymm
  · rw [← closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)]
    simpa only [him] using image_closure_subset_closure_image (s := ball (0:ℂ) 1) hF.continuous
  · have hclosed : IsClosed (F '' closedBall (0:ℂ) 1) :=
      ((isCompact_closedBall (0:ℂ) 1).image hF.continuous).isClosed
    apply closure_minimal _ hclosed
    rw [← him]
    exact image_mono ball_subset_closedBall

end StrictHotSpots.Riemann
end RiemannClosedExtensionCompatibleLayer


section RiemannGlobalInverseCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann

lemma dist_image_le_on_ball {U : Set ℂ} (ho : IsOpen U) {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f U) {B : ℝ} (hB : ∀ z ∈ U, ‖deriv f z‖ ≤ B)
    {c : ℂ} {r : ℝ} (hin : ball c r ⊆ U) {x y : ℂ}
    (hx : x ∈ ball c r) (hy : y ∈ ball c r) :
    dist (f x) (f y) ≤ B*dist x y := by
  simpa only [dist_eq_norm] using (convex_ball c r).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hd z (hin hz)).differentiableAt (ho.mem_nhds (hin hz)))
    (fun z hz => hB z (hin hz)) hy hx




theorem lipschitz_of_rolling_balls {U : Set ℂ} (ho : IsOpen U) (hc : Uᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier U, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ U ∧ ball (p+r•n) r ⊆ Uᶜ)
    {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f U)
    (hm : MapsTo f U (ball 0 1)) {B : ℝ} (hB : 0 < B)
    (hbound : ∀ x ∈ U, ‖deriv f x‖ ≤ B) :
    ∃ L : ℝ≥0, LipschitzOnWith L f U := by
  let L : ℝ := 40*B+40/r
  have hL : 0 < L := by dsimp [L]; positivity
  refine ⟨⟨L,hL.le⟩,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  change dist (f x) (f y) ≤ L*dist x y
  have hδx := boundary_distance_pos ho hc hx
  have hδy := boundary_distance_pos ho hc hy
  have hLB : B ≤ L := by
    dsimp [L]
    have := div_pos (by norm_num : (0:ℝ)<40) hr
    linarith
  by_cases hdirect : dist x y < infDist x Uᶜ
  · have hh := dist_image_le_on_ball ho hd hbound (ball_infDist_compl_subset (s := U) (x := x))
      (mem_ball_self hδx) (by simpa only [mem_ball,dist_comm] using hdirect)
    exact hh.trans (mul_le_mul_of_nonneg_right hLB dist_nonneg)
  by_cases hnear : dist x y < r/10
  · let d := dist x y
    have hd0 : 0 < d := hδx.trans_le (le_of_not_gt hdirect)
    have hdx : infDist x Uᶜ ≤ d := le_of_not_gt hdirect
    have hdy : infDist y Uᶜ ≤ 2*d := by
      have hh : infDist y Uᶜ ≤ infDist x Uᶜ+dist y x := infDist_le_infDist_add_dist
      rw [dist_comm y x] at hh
      linarith
    obtain ⟨p,hp,hpx,hxp,hballx⟩ := nearest_frontier ho hc hx
    obtain ⟨q,hq,hqy,hyq,hbally⟩ := nearest_frontier ho hc hy
    obtain ⟨n,hn,hip,hop⟩ := hroll p hp
    obtain ⟨m,hnm,hiq,hoq⟩ := hroll q hq
    have hxpball : x ∈ ball (p-r•n) r :=
      (Rolling.near_interior_ball hn hr hxp hballx hop (by rw [hpx]; dsimp [d] at hdx; linarith)).2
    have hyqball : y ∈ ball (q-r•m) r :=
      (Rolling.near_interior_ball hnm hr hyq hbally hoq (by rw [hqy]; dsimp [d] at hdy; linarith)).2
    have hpq : dist p q ≤ 4*d := by
      have hh := dist_triangle4 p x y q
      rw [dist_comm p x,hpx,hqy] at hh
      dsimp [d] at *
      linarith
    have hcc : dist (p-r•n) (q-r•m) ≤ 8*d :=
      (Rolling.interior_centers_bound hr hn hnm hip hop hiq hoq).trans (by linarith)
    let a := p-(9*d)•n
    have ht : 9*d < r := by dsimp [d]; linarith
    have hap : dist a p = 9*d := by
      simp [a,hn,abs_of_pos hd0]
    have hac : dist a (p-r•n) = r-9*d := by
      rw [dist_eq_norm,show a-(p-r•n)=(r-9*d)•n by
        dsimp only [a]
        rw [sub_smul]
        abel,
        norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr ht)]
    have ha₁ : a ∈ ball (p-r•n) r := by rw [mem_ball,hac]; linarith
    have ha₂ : a ∈ ball (q-r•m) r := by
      have hh := dist_triangle a (p-r•n) (q-r•m)
      rw [hac] at hh
      change dist a (q-r•m) < r
      linarith
    have hxa : dist x a ≤ 10*d := by
      have hh := dist_triangle x p a
      rw [hpx,dist_comm p a,hap] at hh
      linarith
    have hay : dist a y ≤ 11*d := by
      have hh := dist_triangle a x y
      rw [dist_comm a x] at hh
      dsimp [d] at *
      linarith
    have h₁ := dist_image_le_on_ball ho hd hbound hip hxpball ha₁
    have h₂ := dist_image_le_on_ball ho hd hbound hiq ha₂ hyqball
    calc
      _ ≤ dist (f x) (f a)+dist (f a) (f y) := dist_triangle _ _ _
      _ ≤ B*(dist x a+dist a y) := by nlinarith only [h₁,h₂]
      _ ≤ B*(21*d) := mul_le_mul_of_nonneg_left (by linarith) hB.le
      _ ≤ L*d := by dsimp [L]; nlinarith [div_pos (by norm_num : (0:ℝ)<40) hr]
  · have hfar : r/10 ≤ dist x y := le_of_not_gt hnear
    have hdist : dist (f x) (f y) ≤ 2 := by
      have hh := dist_triangle (f x) 0 (f y)
      rw [dist_zero_right,dist_zero_left] at hh
      linarith [mem_ball_zero_iff.mp (hm hx),mem_ball_zero_iff.mp (hm hy)]
    apply hdist.trans
    have hpos := div_mul_cancel₀ (40:ℝ) hr.ne'
    have hh := mul_le_mul_of_nonneg_left hfar (show 0 ≤ 40/r by positivity)
    dsimp [L]
    nlinarith [mul_nonneg hB.le (dist_nonneg (x:=x) (y:=y))]

end StrictHotSpots.Riemann
end RiemannGlobalInverseCompatibleLayer


section RiemannClosedBiholomorphicCompatibleLayer
open Set Metric Filter _root_.Complex _root_.OAI.Complex
open scoped Topology NNReal
namespace StrictHotSpots.Riemann



theorem closed_bilipschitz_extension (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (hd : DifferentiableOn ℂ e (ball 0 1))
    (hdi : DifferentiableOn ℂ e.symm e.target)
    (hb : Bornology.IsBounded e.target) (hc : e.targetᶜ.Nonempty)
    {r : ℝ} (hr : 0 < r)
    (hroll : ∀ p ∈ frontier e.target, ∃ n : ℂ, ‖n‖ = 1 ∧
      ball (p-r•n) r ⊆ e.target ∧ ball (p+r•n) r ⊆ e.targetᶜ) :
    ∃ (F G : ℂ → ℂ) (L M : ℝ≥0),
      LipschitzWith L F ∧ LipschitzWith M G ∧
      EqOn e F (ball 0 1) ∧ EqOn e.symm G e.target ∧
      F '' closedBall 0 1 = closure e.target ∧
      G '' closure e.target = closedBall 0 1 ∧
      (∀ z ∈ closedBall 0 1, G (F z) = z) ∧
      (∀ x ∈ closure e.target, F (G x) = x) := by
  obtain ⟨B,hB,hbound⟩ := bounded_deriv_of_rolling_balls e hes hd hdi hb hc hr hroll
  obtain ⟨F,L,hF,he,himage⟩ := closed_disk_extension e hes hd hB.le hbound
  obtain ⟨C,hC,hcbound⟩ := bounded_inverse_deriv_of_rolling_balls e hes hd hdi hc hr hroll
  have hmi : MapsTo e.symm e.target (ball 0 1) := by simpa only [← hes] using e.mapsTo_symm
  obtain ⟨K,hK⟩ := lipschitz_of_rolling_balls e.open_target hc hr hroll hdi hmi hC hcbound
  obtain ⟨G,M,hG,hi⟩ := complex_lipschitz_extension hK
  have hleft₀ : EqOn (G ∘ F) id (ball (0:ℂ) 1) := by
    intro z hz
    change G (F z) = z
    rw [← he hz,← hi (e.map_source (hes.symm ▸ hz)),e.left_inv (hes.symm ▸ hz)]
  have hleft : ∀ z ∈ closedBall (0:ℂ) 1, G (F z) = z := by
    have hh := hleft₀.closure (hG.continuous.comp hF.continuous) continuous_id
    rwa [closure_ball (0:ℂ) (by norm_num : (1:ℝ) ≠ 0)] at hh
  have hright₀ : EqOn (F ∘ G) id e.target := by
    intro x hx
    change F (G x) = x
    rw [← hi hx,← he (hmi hx),e.right_inv hx]
  have hright : ∀ x ∈ closure e.target, F (G x) = x :=
    hright₀.closure (hF.continuous.comp hG.continuous) continuous_id
  refine ⟨F,G,L,M,hF,hG,he,hi,himage,?_,hleft,hright⟩
  rw [← himage,image_image]
  exact image_congr hleft |>.trans (image_id _)



def closedHomeomorph {F G : ℂ → ℂ} (hF : Continuous F) (hG : Continuous G)
    {U : Set ℂ} (hf : MapsTo F (closedBall 0 1) (closure U))
    (hg : MapsTo G (closure U) (closedBall 0 1))
    (hl : ∀ z ∈ closedBall 0 1, G (F z) = z)
    (hr : ∀ x ∈ closure U, F (G x) = x) :
    (closedBall (0:ℂ) 1) ≃ₜ closure U where
  toFun z := ⟨F z,hf z.property⟩
  invFun x := ⟨G x,hg x.property⟩
  left_inv z := Subtype.ext (hl z z.property)
  right_inv x := Subtype.ext (hr x x.property)
  continuous_toFun := hF.continuousOn.domRestrict.codRestrict _
  continuous_invFun := hG.continuousOn.domRestrict.codRestrict _

lemma closed_extension_frontier (e : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) {F G : ℂ → ℂ}
    (_he : EqOn e F (ball 0 1)) (hi : EqOn e.symm G e.target)
    (hf : MapsTo F (closedBall 0 1) (closure e.target))
    (hl : ∀ z ∈ closedBall 0 1, G (F z) = z) :
    MapsTo F (sphere 0 1) (frontier e.target) := by
  intro z hz
  rw [mem_sphere,dist_zero_right] at hz
  have hzcl : z ∈ closedBall (0:ℂ) 1 := by simp only [mem_closedBall_zero_iff,hz,le_refl]
  rw [e.open_target.frontier_eq]
  refine ⟨hf hzcl,?_⟩
  intro hmem
  have him : G (F z) ∈ ball (0:ℂ) 1 := by
    rw [← hi hmem,← hes]
    exact e.map_target hmem
  rw [hl z hzcl,mem_ball_zero_iff,hz] at him
  exact lt_irrefl _ him

end StrictHotSpots.Riemann
end RiemannClosedBiholomorphicCompatibleLayer
end
end RiemannBoundaryCompatible

section ActualClosedConformal

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal
namespace StrictHotSpots.Conformal



structure ClosedDiskChart (Ω : Set Plane) where
  e : OpenPartialHomeomorph Plane Plane
  d : Plane → ℂ
  d' : Plane → ℂ
  source_eq : e.source = DiskH10.disk
  target_eq : e.target = Ω
  smooth : ContDiffOn ℝ ∞ e e.source
  inverse_smooth : ContDiffOn ℝ ∞ e.symm e.target
  deriv : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x
  inverse_deriv : ∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y
  nonzero : ∀ x ∈ e.source, d x ≠ 0
  inverse_nonzero : ∀ y ∈ e.target, d' y ≠ 0
  bound : ℝ
  inverse_bound : ℝ
  bound_pos : 0 < bound
  inverse_bound_pos : 0 < inverse_bound
  bounded_deriv : ∀ x ∈ e.source, ‖d x‖ ≤ bound
  bounded_inverse_deriv : ∀ y ∈ e.target, ‖d' y‖ ≤ inverse_bound
  F : Plane → Plane
  G : Plane → Plane
  Lip : ℝ≥0
  InvLip : ℝ≥0
  lipschitz : LipschitzWith Lip F
  inverse_lipschitz : LipschitzWith InvLip G
  agrees : EqOn e F e.source
  inverse_agrees : EqOn e.symm G e.target
  maps_closure : MapsTo F (closure e.source) (closure Ω)
  inverse_maps_closure : MapsTo G (closure Ω) (closure e.source)
  left_inverse : ∀ z ∈ closure e.source, G (F z) = z
  right_inverse : ∀ x ∈ closure Ω, F (G x) = x



theorem exists_closed_disk_chart {Ω : Set Plane} (hΩ : AdmissibleDomain Ω) :
    Nonempty (ClosedDiskChart Ω) := by
  let U : Set ℂ := coordinate ⁻¹' Ω
  have ho : IsOpen U := hΩ.2.1.preimage coordinate.continuous
  have hs : IsSimplyConnected U := coordinate.toHomeomorph.isSimplyConnected_preimage.mpr hΩ.2.2.2.1
  have hne : U.Nonempty := by
    obtain ⟨x,hx⟩ := hΩ.1
    exact ⟨coordinate.symm x,by simpa [U] using hx⟩
  have hb : Bornology.IsBounded U := by
    have he : U = coordinate.symm '' Ω := by
      ext z
      constructor
      · intro hz
        exact ⟨coordinate z,hz,coordinate.symm_apply_apply z⟩
      · rintro ⟨x,hx,rfl⟩
        simpa [U] using hx
    rw [he]
    exact coordinate.symm.lipschitz.isBounded_image hΩ.2.2.1
  have hproper : U ≠ univ := fun hh => NormedSpace.unbounded_univ ℝ ℂ (hh ▸ hb)
  have hc : Uᶜ.Nonempty := nonempty_compl.mpr hproper
  obtain ⟨Φ,hΦs,hΦt,hΦ,hΦi,hn,hn'⟩ := Riemann.exists_disk_biholomorphism ho hs hne hproper
  obtain ⟨r,hr,hroll⟩ := hΩ.2.2.2.2.complex_rolling_balls hΩ.2.1 hΩ.2.2.1
  have hroll' : ∀ p ∈ frontier Φ.target, ∃ n : ℂ, ‖n‖=1 ∧
      ball (p-r•n) r ⊆ Φ.target ∧ ball (p+r•n) r ⊆ Φ.targetᶜ := by
    simpa only [hΦt] using hroll
  have hb' : Bornology.IsBounded Φ.target := hΦt.symm ▸ hb
  have hc' : Φ.targetᶜ.Nonempty := hΦt.symm ▸ hc
  obtain ⟨B,hB,hbd⟩ := Riemann.bounded_deriv_of_rolling_balls Φ hΦs hΦ
    (hΦt.symm ▸ hΦi) hb' hc' hr hroll'
  obtain ⟨C,hC,hcd⟩ := Riemann.bounded_inverse_deriv_of_rolling_balls Φ hΦs hΦ
    (hΦt.symm ▸ hΦi) hc' hr hroll'
  obtain ⟨F,G,L,M,hF,hG,he,hi,himage,himage',hl,hright⟩ :=
    Riemann.closed_bilipschitz_extension Φ hΦs hΦ (hΦt.symm ▸ hΦi) hb' hc' hr hroll'
  let e := planeChart Φ
  have hes : e.source = DiskH10.disk := by
    rw [planeChart_source,hΦs]
    ext x
    simp only [mem_preimage,mem_ball,dist_zero_right,coordinate.symm.norm_map,DiskH10.disk]
  have het : e.target = Ω := by
    rw [planeChart_target,hΦt]
    ext x
    simp [U]
  have hsrc (x : Plane) (hx : x ∈ e.source) : coordinate.symm x ∈ ball (0:ℂ) 1 := by
    rwa [planeChart_source,hΦs] at hx
  have htgt (x : Plane) (hx : x ∈ e.target) : coordinate.symm x ∈ U := by
    rwa [planeChart_target,hΦt] at hx
  have hsrccl (x : Plane) (hx : x ∈ closure e.source) : coordinate.symm x ∈ closedBall (0:ℂ) 1 := by
    have hsball : e.source = ball (0:Plane) 1 := by
      rw [hes]
      rfl
    rw [hsball,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)] at hx
    simpa only [mem_closedBall_zero_iff,coordinate.symm.norm_map] using hx
  have htgtcl (x : Plane) (hx : x ∈ closure Ω) : coordinate.symm x ∈ closure Φ.target := by
    rw [hΦt]
    change coordinate.symm x ∈ closure (coordinate.toHomeomorph ⁻¹' Ω)
    rw [← coordinate.toHomeomorph.preimage_closure]
    simpa using hx
  let f : Plane → Plane := fun x => coordinate (F (coordinate.symm x))
  let g : Plane → Plane := fun x => coordinate (G (coordinate.symm x))
  have hf : LipschitzWith L f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [f,coordinate.dist_map,coordinate.symm.dist_map] using hF.dist_le_mul (coordinate.symm x) (coordinate.symm y)
  have hg : LipschitzWith M g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [g,coordinate.dist_map,coordinate.symm.dist_map] using hG.dist_le_mul (coordinate.symm x) (coordinate.symm y)
  refine ⟨{
    e := e
    d := fun x => deriv Φ (coordinate.symm x)
    d' := fun x => deriv Φ.symm (coordinate.symm x)
    source_eq := hes
    target_eq := het
    smooth := ?_
    inverse_smooth := ?_
    deriv := ?_
    inverse_deriv := ?_
    nonzero := ?_
    inverse_nonzero := ?_
    bound := B
    inverse_bound := C
    bound_pos := hB
    inverse_bound_pos := hC
    bounded_deriv := ?_
    bounded_inverse_deriv := ?_
    F := f
    G := g
    Lip := L
    InvLip := M
    lipschitz := hf
    inverse_lipschitz := hg
    agrees := ?_
    inverse_agrees := ?_
    maps_closure := ?_
    inverse_maps_closure := ?_
    left_inverse := ?_
    right_inverse := ?_ }⟩
  · change ContDiffOn ℝ ∞ (fun x => coordinate (Φ (coordinate.symm x))) _
    rw [planeChart_source,hΦs]
    exact conjugate_contDiffOn isOpen_ball hΦ
  · change ContDiffOn ℝ ∞ (fun x => coordinate (Φ.symm (coordinate.symm x))) _
    rw [planeChart_target,hΦt]
    exact conjugate_contDiffOn ho hΦi
  · intro x hx
    exact conjugate_hasFDerivAt ((hΦ _ (hsrc x hx)).differentiableAt (isOpen_ball.mem_nhds (hsrc x hx)))
  · intro x hx
    exact conjugate_hasFDerivAt ((hΦi _ (htgt x hx)).differentiableAt (ho.mem_nhds (htgt x hx)))
  · intro x hx
    exact hn _ (hsrc x hx)
  · intro x hx
    exact hn' _ (htgt x hx)
  · intro x hx
    exact hbd _ (hsrc x hx)
  · intro x hx
    exact hcd _ (hΦt.symm ▸ htgt x hx)
  · intro x hx
    exact congrArg coordinate (he (hsrc x hx))
  · intro x hx
    change coordinate (Φ.symm (coordinate.symm x)) = coordinate (G (coordinate.symm x))
    have hm : coordinate.symm x ∈ Φ.target := by rw [hΦt]; exact htgt x hx
    exact congrArg coordinate (hi hm)
  · intro x hx
    have hh : F (coordinate.symm x) ∈ closure Φ.target := himage ▸ mem_image_of_mem F (hsrccl x hx)
    rw [hΦt] at hh
    change coordinate (F (coordinate.symm x)) ∈ closure Ω
    change F (coordinate.symm x) ∈ closure (coordinate.toHomeomorph ⁻¹' Ω) at hh
    rwa [← coordinate.toHomeomorph.preimage_closure] at hh
  · intro x hx
    have hh : G (coordinate.symm x) ∈ closedBall (0:ℂ) 1 := himage' ▸ mem_image_of_mem G (htgtcl x hx)
    have hsball : e.source = ball (0:Plane) 1 := by rw [hes]; rfl
    rw [hsball,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0)]
    simpa only [g,mem_closedBall_zero_iff,coordinate.norm_map] using hh
  · intro x hx
    simpa only [f,g,coordinate.symm_apply_apply,coordinate.apply_symm_apply] using congrArg coordinate (hl _ (hsrccl x hx))
  · intro x hx
    simpa only [f,g,coordinate.symm_apply_apply,coordinate.apply_symm_apply] using congrArg coordinate (hright _ (htgtcl x hx))

end StrictHotSpots.Conformal
end
end ActualClosedConformal

section ClosedConformalData

noncomputable section
open Set Filter Metric
open scoped ContDiff NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



def diskMap : OpenPartialHomeomorph Plane Plane where
  toFun := c.e
  invFun := c.e.symm
  source := DiskH10.disk
  target := Ω
  map_source' := fun _ hx => c.target_eq.subset (c.e.map_source (c.source_eq.symm.subset hx))
  map_target' := fun _ hy => c.source_eq.subset (c.e.map_target (c.target_eq.symm.subset hy))
  left_inv' := fun _ hx => c.e.left_inv (c.source_eq.symm ▸ hx)
  right_inv' := fun _ hy => c.e.right_inv (c.target_eq.symm ▸ hy)
  open_source := PlaneGreen.diskOpen
  open_target := c.target_eq ▸ c.e.open_target
  continuousOn_toFun := c.source_eq ▸ c.e.continuousOn
  continuousOn_invFun := c.e.continuousOn_symm.mono c.target_eq.symm.subset

lemma diskMap_eq : c.diskMap = c.e := by
  apply OpenPartialHomeomorph.ext c.diskMap c.e (fun _ => rfl) (fun _ => rfl)
  exact c.source_eq.symm

lemma diskMap_smooth : ContDiffOn ℝ ∞ c.diskMap DiskH10.disk := by
  change ContDiffOn ℝ ∞ c.e DiskH10.disk
  exact c.source_eq ▸ c.smooth
lemma diskMap_inverse_smooth : ContDiffOn ℝ ∞ c.diskMap.symm Ω := by
  change ContDiffOn ℝ ∞ c.e.symm Ω
  exact c.inverse_smooth.mono c.target_eq.symm.subset
lemma diskMap_deriv : ∀ x ∈ DiskH10.disk, HasFDerivAt c.diskMap (planeMul (c.d x)) x :=
  fun x hx => c.deriv x (c.source_eq.symm ▸ hx)
lemma diskMap_inverse_deriv : ∀ y ∈ Ω, HasFDerivAt c.diskMap.symm (planeMul (c.d' y)) y :=
  fun y hy => c.inverse_deriv y (c.target_eq.symm ▸ hy)
lemma continuous_closed : ContinuousOn c.F (closure DiskH10.disk) := c.lipschitz.continuous.continuousOn
lemma maps_closed : MapsTo c.F (closure DiskH10.disk) (closure Ω) := c.source_eq ▸ c.maps_closure
lemma inverse_maps_closed : MapsTo c.G (closure Ω) (closure DiskH10.disk) :=
  c.source_eq ▸ c.inverse_maps_closure
lemma diskMap_agrees : EqOn c.diskMap c.F DiskH10.disk := fun _ hx => c.agrees (c.source_eq.symm ▸ hx)
lemma diskMap_inverse_agrees : EqOn c.diskMap.symm c.G Ω := fun _ hy => c.inverse_agrees (c.target_eq.symm ▸ hy)

lemma maps_boundary : MapsTo c.F (frontier DiskH10.disk) (frontier Ω) := by
  intro x hx
  refine ⟨c.maps_closed hx.1,?_⟩
  rw [(show IsOpen Ω from c.target_eq ▸ c.e.open_target).interior_eq]
  intro hy
  have hg : c.G (c.F x) ∈ DiskH10.disk := by
    rw [← c.diskMap_inverse_agrees hy]
    exact c.diskMap.map_target hy
  have hi := c.left_inverse x (c.source_eq.symm ▸ hx.1)
  rw [hi] at hg
  exact hx.2 ((show IsOpen DiskH10.disk from PlaneGreen.diskOpen).interior_eq.symm ▸ hg)

lemma inverse_maps_boundary : MapsTo c.G (frontier Ω) (frontier DiskH10.disk) := by
  intro x hx
  refine ⟨c.inverse_maps_closed hx.1,?_⟩
  rw [(show IsOpen DiskH10.disk from PlaneGreen.diskOpen).interior_eq]
  intro hy
  have hg : c.F (c.G x) ∈ Ω := by
    rw [← c.diskMap_agrees hy]
    exact c.diskMap.map_source hy
  rw [c.right_inverse x hx.1] at hg
  exact hx.2 ((show IsOpen Ω from c.target_eq ▸ c.e.open_target).interior_eq.symm ▸ hg)


def boundaryHomeomorph : frontier DiskH10.disk ≃ₜ frontier Ω where
  toFun x := ⟨c.F x,c.maps_boundary x.property⟩
  invFun y := ⟨c.G y,c.inverse_maps_boundary y.property⟩
  left_inv x := Subtype.ext (c.left_inverse x (c.source_eq.symm ▸ x.property.1))
  right_inv y := Subtype.ext (c.right_inverse y y.property.1)
  continuous_toFun := (c.lipschitz.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (c.inverse_lipschitz.continuous.comp continuous_subtype_val).subtype_mk _

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedConformalData

section ClosedSmoothData



noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots


def closedGradient (Ω : Set Plane) (u : Plane → ℝ) (x : Plane) : Plane :=
  (InnerProductSpace.toDual ℝ Plane).symm (fderivWithin ℝ u (closure Ω) x)

lemma closedGradient_eq {Ω : Set Plane} {u : Plane → ℝ} (ho : IsOpen Ω) {x : Plane}
    (hx : x ∈ Ω) : closedGradient Ω u x = gradient u x := by
  unfold closedGradient gradient
  rw [fderivWithin_of_mem_nhds (mem_of_superset (ho.mem_nhds hx) subset_closure)]

lemma closedGradient_continuous {Ω : Set Plane} {u : Plane → ℝ} (ho : IsOpen Ω)
    (hs : SmoothBoundary Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω)) :
    ContinuousOn (closedGradient Ω u) (closure Ω) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderivWithin (hs.uniqueDiffOn_closure ho) (by simp))


lemma continuous_closure_memLp {Ω : Set Plane} {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hf : ContinuousOn f (closure Ω)) : MemLp f 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨C,hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable ho.measurableSet) C
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact hC x (subset_closure hx)

lemma smooth_closure_H1 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hu : ContDiffOn ℝ ∞ u (closure Ω)) : HasH1Gradient Ω u (gradient u) := by
  apply HasH1Gradient.of_contDiffOn ho (hu.mono subset_closure)
    (continuous_closure_memLp ho hb hu.continuousOn)
  apply MemLp.ae_eq _ (continuous_closure_memLp ho hb (closedGradient_continuous ho hs hu))
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact closedGradient_eq ho hx

lemma smooth_closure_zero_H10 {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    (hu : ContDiffOn ℝ ∞ u (closure Ω)) (hz : ∀ x ∈ frontier Ω, u x = 0) :
    (smooth_closure_H1 ho hb hs hu).toH1 ∈ h10Submodule ho :=
  smooth_zero_trace_memH10 ho hu (smooth_closure_H1 ho hb hs hu) hb hz

lemma closure_directional_smooth {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) (hs : SmoothBoundary Ω)
    (hu : ContDiffOn ℝ ∞ u (closure Ω)) (e : Plane) :
    ContDiffOn ℝ ∞ (fun x => fderivWithin ℝ u (closure Ω) x e) (closure Ω) :=
  (hu.fderivWithin (hs.uniqueDiffOn_closure ho) (by simp)).clm_apply contDiffOn_const

end StrictHotSpots

namespace StrictHotSpots.Conformal.ClosedDiskChart
open Set Filter Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

def pullDatum (w : Plane → ℝ) : Plane → ℝ := w ∘ c.F

lemma pullDatum_continuous {w : Plane → ℝ} (hw : ContinuousOn w (closure Ω)) :
    ContinuousOn (c.pullDatum w) (closure disk) := hw.comp c.continuous_closed c.maps_closed

lemma pullDatum_eq_inner {w : Plane → ℝ} : EqOn (c.pullDatum w) (w ∘ c.diskMap) disk :=
  fun _ hx => congrArg w (c.diskMap_agrees hx).symm

lemma pullDatum_smooth {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w Ω) :
    ContDiffOn ℝ ∞ (c.pullDatum w) disk :=
  (hw.comp c.diskMap_smooth c.diskMap.mapsTo).congr c.pullDatum_eq_inner

lemma pullDatum_grad_norm {w : Plane → ℝ} (hw : DifferentiableOn ℝ w Ω)
    {x : Plane} (hx : x ∈ disk) :
    ‖gradient (c.pullDatum w) x‖ = ‖c.d x‖ * ‖gradient w (c.diskMap x)‖ := by
  have he : c.pullDatum w =ᶠ[nhds x] w ∘ c.diskMap :=
    eventually_of_mem (diskOpen.mem_nhds hx) (fun _ hy => c.pullDatum_eq_inner hy)
  have hg : gradient (c.pullDatum w) x = gradient (w ∘ c.diskMap) x := by
    unfold gradient
    rw [he.fderiv_eq]
  rw [hg]
  exact plane_norm_gradient_comp (c.diskMap_deriv x hx)
    ((hw _ (c.diskMap.map_source hx)).differentiableAt
      (c.diskMap.open_target.mem_nhds (c.diskMap.map_source hx)))

lemma pullDatum_bounded_gradient (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, ∀ x ∈ disk, ‖gradient (c.pullDatum w) x‖ ≤ B := by
  obtain ⟨C,hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn
    (closedGradient_continuous c.diskMap.open_target hs hw)
  let B : ℝ≥0 := ⟨c.bound * max C 0,mul_nonneg c.bound_pos.le (le_max_right _ _)⟩
  refine ⟨B,fun x hx => ?_⟩
  rw [c.pullDatum_grad_norm ((hw.mono subset_closure).differentiableOn (by simp)) hx]
  have ht := c.diskMap.map_source hx
  have hcg := hC (c.diskMap x) (subset_closure ht)
  rw [closedGradient_eq (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) ht] at hcg
  exact mul_le_mul (c.bounded_deriv x (c.source_eq.symm.subset hx))
    (hcg.trans (le_max_left _ _)) (norm_nonneg _) c.bound_pos.le

lemma pullDatum_lipschitz (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, LipschitzOnWith B (c.pullDatum w) (closure disk) := by
  obtain ⟨B,hB⟩ := c.pullDatum_bounded_gradient hb hs hw
  have hsm := c.pullDatum_smooth (hw.mono subset_closure)
  have hd (x : Plane) (hx : x ∈ disk) : DifferentiableAt ℝ (c.pullDatum w) x :=
    ((hsm.differentiableOn (by simp)) x hx).differentiableAt (diskOpen.mem_nhds hx)
  have hf (x : Plane) (hx : x ∈ disk) : ‖fderiv ℝ (c.pullDatum w) x‖₊ ≤ B := by
    change ‖fderiv ℝ (c.pullDatum w) x‖ ≤ (B : ℝ)
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hB x hx
  exact ⟨B,LipschitzOnWith.closure (c.pullDatum_continuous hw.continuousOn)
    ((convex_ball (0 : Plane) 1).lipschitzOnWith_of_nnnorm_fderiv_le hd hf)⟩

lemma pullDatum_H1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    HasH1Gradient disk (c.pullDatum w) (gradient (c.pullDatum w)) := by
  have hsm := c.pullDatum_smooth (hw.mono subset_closure)
  apply HasH1Gradient.of_contDiffOn diskOpen hsm
    (continuous_closure_memLp diskOpen diskBounded (c.pullDatum_continuous hw.continuousOn))
  let : IsFiniteMeasure (volume.restrict disk) := isFiniteMeasure_restrict.mpr diskBounded.measure_lt_top.ne
  obtain ⟨B,hB⟩ := c.pullDatum_bounded_gradient hb hs hw
  have hc : ContinuousOn (gradient (c.pullDatum w)) disk :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hsm.continuousOn_fderiv_of_isOpen diskOpen (by simp))
  apply MemLp.of_bound (hc.aestronglyMeasurable diskOpen.measurableSet) B
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  exact hB x hx

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedSmoothData

end OAI
