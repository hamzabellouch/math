import Mathlib
import OAI.Probability.LogConcave.Dynamics.VariationalField

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter Metric
open scoped Topology NNReal

theorem smooth_flow_joint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : ℝ → E → E}
    (hf : ContDiff ℝ (⊤:ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
    (hL : ∀t∈Icc a b,LipschitzWith K (f t)) (s : Icc a b)
    (p₀ : ℝ × E) (hp₀ : p₀.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (fun p : ℝ × E => flow hL hf.continuous s p.2 p.1) p₀ := by
  apply contDiffAt_infty.mpr
  intro n
  let V : ℝ × (ℝ × E) → ℝ × (ℝ × E) := fun p => (0,(p.1,p.1 • f p.2.1 p.2.2))
  have hV : ContDiff ℝ (⊤:ℕ∞) V :=
    contDiff_const.prodMk (contDiff_fst.prodMk (contDiff_fst.smul (hf.comp contDiff_snd)))
  let X := fun x => flow hL hf.continuous s x
  obtain ⟨A,hA⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((flow_continuous hL hf.continuous s (0:E)).continuousOn : ContinuousOn (X 0) (Icc a b))
  let C := Real.exp ((K:ℝ)*(b-a))
  have hC : 0<C := Real.exp_pos _
  obtain ⟨N,hN⟩ := exists_nat_gt (max (b-a) (max (max |a| |b|) (A+C*(‖p₀.2‖+1))))
  let W := LinearGrowthODE.truncated V N
  have hW : ContDiff ℝ (n:WithTop ℕ∞) W := truncated_contDiff (hV.of_le (WithTop.coe_le_coe.mpr le_top)) N
  obtain ⟨L,hWL⟩ := LinearGrowthODE.truncated_lipschitz (hV.of_le (by norm_num)) N
  have hWc : Continuous (uncurry (fun (_ : ℝ) => W)) := hW.continuous.comp continuous_snd
  let Z (p : ℝ × (ℝ × E)) := flow (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) p 1
  have hZ : ContDiff ℝ (n:WithTop ℕ∞) Z := autonomous_flow_contDiff _ hW hWL (by norm_num) ⟨1,by norm_num,le_rfl⟩
  have he : (fun p : ℝ × E => X p.2 p.1) =ᶠ[𝓝 p₀]
      (fun p => (Z (p.1-s,((s:ℝ),p.2))).2.2) := by
    have hn : Ioo a b ×ˢ ball p₀.2 1 ∈ 𝓝 p₀ :=
      (isOpen_Ioo.prod isOpen_ball).mem_nhds ⟨hp₀,mem_ball_self zero_lt_one⟩
    filter_upwards [hn] with p hp
    have hpt : p.1∈Icc a b := ⟨hp.1.1.le,hp.1.2.le⟩
    have hxn : ‖p.2‖≤‖p₀.2‖+1 := by
      have hh := norm_le_norm_add_norm_sub p₀.2 p.2
      rw [←dist_eq_norm,dist_comm] at hh
      linarith [mem_ball.mp hp.2]
    let q : ℝ → ℝ := fun u => (s:ℝ)+(p.1-s)*u
    have hq (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : q u∈Icc a b := by
      have hc := (convex_Icc a b) s.2 hpt (show 0≤1-u by linarith [hu.2]) hu.1 (show 1-u+u=1 by ring)
      convert! hc using 1
      dsimp [q]
      ring
    have hqb (u : ℝ) (hu : u∈Icc (0:ℝ) 1) : ‖(p.1-s,(q u,X p.2 (q u)))‖≤(N:ℝ)+1 := by
      have htime (v : Icc a b) : |(v:ℝ)-s|≤b-a := by
        rw [abs_le]; constructor <;> linarith [v.2.1,v.2.2,s.2.1,s.2.2]
      have hex : Real.exp ((K:ℝ)*|q u-s|)≤C :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (htime ⟨q u,hq u hu⟩) K.coe_nonneg)
      have hX : ‖X p.2 (q u)‖≤A+C*(‖p₀.2‖+1) := by
        have hs := (flow_lipschitz hL hf.continuous s ⟨q u,hq u hu⟩).dist_le_mul p.2 0
        simp only [dist_zero_right] at hs
        have hh : ‖X p.2 (q u)‖≤‖X 0 (q u)‖+dist (X p.2 (q u)) (X 0 (q u)) := by
          simpa only [dist_eq_norm,norm_sub_rev] using (norm_le_norm_add_norm_sub (X 0 (q u)) (X p.2 (q u)))
        exact hh.trans (add_le_add (hA (q u) (hq u hu))
          (hs.trans (mul_le_mul hex hxn (norm_nonneg _) hC.le)))
      have hqt : |q u| ≤ max |a| |b| := by
        rw [abs_le]
        constructor <;> linarith [(hq u hu).1,(hq u hu).2,
          neg_abs_le a,le_abs_self b,le_max_left |a| |b|,le_max_right |a| |b|]
      simp only [Prod.norm_def,Real.norm_eq_abs]
      exact (max_le_max (htime ⟨p.1,hpt⟩) (max_le_max hqt hX)).trans (by linarith)
    let P : ℝ → ℝ × (ℝ × E) := fun u => (p.1-s,(q u,X p.2 (q u)))
    have hqc : Continuous q := by dsimp [q]; fun_prop
    have hPc : Continuous P := continuous_const.prodMk
      (hqc.prodMk ((flow_continuous hL hf.continuous s p.2).comp hqc))
    have hPd (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
        HasDerivWithinAt P (W (P u)) (Icc (0:ℝ) 1) u := by
      have heW : W (P u)=V (P u) := LinearGrowthODE.truncated_eq (hqb u hu)
      rw [heW]
      have hdq : HasDerivWithinAt q (p.1-s) (Icc (0:ℝ) 1) u := by
        convert! (hasDerivWithinAt_const u (Icc (0:ℝ) 1) (s:ℝ)).add
          ((hasDerivWithinAt_id u (Icc (0:ℝ) 1)).const_mul (p.1-s)) using 1
        simp
      have hdX := (flow_deriv hL hf.continuous s p.2 (q u) (hq u hu)).scomp u hdq hq
      exact (hasDerivWithinAt_const u (Icc (0:ℝ) 1) (p.1-s)).prodMk (hdq.prodMk hdX)
    have h0 : P 0=(p.1-s,((s:ℝ),p.2)) := by
      dsimp [P,q]
      simp only [mul_zero,add_zero]
      rw [show X p.2 s=p.2 from flow_initial hL hf.continuous s p.2]
    have h1 : P 1=(p.1-s,(p.1,X p.2 p.1)) := by
      dsimp [P]
      rw [show q 1=p.1 by dsimp [q]; ring]
    have hs := trajectory_dist (fun (_ : ℝ) _ => hWL) hPc.continuousOn hPd
      (flow_continuous (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (p.1-s,((s:ℝ),p.2))).continuousOn
      (flow_deriv (fun _ _ => hWL) hWc (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (p.1-s,((s:ℝ),p.2)))
      (⟨0,le_rfl,by norm_num⟩ : Icc (0:ℝ) 1) (⟨1,by norm_num,le_rfl⟩ : Icc (0:ℝ) 1)
    change dist (P 1) (Z (p.1-s,((s:ℝ),p.2)))≤dist (P 0) _ * _ at hs
    rw [h0,flow_initial,dist_self,zero_mul,dist_le_zero,h1] at hs
    exact congrArg (fun z => z.2.2) hs
  exact ((hZ.comp ((contDiff_fst.sub contDiff_const).prodMk
    (contDiff_const.prodMk contDiff_snd))).snd.snd).contDiffAt.congr_of_eventuallyEq he
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {f : ℝ → E → E}
  (hf : ContDiff ℝ (⊤:ℕ∞) (uncurry f)) {K : ℝ≥0} {a b : ℝ}
  (hab : a≤b) (hL : ∀t∈Icc a b,LipschitzWith K (f t))

lemma spaceTimeForward_smooth (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (spaceTimeForward hab hf.continuous hL) p := by
  have hh := contDiffAt_fst.prodMk (smooth_flow_joint hf hL ⟨a,le_rfl,hab⟩ p hp)
  apply hh.congr_of_eventuallyEq
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Icc_mem_nhds hp.1 hp.2)] with q hq
  simp only [spaceTimeForward,projIcc_of_mem _ hq]

lemma spaceTimeBackward_smooth (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞) (spaceTimeBackward hab hf.continuous hL) p := by
  let D := fun t => fderiv ℝ (f t)
  have hD : Continuous (uncurry D) := by
    have hh := hf.continuous_fderiv (by norm_num)
    have he : uncurry D=fun p : ℝ × E => (fderiv ℝ (uncurry f) p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
      funext p
      have hg : HasFDerivAt (fun z : E => (p.1,z)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
        convert! (hasFDerivAt_const (𝕜:=ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜:=ℝ) p.2) using 1
      exact ((hf.differentiable (by norm_num) p).hasFDerivAt.comp p.2 hg).fderiv
    rw [he]
    exact hh.clm_comp continuous_const
  have hd (t : ℝ) (z : E) : HasFDerivAt (f t) (D t z) z :=
    ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) z).hasFDerivAt
  let H := spaceTimeHomeomorph hab hf.continuous hL
  have hp' : (H.symm p).1∈Ioo a b := hp
  exact H.toOpenPartialHomeomorph.contDiffAt_symm (Set.mem_univ p)
    (spaceTimeForward_hasFDerivAt hab hf.continuous hL hD hd (H.symm p) hp')
    (spaceTimeForward_smooth hf hab hL (H.symm p) hp')

lemma backward_flow_smooth (T : Icc a b) (p : ℝ × E) (hp : p.1∈Ioo a b) :
    ContDiffAt ℝ (⊤:ℕ∞)
      (fun p : ℝ × E => flow hL hf.continuous (projIcc a b hab p.1) p.2 T) p := by
  have hA : ContDiff ℝ (⊤:ℕ∞)
      (fun y => flow hL hf.continuous ⟨a,le_rfl,hab⟩ y T) := by
    apply contDiff_infty.mpr
    intro n
    exact smooth_flow (hf.of_le (WithTop.coe_le_coe.mpr le_top)) hL hab _ T
  have hh := hA.contDiffAt.comp p ((spaceTimeBackward_smooth hf hab hL p hp).snd)
  convert! hh using 1
  funext q
  exact (flow_cocycle hL hf.continuous (projIcc a b hab q.1) ⟨a,le_rfl,hab⟩ T q.2).symm
end LogConcaveSampling.GlobalODE

end

end

section

noncomputable section
namespace LogConcaveSampling.GlobalODE
open Set Function
open scoped Topology NNReal

lemma flow_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b c d : ℝ} {f g : ℝ → E → E} {K L : ℝ≥0}
    (hf : Continuous (uncurry f)) (hg : Continuous (uncurry g))
    (hL : ∀t∈Icc a b,LipschitzWith K (f t))
    (hJ : ∀t∈Icc c d,LipschitzWith L (g t)) (hsub : Icc a b ⊆ Icc c d)
    (he : ∀t∈Icc a b,∀x,f t x=g t x) (s t : Icc a b) (x : E) :
    flow hL hf s x t=flow hJ hg ⟨s,hsub s.2⟩ x t := by
  have hh := trajectory_dist hL (flow_continuous hL hf s x).continuousOn
    (flow_deriv hL hf s x) (flow_continuous hJ hg ⟨s,hsub s.2⟩ x).continuousOn
    (fun u hu => (he u hu _) ▸ (flow_deriv hJ hg ⟨s,hsub s.2⟩ x u (hsub hu)).mono hsub) s t
  simpa only [flow_initial,dist_self,zero_mul,dist_le_zero] using hh
end LogConcaveSampling.GlobalODE

end
end
end

end OAI
