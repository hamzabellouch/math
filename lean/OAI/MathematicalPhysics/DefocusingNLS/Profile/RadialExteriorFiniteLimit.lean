import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteContinuation
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFiniteStability

namespace OAI

/-! Uniform convergence of the finite-interval continuation to its free reference. -/

open Set Filter
namespace DefocusingNLS

theorem exists_radialExterior_clipped_limit (ν : ℕ → ℂ) (μ : ℂ)
    (hν : Tendsto ν atTop (nhds μ)) (g : ℝ → ℂ × ℂ) (hg : Continuous g)
    (δ ρ u T : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T) (hρ1 : ρ < 1)
    (hb : ∀ t ∈ Icc (u-T) u, ‖(g t).1‖+2*δ ≤ ρ)
    (hgd : ∀ t ∈ Icc (u-T) u, HasDerivAt g
      ((0,-Complex.I*(Real.exp (2*t)/2 : ℝ)*(g t).2)+radialExteriorErrorMatrix μ (g t)) t)
    (x : ℕ → ℂ × ℂ) (hx : Tendsto x atTop (nhds (g u))) :
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      (∀ n, Continuous (Z n) ∧ Z n u=x n ∧ ∀ t ∈ Icc (u-T) u,
        HasDerivAt (Z n) (radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ t (Z n t)) t) ∧
      TendstoUniformlyOn Z g atTop (Icc (u-T) u) := by
  have hgc : Continuous (fun t => (g t).1) := continuous_fst.comp hg
  have hρ : 0 ≤ ρ := (by positivity : 0 ≤ ‖(g u).1‖+2*δ).trans (hb u ⟨by linarith,le_rfl⟩)
  choose Z hZ using (fun n => exists_radialExterior_clipped_finite (ν n) n
    (fun t => (g t).1) hgc δ ρ u T hδ hT hb (x n))
  refine ⟨Z,hZ,?_⟩
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (u-T) u)).exists_bound_of_continuousOn hg.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (g u)).trans (hC u ⟨by linarith,le_rfl⟩)
  let L : ℕ → ℝ := fun n => radialExteriorMatrixBound (ν n)+Real.exp (2*u)/2+
    2*(2*(n : ℝ)+1)*ρ^(2*n)
  let K := radialExteriorMatrixBound μ+Real.exp (2*u)/2+1
  have hK : 0 < K := by dsimp [K]; have := radialExteriorMatrixBound_pos μ; positivity
  have hB : Tendsto (fun n => radialExteriorMatrixBound (ν n)) atTop (nhds (radialExteriorMatrixBound μ)) :=
    (show Continuous radialExteriorMatrixBound by unfold radialExteriorMatrixBound; fun_prop).continuousAt.tendsto.comp hν
  have hL : Tendsto L atTop (nhds (radialExteriorMatrixBound μ+Real.exp (2*u)/2)) := by
    convert (hB.add_const (Real.exp (2*u)/2)).add
      ((radial_oddPower_lipschitz_tendsto ρ hρ hρ1).const_mul 2) using 1
    · funext n; dsimp [L]; ring
    · ring_nf
  have hLK : ∀ᶠ n in atTop, L n ≤ K :=
    (hL.eventually (gt_mem_nhds (by dsimp [K]; linarith))).mono (fun _ h => h.le)
  let ε : ℕ → ℝ := fun n => radialExteriorMatrixDifference (ν n) μ*C+ρ^(2*n+1)
  have hM : Tendsto (fun n => radialExteriorMatrixDifference (ν n) μ) atTop (nhds 0) := by
    have hc : Continuous (fun v => radialExteriorMatrixDifference v μ) := by
      unfold radialExteriorMatrixDifference
      fun_prop
    have ht : Tendsto (fun n => radialExteriorMatrixDifference (ν n) μ) atTop
        (nhds (radialExteriorMatrixDifference μ μ)) := hc.continuousAt.tendsto.comp hν
    simpa only [radialExteriorMatrixDifference,sub_self,norm_zero,zero_add] using ht

  have hpow : Tendsto (fun n : ℕ => ρ^(2*n+1)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg ρ)
      (pow_lt_one₀ hρ hρ1 (by decide : 2 ≠ 0))).mul_const ρ
    convert h using 1
    · funext n; rw [pow_succ,← pow_mul]
    · simp
  have hε : Tendsto ε atTop (nhds 0) := by
    simpa only [ε,zero_mul,zero_add] using (hM.mul_const C).add hpow
  let f : ℕ → ℝ → ℂ × ℂ := fun n s => Z n (u-s)
  let f' : ℕ → ℝ → ℂ × ℂ := fun n s =>
    -radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ (u-s) (Z n (u-s))
  let G : ℝ → ℂ × ℂ := fun s => g (u-s)
  let G' : ℝ → ℂ × ℂ := fun s =>
    -((0,-Complex.I*(Real.exp (2*(u-s))/2 : ℝ)*(g (u-s)).2)+radialExteriorErrorMatrix μ (g (u-s)))
  have htime (s : ℝ) (hs : s ∈ Icc 0 T) : u-s ∈ Icc (u-T) u := by
    constructor <;> linarith [hs.1,hs.2]
  have hfd : ∀ n s, s ∈ Icc 0 T → HasDerivAt (f n) (f' n s) s := by
    intro n s hs
    simpa only [f,f',neg_one_smul] using!
      ((hZ n).2.2 (u-s) (htime s hs)).scomp s ((hasDerivAt_id s).const_sub u)
  have hGd : ∀ s, s ∈ Icc 0 T → HasDerivAt G (G' s) s := by
    intro s hs
    simpa only [G,G',neg_one_smul] using!
      (hgd (u-s) (htime s hs)).scomp s ((hasDerivAt_id s).const_sub u)
  have hinit : Tendsto (fun n => f n 0) atTop (nhds (G 0)) := by
    simpa only [f,G,sub_zero,(hZ _).2.1] using hx
  have hbound : ∀ᶠ n in atTop, 0 ≤ ε n ∧
      ∀ s ∈ Icc 0 T, ‖f' n s-G' s‖ ≤ K*‖f n s-G s‖+ε n := by
    filter_upwards [hLK] with n hn
    refine ⟨by dsimp [ε,radialExteriorMatrixDifference]; positivity,?_⟩
    intro s hs
    have hr := htime s hs
    have hlin := radialExteriorFiniteField_linear_difference (ν n) μ n (fun r => (g r).1)
      δ ρ (u-s) hδ (hb _ hr) (g (u-s))
    have hlip := radialExteriorReverseField_lipschitz (ν n) n (fun r => (g r).1) hgc
      δ ρ u T hδ hb ⟨s,hs⟩ (Z n (u-s)) (g (u-s))
    change ‖-radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ (u-s) (Z n (u-s))-
      -((0,-Complex.I*(Real.exp (2*(u-s))/2 : ℝ)*(g (u-s)).2)+radialExteriorErrorMatrix μ (g (u-s)))‖ ≤ _
    rw [neg_sub_neg,norm_sub_rev]
    have hlip' : ‖radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ (u-s) (Z n (u-s))-
        radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ (u-s) (g (u-s))‖ ≤
        L n*‖Z n (u-s)-g (u-s)‖ := by
      simpa only [radialExteriorReverseField_apply,neg_sub_neg,norm_sub_rev,L] using hlip
    let A : (ℂ × ℂ) → ℂ × ℂ := radialExteriorFiniteField (ν n) n (fun r => (g r).1) δ (u-s)
    let v : ℂ × ℂ := (0,-Complex.I*(Real.exp (2*(u-s))/2 : ℝ)*(g (u-s)).2)+
      radialExteriorErrorMatrix μ (g (u-s))
    calc
      _ ≤ ‖A (Z n (u-s))-A (g (u-s))‖+‖A (g (u-s))-v‖ := by
        simpa only [dist_eq_norm] using dist_triangle (A (Z n (u-s))) (A (g (u-s))) v
      _ ≤ L n*‖Z n (u-s)-g (u-s)‖+
          (radialExteriorMatrixDifference (ν n) μ*‖g (u-s)‖+ρ^(2*n+1)) :=
        add_le_add hlip' hlin
      _ ≤ _ := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
        · dsimp [ε]
          have hM0 : 0 ≤ radialExteriorMatrixDifference (ν n) μ := by
            unfold radialExteriorMatrixDifference
            positivity
          exact add_le_add (mul_le_mul_of_nonneg_left (hC _ hr) hM0) le_rfl

  have hu := radial_finite_uniform_limit T K hK f f' G G' ε hε hinit
    (fun n => ((hZ n).1.comp (continuous_const.sub continuous_id)).continuousOn)
    (hg.comp (continuous_const.sub continuous_id)).continuousOn hfd hGd hbound
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro r hr
  filter_upwards [hu r hr] with n hn t ht
  have hs : u-t ∈ Icc (0 : ℝ) T := by constructor <;> linarith [ht.1,ht.2]
  simpa only [f,G,sub_sub_cancel] using hn (u-t) hs

end DefocusingNLS

end OAI
