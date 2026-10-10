import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorFiniteParameter

namespace OAI

/-! Fixed-power continuity persists when the outgoing solution is continued backwards. -/

open Set Filter
namespace DefocusingNLS

theorem radialExterior_finite_parameter_limit (n : ℕ) (ν : ℕ → ℂ) (μ : ℂ)
    (hν : Tendsto ν atTop (nhds μ)) (m : ℝ → ℂ) (hm : Continuous m)
    (δ ρ u T : ℝ) (hδ : 0 ≤ δ) (hT : 0 ≤ T)
    (hb : ∀ t ∈ Icc (u-T) u, ‖m t‖+2*δ ≤ ρ)
    (Z : ℕ → ℝ → ℂ × ℂ) (g : ℝ → ℂ × ℂ)
    (hZc : ∀ i, Continuous (Z i)) (hgc : Continuous g)
    (hZd : ∀ i t, t ∈ Icc (u-T) u →
      HasDerivAt (Z i) (radialExteriorFiniteField (ν i) n m δ t (Z i t)) t)
    (hgd : ∀ t ∈ Icc (u-T) u,
      HasDerivAt g (radialExteriorFiniteField μ n m δ t (g t)) t)
    (hx : Tendsto (fun i => Z i u) atTop (nhds (g u))) :
    TendstoUniformlyOn Z g atTop (Icc (u-T) u) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (u-T) u)).exists_bound_of_continuousOn
    hgc.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg (g u)).trans (hC u ⟨by linarith,le_rfl⟩)
  have hρ0 : 0 ≤ ρ := (by positivity : 0 ≤ ‖m u‖+2*δ).trans (hb u ⟨by linarith,le_rfl⟩)
  let L : ℕ → ℝ := fun i => radialExteriorMatrixBound (ν i)+Real.exp (2*u)/2+
    2*(2*(n : ℝ)+1)*ρ^(2*n)
  let K := radialExteriorMatrixBound μ+Real.exp (2*u)/2+2*(2*(n : ℝ)+1)*ρ^(2*n)+1
  have hK : 0 < K := by dsimp [K]; have := radialExteriorMatrixBound_pos μ; positivity
  have hB : Tendsto (fun i => radialExteriorMatrixBound (ν i)) atTop
      (nhds (radialExteriorMatrixBound μ)) :=
    (show Continuous radialExteriorMatrixBound by unfold radialExteriorMatrixBound; fun_prop).continuousAt.tendsto.comp hν
  have hLK : ∀ᶠ i in atTop, L i ≤ K := by
    have he := ((hB.add_const (Real.exp (2*u)/2)).add_const
      (2*(2*(n : ℝ)+1)*ρ^(2*n))).eventually (gt_mem_nhds (show
        radialExteriorMatrixBound μ+Real.exp (2*u)/2+2*(2*(n : ℝ)+1)*ρ^(2*n) < K by
          dsimp [K]; linarith))
    exact he.mono (fun i hi => hi.le)
  let ε := fun i => radialExteriorMatrixDifference (ν i) μ*C
  have hε : Tendsto ε atTop (nhds 0) := by
    have hc : Continuous (fun v => radialExteriorMatrixDifference v μ) := by
      unfold radialExteriorMatrixDifference
      fun_prop
    have hh := (hc.continuousAt.tendsto.comp hν).mul_const C
    simpa only [ε,radialExteriorMatrixDifference,sub_self,norm_zero,zero_add,zero_mul] using! hh
  let F := fun i s => Z i (u-s)
  let F' := fun i s => -radialExteriorFiniteField (ν i) n m δ (u-s) (Z i (u-s))
  let G := fun s => g (u-s)
  let G' := fun s => -radialExteriorFiniteField μ n m δ (u-s) (g (u-s))
  have htime (s : ℝ) (hs : s ∈ Icc 0 T) : u-s ∈ Icc (u-T) u := by
    constructor <;> linarith [hs.1,hs.2]
  have hFd : ∀ i s, s ∈ Icc 0 T → HasDerivAt (F i) (F' i s) s := by
    intro i s hs
    simpa only [F,F',neg_one_smul] using!
      (hZd i (u-s) (htime s hs)).scomp s ((hasDerivAt_id s).const_sub u)
  have hGd : ∀ s, s ∈ Icc 0 T → HasDerivAt G (G' s) s := by
    intro s hs
    simpa only [G,G',neg_one_smul] using!
      (hgd (u-s) (htime s hs)).scomp s ((hasDerivAt_id s).const_sub u)
  have hbound : ∀ᶠ i in atTop, 0 ≤ ε i ∧
      ∀ s ∈ Icc 0 T, ‖F' i s-G' s‖ ≤ K*‖F i s-G s‖+ε i := by
    filter_upwards [hLK] with i hi
    refine ⟨by dsimp [ε,radialExteriorMatrixDifference]; positivity,?_⟩
    intro s hs
    have hr := htime s hs
    have hpar := radialExteriorFiniteField_parameter_difference (ν i) μ n m δ (u-s) (g (u-s))
    have hlip := radialExteriorReverseField_lipschitz (ν i) n m hm δ ρ u T hδ hb
      ⟨s,hs⟩ (Z i (u-s)) (g (u-s))
    have hlip' : ‖radialExteriorFiniteField (ν i) n m δ (u-s) (Z i (u-s))-
        radialExteriorFiniteField (ν i) n m δ (u-s) (g (u-s))‖ ≤
        L i*‖Z i (u-s)-g (u-s)‖ := by
      simpa only [radialExteriorReverseField_apply,neg_sub_neg,norm_sub_rev,L] using hlip
    change ‖-radialExteriorFiniteField (ν i) n m δ (u-s) (Z i (u-s))-
      -radialExteriorFiniteField μ n m δ (u-s) (g (u-s))‖ ≤ _
    rw [neg_sub_neg,norm_sub_rev]
    calc
      _ ≤ ‖radialExteriorFiniteField (ν i) n m δ (u-s) (Z i (u-s))-
          radialExteriorFiniteField (ν i) n m δ (u-s) (g (u-s))‖+
          ‖radialExteriorFiniteField (ν i) n m δ (u-s) (g (u-s))-
          radialExteriorFiniteField μ n m δ (u-s) (g (u-s))‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (radialExteriorFiniteField (ν i) n m δ (u-s) (Z i (u-s)))
          (radialExteriorFiniteField (ν i) n m δ (u-s) (g (u-s)))
          (radialExteriorFiniteField μ n m δ (u-s) (g (u-s)))
      _ ≤ L i*‖Z i (u-s)-g (u-s)‖+radialExteriorMatrixDifference (ν i) μ*‖g (u-s)‖ :=
        add_le_add hlip' hpar
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hC _ hr) (by unfold radialExteriorMatrixDifference; positivity))
  have hu := radial_finite_uniform_limit T K hK F F' G G' ε hε
    (by simpa only [F,G,sub_zero] using hx)
    (fun i => ((hZc i).comp (continuous_const.sub continuous_id)).continuousOn)
    (hgc.comp (continuous_const.sub continuous_id)).continuousOn hFd hGd hbound
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro η hη
  filter_upwards [hu η hη] with i hi t ht
  have hs : u-t ∈ Icc (0 : ℝ) T := by constructor <;> linarith [ht.1,ht.2]
  simpa only [F,G,sub_sub_cancel] using hi (u-t) hs

end DefocusingNLS

end OAI
