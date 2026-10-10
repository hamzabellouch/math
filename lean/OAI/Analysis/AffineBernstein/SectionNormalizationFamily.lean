import Mathlib
import OAI.Analysis.AffineBernstein.LinearNormalizationCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal

section SectionNormalizationFamily
open scoped Pointwise
open Filter
open scoped Topology

/-- The actual uniform, zero-preserving section normalizations in rigidity.tex.
The radius is fixed before height; the maps are produced from the compact
convex sections and their genuine balance inclusion. -/
theorem centered_section_normalization_family {n : ℕ} (hn : 1 ≤ n)
    {u : Space n → ℝ} (hu : ContDiff ℝ ∞ u) (hp : ∀ x, (hessian u x).PosDef)
    (hzero : u 0=0) (hdzero : fderiv ℝ u 0=0)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hbal : SectionBalance univ u ρ) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : ℝ, 0 < t → ∃ A : Space n ≃L[ℝ] Space n,
      Metric.ball 0 1 ⊆ tangentSection univ (normalizedFunction u A t) 0 1 ∧
      tangentSection univ (normalizedFunction u A t) 0 1 ⊆ Metric.ball 0 R := by
  let C := ρ⁻¹
  have hC : 1 ≤ C := (one_le_inv₀ hρ).mpr hρ1
  have hCp : 0 < C+1 := by linarith
  let R : ℝ := 2*(n:ℝ)*(C+1)+1
  have hR : 1 ≤ R := by
    have H : 0 ≤ 2*(n:ℝ)*(C+1) := by positivity
    dsimp [R]
    linarith
  have hcv := convexOn_of_hessian_posSemidef isOpen_univ convex_univ hu.contDiffOn
    (fun x _ => (hp x).posSemidef)
  have hc := euclideanGraphComplete_entire hu
  have hg (x : Space n) : tangentHeight u 0 x = u x := by simp [tangentHeight,hzero,hdzero]
  refine ⟨R,hR,?_⟩
  intro t ht
  let K := closure (tangentSection univ u 0 t)
  have hKeq : K = {x | u x ≤ t} := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    simp only [mem_univ,true_and,hg]
  have hK : IsCompact K := by
    dsimp [K]
    rw [closure_tangentSection isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) ht]
    exact isCompact_tangent_sublevel isOpen_univ convex_univ hu.contDiffOn (fun x _ => hp x) hc (mem_univ 0) t
  have hKcv : Convex ℝ K := by
    rw [hKeq]
    simpa only [mem_univ,true_and] using hcv.convex_le t
  have hK0 : (0:Space n) ∈ K := by rw [hKeq]; simpa only [mem_ofPred_eq,hzero] using ht.le
  have hKi : (interior K).Nonempty := by
    refine ⟨0,mem_interior_iff_mem_nhds.mpr ?_⟩
    have hopen : IsOpen {x | u x < t} := isOpen_lt hu.continuous continuous_const
    have hn := hopen.mem_nhds (show (0:Space n) ∈ {x | u x < t} by
      simpa only [mem_ofPred_eq,hzero] using ht)
    apply mem_of_superset hn
    intro x hx
    rw [hKeq]
    exact (show u x < t from hx).le
  have hKb : -K ⊆ C • K := by
    intro z hz
    have hz' : -z ∈ K := by simpa using hz
    have H := hbal 0 (mem_univ _) t ht (-z) hz'
    have Hz : ρ • z ∈ K := by simpa only [zero_sub,sub_zero,smul_neg,neg_neg] using H
    exact Set.mem_smul_set.mpr ⟨ρ • z,Hz,by simp [C,smul_smul,hρ.ne']⟩
  obtain ⟨L,hLin,hLout⟩ := centered_body_normalization hn hK hKcv hKi hK0 hC hKb
  let s : ℝ := (C+1)⁻¹
  have hs : 0 < s := inv_pos.mpr hCp
  let S : Space n ≃L[ℝ] Space n := (LinearEquiv.smulOfNeZero ℝ (Space n) s hs.ne').toContinuousLinearEquiv
  let A := S.trans L.symm
  have hLA (y : Space n) : L (A y) = s • y := by simp [A,S]
  let v := normalizedFunction u A t
  have hv := contDiff_normalizedFunction hu A t
  have hv0 : v 0=0 := by simp [v,normalizedFunction,hzero]
  have hdv0 : fderiv ℝ v 0=0 := by simp [v,fderiv_normalizedFunction hu,hdzero]
  have hgv (y : Space n) : tangentHeight v 0 y = v y := by simp [tangentHeight,hv0,hdv0]
  refine ⟨A,?_,?_⟩
  · intro y hy
    have hyn : ‖y‖ ≤ 1 := (mem_ball_zero_iff.mp hy).le
    have hzin : L ((2:ℝ) • A y) ∈ Metric.closedBall (0:Space n) (2/(C+1)) := by
      rw [Metric.mem_closedBall,dist_zero_right,map_smul,hLA,smul_smul,norm_smul,
        Real.norm_eq_abs,abs_of_pos (mul_pos (by norm_num) hs)]
      calc
        _ ≤ (2*s)*1 := mul_le_mul_of_nonneg_left hyn (by positivity)
        _ = 2/(C+1) := by simp [s,div_eq_mul_inv]
    obtain ⟨z,hz,hze⟩ := hLin hzin
    have hzk : (2:ℝ) • A y ∈ K := L.injective hze ▸ hz
    have hzu : u ((2:ℝ) • A y) ≤ t := by rwa [hKeq] at hzk
    have hconv := hcv.2 (mem_univ 0) (mem_univ ((2:ℝ) • A y))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
    have huAy : u (A y) ≤ t/2 := by
      simp only [smul_zero,zero_add,smul_smul,show (1:ℝ)/2*2=1 by norm_num,one_smul,
        hzero,smul_eq_mul,mul_zero,zero_add] at hconv
      linarith
    refine ⟨mem_univ y,?_⟩
    change tangentHeight v 0 y < 1
    rw [hgv]
    change t⁻¹*u (A y)<1
    have H := mul_le_mul_of_nonneg_left huAy (inv_nonneg.mpr ht.le)
    have He : t⁻¹*(t/2)=(1:ℝ)/2 := by field_simp
    rw [He] at H
    linarith
  · intro y hy
    have hyv : v y < 1 := by
      have H : tangentHeight v 0 y < 1 := hy.2
      rwa [hgv] at H
    have hyu : u (A y)<t := by
      change t⁻¹*u (A y)<1 at hyv
      rw [mul_comm,← div_eq_mul_inv] at hyv
      exact (div_lt_iff₀ ht).mp hyv |>.trans_eq (one_mul t)
    have hyK : A y ∈ K := by rw [hKeq]; exact hyu.le
    have HL := hLout ⟨A y,hyK,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right,hLA,norm_smul,Real.norm_eq_abs,abs_of_pos hs] at HL
    have HLy : ‖y‖ ≤ 2*(n:ℝ)*(C+1) := by
      have H := mul_le_mul_of_nonneg_right HL hCp.le
      have He : s*‖y‖*(C+1)=‖y‖ := by dsimp [s]; field_simp
      rwa [He] at H
    rw [Metric.mem_ball,dist_zero_right]
    dsimp [R]
    linarith

end SectionNormalizationFamily


end
end AffineBernstein
end

end OAI
