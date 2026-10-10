import OAI.Geometry.NodalSets.Elliptic.RealPhaseJet

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Metric
open scoped ContDiff
noncomputable section

lemma compact_moving_derivative_bound {T E : Type*} [TopologicalSpace T] [CompactSpace T]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Coord → E) (hf : ContDiff ℝ ∞ f) (y : T → Coord) (hy : Continuous y) (r : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ t x, ‖x-y t‖ ≤ r → ‖iteratedFDeriv ℝ k f x‖ ≤ C := by
  have hc : Continuous (fun z : T × Coord ↦ iteratedFDeriv ℝ k f (y z.1+z.2)) :=
    (hf.continuous_iteratedFDeriv (by exact_mod_cast (show (k:ℕ∞) ≤ ⊤ from le_top))).comp
      ((hy.comp continuous_fst).add continuous_snd)
  obtain ⟨C,hC,hb⟩ := ((isCompact_univ.prod (isCompact_closedBall (0:Coord) r)).image hc).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro t x hx
  have hh := hb _ (show iteratedFDeriv ℝ k f (y t+(x-y t)) ∈
      (fun z : T × Coord ↦ iteratedFDeriv ℝ k f (y z.1+z.2)) '' (univ ×ˢ closedBall 0 r) from
    ⟨(t,x-y t),⟨mem_univ _,by simpa using hx⟩,rfl⟩)
  simpa using hh

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_phase_gradient_remainders (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0) :
    ∃ delta > 0, ∃ C > 0, ∀ t x v, ‖x-y t.1‖ ≤ delta →
      |(fderiv ℝ (b.phase t) x v).re - (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤
        C*‖x-y t.1‖^2*‖v‖ ∧
      |(fderiv ℝ (b.phase t) x v).im - g (y t.1) (d.q t.1 t.2) v| ≤ C*‖x-y t.1‖*‖v‖ := by
  obtain ⟨delta,hd,Cp,hCp,D,hD,hb⟩ := b.uniform_spatial_bounds hg hp hy 3
  obtain ⟨Cs,hCs,hSb⟩ := compact_moving_derivative_bound S hS y hy delta 3
  have hf (t : T × Fin 3) (x : Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ContDiffAt ℝ ∞ (b.realDefect t) x :=
    (Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1).sub hS.contDiffAt
  have hthird (t : T × Fin 3) (x : Coord) (hx : ‖x-y t.1‖ ≤ delta) :
      ‖iteratedFDeriv ℝ 3 (b.realDefect t) x‖ ≤ Cp+Cs := by
    have hphi := (hb t x hx).2.1
    have hrp : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp _ hphi
    change ‖iteratedFDeriv ℝ 3 ((fun z ↦ (b.phase t z).re)-S) x‖ ≤ _
    rw [iteratedFDeriv_sub_apply
      (hrp.of_le
        (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))
      (hS.contDiffAt.of_le (by change (↑(3:ℕ∞):ℕ∞ω) ≤ ↑(⊤:ℕ∞); exact WithTop.coe_le_coe.mpr le_top))]
    exact (norm_sub_le _ _).trans (add_le_add
      ((realPart_iterated_norm_le _ _ hphi 3).trans ((hb t x hx).2.2.2.1 3 le_rfl)) (hSb t.1 x hx))
  refine ⟨delta,hd,Cp+Cs,by positivity,?_⟩
  intro t x v hx
  have hq := first_order_remainder_bound (fderiv ℝ (b.realDefect t)) (y t.1) delta (Cp+Cs)
    (by positivity) (fun z hz ↦ (hf t z hz).fderiv_right (by simp))
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
      exact hthird t z hz) x hx
  have hv := (fderiv ℝ (b.realDefect t) x - fderiv ℝ (b.realDefect t) (y t.1) -
    fderiv ℝ (fderiv ℝ (b.realDefect t)) (y t.1) (x-y t.1)).le_opNorm v
  have hvb := hv.trans (mul_le_mul_of_nonneg_right hq (norm_nonneg v))
  rw [b.real_defect_first hp hS hp0] at hvb
  simp only [sub_zero,sub_apply] at hvb
  rw [b.real_defect_second hg hs hp hS hp0] at hvb
  have hdx : fderiv ℝ (b.realDefect t) x v = (fderiv ℝ (b.phase t) x v).re-fderiv ℝ S x v := by
    have hrp : ContDiffAt ℝ ∞ (fun z ↦ (b.phase t z).re) x :=
      Complex.reCLM.contDiff.contDiffAt.comp _ (hb t x hx).2.1
    unfold realDefect
    rw [fderiv_fun_sub
      (hrp.differentiableAt (by simp))
      (hS.differentiable (by simp) x),sub_apply,
      realPart_fderiv _ _ ((hb t x hx).2.1.differentiableAt (by simp))]
  rw [hdx] at hvb
  have hreal : |(fderiv ℝ (b.phase t) x v).re - (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤
      (Cp+Cs)*‖x-y t.1‖^2*‖v‖ := by
    convert hvb using 1
    congr 1
    ring
  have hphi := norm_sub_le_on_closedBall (fderiv ℝ (b.phase t)) (y t.1) delta Cp hCp.le
    (fun z hz ↦ (((hb t z hz).2.1.fderiv_right (by simp)) :
      ContDiffAt ℝ ∞ (fderiv ℝ (b.phase t)) z).differentiableAt (by simp))
    (fun z hz ↦ by
      rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
      exact (hb t z hz).2.2.2.1 2 (by omega)) hd.le x hx
  have hvec := ((fderiv ℝ (b.phase t) x-fderiv ℝ (b.phase t) (y t.1)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hphi (norm_nonneg v))
  have him := (Complex.abs_im_le_norm _).trans hvec
  simp only [sub_apply,Complex.sub_im] at him
  rw [b.phase_first hp hp0] at him
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,zero_mul,one_mul,zero_add] at him
  exact ⟨hreal,him.trans (by gcongr; linarith)⟩

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
