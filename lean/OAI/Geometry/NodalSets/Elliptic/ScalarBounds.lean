import OAI.Geometry.NodalSets.Elliptic.FrozenPhaseLemmas
import OAI.Geometry.NodalSets.Elliptic.HalfScaleLemmas
import OAI.Geometry.NodalSets.Elliptic.Logarithm

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

lemma exp_wave_relative_norm (a phi : ℂ) (N S : ℝ) :
    ‖a*Complex.exp ((N:ℂ)*phi)‖*Real.exp (-N*S) = ‖a‖*Real.exp (N*(phi.re-S)) := by
  rw [norm_mul,Complex.norm_exp,mul_assoc,← Real.exp_add]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  congr 2
  ring

variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_relative_wave_bounds (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (hS : ContDiff ℝ ∞ S)
    (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (L : ℝ) (hL : 0 < L) :
    ∃ c > 0, ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ t x, ‖x-y t.1‖ ≤ L*N^(-1/2:ℝ) →
      c ≤ ‖b.wave N t x‖*Real.exp (-N*S x) ∧ ‖b.wave N t x‖*Real.exp (-N*S x) ≤ C := by
  obtain ⟨ra,hra,A,hA,D,hD,ha⟩ := b.uniform_amplitude_bounds hg hp hy
  obtain ⟨rp,hrp,P,hP,hphase⟩ := b.uniform_real_phase_value_bound hg hp hS hy hp0
  refine ⟨(1/2)*Real.exp (-P*L^2),by positivity,(3/2)*Real.exp (P*L^2),by positivity,?_⟩
  filter_upwards [half_scale_eventually L D (min ra rp) (lt_min hra hrp)] with N hn
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hn.1
  intro t x hx
  have hxa := (hx.trans hn.2.1).trans (min_le_left ra rp)
  have hxp := (hx.trans hn.2.1).trans (min_le_right ra rp)
  obtain ⟨hxt,hInv,_,hamp⟩ := ha t x hxa
  obtain ⟨_,_,hlo,hup,_,_⟩ := hamp N hn.1
  have hcut : ‖(b.F t).symm x‖ < N^(-1/3:ℝ) :=
    (hInv.trans (mul_le_mul_of_nonneg_left hx (by linarith))).trans_lt hn.2.2
  rw [(b.wave_germ_of_small_inverse N hN t x hxt hcut).self_of_nhds,exp_wave_relative_norm]
  have hsq : ‖x-y t.1‖^2 ≤ L^2/N := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow,half_scale_square hN] at hh
    simpa only [div_eq_mul_inv] using hh
  have hb := (hphase t x hxp).trans (mul_le_mul_of_nonneg_left hsq hP.le)
  have hb' := mul_le_mul_of_nonneg_left hb hN.le
  have hnabs : |N*((b.phase t x).re-S x)| ≤ P*L^2 := by
    rw [abs_mul,abs_of_pos hN]
    calc
      _ ≤ N*(P*(L^2/N)) := hb'
      _ = _ := by field_simp
  obtain ⟨hl,hu⟩ := abs_le.mp hnabs
  constructor
  · exact mul_le_mul hlo (Real.exp_le_exp.mpr (by linarith)) (by positivity) (norm_nonneg _)
  · exact mul_le_mul hup (Real.exp_le_exp.mpr hu) (by positivity) (by norm_num)

end TripleSourceWaveData

end
end Yau.Geometry

end OAI
