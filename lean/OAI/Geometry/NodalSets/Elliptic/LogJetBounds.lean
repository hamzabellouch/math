import OAI.Geometry.NodalSets.Elliptic.HalfScaleLemmas
import OAI.Geometry.NodalSets.Elliptic.Logarithm
import OAI.Geometry.NodalSets.Elliptic.PhaseBounds

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]
variable {g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ} {w S : Coord → ℝ}
variable {y : T → Coord} {d : SourceFrameTriple g S y} {m J K k0 : ℕ}
namespace TripleSourceWaveData
variable (b : TripleSourceWaveData g w S y d m J K k0)

theorem uniform_logarithmic_jet_estimates (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (hS : ContDiff ℝ ∞ S) (hy : Continuous y) (hp0 : ∀ t, metricGradient g S (y t) ≠ 0)
    (L : ℝ) (hL : 0 < L) :
    ∃ Ca > 0, ∃ Cr > 0, ∃ Ci > 0, ∀ᶠ N : ℝ in atTop, ∀ t x,
      ‖x-y t.1‖ ≤ L*N^(-1/2:ℝ) →
      ‖b.amplitude N t x-1‖ ≤ Ca*N^(-1/2:ℝ) ∧
      (1/2:ℝ) ≤ ‖b.amplitude N t x‖ ∧ ‖b.amplitude N t x‖ ≤ 3/2 ∧
      b.wave N t x ≠ 0 ∧ ∀ v,
      |(normalizedLogJet N (b.wave N t) x v).re -
        (fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v)| ≤ Cr/N*‖v‖ ∧
      |(normalizedLogJet N (b.wave N t) x v).im - g (y t.1) (d.q t.1 t.2) v| ≤
        Ci*N^(-1/2:ℝ)*‖v‖ := by
  obtain ⟨ra,hra,A,hA,D,hD,ha⟩ := b.uniform_amplitude_bounds hg hp hy
  obtain ⟨rp,hrp,P,hP,hphase⟩ := b.uniform_phase_gradient_remainders hg hs hp hS hy hp0
  refine ⟨A*L,by positivity,P*L^2+2*A,by positivity,P*L+2*A,by positivity,?_⟩
  filter_upwards [half_scale_eventually L D (min ra rp) (lt_min hra hrp)] with N hn
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one hn.1
  intro t x hx
  have hxa : ‖x-y t.1‖ ≤ ra := (hx.trans hn.2.1).trans (min_le_left _ _)
  have hxp : ‖x-y t.1‖ ≤ rp := (hx.trans hn.2.1).trans (min_le_right _ _)
  obtain ⟨hxt,hInv,_,hamp⟩ := ha t x hxa
  obtain ⟨hsm,hnear,hlo,hup,hne,hder⟩ := hamp N hn.1
  have hcut : ‖(b.F t).symm x‖ < N^(-1/3:ℝ) :=
    (hInv.trans (mul_le_mul_of_nonneg_left hx (by linarith))).trans_lt hn.2.2
  have hsq : ‖x-y t.1‖^2 ≤ L^2/N := by
    have hh := pow_le_pow_left₀ (norm_nonneg _) hx 2
    rw [mul_pow,half_scale_square hN] at hh
    simpa only [div_eq_mul_inv] using hh
  have hnear' : ‖b.amplitude N t x-1‖ ≤ (A*L)*N^(-1/2:ℝ) :=
    hnear.trans (by calc
      A*‖x-y t.1‖ ≤ A*(L*N^(-1/2:ℝ)) := mul_le_mul_of_nonneg_left hx hA.le
      _ = _ := by ring)
  refine ⟨hnear',hlo,hup,(b.wave_log_jet N hN t x 0 hxt hcut hne).1,?_⟩
  intro v
  have he := (b.wave_log_jet N hN t x v hxt hcut hne).2
  have hc := log_amplitude_correction_bound (b.amplitude N t x)
    (fderiv ℝ (b.amplitude N t) x v) N (A*‖v‖) hN (by positivity) hlo
    (((fderiv ℝ (b.amplitude N t) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hder (norm_nonneg v)))
  obtain ⟨hr,hi⟩ := hphase t x v hxp
  rw [he,Complex.add_re,Complex.add_im]
  constructor
  · have hcR := (Complex.abs_re_le_norm _).trans hc
    calc
      _ = |((fderiv ℝ (b.phase t) x v).re-(fderiv ℝ S x v-b.eta t*g (y t.1) (x-y t.1) v))+
          ((N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x)).re| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hr hcR)
      _ ≤ P*(L^2/N)*‖v‖+2*(A*‖v‖)/N := by gcongr
      _ = _ := by ring
  · have hcI := (Complex.abs_im_le_norm _).trans hc
    calc
      _ = |((fderiv ℝ (b.phase t) x v).im-g (y t.1) (d.q t.1 t.2) v)+
          ((N:ℂ)⁻¹*(fderiv ℝ (b.amplitude N t) x v/b.amplitude N t x)).im| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hi hcI)
      _ = P*‖x-y t.1‖*‖v‖+(2*A*‖v‖)*N⁻¹ := by ring
      _ ≤ P*(L*N^(-1/2:ℝ))*‖v‖+(2*A*‖v‖)*N^(-1/2:ℝ) := by
        gcongr
        exact inverse_le_half_scale hn.1
      _ = _ := by ring

end TripleSourceWaveData
end
end Yau.Geometry

end OAI
