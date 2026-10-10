import Mathlib
import OAI.Combinatorics.KMedian.Model
import OAI.Combinatorics.KMedian.Instance

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable (I : Instance)
local instance completionGeometryPseudoMetricSpace : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

structure CloseCenters (G : Finset (Fin I.n)) (O : Finset (Fin I.n)) (δ : ℝ) where
  radius : ↥G → ℝ
  radius_nonneg : ∀ t, 0 ≤ radius t
  separated : ∀ t u, t ≠ u → radius t ≤ dist t.val u.val
  matchTo : ↥G → Fin I.n
  match_mem : ∀ t, matchTo t ∈ O
  close : ∀ t, dist t.val (matchTo t) < δ*radius t

namespace CloseCenters
variable {I} {G O : Finset (Fin I.n)} {δ : ℝ}

theorem match_injective (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ < 1/2) :
    Function.Injective C.matchTo := by
  intro t u he
  by_contra htu
  have ht := C.close t
  have hu := C.close u
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have hh := dist_triangle t.val (C.matchTo t) u.val
  rw [he] at ht
  rw [he,dist_comm (C.matchTo u) u.val] at hh
  have hm1 := mul_le_mul_of_nonneg_left hrt hδ
  have hm2 := mul_le_mul_of_nonneg_left hru hδ
  have hd := dist_nonneg (x:=t.val) (y:=u.val)
  have hp := mul_nonneg (show 0 ≤ 1-2*δ by linarith) hd
  linarith only [ht,hu,hh,hm1,hm2,hp]

theorem near_unique (C : CloseCenters I G O δ)
    {t u : ↥G} {j : Fin I.n} (ht : dist j t.val ≤ C.radius t/3)
    (hu : dist j u.val ≤ C.radius u/3) : t=u := by
  by_contra htu
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have htri := dist_triangle t.val j u.val
  rw [dist_comm t.val j] at htri
  have hd0 : dist t.val u.val=0 := by nlinarith only [hrt,hru,htri,ht,hu,dist_nonneg (x:=t.val) (y:=u.val)]
  have hrt0 : C.radius t=0 := by linarith only [hrt,hd0,C.radius_nonneg t]
  have hcl := C.close t
  rw [hrt0,mul_zero] at hcl
  exact (dist_nonneg (x:=t.val) (y:=C.matchTo t)).not_gt hcl

theorem near_match_best (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    {t u : ↥G} {j : Fin I.n} (ht : dist j t.val ≤ C.radius t/3) :
    dist j (C.matchTo t) ≤ dist j (C.matchTo u) := by
  by_cases htu : t=u
  · rw [htu]
  have hrt := C.separated t u htu
  have hru : C.radius u ≤ dist t.val u.val := by
    simpa only [dist_comm] using C.separated u t (Ne.symm htu)
  have hct := (C.close t).le
  have hcu := (C.close u).le
  have h1 := dist_triangle j t.val (C.matchTo t)
  have h2 := dist_triangle t.val j (C.matchTo u)
  have h3 := dist_triangle t.val (C.matchTo u) u.val
  rw [dist_comm t.val j] at h2
  rw [dist_comm (C.matchTo u) u.val] at h3
  have hm1 := mul_le_mul_of_nonneg_left hrt hδ
  have hm2 := mul_le_mul_of_nonneg_left hru hδ
  have hm3 := mul_nonneg (show 0 ≤ 1/3-2*δ by linarith)
    (dist_nonneg (x:=t.val) (y:=u.val))
  linarith only [ht,hrt,hct,hcu,h1,h2,h3,hm1,hm2,hm3]

theorem outside_connection (C : CloseCenters I G O δ) (hδ : 0 ≤ δ) (hsmall : δ ≤ 1/6)
    (t : ↥G) {j a : Fin I.n} (houter : C.radius t/3 ≤ dist j t.val)
    (ha : dist t.val a ≤ δ*C.radius t) :
    dist j a ≤ (1+12*δ)*dist j (C.matchTo t) := by
  have hct := (C.close t).le
  have h1 := dist_triangle j (C.matchTo t) t.val
  rw [dist_comm (C.matchTo t) t.val] at h1
  have h2 := dist_triangle j t.val a
  have hr : C.radius t ≤ 6*dist j (C.matchTo t) := by
    have hm := mul_nonneg (show 0 ≤ 1/6-δ by linarith) (C.radius_nonneg t)
    linarith only [houter,hct,h1,hm]
  have h3 : dist j t.val ≤ dist j (C.matchTo t)+δ*C.radius t := by linarith only [h1,hct]
  have hm := mul_le_mul_of_nonneg_left hr hδ
  nlinarith only [h2,h3,ha,hm]

end CloseCenters
end MetricKMedian.Reduction
end
end

end OAI
