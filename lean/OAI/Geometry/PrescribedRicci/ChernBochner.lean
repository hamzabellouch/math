import Mathlib
import OAI.Geometry.PrescribedRicci.ChernPairDifferential
import OAI.Geometry.PrescribedRicci.KahlerGradientEnergy

namespace OAI

/-! Chern Bochner. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder
namespace Anticanonical.SourceSmooth.KaehlerMetric
open MongeAmpere
variable {d : ℕ} {n : Type*} [Fintype n]

lemma bar_covHol {C : Coordinates d → Fin d → Matrix n n ℂ} {f : Coordinates d → n → ℂ}
    {z : Coordinates d} (hC : ∀ a i j, ContDiffAt ℝ ∞ (fun y => C y a i j) z)
    (hf : ∀ i, ContDiffAt ℝ ∞ (fun y => f y i) z) (a b : Fin d) :
    barVector (fun y => covHol C f y a) z b =
      covHol C (fun y => barVector f y b) z a+
        barArray (fun y => C y a) z b*ᵥ f z := by
  ext i
  have hc (j : n) : DifferentiableAt ℝ (fun y => C y a i j*f y j) z :=
    ((hC a i j).differentiableAt (by simp)).fun_mul ((hf j).differentiableAt (by simp))
  change barDeriv (fun y => holDeriv (fun w => f w i) y a + ∑ j, C y a i j*f y j) z b =
    holDeriv (fun y => barDeriv (fun w => f w i) y b) z a+
      ∑ j, C z a i j*barDeriv (fun y => f y j) z b+
        ∑ j, barDeriv (fun y => C y a i j) z b*f z j
  rw [barDeriv_add ((contDiffAt_holDeriv (hf i) a).differentiableAt (by simp))
      (DifferentiableAt.fun_sum (u:=Finset.univ) (fun j _ => hc j)),
    barDeriv_sum hc,scalar_bar_hol_comm (hf i)]
  simp_rw [barDeriv_mul ((hC a i _).differentiableAt (by simp)) ((hf _).differentiableAt (by simp))]
  rw [Finset.sum_add_distrib]
  abel

lemma hermPair_bochners_identity {s : Set (Coordinates d)} (hs : IsOpen s)
    {K : Coordinates d → Matrix n n ℂ} {C : Coordinates d → Fin d → Matrix n n ℂ}
    {f : Coordinates d → n → ℂ} {z : Coordinates d} (hz : z ∈ s)
    (hK : ∀ y ∈ s, ∀ i j, ContDiffAt ℝ ∞ (fun w => K w i j) y)
    (hC : ∀ y ∈ s, ∀ a i j, ContDiffAt ℝ ∞ (fun w => C w a i j) y)
    (hf : ∀ y ∈ s, ∀ i, ContDiffAt ℝ ∞ (fun w => f w i) y)
    (hhol : ∀ y ∈ s, ∀ a, holArray K y a = K y*C y a)
    (hbar : ∀ y ∈ s, ∀ a, barArray K y a = (C y a)ᴴ*K y) (a b : Fin d) :
    barDeriv (fun y => holDeriv (fun w => hermPair (K w) (f w) (f w)) y a) z b =
      hermPair (K z) (covHol C (fun y => barVector f y a) z b) (f z)+
      hermPair (K z) (barVector f z a) (barVector f z b)+
      hermPair (K z) (covHol C f z b) (covHol C f z a)+
      hermPair (K z) (f z) (covHol C (fun y => barVector f y b) z a)+
      hermPair (K z) (f z) (barArray (fun y => C y a) z b*ᵥ f z) := by
  have hKz := hK z hz
  have hfz := hf z hz
  have hbarf (u : Fin d) (i : n) : ContDiffAt ℝ ∞ (fun y => barVector f y u i) z :=
    contDiffAt_barDeriv (hfz i) u
  have hcovf (u : Fin d) := covHol_smooth (hC z hz) hfz u
  have he : (fun y => holDeriv (fun w => hermPair (K w) (f w) (f w)) y a) =ᶠ[nhds z]
      (fun y => hermPair (K y) (barVector f y a) (f y)+
        hermPair (K y) (f y) (covHol C f y a)) := by
    filter_upwards [hs.mem_nhds hz] with y hy
    exact hermPair_hol_compatible
      (fun i j => (hK y hy i j).differentiableAt (by simp))
      (fun i => (hf y hy i).differentiableAt (by simp))
      (fun i => (hf y hy i).differentiableAt (by simp)) a (hhol y hy a)
  rw [barDeriv_congr he]
  rw [barDeriv_add ((hermPair_smooth hKz (hbarf a) hfz).differentiableAt (by simp))
    ((hermPair_smooth hKz hfz (hcovf a)).differentiableAt (by simp))]
  rw [hermPair_bar_compatible (fun i j => (hKz i j).differentiableAt (by simp))
      (fun i => (hbarf a i).differentiableAt (by simp))
      (fun i => (hfz i).differentiableAt (by simp)) b (hbar z hz b),
    hermPair_bar_compatible (fun i j => (hKz i j).differentiableAt (by simp))
      (fun i => (hfz i).differentiableAt (by simp))
      (fun i => (hcovf a i).differentiableAt (by simp)) b (hbar z hz b),
    bar_covHol (hC z hz) hfz,hermPair_add_right]
  abel

end Anticanonical.SourceSmooth.KaehlerMetric

end

end OAI
