import OAI.Geometry.NodalSets.Elliptic.RealWeightedElliptic

namespace OAI

noncomputable section

namespace Yau.Geometry

open Filter
open scoped Topology ContDiff

lemma realCoordPartial_eventuallyEq {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord}
    (h : f =ᶠ[𝓝 x] g) (i : Fin 4) :
    (fun y ↦ Yau.coordPartial f y i) =ᶠ[𝓝 x] (fun y ↦ Yau.coordPartial g y i) := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
  simp only [Yau.coordPartial,hy]

lemma realWeightedElliptic_eventuallyEq (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord} (h : f =ᶠ[𝓝 x] g) :
    realWeightedElliptic gamma B f =ᶠ[𝓝 x] realWeightedElliptic gamma B g := by
  have hflux (i : Fin 4) :
      (fun y ↦ gamma y*realMatrixFlux B f y i) =ᶠ[𝓝 x]
        (fun y ↦ gamma y*realMatrixFlux B g y i) := by
    filter_upwards [eventually_all.mpr (fun j ↦ realCoordPartial_eventuallyEq h j)] with y hy
    simp only [realMatrixFlux,hy]
  filter_upwards [eventually_all.mpr (fun i ↦ realCoordPartial_eventuallyEq (hflux i) i)] with y hy
  simp only [realWeightedElliptic,Yau.weightedDiv,Yau.coordDiv,hy]

lemma realWeightedElliptic_zero (gamma : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) :
    realWeightedElliptic gamma B (fun _ ↦ 0) = 0 := by
  have h : realMatrixFlux B (fun _ ↦ 0) = fun _ _ ↦ 0 := by
    funext x i; simp [realMatrixFlux,Yau.coordPartial]
  funext x
  simp [realWeightedElliptic,h,Yau.weightedDiv,Yau.coordDiv,Yau.coordPartial]

def realEllipticResidual (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (x : Yau.Jets.Coord) : ℝ := realWeightedElliptic gamma B f x+potential x*f x

lemma realEllipticResidual_eventuallyEq (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    {f g : Yau.Jets.Coord → ℝ} {x : Yau.Jets.Coord} (h : f =ᶠ[𝓝 x] g) :
    realEllipticResidual gamma potential B f =ᶠ[𝓝 x] realEllipticResidual gamma potential B g := by
  filter_upwards [realWeightedElliptic_eventuallyEq gamma B h,h] with y hL hy
  simp only [realEllipticResidual,hL,hy]

lemma realEllipticResidual_zero (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) :
    realEllipticResidual gamma potential B (fun _ ↦ 0) = 0 := by
  funext x; simp [realEllipticResidual,realWeightedElliptic_zero]

lemma realEllipticResidual_tsupport (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ) :
    tsupport (realEllipticResidual gamma potential B f) ⊆ tsupport f := by
  intro x hx
  by_contra hn
  have he := realEllipticResidual_eventuallyEq gamma potential B
    (notMem_tsupport_iff_eventuallyEq.mp hn)
  change realEllipticResidual gamma potential B f =ᶠ[𝓝 x]
    realEllipticResidual gamma potential B (fun _ ↦ 0) at he
  rw [realEllipticResidual_zero] at he
  exact (notMem_tsupport_iff_eventuallyEq.mpr he) hx

lemma realEllipticResidual_smooth (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0) (hp : ContDiff ℝ ∞ potential)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (realEllipticResidual gamma potential B f) :=
  (realWeightedElliptic_smooth gamma B f hg hgn hB hf).add (hp.mul hf)

lemma realEllipticResidual_compact (gamma potential : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ) (f : Yau.Jets.Coord → ℝ)
    (hc : HasCompactSupport f) : HasCompactSupport (realEllipticResidual gamma potential B f) :=
  (realWeightedElliptic_compact gamma B f hc).add hc.mul_left

open Matrix MeasureTheory
open scoped ContDiff

theorem real_weighted_square_identity
    (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j))
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (t : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x -
        t*Yau.weightedSkewTransport gamma V v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x)^2) +
      t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) +
      2*t*(∫ x, gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) +
      2*t^3*(∫ x, gamma x*Yau.pairing q V x*v x^2) := by
  let L := realWeightedElliptic gamma B v
  let T := Yau.weightedSkewTransport gamma V v
  let S := fun x ↦ L x+t^2*q x*v x
  have hL : ContDiff ℝ ∞ L := realWeightedElliptic_smooth gamma B v hg hgn hB hv
  have hLc : HasCompactSupport L := realWeightedElliptic_compact gamma B v hc
  have hT : ContDiff ℝ ∞ T := Yau.weightedSkewTransport_smooth gamma V v hg hgn hV hv
  have hTc : HasCompactSupport T := Yau.weightedSkewTransport_compact gamma V v hc
  have hS : ContDiff ℝ ∞ S := hL.add ((contDiff_const.mul hq).mul hv)
  have hSc : HasCompactSupport S := hLc.add hc.mul_left
  have hcS2 : HasCompactSupport (fun x ↦ S x^2) := by
    convert hSc.mul_right (f' := S) using 1; first | rfl | (ext x; simp [pow_two])
  have hcT2 : HasCompactSupport (fun x ↦ T x^2) := by
    convert hTc.mul_right (f' := T) using 1; first | rfl | (ext x; simp [pow_two])
  have hiS : Integrable (fun x ↦ gamma x*(S x)^2) :=
    (hg.mul (hS.pow 2)).continuous.integrable_of_hasCompactSupport hcS2.mul_left
  have hiT : Integrable (fun x ↦ gamma x*(T x)^2) :=
    (hg.mul (hT.pow 2)).continuous.integrable_of_hasCompactSupport hcT2.mul_left
  have hiTL := Yau.compact_weighted_product_integrable gamma T L hg.continuous hT.continuous hL.continuous hTc
  have hiq : Integrable (fun x ↦ gamma x*q x*v x*T x) :=
    (((hg.mul hq).mul hv).mul hT).continuous.integrable_of_hasCompactSupport hc.mul_left.mul_right
  have hexpand : (fun x ↦ gamma x*(L x+t^2*q x*v x-t*T x)^2) =
      (fun x ↦ ((gamma x*(S x)^2 + t^2*(gamma x*(T x)^2)) -
        2*t*(gamma x*T x*L x)) - 2*t^3*(gamma x*q x*v x*T x)) := by
    funext x; dsimp [S]; ring
  change (∫ x, gamma x*(L x+t^2*q x*v x-t*T x)^2) = _
  rw [hexpand,integral_sub
      (f := fun x ↦ gamma x*(S x)^2 + t^2*(gamma x*(T x)^2) - 2*t*(gamma x*T x*L x))
      (g := fun x ↦ 2*t^3*(gamma x*q x*v x*T x))
      ((hiS.add (hiT.const_mul (t^2))).sub (hiTL.const_mul (2*t)))
      (hiq.const_mul (2*t^3)),
    integral_sub (f := fun x ↦ gamma x*(S x)^2 + t^2*(gamma x*(T x)^2))
      (g := fun x ↦ 2*t*(gamma x*T x*L x))
      (hiS.add (hiT.const_mul (t^2))) (hiTL.const_mul (2*t)),
    integral_add hiS (hiT.const_mul (t^2))]
  simp only [integral_const_mul]
  have hgreen := (real_weighted_elliptic_green gamma B T v hg hgn hB hT hv hTc).2.2
  have hmult := Yau.weighted_transport_multiplier gamma q v V hg hgn hq hv hc hV
  change (∫ x, gamma x*T x*L x) = _ at hgreen
  change (∫ x, gamma x*q x*v x*T x) = _ at hmult
  rw [hgreen,hmult]
  change (∫ x, gamma x*(S x)^2) + _ - _ - _ = (∫ x, gamma x*(S x)^2) + _ + _ + _
  ring

end Yau.Geometry

end

end OAI
