import OAI.Geometry.NodalSets.Elliptic.RealEllipticLocalityLemmas
import OAI.Geometry.NodalSets.Elliptic.RealMatrixEnergyProducts

namespace OAI

namespace Yau.Geometry
open Matrix MeasureTheory
open scoped ContDiff
noncomputable section

theorem real_weighted_commutator_energy
    (gamma v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) :
    2*(∫ x, gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) =
      2*(∫ x, gamma x*realTransportDeformation B V v x) -
      (∫ x, gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) := by
  let E := realMatrixEnergy B v v
  let r := Yau.weightedDiv gamma V
  let C := fun x ↦ gamma x*v x*realMatrixEnergy B r v x
  have hE : ContDiff ℝ ∞ E := realMatrixEnergy_smooth B hB v v hv hv
  have hEc : HasCompactSupport E := realMatrixEnergy_compact_left B v v hc
  have hr : ContDiff ℝ ∞ r := Yau.weightedDiv_smooth hg hgn hV
  have hiA : Integrable (fun x ↦ gamma x*Yau.pairing E V x) :=
    (hg.mul (Yau.pairing_smooth hE hV)).continuous.integrable_of_hasCompactSupport
      (Yau.real_pairing_compact E V hEc).mul_left
  have hiD : Integrable (fun x ↦ gamma x*realTransportDeformation B V v x) :=
    (hg.mul (realTransportDeformation_smooth B V v hB hV hv)).continuous.integrable_of_hasCompactSupport
      (realTransportDeformation_compact B V v hc).mul_left
  have hiR : Integrable (fun x ↦ gamma x*r x*E x) :=
    ((hg.mul hr).mul hE).continuous.integrable_of_hasCompactSupport hEc.mul_left
  have hiC : Integrable C := Yau.compact_weighted_product_integrable gamma v (realMatrixEnergy B r v)
    hg.continuous hv.continuous (realMatrixEnergy_smooth B hB r v hr hv).continuous hc
  have hzero := (Yau.compact_weighted_integration_by_parts gamma E hg hgn hE hEc V hV).2.2
  have hreorder : (fun x ↦ gamma x*E x*Yau.weightedDiv gamma V x) =
      (fun x ↦ gamma x*r x*E x) := by funext x; dsimp [r]; ring
  rw [hreorder] at hzero
  have hpoint : (fun x ↦ gamma x*realMatrixEnergy B (Yau.weightedSkewTransport gamma V v) v x) =
      (fun x ↦ ((gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x) +
        gamma x*r x*E x) + C x) := by
    funext x
    rw [realMatrixEnergy_skew_transport gamma B V v hg hgn hB hs hV hv]
    dsimp [E,r,C]
    ring
  have hcsq : HasCompactSupport (fun x ↦ v x^2) := by
    convert hc.mul_right (f' := v) using 1
    first | rfl | (ext point; simp [pow_two])
  have hgreen := (real_weighted_elliptic_green gamma B (fun x ↦ v x^2) r
    hg hgn hB (hv.pow 2) hr hcsq).2.2
  have hsquare : (fun x ↦ gamma x*realMatrixEnergy B (fun y ↦ v y^2) r x) =
      (fun x ↦ 2*C x) := by
    funext x
    rw [show (fun y ↦ v y^2) = (fun y ↦ v y*v y) by funext y; ring,
      realMatrixEnergy_mul_left B v v r hv hv,
      realMatrixEnergy_symmetric B hs v r]
    dsimp [C]; ring
  rw [hsquare,integral_const_mul] at hgreen
  rw [hpoint,integral_add
      (f := fun x ↦ gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x + gamma x*r x*E x)
      (g := C) ((hiA.add hiD).add hiR) hiC,
    integral_add (f := fun x ↦ gamma x*Yau.pairing E V x + gamma x*realTransportDeformation B V v x)
      (g := fun x ↦ gamma x*r x*E x) (hiA.add hiD) hiR,
    integral_add hiA hiD,hzero]
  change 2*((-(∫ x, gamma x*r x*E x)+(∫ x, gamma x*realTransportDeformation B V v x)) +
      (∫ x, gamma x*r x*E x)+(∫ x, C x)) =
      2*(∫ x, gamma x*realTransportDeformation B V v x) -
      (∫ x, gamma x*v x^2*realWeightedElliptic gamma B r x)
  linarith only [hgreen]

theorem real_weighted_commutator_identity
    (gamma q v : Yau.Jets.Coord → ℝ)
    (B : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
    (V : Yau.Jets.Coord → Yau.Jets.Coord)
    (hg : ContDiff ℝ ∞ gamma) (hgn : ∀ x, gamma x ≠ 0)
    (hq : ContDiff ℝ ∞ q) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport v)
    (hB : ∀ i j, ContDiff ℝ ∞ (fun x ↦ B x i j)) (hs : ∀ x i j, B x i j = B x j i)
    (hV : ∀ i, ContDiff ℝ ∞ (fun x ↦ V x i)) (t : ℝ) :
    (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x -
        t*Yau.weightedSkewTransport gamma V v x)^2) =
      (∫ x, gamma x*(realWeightedElliptic gamma B v x + t^2*q x*v x)^2) +
      t^2*(∫ x, gamma x*(Yau.weightedSkewTransport gamma V v x)^2) +
      2*t*(∫ x, gamma x*realTransportDeformation B V v x) -
      t*(∫ x, gamma x*v x^2*realWeightedElliptic gamma B (Yau.weightedDiv gamma V) x) +
      2*t^3*(∫ x, gamma x*Yau.pairing q V x*v x^2) := by
  rw [real_weighted_square_identity gamma q v B V hg hgn hq hv hc hB hV]
  have he := real_weighted_commutator_energy gamma v B V hg hgn hv hc hB hs hV
  have he' := congrArg (fun z : ℝ ↦ t*z) he
  nlinarith only [he']

end
end Yau.Geometry

end OAI
