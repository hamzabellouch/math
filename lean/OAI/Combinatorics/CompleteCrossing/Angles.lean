import OAI.Combinatorics.CompleteCrossing.Plane
import OAI.Combinatorics.Crossing.ChordOrientations
import OAI.Combinatorics.Crossing.RadialBoundaryPorts
import OAI.Combinatorics.Crossing.SimilarityCoordinates
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

namespace OAI

/-! Spoke angles, circle angles, scaling, and coordinate frames. -/

section

noncomputable section
open scoped Classical
namespace Paper170

def complexPoint (a : Plane) : ℂ := ⟨a.1, a.2⟩

lemma complexPoint_injective : Function.Injective complexPoint := by
  intro a b h
  exact Prod.ext (congrArg Complex.re h) (congrArg Complex.im h)

@[simp] lemma complexPoint_zero : complexPoint 0 = 0 := rfl

@[simp] lemma complexPoint_smul (r : ℝ) (a : Plane) :
    complexPoint (r • a) = (r : ℂ) * complexPoint a := by
  apply Complex.ext <;> simp [complexPoint]

lemma complexPoint_ne_zero {a : Plane} (ha : a ≠ 0) : complexPoint a ≠ 0 := by
  exact fun h => ha (complexPoint_injective h)

lemma spokeAngle_coe (cut : ℝ) (a : Plane) (ha : a ≠ 0) :
    (spokeAngle cut a : Real.Angle) = (Complex.arg (complexPoint a) : Real.Angle) - cut := by
  change (Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a) : Real.Angle) = _
  rw [Complex.arg_mul_coe_angle (Complex.exp_ne_zero _) (complexPoint_ne_zero ha)]
  simp [Complex.arg_exp, sub_eq_add_neg, add_comm]

lemma finite_spoke_cut {ι : Type*} [Fintype ι] (a : ι → Plane) (ha : ∀ i, a i ≠ 0) :
    ∃ cut : ℝ, ∀ i, spokeAngle cut (a i) ≠ Real.pi := by
  have hreal (t : ℝ) : (Real.arctan t : Real.Angle).toReal = Real.arctan t := by
    apply Real.Angle.toReal_coe_eq_self_iff.mpr
    rcases Real.arctan_mem_Ioo t with ⟨hl, hu⟩
    constructor <;> linarith [Real.pi_pos]
  have hinj : Function.Injective (fun t : ℝ => (Real.arctan t : Real.Angle)) := by
    intro t u h
    apply Real.arctan_injective
    simpa only [hreal] using congrArg Real.Angle.toReal h
  let := Infinite.of_injective _ hinj
  let bad : ι → Real.Angle := fun i => (Complex.arg (complexPoint (a i)) : Real.Angle) - Real.pi
  obtain ⟨θ, hθ⟩ := (Set.finite_range bad).exists_notMem
  refine ⟨θ.toReal, ?_⟩
  intro i hi
  have h := spokeAngle_coe θ.toReal (a i) (ha i)
  rw [hi, Real.Angle.coe_toReal] at h
  apply hθ
  refine ⟨i, ?_⟩
  apply sub_eq_iff_eq_add.mpr
  simpa [add_comm] using (eq_sub_iff_add_eq.mp h).symm

lemma spokeAngle_eq_smul (cut : ℝ) (a b : Plane) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : spokeAngle cut a = spokeAngle cut b) : ∃ r : ℝ, 0 < r ∧ r • a = b := by
  let q := Complex.exp (-(cut : ℂ) * Complex.I)
  have hq : q ≠ 0 := Complex.exp_ne_zero _
  have ha' : q * complexPoint a ≠ 0 := mul_ne_zero hq (complexPoint_ne_zero ha)
  have hb' : q * complexPoint b ≠ 0 := mul_ne_zero hq (complexPoint_ne_zero hb)
  let r : ℝ := ‖q * complexPoint b‖ / ‖q * complexPoint a‖
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hb') (norm_pos_iff.mpr ha')
  refine ⟨r, hr, complexPoint_injective ?_⟩
  rw [complexPoint_smul]
  apply mul_left_cancel₀ hq
  have heq := (Complex.arg_eq_arg_iff ha' hb').mp h
  rw [← Complex.ofReal_div] at heq
  change ((r : ℂ) * (q * complexPoint a)) = q * complexPoint b at heq
  calc
    q * ((r : ℂ) * complexPoint a) = (r : ℂ) * (q * complexPoint a) := by ring
    _ = q * complexPoint b := heq

end Paper170

end
end

section

noncomputable section
namespace Paper170

lemma spokeAngle_smul (cut r : ℝ) (hr : 0 < r) (a : Plane) :
    spokeAngle cut (r • a) = spokeAngle cut a := by
  change Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint (r • a)) = _
  rw [complexPoint_smul, mul_left_comm, Complex.arg_real_mul _ hr]
  rfl

end Paper170

end
end

section

noncomputable section
open scoped Classical
namespace Paper170

lemma circlePoint_complex (t : ℝ) :
    complexPoint (Zarankiewicz.circlePoint t) =
      (Real.cos (2 * Real.arctan t) : ℂ) + (Real.sin (2 * Real.arctan t) : ℂ) * Complex.I := by
  have hden := Zarankiewicz.circle_denominator_pos t
  have hsqrt := Real.sq_sqrt hden.le
  have hsqrt0 : Real.sqrt (1 + t ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hden)
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    dsimp [complexPoint, Zarankiewicz.circlePoint]
    field_simp
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    dsimp [complexPoint, Zarankiewicz.circlePoint]
    field_simp
    rw [hsqrt]

lemma circlePoint_arg (t : ℝ) :
    Complex.arg (complexPoint (Zarankiewicz.circlePoint t)) = 2 * Real.arctan t := by
  rw [circlePoint_complex]
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  apply Complex.arg_cos_add_sin_mul_I
  rcases Real.arctan_mem_Ioo t with ⟨hl, hu⟩
  constructor <;> linarith

lemma circlePoint_arg_lt (a b : ℝ) :
    Complex.arg (complexPoint (Zarankiewicz.circlePoint a)) <
      Complex.arg (complexPoint (Zarankiewicz.circlePoint b)) ↔ a < b := by
  rw [circlePoint_arg, circlePoint_arg, mul_lt_mul_iff_right₀ (by norm_num : (0 : ℝ) < 2)]
  exact Real.arctan_strictMono.lt_iff_lt

def angleRotation (cut : ℝ) (a : Plane) : Plane :=
  Zarankiewicz.similarityPoint 0
    ((Complex.exp (-(cut : ℂ) * Complex.I)).re, (Complex.exp (-(cut : ℂ) * Complex.I)).im) a

lemma angleRotation_complex (cut : ℝ) (a : Plane) :
    complexPoint (angleRotation cut a) =
      Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a := by
  apply Complex.ext <;> simp [complexPoint, angleRotation, Zarankiewicz.similarityPoint, add_comm]

lemma angleRotation_unit (cut : ℝ) (a : Plane) (ha : squaredLength a = 1) :
    squaredLength (angleRotation cut a) = 1 := by
  have he : Complex.normSq (Complex.exp (-(cut : ℂ) * Complex.I)) = 1 := by
    rw [← Complex.sq_norm]
    simp [Complex.norm_exp]
  have hform (p : Plane) : Complex.normSq (complexPoint p) = squaredLength p := by
    simp [Complex.normSq_apply, complexPoint, squaredLength, pow_two]
  have h : Complex.normSq (complexPoint a) = 1 := by rw [hform, ha]
  rw [← hform]
  rw [angleRotation_complex, map_mul, he, h, mul_one]

lemma angleRotation_injective (cut : ℝ) : Function.Injective (angleRotation cut) := by
  intro a b h
  apply complexPoint_injective
  apply mul_left_cancel₀ (Complex.exp_ne_zero (-(cut : ℂ) * Complex.I))
  simpa only [angleRotation_complex] using congrArg complexPoint h

lemma angleRotation_sign (cut : ℝ) (a b c d : Plane) :
    segmentIntersection (angleRotation cut a) (angleRotation cut b)
      (angleRotation cut c) (angleRotation cut d) = segmentIntersection a b c d := by
  simp only [segmentIntersection_eq_segmentCrossingSign]
  apply Zarankiewicz.segmentCrossingSign_similarity
  intro h
  apply Complex.exp_ne_zero (-(cut : ℂ) * Complex.I)
  exact Complex.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

lemma angleRotation_parameter (cut : ℝ) (a : Plane) (ha : squaredLength a = 1)
    (hc : spokeAngle cut a ≠ Real.pi) :
    ∃ t, Zarankiewicz.circlePoint t = angleRotation cut a := by
  have hu := angleRotation_unit cut a ha
  have hx : (angleRotation cut a).1 ≠ -1 := by
    intro h
    have hy : (angleRotation cut a).2 = 0 := by
      dsimp [squaredLength] at hu
      rw [h] at hu
      nlinarith [sq_nonneg (angleRotation cut a).2]
    apply hc
    change Complex.arg (Complex.exp (-(cut : ℂ) * Complex.I) * complexPoint a) = _
    rw [← angleRotation_complex]
    exact Complex.arg_eq_pi_iff.mpr ⟨by simpa only [complexPoint, h] using (by norm_num : (-1:ℝ)<0), hy⟩
  exact ⟨(angleRotation cut a).2 / (1 + (angleRotation cut a).1),
    Zarankiewicz.circlePoint_surjective_away_cut _ hu hx⟩

theorem signed_chord_formula (p : Fin 4 → Plane) (hp : Function.Injective p)
    (hc : ∀ i, squaredLength (p i) = 1) (cut : ℝ)
    (hcut : ∀ i, spokeAngle cut (p i) ≠ Real.pi) :
    segmentIntersection (p 0) (p 1) (p 2) (p 3) = (1 / 2 : ℝ) *
      (circleComparison cut (p 0) (p 2) - circleComparison cut (p 0) (p 3) -
        circleComparison cut (p 1) (p 2) + circleComparison cut (p 1) (p 3)) := by
  choose t ht using fun i => angleRotation_parameter cut (p i) (hc i) (hcut i)
  have hi : Function.Injective t := by
    intro i j hij
    apply hp
    apply angleRotation_injective cut
    rw [← ht i, ← ht j, hij]
  have hs (i j : Fin 4) : circleComparison cut (p i) (p j) = Zarankiewicz.orderSign (t i) (t j) := by
    have he (k : Fin 4) : spokeAngle cut (p k) = Complex.arg (complexPoint (Zarankiewicz.circlePoint (t k))) := by
      rw [ht, angleRotation_complex]
      rfl
    simp only [circleComparison, he, circlePoint_arg_lt, Zarankiewicz.orderSign]
  rw [← angleRotation_sign cut, ← ht 0, ← ht 1, ← ht 2, ← ht 3,
    segmentIntersection_eq_segmentCrossingSign,
    Zarankiewicz.circle_chord_pairing _ _ _ _ (hi.ne (by decide)) (hi.ne (by decide))
      (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide)) (hi.ne (by decide))]
  simp only [hs]
  ring

end Paper170

end
end

section

noncomputable section
open Set
open scoped Classical
namespace Paper170

variable {V E : Type} {G : Graph V E}

lemma outwardSpoke_ne_zero (N : NormalizedDrawing G) (v : V) (e : E) :
    outwardSpoke N v e ≠ 0 := by
  unfold outwardSpoke
  split_ifs
  · exact (N.polygonal e).direction_ne_zero (N.edge_injective e) 0 (N.polygonal e).positive
  · have h := (N.polygonal e).direction_ne_zero (N.edge_injective e)
      ((N.polygonal e).pieces - 1) (by have := (N.polygonal e).positive; omega)
    have hi : (N.polygonal e).pieces - 1 + 1 = (N.polygonal e).pieces := by
      have := (N.polygonal e).positive
      omega
    rw [hi] at h
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp h))

lemma outwardSpoke_interior (N : NormalizedDrawing G) (v : V) (e : G.IncidentEdge v)
    (t : ℝ) (ht : 0 < t ∧ t < 1) :
    N.vertex v + t • outwardSpoke N v e.val ∈ edgeInterior N.toContinuousDrawing e.val := by
  by_cases hs : G.src e.val = v
  · have h := (N.polygonal e.val).segment_mem_interior N.toContinuousDrawing e.val
      ⟨0, (N.polygonal e.val).positive⟩ t ht
    have hp : (N.polygonal e.val).vertices 0 = N.vertex v := by
      simpa [hs] using (N.polygonal e.val).vertices_first
    convert h using 1
    rw [outwardSpoke, ite_eq_left hs, hp]
    simp only [segmentPoint]
    module
  · have hd : G.dst e.val = v := e.property.resolve_left hs
    have hi : (N.polygonal e.val).pieces - 1 + 1 = (N.polygonal e.val).pieces := by
      have := (N.polygonal e.val).positive
      omega
    have h := (N.polygonal e.val).segment_mem_interior N.toContinuousDrawing e.val
      ⟨(N.polygonal e.val).pieces - 1, by have := (N.polygonal e.val).positive; omega⟩
      (1-t) ⟨by linarith, by linarith⟩
    have hp : (N.polygonal e.val).vertices (N.polygonal e.val).pieces = N.vertex v := by
      simpa [hd] using (N.polygonal e.val).vertices_last
    simp only [hi, hp] at h
    convert h using 1
    rw [outwardSpoke, ite_eq_right hs, hp]
    simp only [segmentPoint]
    module

lemma spokeAngle_injective (N : NormalizedDrawing G) (v : V) (cut : ℝ) :
    Function.Injective (fun e : G.IncidentEdge v => spokeAngle cut (outwardSpoke N v e.val)) := by
  intro e f h
  by_contra hne
  have hef : e.val ≠ f.val := fun h => hne (Subtype.ext h)
  have hadj : G.src e.val = G.src f.val ∨ G.src e.val = G.dst f.val ∨
      G.dst e.val = G.src f.val ∨ G.dst e.val = G.dst f.val := by
    rcases e.property with he | he <;> rcases f.property with hf | hf <;> grind
  obtain ⟨r, hr, heq⟩ := spokeAngle_eq_smul cut (outwardSpoke N v e.val)
    (outwardSpoke N v f.val) (outwardSpoke_ne_zero N v e.val) (outwardSpoke_ne_zero N v f.val) h
  have hden : 0 < 1+r := by linarith
  have ht : 0 < 1/(1+r) ∧ 1/(1+r) < 1 := by
    constructor
    · exact div_pos zero_lt_one hden
    · exact (div_lt_one hden).mpr (by linarith)
  have hu : 0 < r/(1+r) ∧ r/(1+r) < 1 := by
    constructor
    · exact div_pos hr hden
    · exact (div_lt_one hden).mpr (by linarith)
  have hx := outwardSpoke_interior N v e (r/(1+r)) hu
  have hy := outwardSpoke_interior N v f (1/(1+r)) ht
  have hxy : N.vertex v + (1/(1+r)) • outwardSpoke N v f.val =
      N.vertex v + (r/(1+r)) • outwardSpoke N v e.val := by
    rw [← heq, smul_smul]
    congr 2
    ring
  rw [hxy] at hy
  exact Set.disjoint_left.mp (N.no_adjacent e.val f.val hef hadj) hx hy

theorem spoke_orders_exist [Fintype V] [Fintype E] (G : Graph V E)
    (N : NormalizedDrawing G) : Nonempty (SpokeOrders N) := by
  have hc (v : V) : ∃ cut : ℝ, ∀ e : G.IncidentEdge v,
      spokeAngle cut (outwardSpoke N v e.val) ≠ Real.pi :=
    finite_spoke_cut _ (fun e => outwardSpoke_ne_zero N v e.val)
  choose cut hcut using hc
  exact ⟨{
    cut := cut
    order := fun v => LinearOrder.lift' _ (spokeAngle_injective N v (cut v))
    cut_avoids := hcut
    compatible := fun _ _ _ => Iff.rfl
  }⟩

end Paper170

end
end

section

noncomputable section
open Zarankiewicz
namespace Paper170

theorem complexPoint_similarity (o u x : Plane) :
    complexPoint (similarityPoint o u x)=complexPoint o+complexPoint u*complexPoint x := by
  apply Complex.ext <;> simp [complexPoint,similarityPoint,add_comm]

def angleCoordinateFrame (cut radius : ℝ) : Plane :=
  radius • (((Complex.exp (-(cut:ℂ)*Complex.I))⁻¹).re,
    ((Complex.exp (-(cut:ℂ)*Complex.I))⁻¹).im)

theorem complexPoint_angleCoordinateFrame (cut radius : ℝ) :
    complexPoint (angleCoordinateFrame cut radius)=
      (radius:ℂ)*(Complex.exp (-(cut:ℂ)*Complex.I))⁻¹ := by
  rw [angleCoordinateFrame,complexPoint_smul]
  rfl

theorem angleCoordinateFrame_length (cut radius : ℝ) :
    squaredLength (angleCoordinateFrame cut radius)=radius^2 := by
  have hq : Complex.normSq (Complex.exp (-(cut:ℂ)*Complex.I))=1 := by
    rw [← Complex.sq_norm]
    simp [Complex.norm_exp]
  have hnorm (p : Plane) : squaredLength p=Complex.normSq (complexPoint p) := by
    simp [complexPoint,squaredLength,Complex.normSq_apply,pow_two]
  rw [hnorm,complexPoint_angleCoordinateFrame,map_mul,map_inv₀,hq,inv_one,mul_one]
  simp [Complex.normSq_apply,pow_two]

theorem angleCoordinateFrame_ne_zero (cut radius : ℝ) (hr : 0<radius) :
    angleCoordinateFrame cut radius≠0 := by
  intro he
  have hl := angleCoordinateFrame_length cut radius
  rw [he] at hl
  have hz : squaredLength (0:Plane)=0 := by norm_num [squaredLength]
  rw [hz] at hl
  nlinarith

theorem angleCoordinateFrame_point (cut radius : ℝ) (hr : 0<radius) (o x : Plane) :
    similarityPoint o (angleCoordinateFrame cut radius)
      (angleRotation cut (radius⁻¹ • (x-o)))=x := by
  apply complexPoint_injective
  rw [complexPoint_similarity,complexPoint_angleCoordinateFrame,angleRotation_complex,
    complexPoint_smul]
  have hsub : complexPoint (x-o)=complexPoint x-complexPoint o := rfl
  rw [hsub]
  have hr' : (radius:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have hq : Complex.exp (-(cut:ℂ)*Complex.I)≠0 := Complex.exp_ne_zero _
  rw [Complex.ofReal_inv]
  field_simp
  ring

end Paper170

end
end

end OAI
