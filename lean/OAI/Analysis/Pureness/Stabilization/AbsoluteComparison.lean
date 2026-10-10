import OAI.Analysis.Pureness.Stabilization.Perturbation

namespace OAI
noncomputable section
open scoped NNReal Topology
namespace CuntzTrace
variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace Positive

def abs (x : A) : Positive A := ⟨CFC.sqrt (star x * x), CFC.sqrt_nonneg _⟩
@[simp] lemma abs_sq (x : A) : (abs x).1 * (abs x).1 = star x * x :=
  CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)
end Positive

lemma squareCutMultiplier_bound {δ : ℝ≥0} (hδ : 0 < δ) (t : ℝ) :
    squareCutMultiplier δ t * squareCutMultiplier δ t ≤
      (δ : ℝ)⁻¹ ^ 2 * max (t - δ) 0 := by
  have hm : 0 < max t (δ : ℝ) := lt_of_lt_of_le hδ (le_max_right _ _)
  have hs : squareCutMultiplier δ t * squareCutMultiplier δ t =
      max (t - δ) 0 / (max t δ) ^ 2 := by
    dsimp [squareCutMultiplier]
    rw [div_mul_div_comm, ← sq, Real.sq_sqrt (le_max_right _ _), ← sq]
  rw [hs]
  have hd : 0 < (δ : ℝ) ^ 2 := sq_pos_of_pos hδ
  have hb : (δ : ℝ) ^ 2 ≤ (max t δ) ^ 2 := by exact pow_le_pow_left₀ δ.2 (le_max_right t (δ : ℝ)) 2
  have hh := div_le_div_of_nonneg_left (le_max_right (t-δ) 0) hd hb
  simpa only [div_eq_mul_inv, inv_pow, mul_comm] using hh

lemma squareCut_factorization (a : Positive A) (δ : ℝ≥0) (hδ : 0 < δ) :
    ∃ g : A, star g = g ∧ g * (a.1 * a.1) * g = (Positive.cut δ a).1 ∧
      g * g ≤ ((δ : ℝ)⁻¹ ^ 2) • (Positive.cut δ a).1 := by
  let f := squareCutMultiplier δ
  have hf : Continuous f := squareCutMultiplier_continuous hδ
  have hf0 : f 0 = 0 := squareCutMultiplier_zero δ
  have ha := IsSelfAdjoint.of_nonneg a.2
  refine ⟨cfcₙ f a.1, (cfcₙ_predicate f a.1).star_eq, ?_, ?_⟩
  · calc
      _ = cfcₙ (fun t : ℝ => f t * (t * t) * f t) a.1 := by
        rw [cfcₙ_mul (fun t : ℝ => f t * (t * t)) f a.1,
          cfcₙ_mul f (fun t : ℝ => t * t) a.1,
          cfcₙ_mul (fun t : ℝ => t) (fun t : ℝ => t) a.1, cfcₙ_id' ℝ a.1]
      _ = _ := cfcₙ_congr fun t _ => squareCutMultiplier_identity hδ t
  · rw [← cfcₙ_mul f f a.1]
    change cfcₙ (fun t => f t * f t) a.1 ≤
      ((δ : ℝ)⁻¹ ^ 2) • cfcₙ (fun t : ℝ => max (t - δ) 0) a.1
    rw [← cfcₙ_const_mul ((δ : ℝ)⁻¹ ^ 2) (fun t : ℝ => max (t - δ) 0) a.1]
    exact (cfcₙ_le_iff _ _ a.1).mpr (fun t _ => squareCutMultiplier_bound hδ t)

lemma abs_cuntzBelow_starMul (x : A) : CuntzBelow (Positive.abs x) (Positive.starMul x) := by
  apply CuntzBelow.of_cuts
  intro δ hδ η hη
  obtain ⟨g, hgs, hg, _⟩ := squareCut_factorization (Positive.abs x) δ hδ
  rw [Positive.abs_sq] at hg
  exact ⟨g, by simpa [Positive.starMul, hgs, hg] using hη⟩

lemma starMul_cuntzBelow_abs (x : A) : CuntzBelow (Positive.starMul x) (Positive.abs x) := by
  let a := Positive.abs x
  have hs := (CFC.sqrt_nonneg a.1).star_eq
  have heq : star (CFC.sqrt a.1) * a.1 * CFC.sqrt a.1 = star x * x := by
    rw [hs]
    calc
      _ = CFC.sqrt a.1 * (CFC.sqrt a.1 * CFC.sqrt a.1) * CFC.sqrt a.1 := by
        rw [CFC.sqrt_mul_sqrt_self a.1 a.2]
      _ = (CFC.sqrt a.1 * CFC.sqrt a.1) * (CFC.sqrt a.1 * CFC.sqrt a.1) := by noncomm_ring
      _ = star x * x := by rw [CFC.sqrt_mul_sqrt_self a.1 a.2]; exact Positive.abs_sq x
  intro η hη
  refine ⟨CFC.sqrt a.1, ?_⟩
  change ‖star (CFC.sqrt a.1) * a.1 * CFC.sqrt a.1 - star x * x‖ < η
  rw [heq, sub_self, norm_zero]
  exact hη

lemma starMul_add_le (x y : A) (t : ℝ) (ht : 0 < t) :
    star (x+y) * (x+y) ≤ (1+t) • (star x*x) + (1+t⁻¹) • (star y*y) := by
  have h := smul_nonneg (inv_nonneg.mpr ht.le) (star_mul_self_nonneg (t • x - y))
  have heq : t⁻¹ • (star (t • x - y) * (t • x - y)) =
      ((1+t) • (star x*x) + (1+t⁻¹) • (star y*y)) - star (x+y)*(x+y) := by
    simp only [star_sub, star_smul, star_trivial, sub_mul, mul_sub, smul_mul_assoc,
      mul_smul_comm, star_add, add_mul, mul_add, smul_sub, smul_smul]
    simp only [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    module
  rw [heq] at h
  exact sub_nonneg.mp h

theorem abs_cut_cuntzBelow_of_norm_sub_lt (x y : A) (ε : ℝ≥0) (hε : 0 < ε)
    (hxy : ‖x-y‖ < (ε : ℝ)) :
    CuntzBelow (Positive.cut ε (Positive.abs x)) (Positive.abs y) := by
  obtain ⟨g, hgs, hgc, hgg⟩ := squareCut_factorization (Positive.abs x) ε hε
  rw [Positive.abs_sq] at hgc
  let c := Positive.cut ε (Positive.abs x)
  let d := Positive.starMul (y*g)
  let β : ℝ := ‖x-y‖ ^ 2 * (ε : ℝ)⁻¹ ^ 2
  have hβ0 : 0 ≤ β := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hβ1 : β < 1 := by
    have h := (div_lt_one (show (0 : ℝ) < ε from hε)).mpr hxy
    have hp : 0 ≤ ‖x-y‖ / (ε : ℝ) := div_nonneg (norm_nonneg _) ε.2
    have heq : β = (‖x-y‖ / (ε : ℝ)) ^ 2 := by dsimp [β]; rw [div_eq_mul_inv, mul_pow]
    rw [heq]
    nlinarith
  let t := (1-β)⁻¹
  have ht : 0 < t := inv_pos.mpr (by linarith)
  have htinv : 1+t⁻¹ = 2-β := by dsimp [t]; rw [inv_inv]; ring
  have he : star ((x-y)*g)*((x-y)*g) ≤ β • c.1 := by
    have h := CStarAlgebra.star_left_conjugate_le_norm_smul
      (a := g) (b := star (x-y)*(x-y)) (IsSelfAdjoint.of_nonneg (star_mul_self_nonneg _))
    rw [hgs, CStarRing.norm_star_mul_self] at h
    have heq : star ((x-y)*g)*((x-y)*g) = g*(star (x-y)*(x-y))*g := by
      rw [star_mul, hgs]; noncomm_ring
    rw [heq]
    exact h.trans (by simpa only [smul_smul, ← pow_two] using
      smul_le_smul_of_nonneg_left hgg (mul_nonneg (norm_nonneg (x-y)) (norm_nonneg (x-y))))
  have hc : c.1 ≤ (1+t) • d.1 + ((2-β)*β) • c.1 := by
    have h := starMul_add_le (y*g) ((x-y)*g) t ht
    have hs : y*g+(x-y)*g = x*g := by noncomm_ring
    have hi : star (x*g)*(x*g) = c.1 := by
      rw [star_mul, hgs]
      calc
        _ = g*(star x*x)*g := by noncomm_ring
        _ = c.1 := hgc
    rw [hs, hi, htinv] at h
    have hscaled : (2-β) • (star ((x-y)*g)*((x-y)*g)) ≤ ((2-β)*β) • c.1 := by
      simpa only [smul_smul] using smul_le_smul_of_nonneg_left he (by linarith : 0 ≤ 2-β)
    exact h.trans (add_le_add le_rfl hscaled)
  let q := 1-(2-β)*β
  have hq : 0 < q := by dsimp [q]; nlinarith [sq_pos_of_pos (show 0 < 1-β by linarith)]
  have hsmall : q • c.1 ≤ (1+t) • d.1 := by
    dsimp [q]
    rw [sub_smul, one_smul]
    exact sub_le_iff_le_add.mpr hc
  have hdom : c.1 ≤ (q⁻¹*(1+t)) • d.1 := by
    have h := smul_le_smul_of_nonneg_left hsmall (inv_nonneg.mpr hq.le)
    simpa only [smul_smul, inv_mul_cancel₀ hq.ne', one_smul] using h
  have hd : CuntzBelow d (Positive.starMul y) := by
    intro η hη
    refine ⟨g, ?_⟩
    have hi : star g*(star y*y)*g = star (y*g)*(y*g) := by rw [star_mul]; noncomm_ring
    change ‖star g*(star y*y)*g - star (y*g)*(y*g)‖ < η
    rw [hi, sub_self, norm_zero]
    exact hη
  exact (CuntzBelow.of_le_smul c d (q⁻¹*(1+t)) (mul_nonneg (inv_nonneg.mpr hq.le)
    (by linarith)) hdom).trans (hd.trans (starMul_cuntzBelow_abs y))
end CuntzTrace

end

end OAI
