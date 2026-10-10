import OAI.Geometry.TranslativeCovering.DecayNormalization

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace NormalizedCaps
open MeasureTheory SphericalLaw CapCost CapAffinity ProjectiveCaps
open scoped ENNReal NNReal

lemma scale_sqrt {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) :
    Real.sqrt (a/c*(b/c)) = Real.sqrt (a*b)/c := by
  rw [div_mul_div_comm, Real.sqrt_div (mul_nonneg ha hb), ← pow_two,Real.sqrt_sq hc.le]

lemma intensity_overlap {n : ℕ} [NeZero n] (e f g : Sphere n)
    {l u U t r s k : ℝ} (hl : 0 < l) (hU : U < 1)
    (_ht : 0 ≤ t) (ht1 : t < 1)
    (hlr : l ≤ r) (hru : r ≤ u) (hls : l ≤ s) (hsu : s ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l) :
    (intensity e t).real (cap f.val r ∩ cap g.val s) ≤
      2*Real.exp (-(n:ℝ)*(2*l*k/Real.pi^2)*(angle f.val g.val)^2) *
        Real.sqrt ((intensity e t).real (cap f.val r)*(intensity e t).real (cap g.val s)) := by
  simp_rw [intensity_real]
  rw [scale_sqrt measureReal_nonneg measureReal_nonneg (cap_real_pos e ht1), ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (doublecap_overlap f g hl hU hlr hru hls hsu huU hk hkl hku hdim)
    (cap_real_pos e ht1).le

lemma clipped_affinity {n : ℕ} [NeZero n] {I : Type u_1} (e : Sphere n)
    (axes : I → Sphere n) (τ : I → ℝ) {l u U t k H c : ℝ}
    (hl : 0 < l) (hU : U < 1) (ht : 0 ≤ t) (ht1 : t < 1)
    (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u) (huU : u ≤ U)
    (hk : 0 ≤ k) (hkl : k ≤ l/16) (hku : 4*k ≤ U-u)
    (hdim : 2*(1/l+1/(1-U^2)) ≤ (n:ℝ)*l)
    (hH : 1 ≤ H) (hraw : ∀ i,(intensity e t).real (cap (axes i).val (τ i)) ≤ H)
    (hc : 0 ≤ c) (hca : c ≤ (2*l*k/Real.pi^2)/4) (hcy : c ≤ 1/8) (i j : I) :
    let μ := intensity e t
    let C := fun i => cap (axes i).val (τ i)
    let s := fun i => -Real.log (min (μ.real (C i)) (1/2))
    μ.real (C i ∩ C j)/Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) ≤
      4*H*Real.exp (-c*(costDist n (fun i => (axes i).val) s i j)^2) := by
  dsimp only
  let μ := intensity e t
  let C := fun i => cap (axes i).val (τ i)
  let s := fun i => -Real.log (min (μ.real (C i)) (1/2))
  have hp (i : I) : 0 < μ.real (C i) := by
    rw [show μ.real (C i) = (σ n).real (C i)/(σ n).real (cap e.val t) from intensity_real e t _]
    exact div_pos (cap_real_pos (axes i) ((hτu i).trans_lt (huU.trans_lt hU))) (cap_real_pos e ht1)
  have hb (i : I) : 0 < min (μ.real (C i)) (1/2) := lt_min (hp i) (by norm_num)
  have hd : 0 < Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) :=
    Real.sqrt_pos.mpr (mul_pos (hb i) (hb j))
  have h1 := intensity_overlap e (axes i) (axes j) hl hU ht ht1 (hτl i) (hτu i)
    (hτl j) (hτu j) huU hk hkl hku hdim
  have hsqrt := DecayNormalization.sqrt_clipped (hp i) (hp j) hH (hraw i) (hraw j)
  have hangle : μ.real (C i ∩ C j)/Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) ≤
      4*H*Real.exp (-(2*l*k/Real.pi^2)*((n:ℝ)*(angle (axes i).val (axes j).val)^2)) := by
    apply (div_le_iff₀ hd).mpr
    have hh := h1.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))
    rw [show -(2*l*k/Real.pi^2)*((n:ℝ)*(angle (axes i).val (axes j).val)^2) =
      -(n:ℝ)*(2*l*k/Real.pi^2)*(angle (axes i).val (axes j).val)^2 by ring]
    convert hh using 1
    ring
  have hmin := DecayNormalization.clipped_trivial (hp i) (hp j) hH (hraw i) (hraw j)
    (measureReal_mono Set.inter_subset_left) (measureReal_mono Set.inter_subset_right)
  have hcost : μ.real (C i ∩ C j)/Real.sqrt (min (μ.real (C i)) (1/2)*min (μ.real (C j)) (1/2)) ≤
      4*H*Real.exp (-|s i-s j|/2) := hmin.trans (by
    dsimp [s]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    linarith)
  have hdist : (costDist n (fun i => (axes i).val) s i j)^2 ≤
      2*((n:ℝ)*(angle (axes i).val (axes j).val)^2)+2*|s i-s j| := by
    dsimp [costDist]
    have hnn := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
    have hss := Real.sq_sqrt (abs_nonneg (s i-s j))
    nlinarith [sq_nonneg (Real.sqrt n * angle (axes i).val (axes j).val - Real.sqrt |s i-s j|)]
  exact DecayNormalization.combine (div_nonneg measureReal_nonneg hd.le) (by linarith)
    (by positivity) hc (by positivity) (abs_nonneg _) hdist hca hcy hangle hcost

end NormalizedCaps

end OAI
