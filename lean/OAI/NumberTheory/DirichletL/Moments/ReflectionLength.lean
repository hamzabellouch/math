import OAI.NumberTheory.DirichletL.Moments.ReflectionTails

namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma nonempty_clipped_scale (S B q : ℝ) (hS : 0<S) (hq : 1≤q)
    (hsupport : q/S≤B) : max 1 S≤max 1 B*S := by
  have hh : 1≤B*S := hq.trans ((div_le_iff₀ hS).mp hsupport)
  apply max_le
  · exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS.le)
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 B) hS.le

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

theorem eventually_reflected_length (C B box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M n Q R d h s q : ℝ),
      0<Q → 0<d → 0<s → Q*R≤C*Z^M → d≤R → 1≤h →
      s≤Z^(xi/2) → 1≤q → q/(s*(Q*d/(Z^n*h)))≤B →
      let declared := Real.logb Z (box*max 1 (s*(Q*d/(Z^n*h))))
      0≤declared ∧ declared≤M-n+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (C*max 1 B*box))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro M n Q R d h s q hQ hd hs hcap hdR hh hsm hq hsupport
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : 0<s*(Q*d/(Z^n*h)) := by positivity
  have hraw := reflected_scale_bound Z M n xi C Q R d h s hZ hC.le hQ.le hd.le hs.le hcap hdR hh hsm
  have hclip := nonempty_clipped_scale _ B q hp hq hsupport
  have hT : 1≤box*max 1 (s*(Q*d/(Z^n*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤box*max 1 (s*(Q*d/(Z^n*h))) :=
        mul_le_mul hbox (le_max_left _ _) (by norm_num) (by linarith)
  constructor
  · exact Real.logb_nonneg hZ hT
  · apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hT)).mpr
    calc
      _≤box*(max 1 B*(C*Z^(M-n+xi/2))) :=
        mul_le_mul_of_nonneg_left (hclip.trans
          (mul_le_mul_of_nonneg_left hraw (le_max_of_le_left (by norm_num)))) (by linarith)
      _=(C*max 1 B*box)*Z^(M-n+xi/2) :=by ring
      _≤Z^(xi/2)*Z^(M-n+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
      _=Z^(M-n+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
