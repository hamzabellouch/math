import OAI.Geometry.TranslativeCovering.Blocks

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
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1

namespace RadiusLens
open Set MeasureTheory CapCost LensQuantitative SphericalLaw CapGeometry BlockGeometry
open scoped BigOperators

lemma lens_at_radius {n : ℕ} [NeZero n] {I : Type u_1} [Fintype I] [DecidableEq I]
    (e : Sphere n) (axes : I → Sphere n) (τ : I → ℝ) (d : I → I → ℝ)
    {l u u₀ t : ℝ} (hl : 0 < l) (hu : u < 1) (_hu₀ : 0 ≤ u₀)
    (ht : 0 ≤ t) (ht1 : t < 1) (hτl : ∀ i,l ≤ τ i) (hτu : ∀ i,τ i ≤ u₀)
    (hmetric : ∀ i j,(n:ℝ)*(ProjectiveCaps.angle (axes i).val (axes j).val)^2 ≤ d i j^2)
    (S : Finset I) (hS : S.Nonempty) (a : I) (ha : a ∈ S)
    (hmin : ∀ i ∈ S,(intensity e t).real (cap (axes a).val (τ a)) ≤
      (intensity e t).real (cap (axes i).val (τ i)))
    (hdim : 2*(1/l+1/(1-u^2)) ≤ (n:ℝ)*l)
    (hrsmall : radius d S/(n:ℝ) < 2)
    (hsmall : (u₀+radius d S/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+
      4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) ≤ u^2) (hu0 : 0 ≤ u) :
    Real.exp (-(3+(1/l+1/(1-u^2))+2*(1/l+1/(1-u^2))/l)*
      (1+radius d S+Real.log S.card))*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) ≤
      (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
  let A := 1/l+1/(1-u^2)
  have hA : 0 ≤ A := by
    have hh : 0 < 1-u^2 := by nlinarith
    dsimp [A]; positivity
  have hn : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let r := radius d S
  have hr : 0 ≤ r := radius_nonneg d S
  let Φ := Real.sqrt (r/(n:ℝ))
  have hΦ : Φ^2 = r/(n:ℝ) := Real.sq_sqrt (div_nonneg hr hn.le)
  have hm : 1 ≤ (S.card:ℝ) := by exact_mod_cast Finset.one_le_card.mpr hS
  have hmlog : 0 ≤ Real.log S.card := Real.log_nonneg hm
  have hlog : 0 ≤ Real.log (2*(S.card:ℝ)) := Real.log_nonneg (by linarith)
  let h := Real.sqrt (4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))
  have hh2 : h^2 = 4*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := Real.sq_sqrt (by positivity)
  let δ := Φ^2/2+Φ*h
  have hδ : 0 ≤ δ := by dsimp [δ,Φ,h]; positivity
  have hδle : δ ≤ r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := by
    calc
      δ ≤ Φ^2+h^2/2 := by dsimp [δ]; nlinarith only [sq_nonneg (Φ-h)]
      _ = _ := by rw [hΦ,hh2]; ring
  obtain ⟨j,hj,hcenter⟩ := exists_center d hS
  obtain ⟨k,hk,hkmax⟩ := Finset.exists_mem_eq_sup' hS τ
  have hτmax (i : S) : τ i ≤ τ k := by
    rw [← hkmax]
    exact Finset.le_sup' τ i.property
  have hang (i : S) : ProjectiveCaps.angle (axes j).val (axes i).val ≤ Φ := by
    apply (Real.le_sqrt (ProjectiveCaps.angle_nonneg _ _) (div_nonneg hr hn.le)).mpr
    exact (le_div_iff₀ hn).mpr (by
      simpa only [mul_comm] using (hmetric j i).trans (hcenter i i.property))
  have hsqrt : Real.sqrt ((τ k+δ)^2+h^2) ≤ u := by
    apply Real.sqrt_le_iff.mpr ⟨hu0,?_⟩
    have h1 : 0 ≤ τ k+δ := add_nonneg (hl.trans_le (hτl k)).le hδ
    have h2 : τ k+δ ≤ u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l) := by linarith only [hτu k,hδle]
    have hsquare : (τ k+δ)^2 ≤ (u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2 := sq_le_sq₀ h1 (h1.trans h2) |>.mpr h2
    calc
      (τ k+δ)^2+h^2 ≤ (u₀+r/(n:ℝ)+2*Real.log (2*(S.card:ℝ))/((n:ℝ)*l))^2+h^2 :=
        by simpa only [add_comm] using add_le_add_right hsquare (h^2)
      _ ≤ u^2 := by simpa only [hh2,r] using hsmall
  have : Nonempty S := ⟨⟨a,ha⟩⟩
  have hbound := intensity_lens e (axes j) (fun i : S => axes i) (fun i : S => τ i)
    hl hu ht ht1 (hτl k) (Real.sqrt_nonneg _) (by change Φ^2 < 2; rw [hΦ]; exact hrsmall)
    hang hτmax hdim (by simpa only [Fintype.card_coe,Φ,h,δ,add_assoc] using hsqrt)
  have heq : (intensity e t).real (cap (axes j).val (τ k)) =
      (intensity e t).real (cap (axes k).val (τ k)) := by
    simp only [intensity_real,cap_eq_mass (axes j) (axes k)]
  rw [heq] at hbound
  have hmass := hmin k hk
  have hminimum : 0 ≤ min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) :=
    le_min measureReal_nonneg (by norm_num)
  have hb : min ((intensity e t).real (cap (axes a).val (τ a))) (1/2)/4 *
      Real.exp (-(n:ℝ)*A*δ) ≤ (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
    have hle := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right ((min_le_left ((intensity e t).real (cap (axes a).val (τ a))) (1/2)).trans hmass) (by norm_num : (0:ℝ) ≤ 4))
      (Real.exp_pos (-(n:ℝ)*A*δ)).le
    have hbound' : (intensity e t).real (cap (axes k).val (τ k))/4 *
        Real.exp (-(n:ℝ)*A*δ) ≤ (intensity e t).real (⋂ i ∈ S,cap (axes i).val (τ i)) := by
      simpa only [A,δ,h,Φ,Fintype.card_coe,Set.iInter_subtype] using hbound
    exact hle.trans hbound'
  have hexp : Real.exp (-(3+A+2*A/l)*(1+r+Real.log S.card)) ≤ Real.exp (-(n:ℝ)*A*δ)/4 := by
    have hnδ : (n:ℝ)*δ ≤ r+2*Real.log (2*(S.card:ℝ))/l := by
      have hh := mul_le_mul_of_nonneg_left hδle hn.le
      convert hh using 1
      first | rfl | (field_simp)
    have hnA := mul_le_mul_of_nonneg_left hnδ hA
    have hl2 : Real.log 2 ≤ 1 := by have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    have hl4 : Real.log 4 ≤ 2 := by
      rw [show (4:ℝ) = 2*2 by norm_num,Real.log_mul (by norm_num) (by norm_num)]
      linarith
    have hal : 0 ≤ 2*A/l := by positivity
    have hlmul := mul_le_mul_of_nonneg_left hl2 hal
    rw [Real.log_mul (by norm_num) (by linarith : (S.card:ℝ) ≠ 0)] at hnA
    have hbig : (n:ℝ)*A*δ+Real.log 4 ≤ (3+A+2*A/l)*(1+r+Real.log S.card) := by
      have h1 := mul_nonneg hA hmlog
      have h2 := mul_nonneg hal hr
      simp only [div_eq_mul_inv] at hnA hlmul h2 ⊢
      nlinarith only [hnA,hlmul,hl4,h1,h2,hr,hmlog,hA]
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 4),← Real.exp_sub]
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ (Real.exp (-(n:ℝ)*A*δ)/4)*min ((intensity e t).real (cap (axes a).val (τ a))) (1/2) :=
      mul_le_mul_of_nonneg_right hexp hminimum
    _ = _ := by ring
    _ ≤ _ := hb

end RadiusLens

end OAI
