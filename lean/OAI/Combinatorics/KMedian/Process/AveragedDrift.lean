import Mathlib
import OAI.Combinatorics.KMedian.Geometry.GraphComparison

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem cap_average {H : Type*} [Fintype H] {ρ q bH : H → ℝ}
    {b d N pHat y w s : ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq : ∀ h, 0 ≤ q h)
    (hw : w ≤ y) (hy : y ≤ 1)
    (hm : ∑ h, ρ h*q h=1-w)
    (hs : ∑ h, ρ h*(q h)^2=s*(1-w))
    (hb : ∀ h, bH h ≤ b)
    (htaper : ∀ h, 0 < q h → bH h ≤ d+(1-pHat*q h)*N) :
    (∑ h, ρ h*q h*bH h) ≤ (1-y)*b+(y-w)*(d+(1-pHat*s)*N) := by
  let F := ∑ h, ρ h*q h*bH h
  have hfirst : F ≤ (1-w)*b := by
    rw [← hm, Finset.sum_mul]
    exact Finset.sum_le_sum (fun h _ => mul_le_mul_of_nonneg_left (hb h) (mul_nonneg (hρ h) (hq h)))
  have hsecond : F ≤ (1-w)*(d+(1-pHat*s)*N) := by
    have hterm : ∀ h, ρ h*q h*bH h ≤ ρ h*q h*(d+(1-pHat*q h)*N) := by
      intro h
      by_cases hpos : 0 < q h
      · exact mul_le_mul_of_nonneg_left (htaper h hpos) (mul_nonneg (hρ h) (hq h))
      · have hz : q h=0 := le_antisymm (le_of_not_gt hpos) (hq h)
        simp only [hz, mul_zero, zero_mul, le_refl]
    have hsum := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hterm h)
    have hid : (∑ h, ρ h*q h*(d+(1-pHat*q h)*N)) = (1-w)*(d+(1-pHat*s)*N) := by
      simp_rw [show ∀ h, ρ h*q h*(d+(1-pHat*q h)*N) =
          (ρ h*q h)*(d+N)-(ρ h*(q h)^2)*(pHat*N) by intro h; ring]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hm, hs]
      ring
    exact hsum.trans_eq hid
  by_cases hzero : 1-w=0
  · have hw1 : w=1 := by linarith only [hzero]
    have hy1 : y=1 := le_antisymm hy (hw1 ▸ hw)
    simpa only [hw1, hy1, sub_self, zero_mul, add_zero] using hfirst
  · have hpos : 0 < 1-w := lt_of_le_of_ne (sub_nonneg.mpr (hw.trans hy)) (Ne.symm hzero)
    have h1 := mul_le_mul_of_nonneg_left hfirst (sub_nonneg.mpr hy)
    have h2 := mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hw)
    apply (mul_le_mul_iff_right₀ hpos).mp
    dsimp only [F] at h1 h2 ⊢
    nlinarith only [h1, h2]

noncomputable def unnormalizedDrift {I : Type*} [Fintype I]
    (μ d N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  let V := ∑ i, μ i*d i
  let w := fun i => ∑ t, μ t*q i t
  let a := 1+m x+B x*y;
  -(3*y+B x*(y-x)^2)*V+
    ∑ i, μ i*((y-w i)*(d i+(1-pHat*s i)*N i)+a*w i*d i+B x*V*w i+
      B x*(∑ t, μ t*K i t*d t)-
      ∑ t, μ t*(1-q i t)*max (d t-a*d i) 0)

theorem normalization_identity {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x pHat : ℝ) {y L : ℝ}
    (hy : y ≠ 0) (hL : 0 ≤ L) (hD : average π D=1) :
    unnormalizedDrift (fun i => y*π i) (fun i => L*D i) (fun i => L*N i) s q K x y pHat =
      (y^2*L)*normalizedDrift π D N s q K x y pHat := by
  have hV : (∑ i, (y*π i)*(L*D i))=y*L := by
    simp only [mul_mul_mul_comm y _ L _, ← Finset.mul_sum]
    change y*L*average π D=y*L
    rw [hD, mul_one]
  have hw : ∀ i, (∑ t, (y*π t)*q i t)=y*average π (q i) := by
    intro i
    simp only [average, Finset.mul_sum, mul_assoc]
  have hk : ∀ i, (∑ t, (y*π t)*K i t*(L*D t)) =
      y*L*average π (fun t => K i t*D t) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hh : ∀ i, (∑ t, (y*π t)*(1-q i t)*max (L*D t-(1+m x+B x*y)*(L*D i)) 0) =
      y*L*average π (fun t => (1-q i t)*max (D t-(1+m x+B x*y)*D i) 0) := by
    intro i
    simp only [average, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [show L*D t-(1+m x+B x*y)*(L*D i)=L*(D t-(1+m x+B x*y)*D i) by ring,
      ← mul_zero L, ← mul_max_of_nonneg _ _ hL]
    ring_nf
  unfold unnormalizedDrift normalizedDrift
  dsimp only
  rw [hV]
  simp_rw [hw, hk, hh]
  simp only [average]
  have hB : B x=2*P x := rfl
  rw [hB]
  have hconst : -(3*y+2*P x*(y-x)^2)*(y*L) =
      y^2*L*(-3-2*(P x*(y-x)^2/y)) := by field_simp [hy]; ring
  have hterms : (∑ i, y*π i*((y-y*∑ t, π t*q i t)*(L*D i+(1-pHat*s i)*(L*N i))+
      (1+m x+2*P x*y)*(y*∑ t, π t*q i t)*(L*D i)+
      2*P x*(y*L)*(y*∑ t, π t*q i t)+2*P x*(y*L*∑ t, π t*(K i t*D t))-
      y*L*∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) =
      ∑ i, y^2*L*(π i*((1-∑ t, π t*q i t)*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*(∑ t, π t*q i t)*D i+2*P x*y*(∑ t, π t*q i t)+
        2*P x*(∑ t, π t*(K i t*D t))-
        ∑ t, π t*((1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [mul_add, Finset.mul_sum]
  exact congrArg₂ (·+·) hconst hterms

theorem unnormalized_drift_le {I : Type*} [Fintype I]
    {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
    (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
    unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i) := by
  let V := ∑ i, μ i*d i
  let L := V/y
  let π := fun i => μ i/y
  let D := fun i => d i/L
  let R := fun i => N i/L
  have hyne := ne_of_gt hy0
  have hLpos : 0 < L := div_pos hV hy0
  have hLne := ne_of_gt hLpos
  have hyL : y*L=V := by dsimp only [L]; exact mul_div_cancel₀ _ hyne
  have hπ0 : ∀ i, 0 ≤ π i := fun i => div_nonneg (hμ0 i) hy0.le
  have hπ : ∑ i, π i=1 := by dsimp only [π]; rw [← Finset.sum_div, hμ, div_self hyne]
  have hμid : ∀ i, y*π i=μ i := fun i => mul_div_cancel₀ _ hyne
  have hdid : ∀ i, L*D i=d i := fun i => mul_div_cancel₀ _ hLne
  have hNid : ∀ i, L*R i=N i := fun i => mul_div_cancel₀ _ hLne
  have hD : average π D=1 := by
    unfold average
    simp_rw [show ∀ i, π i*D i=(μ i*d i)/(y*L) by intro i; dsimp only [π, D]; ring]
    rw [← Finset.sum_div, hyL, div_self (ne_of_gt hV)]
  have hD0 : ∀ i, 0 ≤ D i := fun i => div_nonneg (hd0 i) hLpos.le
  have hR0 : ∀ i, 0 ≤ R i := fun i => div_nonneg (hN i) hLpos.le
  have hcomp' : ∀ i t, q i t < 1 → R i*(1-pHat*q i t) ≤ D i+D t := by
    intro i t hit
    have hh := div_le_div_of_nonneg_right (hcomp i t hit) hLpos.le
    dsimp only [R, D]
    simpa only [div_mul_eq_mul_div, add_div] using hh
  have hw : ∀ i, y*average π (q i)=∑ u, μ u*q i u := by
    intro i
    simp only [average, Finset.mul_sum, ← mul_assoc, hμid]
  have hK' : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2 := by
    intro i t
    simpa only [hw] using hK i t
  have hh := normalized_drift_le hx0 hx hy0 hy hπ0 hπ hD0 hD hR0 hs0 hs
    hq0 hq hp0 hp hζ0 hζ he hcomp' hK'
  have hnorm := normalization_identity π D R s q K x pHat hyne hLpos.le hD
  simp only [hμid, hdid, hNid] at hnorm
  rw [hnorm]
  have hscale := mul_le_mul_of_nonneg_left hh (mul_nonneg (sq_nonneg y) hLpos.le)
  have hV0 : 0 ≤ V := hV.le
  have hyV := mul_le_of_le_one_left hV0 hy
  have hprod := mul_le_mul_of_nonneg_left hyV (mul_nonneg (by norm_num : (0:ℝ) ≤ 12) hζ0)
  have heq : y^2*L=y*V := by calc
    y^2*L = y*(y*L) := by ring
    _ = y*V := by rw [hyL]
  rw [heq] at hscale ⊢
  calc
    y*V*normalizedDrift π D R s q K x y pHat ≤ y*V*(12*ζ) := hscale
    _ = 12*ζ*(y*V) := by ring
    _ ≤ 12*ζ*V := hprod

end MetricKMedian.GraphComparison
end
end

end OAI
