import Mathlib
import OAI.Combinatorics.KMedian.Analysis.FiniteComparison

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

noncomputable def externalMass {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*q i h
noncomputable def externalSquare {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  ∑ h, ρ h*(q i h)^2
noncomputable def rowType {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i : I) : ℝ :=
  externalSquare ρ q i/externalMass ρ q i
noncomputable def kernel {I H : Type*} [Fintype H] (ρ : H → ℝ) (q : I → H → ℝ) (i t : I) : ℝ :=
  ∑ h, ρ h*q i h*q t h

theorem external_bounds {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq0 : ∀ i h, 0 ≤ q i h) (hq : ∀ i h, q i h ≤ 1) (i : I) :
    0 ≤ externalSquare ρ q i ∧ externalSquare ρ q i ≤ externalMass ρ q i := by
  constructor
  · exact Finset.sum_nonneg (fun h _ => mul_nonneg (hρ h) (sq_nonneg _))
  · apply Finset.sum_le_sum
    intro h _
    apply mul_le_mul_of_nonneg_left _ (hρ h)
    nlinarith [hq0 i h, hq i h]

theorem row_type_bounds {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (hq0 : ∀ i h, 0 ≤ q i h) (hq : ∀ i h, q i h ≤ 1) (i : I) :
    0 ≤ rowType ρ q i ∧ rowType ρ q i ≤ 1 ∧
      rowType ρ q i*externalMass ρ q i=externalSquare ρ q i := by
  have hb := external_bounds hρ hq0 hq i
  have hm : 0 ≤ externalMass ρ q i := hb.1.trans hb.2
  by_cases hz : externalMass ρ q i=0
  · have hs : externalSquare ρ q i=0 := by linarith
    simp [rowType, hz, hs]
  · have hp : 0 < externalMass ρ q i := lt_of_le_of_ne hm (Ne.symm hz)
    exact ⟨div_nonneg hb.1 hm, (div_le_one hp).mpr hb.2, div_mul_cancel₀ _ hz⟩

theorem kernel_bound {I H : Type*} [Fintype H] {ρ : H → ℝ} {q : I → H → ℝ}
    (hρ : ∀ h, 0 ≤ ρ h) (i t : I) :
    kernel ρ q i t ≤ (externalSquare ρ q i+externalSquare ρ q t)/2 := by
  have hp : ∀ h, 2*(ρ h*q i h*q t h) ≤ ρ h*(q i h)^2+ρ h*(q t h)^2 := by
    intro h
    have hn := mul_nonneg (hρ h) (sq_nonneg (q i h-q t h))
    nlinarith only [hn]
  have hsum := Finset.sum_le_sum (fun h (_ : h ∈ Finset.univ) => hp h)
  simp only [Finset.sum_add_distrib, ←Finset.mul_sum] at hsum
  unfold kernel externalSquare
  linarith only [hsum]

theorem kernel_average_bound {I : Type*} [Fintype I] {π D s r : I → ℝ} {K : I → I → ℝ} {y : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hK : ∀ i t, K i t ≤ (s i*(1-y*r i)+s t*(1-y*r t))/2) :
    2*average π (fun i => average π (fun t => K i t*D t)) ≤
      average π (fun i => s i*(1-y*r i)*(1+D i)) := by
  have hb := average_mono hπ0 (fun i => average_mono hπ0
    (fun t => mul_le_mul_of_nonneg_right (hK i t) (hD0 t)))
  have hid : average π (fun i => average π (fun t =>
      ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t)) =
      (1/2)*average π (fun i => s i*(1-y*r i)*(1+D i)) := by
    have hpoint : ∀ i t, ((s i*(1-y*r i)+s t*(1-y*r t))/2)*D t =
        (1/2)*(s i*(1-y*r i))*D t+(1/2)*(s t*(1-y*r t)*D t) := by intros; ring
    simp_rw [hpoint, average_add, average_mul, hD, mul_one, average_const hπ]
    rw [average_mul, ←mul_add, ←average_add]
    congr 2
    funext i
    ring
  rw [hid] at hb
  linarith only [hb]

theorem taper_error {p pHat ζ u : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1/2)
    (hζ0 : 0 ≤ ζ) (he : |pHat-p| ≤ ζ) (hu0 : 0 ≤ u) (hu : u ≤ 1) :
    0 ≤ (1-pHat*u)-(1-2*ζ)*(1-p*u) ∧
      (1-pHat*u)-(1-2*ζ)*(1-p*u) ≤ 3*ζ := by
  have hehe := abs_le.mp he
  have huζ := mul_le_mul_of_nonneg_left hu hζ0
  have hupper := mul_le_mul_of_nonneg_right hehe.1 hu0
  have hlower := mul_le_mul_of_nonneg_right hehe.2 hu0
  have hpu := mul_le_mul hp hu hu0 (by norm_num : (0:ℝ) ≤ 1/2)
  have hpu0 := mul_nonneg hp0 hu0
  have hpuz := mul_le_mul_of_nonneg_left hpu hζ0
  have hpuz0 := mul_nonneg hζ0 hpu0
  constructor <;> nlinarith only [huζ, hupper, hlower, hpuz, hpuz0]

theorem radius_control {I : Type*} [Fintype I] {π D : I → ℝ} {q : I → I → ℝ}
    {N : I → ℝ} {pHat : ℝ}
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1) (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1)
    (hN0 : ∀ i, 0 ≤ N i) (_hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t) (i : I) :
    (1-average π (q i))*N i ≤ 2*(D i+1) := by
  have hpoint : ∀ t, (1-q i t)*N i ≤ 2*(D i+D t) := by
    intro t
    rcases eq_or_lt_of_le (hq i t) with heq | hlt
    · rw [heq]
      have hpos := add_nonneg (hD0 i) (hD0 t)
      nlinarith
    · have hh := hcomp i t hlt
      have hpq := mul_le_mul hp (hq i t) (hq0 i t) (by norm_num : (0:ℝ) ≤ 1/2)
      have hden : 1/2 ≤ 1-pHat*q i t := by linarith
      have hmul := mul_le_mul_of_nonneg_left hden (hN0 i)
      have hcut := mul_nonneg (hq0 i t) (hN0 i)
      nlinarith only [hh, hmul, hcut]
  have hb := average_mono hπ0 hpoint
  simp only [average_mul_right, average_sub, average_mul, average_add, average_const hπ, hD] at hb
  exact hb

noncomputable def normalizedDrift {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  -3-2*(P x*(y-x)^2/y)+average π (fun i =>
    (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
    (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
    2*P x*average π (fun t => K i t*D t)-
    average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))

theorem normalized_drift_le {I : Type*} [Fintype I]
    {π D N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i=1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D=1) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ D i+D t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-y*average π (q i))+s t*(1-y*average π (q t)))/2) :
    normalizedDrift π D N s q K x y pHat ≤ 12*ζ := by
  let R : I → ℝ := fun i => (1-2*ζ)*N i
  let err : I → ℝ := fun i => (1-average π (q i))*N i*
    ((1-pHat*s i)-(1-2*ζ)*(1-P x*s i))
  have hpP := P_le_half hx0
  have hpP0 := P_nonneg x
  have hR : ∀ i, 0 ≤ R i := by
    intro i
    exact mul_nonneg (by linarith only [hζ]) (hN i)
  have hcompR : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t := by
    intro i t hit
    have ht := (taper_error hpP0 hpP hζ0 he (hq0 i t) (hq i t)).1
    have hm := mul_le_mul_of_nonneg_right (sub_nonneg.mp ht) (hN i)
    dsimp only [R]
    nlinarith only [hm, hcomp i t hit]
  have hfinite := finite_comparison hx0 hx hy0 hy hπ0 hπ hD0 hD hR
    hq0 hq hs0 hs hcompR
  have herr : ∀ i, err i ≤ 6*ζ*(D i+1) := by
    intro i
    have hr : average π (q i) ≤ 1 := by
      have hr := average_mono hπ0 (hq i)
      simpa only [average_const hπ] using hr
    have hn : 0 ≤ (1-average π (q i))*N i :=
      mul_nonneg (sub_nonneg.mpr hr) (hN i)
    have ht := (taper_error hpP0 hpP hζ0 he (hs0 i) (hs i)).2
    have hrad := radius_control hπ0 hπ hD0 hD hN hp0 hp hq0 hq hcomp i
    have h1 := mul_le_mul_of_nonneg_left ht hn
    have h2 := mul_le_mul_of_nonneg_left hrad (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hζ0)
    dsimp only [err]
    nlinarith only [h1, h2]
  have herrAvg : average π err ≤ 12*ζ := by
    have hh := average_mono hπ0 herr
    simp only [average_mul, average_add, hD, average_const hπ] at hh
    nlinarith only [hh]
  have hker := mul_le_mul_of_nonneg_left (kernel_average_bound hπ0 hπ hD0 hD hK) hpP0
  have hid : normalizedDrift π D N s q K x y pHat =
      average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) +
      average π err -2*(P x*(y-x)^2/y)+
      P x*(2*average π (fun i => average π (fun t => K i t*D t))-
        average π (fun i => s i*(1-y*average π (q i))*(1+D i))) := by
    have hrow : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)) := by
      intro i
      unfold rawRow
      dsimp only [R, err]
      ring
    unfold normalizedDrift
    have heq : ∀ i,
        (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
        (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
        2*P x*average π (fun t => K i t*D t)-
        average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0) =
        (rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)+err i+
        2*D i+1-P x*(s i*(1-y*average π (q i))*(1+D i)))+
        2*P x*average π (fun t => K i t*D t) := by
      intro i
      have hh := hrow i
      linarith only [hh]
    simp only [heq, average_add, average_sub, average_mul, hD, average_const hπ]
    ring
  rw [hid]
  nlinarith only [hfinite, herrAvg, hker]

end MetricKMedian.GraphComparison
end
end

end OAI
