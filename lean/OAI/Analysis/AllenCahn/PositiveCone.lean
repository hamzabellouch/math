import OAI.Analysis.AllenCahn.BernsteinGradient
import OAI.Analysis.AllenCahn.StrongMaximum

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff
open Filter Topology

def positiveLinearCone {n : ℕ} (P : Space n → ℝ) : Set (Space n → ℝ) :=
  {f | ContDiff ℝ ∞ f ∧ (∀ x, 0 ≤ f x) ∧
    (∀ x, Laplacian.laplacian f x = P x * f x) ∧ f 0 = 1}

lemma positiveLinearCone_pos {n : ℕ} {P f : Space n → ℝ}
    (hP : ∀ x, P x ≤ 2) (hf : f ∈ positiveLinearCone P) : ∀ x, 0 < f x := by
  intro x
  by_contra h
  have hz : f x = 0 := le_antisymm (le_of_not_gt h) (hf.2.1 x)
  have hh := PositiveMaximum.nonnegative_supersolution_eq_zero (smooth_C2 hf.1) hf.2.1
    (fun y => by rw [hf.2.2.1 y]; exact mul_le_mul_of_nonneg_right (hP y) (hf.2.1 y)) hz 0
  rw [hf.2.2.2] at hh
  norm_num at hh

lemma positiveLinearCone_convex {n : ℕ} (P : Space n → ℝ) :
    Convex ℝ (positiveLinearCone P) := by
  intro f hf g hg a b ha hb hab
  have hs : ContDiff ℝ ∞ (a • f + b • g) := (hf.1.const_smul a).add (hg.1.const_smul b)
  refine ⟨hs, fun x => ?_, fun x => ?_, ?_⟩
  · change 0 ≤ a * f x + b * g x
    exact add_nonneg (mul_nonneg ha (hf.2.1 x)) (mul_nonneg hb (hg.2.1 x))
  · change Laplacian.laplacian (fun y => a * f y + b * g y) x = _
    rw [laplacian_fun_add (contDiff_const.mul (smooth_C2 hf.1)) (contDiff_const.mul (smooth_C2 hg.1)),
      laplacian_fun_const_mul (smooth_C2 hf.1), laplacian_fun_const_mul (smooth_C2 hg.1),
      hf.2.2.1, hg.2.2.1]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf.2.2.2, hg.2.2.2, mul_one] using hab

lemma positiveLinearCone_normalize {n : ℕ} {P f : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ x, 0 ≤ f x)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) (h0 : 0 < f 0) :
    (fun x => (f 0)⁻¹ * f x) ∈ positiveLinearCone P := by
  refine ⟨contDiff_const.mul hf, fun x => mul_nonneg (inv_nonneg.mpr h0.le) (hp x), ?_, ?_⟩
  · intro x
    rw [laplacian_fun_const_mul (smooth_C2 hf), heq x]
    ring
  · exact inv_mul_cancel₀ h0.ne'

lemma positiveLinearCone_extreme_translate {n : ℕ} {P f : Space n → ℝ}
    (hP : ContDiff ℝ ∞ P) {R : ℝ} (hR : 0 ≤ R)
    (hPb : ∀ x, |P x| ≤ R) (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (hP2 : ∀ x, P x ≤ 2)
    (hf : f ∈ (positiveLinearCone P).extremePoints ℝ)
    (t : Space n) (ht : ∀ x, P (t + x) = P x) :
    ∀ x, f (t + x) = f t * f x := by
  have hm := hf.1
  have hp := positiveLinearCone_pos hP2 hm
  let C := Real.exp (Real.sqrt (linearLogGradientBound n R) * ‖t‖) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let g := fun x => C⁻¹ * f (t + x)
  let k := fun x => f x - g x
  have hts : ContDiff ℝ ∞ (fun x => f (t+x)) := hm.1.comp (contDiff_const.add contDiff_id)
  have hgs : ContDiff ℝ ∞ g := contDiff_const.mul hts
  have hks : ContDiff ℝ ∞ k := hm.1.sub hgs
  have hgp (x) : 0 < g x := mul_pos (inv_pos.mpr hC) (hp (t+x))
  have hglt (x) : g x < f x := by
    have H := positive_linear_harnack hm.1 hP hp hR hPb hPd hm.2.2.1 x (t+x)
    simp only [add_sub_cancel_right] at H
    have HH : f (t+x) < C * f x := by dsimp [C]; nlinarith [hp x]
    change C⁻¹ * f (t+x) < f x
    simpa only [div_eq_inv_mul] using (div_lt_iff₀ hC).mpr (by simpa [mul_comm] using HH)
  have hkp (x) : 0 < k x := sub_pos.mpr (hglt x)
  have hgeq (x) : Laplacian.laplacian g x = P x * g x := by
    dsimp only [g]
    rw [laplacian_fun_const_mul (smooth_C2 hts),
      laplacian_translate (smooth_C2 hm.1), hm.2.2.1, ht]
    ring
  have hkeq (x) : Laplacian.laplacian k x = P x * k x := by
    dsimp only [k]
    rw [laplacian_fun_sub (smooth_C2 hm.1) (smooth_C2 hgs), hm.2.2.1, hgeq]
    ring
  have hgmem := positiveLinearCone_normalize hgs (fun x => (hgp x).le) hgeq (hgp 0)
  have hkmem := positiveLinearCone_normalize hks (fun x => (hkp x).le) hkeq (hkp 0)
  have hab : g 0 + k 0 = 1 := by dsimp [k]; rw [hm.2.2.2]; ring
  have hseg : f ∈ openSegment ℝ (fun x => (g 0)⁻¹ * g x) (fun x => (k 0)⁻¹ * k x) := by
    refine ⟨g 0, k 0, hgp 0, hkp 0, hab, ?_⟩
    funext x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (hgp 0).ne', one_mul,
      ← mul_assoc, mul_inv_cancel₀ (hkp 0).ne', one_mul]
    dsimp [k]; ring
  have hex := hf.2 hgmem hkmem hseg
  intro x
  have H := congrFun hex x
  change (C⁻¹ * f (t + 0))⁻¹ * (C⁻¹ * f (t+x)) = f x at H
  simp only [add_zero] at H
  field_simp [hC.ne', (hp t).ne'] at H
  nlinarith [H]

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open scoped ContDiff

lemma positiveLinearCone_extreme_character {n : ℕ} {P f : Space n → ℝ}
    (hP : ContDiff ℝ ∞ P) {R : ℝ} (hR : 0 ≤ R)
    (hPb : ∀ x, |P x| ≤ R) (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (hP2 : ∀ x, P x ≤ 2)
    (hf : f ∈ (positiveLinearCone P).extremePoints ℝ)
    (H : Submodule ℝ (Space n)) (hH : ∀ t ∈ H, ∀ x, P (t+x) = P x) :
    ∃ b : H, ∀ (t : H) (x : Space n),
      f ((t : Space n) + x) = Real.exp (inner ℝ b t) * f x := by
  have hp := positiveLinearCone_pos hP2 hf.1
  have htrans (t : H) := positiveLinearCone_extreme_translate hP hR hPb hPd hP2 hf
    (t : Space n) (hH t t.property)
  let L : H →+ ℝ :=
    { toFun := fun t => Real.log (f (t : Space n))
      map_zero' := by simp [hf.1.2.2.2]
      map_add' := by
        intro a b
        change Real.log (f ((a : Space n) + (b : Space n))) = _
        rw [htrans a, Real.log_mul (hp a).ne' (hp b).ne'] }
  have hL : Continuous L :=
    (hf.1.1.continuous.log (fun x => (hp x).ne')).comp continuous_subtype_val
  let l : H →L[ℝ] ℝ := L.toRealLinearMap hL
  let b : H := (InnerProductSpace.toDual ℝ H).symm l
  refine ⟨b, fun t x => ?_⟩
  rw [htrans t]
  congr 1
  have he : inner ℝ b t = Real.log (f (t : Space n)) := by
    exact InnerProductSpace.toDual_symm_apply
  rw [he, Real.exp_log (hp t)]

lemma linear_quotient_drift {n : ℕ} {f u P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (hp : ∀ x, 0 < f x)
    (heq : ∀ x, Laplacian.laplacian f x = P x * f x) (x : Space n) :
    Laplacian.laplacian (fun y => u y/f y) x -
      fderiv ℝ (fun y => u y/f y) x ((-2:ℝ) • gradient (fun y => Real.log (f y)) x) =
      (Laplacian.laplacian u x-P x*u x)/f x := by
  let q := fun y => u y/f y
  have hq : ContDiff ℝ ∞ q := hu.div hf (fun y => (hp y).ne')
  have hfq : (fun y => q y*f y) = u := by funext y; dsimp [q]; field_simp [(hp y).ne']
  have H := laplacian_fun_mul (smooth_C2 hq) (smooth_C2 hf) x
  rw [hfq, heq x] at H
  rw [gradient_log (hf.differentiable (by simp) x) (hp x).ne', smul_smul,
    map_smul, smul_eq_mul, ← inner_gradient_left]
  change Laplacian.laplacian q x - (-2*(f x)⁻¹)*inner ℝ (gradient q x) (gradient f x) = _
  dsimp [q] at H
  apply (eq_div_iff (hp x).ne').mpr
  have H' := H
  field_simp [ne_of_gt (hp x)] at H' ⊢
  nlinarith

lemma positive_linear_jet_step {n : ℕ} {f u P : Space n → ℝ}
    (hf : ContDiff ℝ ∞ f) (hu : ContDiff ℝ ∞ u) (hp : ∀ x, 0 < f x)
    (heq : ∀ x, Laplacian.laplacian f x = P x*f x)
    {M C L : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hb : ∀ x, |u x| ≤ M*f x)
    (hPu : ∀ x, |Laplacian.laplacian u x-P x*u x| ≤ C*f x)
    (hlog : ∀ x, ‖gradient (fun y => Real.log (f y)) x‖ ≤ L)
    (i : Fin n) (x : Space n) :
    |coordDeriv u i x| ≤ (2*(2*M+C+3)*(2*L+1)+M*L)*f x := by
  let q := fun y => u y/f y
  have hq : ContDiff ℝ ∞ q := hu.div hf (fun y => (hp y).ne')
  have hqb (y) : |q y| ≤ M := by
    rw [show q y=u y/f y from rfl, abs_div, abs_of_pos (hp y)]
    exact (div_le_iff₀ (hp y)).mpr (hb y)
  have hdb (y) : ‖(-2:ℝ) • gradient (fun z => Real.log (f z)) y‖ ≤ 2*L := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using
      mul_le_mul_of_nonneg_left (hlog y) (by norm_num : (0:ℝ) ≤ 2)
  have hdp (y) : |Laplacian.laplacian q y-fderiv ℝ q y
      ((-2:ℝ) • gradient (fun z => Real.log (f z)) y)| ≤ C := by
    rw [linear_quotient_drift hf hu hp heq, abs_div, abs_of_pos (hp y)]
    exact (div_le_iff₀ (hp y)).mpr (hPu y)
  have H := PoissonSupport.DeGiorgi.bounded_drift_gradient (smooth_C2 hq)
    (fun y => (-2:ℝ) • gradient (fun z => Real.log (f z)) y)
    hM hC (by positivity : 0 ≤ 2*L) hqb hdb hdp x
  have Hqi : |coordDeriv q i x| ≤ 2*(2*M+C+3)*(2*L+1) :=
    (coordDeriv_abs_le_gradient q i x).trans H
  have Hfi : |coordDeriv f i x/f x| ≤ L := by
    rw [← coordDeriv_log (hf.differentiable (by simp)) (fun y => (hp y).ne')]
    exact (coordDeriv_abs_le_gradient _ i x).trans (hlog x)
  have he : coordDeriv u i x =
      (coordDeriv q i x+q x*(coordDeriv f i x/f x))*f x := by
    rw [coordDeriv_div (hu.differentiable (by simp)) (hf.differentiable (by simp))
      (fun y => (hp y).ne')]
    dsimp [q]
    field_simp [ne_of_gt (hp x)]
    ring
  rw [he, abs_mul, abs_of_pos (hp x)]
  apply mul_le_mul_of_nonneg_right _ (hp x).le
  calc |coordDeriv q i x+q x*(coordDeriv f i x/f x)| ≤
      |coordDeriv q i x| + |q x| * |coordDeriv f i x/f x| := by simpa only [abs_mul] using abs_add_le (coordDeriv q i x) (q x*(coordDeriv f i x/f x))
    _ ≤ 2*(2*M+C+3)*(2*L+1)+M*L := add_le_add Hqi (mul_le_mul (hqb x) Hfi (abs_nonneg _) hM)

lemma positiveLinearCone_relative_jets {n : ℕ} {P : Space n → ℝ}
    (hP : ContDiff ℝ ∞ P) {R : ℝ} (hR : 0 ≤ R)
    (hPb : ∀ x, |P x| ≤ R) (hPd : ∀ i x, |coordDeriv P i x| ≤ R)
    (hP2 : ∀ x, P x ≤ 2)
    (hPjets : ∀ l : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |coordinateJet P l x| ≤ C) :
    ∀ l : List (Fin n), ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ positiveLinearCone P,
      ∀ x, |coordinateJet f l x| ≤ M*f x := by
  have H (k : ℕ) : ∀ l : List (Fin n), l.length ≤ k → ∃ M : ℝ, 0 ≤ M ∧
      ∀ f ∈ positiveLinearCone P, ∀ x, |coordinateJet f l x| ≤ M*f x := by
    induction k with
    | zero =>
      intro l hl
      have he : l=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hl)
      subst l
      refine ⟨1, by norm_num, ?_⟩
      intro f hf x
      simpa only [coordinateJet, one_mul, abs_of_nonneg (hf.2.1 x)] using (le_rfl : f x ≤ f x)
    | succ k ih =>
      intro l hl
      cases l with
      | nil =>
        refine ⟨1, by norm_num, ?_⟩
        intro f hf x
        simpa only [coordinateJet, one_mul, abs_of_nonneg (hf.2.1 x)] using (le_rfl : f x ≤ f x)
      | cons i l =>
        have hlen : l.length ≤ k := by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hl
        obtain ⟨M,hM,hMb⟩ := ih l hlen
        obtain ⟨C,hC,hCb⟩ := list_relative_sum_bound (jetSplits l)
          (fun p f x => coordinateJet P p.1 x*coordinateJet f p.2 x)
          (fun f x => f x) (positiveLinearCone P) (by
            intro p hp
            obtain ⟨D,hD,hDb⟩ := hPjets p.1
            obtain ⟨N,hN,hNb⟩ := ih p.2 ((jetSplits_length l p hp).2.trans hlen)
            refine ⟨D*N, mul_nonneg hD hN, ?_⟩
            intro f hf x
            rw [abs_mul]
            calc |coordinateJet P p.1 x| * |coordinateJet f p.2 x| ≤ D*(N*f x) :=
                mul_le_mul (hDb x) (hNb f hf x) (abs_nonneg _) hD
              _ = (D*N)*f x := by ring)
        let L := Real.sqrt (linearLogGradientBound n R)
        let C' := C+R*M
        have hC' : 0 ≤ C' := add_nonneg hC (mul_nonneg hR hM)
        refine ⟨2*(2*M+C'+3)*(2*L+1)+M*L, by dsimp [L]; positivity, ?_⟩
        intro f hf x
        have hfp := positiveLinearCone_pos hP2 hf
        have hjet := coordinateJet_smooth hf.1 l
        have hsource (y) : |Laplacian.laplacian (coordinateJet f l) y-P y*coordinateJet f l y| ≤ C'*f y := by
          have he : Laplacian.laplacian f = fun z => P z*f z := funext hf.2.2.1
          rw [coordinateJet_laplacian hf.1 l, he, coordinateJet_mul hP hf.1]
          calc |((jetSplits l).map (fun p => coordinateJet P p.1 y*coordinateJet f p.2 y)).sum -
              P y*coordinateJet f l y| ≤
              |((jetSplits l).map (fun p => coordinateJet P p.1 y*coordinateJet f p.2 y)).sum| +
                |P y| * |coordinateJet f l y| := by simpa only [abs_mul, abs_neg, sub_eq_add_neg] using abs_add_le (((jetSplits l).map (fun p => coordinateJet P p.1 y*coordinateJet f p.2 y)).sum) (-(P y*coordinateJet f l y))
            _ ≤ C*f y+R*(M*f y) := add_le_add (hCb f hf y)
              (mul_le_mul (hPb y) (hMb f hf y) (abs_nonneg _) hR)
            _ = C'*f y := by dsimp [C']; ring
        exact positive_linear_jet_step hf.1 hjet hfp hf.2.2.1 hM hC'
          (Real.sqrt_nonneg _) (hMb f hf) hsource
          (positive_linear_log_gradient hf.1 hP hfp hR hPb hPd hf.2.2.1) i x
  intro l
  exact H l.length l le_rfl

end DeGiorgi
end

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped SchwartzMap Laplacian ContDiff
open FourierTransform
open Filter Topology
open scoped ContDiff

def sech (y : ℝ) : ℝ := (Real.cosh y)⁻¹

lemma sech_pos (y : ℝ) : 0 < sech y := inv_pos.mpr (Real.cosh_pos y)

lemma cosh_sq_ge_one (y : ℝ) : 1 ≤ Real.cosh y ^ 2 := by
  nlinarith [Real.cosh_sq_sub_sinh_sq y, sq_nonneg (Real.sinh y)]

lemma contDiff_sech : ContDiff ℝ ∞ sech :=
  Real.contDiff_cosh.inv (fun y => (Real.cosh_pos y).ne')

lemma sech_hasDerivAt (y : ℝ) :
    HasDerivAt sech (-Real.sinh y / Real.cosh y ^ 2) y := by
  exact (Real.hasDerivAt_cosh y).inv (Real.cosh_pos y).ne'

lemma sech_deriv (y : ℝ) : deriv sech y = -Real.sinh y / Real.cosh y ^ 2 :=
  (sech_hasDerivAt y).deriv

lemma sech_hasDerivAt_twice (y : ℝ) :
    HasDerivAt (deriv sech) ((1 - 2 * sech y ^ 2) * sech y) y := by
  have H := ((Real.hasDerivAt_sinh y).neg.div ((Real.hasDerivAt_cosh y).pow 2)
    (pow_ne_zero 2 (Real.cosh_pos y).ne'))
  have he : (-(Real.cosh y) * Real.cosh y ^ 2 - -Real.sinh y *
      (2 * Real.cosh y ^ (2-1) * Real.sinh y)) / (Real.cosh y ^ 2) ^ 2 =
      (1 - 2 * sech y ^ 2) * sech y := by
    dsimp [sech]
    field_simp
    nlinarith [Real.cosh_sq_sub_sinh_sq y]
  change HasDerivAt (fun z => -Real.sinh z / Real.cosh z ^ 2)
    ((-Real.cosh y * Real.cosh y ^ 2 - -Real.sinh y *
      (2 * Real.cosh y ^ (2-1) * Real.sinh y)) / (Real.cosh y ^ 2) ^ 2) y at H
  rw [he] at H
  simpa only [← funext sech_deriv] using H

lemma positive_antitone_flux_zero {w W p : ℝ → ℝ}
    (hw : Differentiable ℝ w) (hwp : ∀ x, 0 < w x)
    (hW : Antitone W) (hp : ∀ x, 1 ≤ p x)
    (heq : ∀ x, deriv w x = W x * p x) : ∀ x, W x = 0 := by
  intro z
  rcases lt_trichotomy (W z) 0 with hz | hz | hz
  · let y := z + (w z + 1) / (-W z)
    have hzy : z ≤ y := by dsimp [y]; exact le_add_of_nonneg_right (div_nonneg (by linarith [hwp z]) (by linarith))
    have hb : ∀ x ∈ interior (Set.Ici z), deriv w x ≤ W z := by
      intro x hx
      have hzx : x ∈ Set.Ici z := interior_subset hx
      rw [heq x]
      have hWx := hW hzx
      calc
        W x * p x ≤ W z * p x := mul_le_mul_of_nonneg_right hWx (by linarith [hp x])
        _ ≤ W z := by nlinarith [hp x]
    have HH := (convex_Ici z).image_sub_le_mul_sub_of_deriv_le
      hw.continuous.continuousOn hw.differentiableOn hb z (by simp) y hzy hzy
    have hm : W z * (y-z) = -(w z + 1) := by dsimp [y]; field_simp [ne_of_lt hz]; ring
    rw [hm] at HH
    linarith [hwp y]
  · exact hz
  · let y := z - (w z + 1) / W z
    have hyz : y ≤ z := by dsimp [y]; exact sub_le_self z (div_nonneg (by linarith [hwp z]) hz.le)
    have hb : ∀ x ∈ interior (Set.Iic z), W z ≤ deriv w x := by
      intro x hx
      have hxz : x ∈ Set.Iic z := interior_subset hx
      rw [heq x]
      have hWx := hW hxz
      calc
        W z ≤ W z * p x := by nlinarith [hp x]
        _ ≤ W x * p x := mul_le_mul_of_nonneg_right hWx (by linarith [hp x])
    have HH := (convex_Iic z).mul_sub_le_image_sub_of_le_deriv
      hw.continuous.continuousOn hw.differentiableOn hb y hyz z (by simp) hyz
    have hm : W z * (z-y) = w z + 1 := by dsimp [y]; field_simp [ne_of_gt hz]; ring
    rw [hm] at HH
    linarith [hwp y]

end DeGiorgi
end

end OAI
