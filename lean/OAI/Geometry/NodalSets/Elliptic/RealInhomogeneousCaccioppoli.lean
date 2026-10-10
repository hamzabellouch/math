import OAI.Geometry.NodalSets.Elliptic.RealInhomogeneousPointwise
import OAI.Geometry.NodalSets.Elliptic.RealInhomogeneousWeakEquation
import OAI.Geometry.NodalSets.Elliptic.RealTransportQuadratic

namespace OAI

namespace Yau.Geometry
open MeasureTheory
open scoped ContDiff
noncomputable section

lemma real_pairing_cutoff (eta W : Yau.Jets.Coord → ℝ)
    (heta : ContDiff ℝ ∞ eta) (hW : ContDiff ℝ ∞ W)
    (F : Yau.Jets.Coord → Yau.Jets.Coord) (x : Yau.Jets.Coord) :
    Yau.pairing (fun y ↦ eta y^2*W y) F x =
      eta x^2*(∑ i, Yau.coordPartial W x i*F x i)+
        2*eta x*W x*(∑ i, Yau.coordPartial eta x i*F x i) := by
  change (∑ i, realCoordGradient (fun y ↦ eta y^2*W y) x i*F x i) = _
  rw [realCoordGradient_cutoff eta W heta hW x]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,Finset.sum_add_distrib,
    mul_assoc,← Finset.mul_sum,realCoordGradient]

theorem real_inhomogeneous_caccioppoli (k L M : ℝ)
    (hk : 0 < k) (hL : 0 < L) (hM : 0 ≤ M) :
    ∃ K > 0, ∀ (C : Yau.Jets.Coord → Matrix (Fin 4) (Fin 4) ℝ)
      (V W f eta : Yau.Jets.Coord → ℝ) (F : Yau.Jets.Coord → Yau.Jets.Coord),
      (∀ i j, ContDiff ℝ ∞ (fun x ↦ C x i j)) → ContDiff ℝ ∞ V →
      ContDiff ℝ ∞ W → ContDiff ℝ ∞ f → ContDiff ℝ ∞ eta →
      (∀ i, ContDiff ℝ ∞ (fun x ↦ F x i)) → HasCompactSupport eta →
      (∀ x i j, C x i j=C x j i) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        k*(∑ i, z i^2) ≤ ∑ i, ∑ j, z i*C x i j*z j) →
      (∀ x ∈ tsupport eta, ∀ z : Yau.Jets.Coord,
        (∑ i, ∑ j, z i*C x i j*z j) ≤ L*(∑ i, z i^2)) →
      (∀ x ∈ tsupport eta, |V x| ≤ M) →
      (∀ x, Yau.coordDiv (realMatrixFlux C W) x+V x*W x=Yau.coordDiv F x+f x) →
      Integrable (fun x ↦ eta x^2*realGradientSquare W x) ∧
      Integrable (fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2) ∧
      Integrable (fun x ↦ eta x^2*f x^2) ∧
      Integrable (fun x ↦ eta x^2*(∑ i, F x i^2)) ∧
      (∫ x, eta x^2*realGradientSquare W x) ≤ K *
        ((∫ x, (eta x^2+realGradientSquare eta x)*W x^2)+
          (∫ x, eta x^2*f x^2)+(∫ x, eta x^2*(∑ i, F x i^2))) := by
  let D := M+4*L+k⁻¹+3
  refine ⟨(2/k)*D,by dsimp [D]; positivity,?_⟩
  intro C V W f eta F hC hV hW hf heta hF hc hs hlo hhi hpot he
  let phi := fun x ↦ eta x^2*W x
  let a := fun x ↦ eta x^2*realGradientSquare W x
  let q := fun x ↦ (eta x^2+realGradientSquare eta x)*W x^2
  let r := fun x ↦ eta x^2*f x^2
  let s := fun x ↦ eta x^2*(∑ i, F x i^2)
  have hcsq : HasCompactSupport (fun x ↦ eta x^2) := by
    convert hc.mul_right (f' := eta) using 1
    first | rfl | (ext x; simp [pow_two])
  have ha : Integrable a := ((heta.pow 2).mul (realGradientSquare_smooth W hW)).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  have hq : Integrable q := (((heta.pow 2).add (realGradientSquare_smooth eta heta)).mul (hW.pow 2)).continuous.integrable_of_hasCompactSupport
    (hcsq.add (realGradientSquare_compact eta hc)).mul_right
  have hr : Integrable r := ((heta.pow 2).mul (hf.pow 2)).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  have hsint : Integrable s := ((heta.pow 2).mul (ContDiff.sum (fun i _ ↦ (hF i).pow 2))).continuous.integrable_of_hasCompactSupport hcsq.mul_right
  obtain ⟨hE,hP,hFint,hfint,hweak⟩ := real_inhomogeneous_density_test C V W f phi F
    hC hV hW hf hF ((heta.pow 2).mul hW) hcsq.mul_right he
  let R := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x-Yau.pairing phi F x+phi x*f x
  have hR : Integrable R := ((hE.sub hP).sub hFint).add hfint
  have hRzero : (∫ x, R x)=0 := by
    dsimp [R]
    rw [integral_add (f := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x-Yau.pairing phi F x)
        ((hE.sub hP).sub hFint) hfint,
      integral_sub (f := fun x ↦ realMatrixEnergy C phi W x-phi x*V x*W x) (hE.sub hP) hFint,
      integral_sub hE hP,hweak]
    ring
  have hpoint (x : Yau.Jets.Coord) : k/2*a x ≤ R x+D*(q x+r x+s x) := by
    by_cases hx : x ∈ tsupport eta
    · have hh := real_inhomogeneous_pointwise k L M hk hL hM (C x) (hs x)
        (fun z ↦ by simpa only [coordMatrixForm_apply] using hlo x hx z)
        (fun z ↦ by simpa only [coordMatrixForm_apply] using hhi x hx z)
        (eta x) (W x) (V x) (f x) (hpot x hx)
        (realCoordGradient W x) (realCoordGradient eta x) (F x)
      dsimp [R,phi]
      rw [realMatrixEnergy_cutoff C eta W heta hW x,real_pairing_cutoff eta W heta hW F x]
      exact hh
    · have hz : eta x=0 := image_eq_zero_of_notMem_tsupport hx
      have hd := realCoordGradient_zero_off_support eta hx
      have hdz (i : Fin 4) : Yau.coordPartial eta x i=0 := congrFun hd i
      simp [a,R,phi,q,r,s,hz,realGradientSquare,hdz,
        realMatrixEnergy_cutoff C eta W heta hW x,real_pairing_cutoff eta W heta hW F x]
  have hint := integral_mono (ha.const_mul (k/2)) (hR.add (((hq.add hr).add hsint).const_mul D)) hpoint
  change (∫ x, k/2*a x) ≤ ∫ x, R x+D*(q x+r x+s x) at hint
  rw [integral_const_mul,integral_add (g := fun x ↦ D*(q x+r x+s x)) hR (((hq.add hr).add hsint).const_mul D),
    integral_const_mul,integral_add (f := fun x ↦ q x+r x) (hq.add hr) hsint,integral_add hq hr,hRzero,zero_add] at hint
  refine ⟨ha,hq,hr,hsint,?_⟩
  change (∫ x, a x) ≤ (2/k)*D*((∫ x, q x)+(∫ x, r x)+(∫ x, s x))
  have hi : (2/k)*(k/2)=1 := by field_simp
  have hh := mul_le_mul_of_nonneg_left hint (show 0 ≤ 2/k by positivity)
  rw [← mul_assoc,hi,one_mul] at hh
  simpa only [mul_assoc] using hh

end
end Yau.Geometry

end OAI
