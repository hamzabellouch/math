import OAI.Analysis.LienardCycles.MixedDerivatives

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open PartialCalculus QuadraticCoordinates

noncomputable def C (q : (ℝ × ℝ) × ℝ) : ℝ := -2*(J q*A q+1/q.2)
noncomputable def E (q : (ℝ × ℝ) × ℝ) : ℝ := 2*A q/(q.2*(1-(A q)^2))
noncomputable def K (q : (ℝ × ℝ) × ℝ) : ℝ := 2*(1+(A q)^2)/(q.2*(1-(A q)^2)^2)
noncomputable def U (q : (ℝ × ℝ) × ℝ) : ℝ := Dz q/(1-(D q)^2)
noncomputable def V (q : (ℝ × ℝ) × ℝ) : ℝ := Dk q/(1-(D q)^2)
noncomputable def T (q : (ℝ × ℝ) × ℝ) : ℝ := Ak q/Az q
noncomputable def B (q : (ℝ × ℝ) × ℝ) : ℝ := V q-T q*U q

lemma Az_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Az ((z,k),s))
      ((1-(A ((z,k),r))^2)*Jz ((z,k),r)+C ((z,k),r)*Az ((z,k),r)) r := by
  apply mixed_z_radius (f := A)
    (fr := fun q => J q*(1-(A q)^2)-2*A q/q.2) (fun _ hp => A_analytic hp) hr
    (fun a => A_deriv hr)
  convert! ((Jz_hasDerivAt (z := z) (k := k) hr).mul
    (((Az_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1)).sub
      (((Az_hasDerivAt (z := z) (k := k) hr).const_mul 2).div_const r) using 1
  dsimp [C]
  ring

lemma Ak_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Ak ((z,k),s))
      ((1-(A ((z,k),r))^2)*Jk ((z,k),r)+C ((z,k),r)*Ak ((z,k),r)) r := by
  apply mixed_k_radius (f := A)
    (fr := fun q => J q*(1-(A q)^2)-2*A q/q.2) (fun _ hp => A_analytic hp) hr
    (fun a => A_deriv hr)
  convert! ((Jk_hasDerivAt (z := z) (k := k) hr).mul
    (((Ak_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1)).sub
      (((Ak_hasDerivAt (z := z) (k := k) hr).const_mul 2).div_const r) using 1
  dsimp [C]
  ring

lemma E_z_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => E ((s,k),r)) (K ((z,k),r)*Az ((z,k),r)) z := by
  convert! ((Az_hasDerivAt (z := z) (k := k) hr).const_mul 2).div
    ((((Az_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1).const_mul r)
      (ne_of_gt (mul_pos hr (A_gap_pos (q := ((z,k),r)) hr))) using 1
  dsimp [E,K]
  field_simp
  ring

lemma E_k_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => E ((z,s),r)) (K ((z,k),r)*Ak ((z,k),r)) k := by
  convert! ((Ak_hasDerivAt (z := z) (k := k) hr).const_mul 2).div
    ((((Ak_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1).const_mul r)
      (ne_of_gt (mul_pos hr (A_gap_pos (q := ((z,k),r)) hr))) using 1
  dsimp [E,K]
  field_simp
  ring

lemma D_deriv' {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => D ((z,k),s)) (E ((z,k),r)*(1-(D ((z,k),r))^2)) r := by
  convert D_deriv (z := z) (k := k) hr using 1
  dsimp [E]
  ring

lemma Dz_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Dz ((z,k),s))
      (K ((z,k),r)*Az ((z,k),r)*(1-(D ((z,k),r))^2)-
        2*E ((z,k),r)*D ((z,k),r)*Dz ((z,k),r)) r := by
  apply mixed_z_radius (f := D) (fr := fun q => E q*(1-(D q)^2))
    (fun _ hp => D_analytic hp) hr (fun a => D_deriv' hr)
  convert! (E_z_deriv (z := z) (k := k) hr).mul
    (((Dz_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1) using 1
  dsimp only [Pi.pow_apply]
  ring

lemma Dk_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => Dk ((z,k),s))
      (K ((z,k),r)*Ak ((z,k),r)*(1-(D ((z,k),r))^2)-
        2*E ((z,k),r)*D ((z,k),r)*Dk ((z,k),r)) r := by
  apply mixed_k_radius (f := D) (fr := fun q => E q*(1-(D q)^2))
    (fun _ hp => D_analytic hp) hr (fun a => D_deriv' hr)
  convert! (E_k_deriv (z := z) (k := k) hr).mul
    (((Dk_hasDerivAt (z := z) (k := k) hr).pow 2).const_sub 1) using 1
  dsimp only [Pi.pow_apply]
  ring

lemma U_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => U ((z,k),s)) (K ((z,k),r)*Az ((z,k),r)) r := by
  convert! (Dz_deriv (z := z) (k := k) hr).div
    (((D_deriv' (z := z) (k := k) hr).pow 2).const_sub 1)
      (ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)) using 1
  dsimp only [Pi.pow_apply]
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
  ring

lemma V_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => V ((z,k),s)) (K ((z,k),r)*Ak ((z,k),r)) r := by
  convert! (Dk_deriv (z := z) (k := k) hr).div
    (((D_deriv' (z := z) (k := k) hr).pow 2).const_sub 1)
      (ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)) using 1
  dsimp only [Pi.pow_apply]
  field_simp [ne_of_gt (D_gap_pos (q := ((z,k),r)) hr)]
  ring

lemma T_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => T ((z,k),s))
      (-(1-(A ((z,k),r))^2)*Q ((J ((z,k),r),k),r)*Jz ((z,k),r)/
        (r*(Az ((z,k),r))^2)) r := by
  convert! (Ak_deriv (z := z) (k := k) hr).div (Az_deriv (z := z) (k := k) hr)
    (ne_of_gt (Az_pos (z := z) (k := k) hr)) using 1
  have h1 := Az_formula (z := z) (k := k) hr
  have h2 := Ak_formula (z := z) (k := k) hr
  rw [h1,h2]
  field_simp
  ring

lemma B_deriv {z k r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun s => B ((z,k),s))
      ((1-(A ((z,k),r))^2)*Q ((J ((z,k),r),k),r)*Jz ((z,k),r)/
        (r*(Az ((z,k),r))^2)*U ((z,k),r)) r := by
  convert! (V_deriv (z := z) (k := k) hr).sub
    ((T_deriv (z := z) (k := k) hr).mul (U_deriv (z := z) (k := k) hr)) using 1
  dsimp [B,T]
  field_simp [ne_of_gt (Az_pos (z := z) (k := k) hr)]
  ring

lemma B_formula {z k r : ℝ} (hr : 0 < r) :
    B ((z,k),r) = G ((J ((z,k),r),k),r)/(P ((J ((z,k),r),k),r)*(1-(D ((z,k),r))^2)) := by
  dsimp only [B,V,T,U]
  rw [Dk_formula hr,Dz_formula hr,Az_formula hr,Ak_formula hr]
  dsimp [G]
  field_simp [ne_of_gt (QuadraticVariation.P_pos (d := J ((z,k),r)) (k := k) hr),
    ne_of_gt (Jz_pos (z := z) (k := k) hr),ne_of_gt hr]
  ring

end QuinticLienard.ReferenceCharacteristic

end OAI
