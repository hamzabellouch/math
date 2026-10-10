import OAI.Geometry.Relativity.CKS.AngularSlice

namespace OAI

noncomputable section
namespace CKSFrame
noncomputable section
open CKSCalculus
open scoped BigOperators

def u (r : ℝ) (c : ConnectionData) : ℝ := r*mean c/2
def v (r : ℝ) (t : TensorData) : ℝ := r*t.p/2
def mass (r : ℝ) (c : ConnectionData) (t : TensorData) : ℝ :=
  r/2*(1+(v r t)^2-(u r c)^2)

def normalMass (r U : ℝ) (c : ConnectionData) (dc : I → ConnectionData)
    (t : TensorData) (dt : I → TensorData) : ℝ :=
  U/2*(1+(v r t)^2-(u r c)^2)+r*((v r t)*(U*t.p/2+r*(dt 0).p/2)-
    (u r c)*(U*mean c/2+r*normalMean dc/2))

theorem mass_identity {r : ℝ} (hr : r ≠ 0) (U : ℝ) (c : ConnectionData)
    (dc : I → ConnectionData) (t : TensorData) (dt : I → TensorData)
    (hu : u r c ≠ 0) :
    energy c dc t-v r t/u r c*momentum c t dt 0 =
      2*normalMass r U c dc t dt/(u r c*r^2)+(leafScalar c dc/2-1/r^2)+
      (U/u r c-1)*(2-6*mass r c t/r)/r^2+accelDiv c dc-accelNormSq c-
      (shearNormSq c+tauNormSq t)/2+v r t/u r c*shearTau c t-etaNormSq t-
      v r t/u r c*(etaDiv c t dt-2*etaAcceleration c t) := by
  rw [energy_decomposition,normal_momentum_decomposition]
  have hH : mean c ≠ 0 := by intro h; apply hu; simp [u,h]
  unfold normalMass mass u v
  field_simp
  ring

abbrev Chart := I → ℝ

def normalVector (U : ℝ) (s : A → ℝ) : Chart := ![U,-U*s 0,-U*s 1]

def massField (H p : Chart → ℝ) : Chart → ℝ := fun x =>
  x 0/2*(1+(x 0*p x/2)^2-(x 0*H x/2)^2)

lemma normal_radius (U : ℝ) (s : A → ℝ) (x : Chart) :
    D (normalVector U s) (fun y : Chart => y 0) x = U := by
  change D (normalVector U s) (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : I => ℝ) 0) x = U
  rw [D_clm]
  rfl

lemma normal_mass_derivative {H p : Chart → ℝ} {x : Chart}
    (hH : DifferentiableAt ℝ H x) (hp : DifferentiableAt ℝ p x) (U : ℝ) (s : A → ℝ) :
    D (normalVector U s) (massField H p) x =
      U/2*(1+(x 0*p x/2)^2-(x 0*H x/2)^2)+x 0*((x 0*p x/2)*
        (U*p x/2+x 0*D (normalVector U s) p x/2)-
        (x 0*H x/2)*(U*H x/2+x 0*D (normalVector U s) H x/2)) := by
  have hr : DifferentiableAt ℝ (fun y : Chart => y 0) x := by fun_prop
  have ht : DifferentiableAt ℝ (fun y : Chart => y 0*p y/2) x := diffAt_div (hr.fun_mul hp) (differentiableAt_const _) (by norm_num)
  have hu : DifferentiableAt ℝ (fun y : Chart => y 0*H y/2) x := diffAt_div (hr.fun_mul hH) (differentiableAt_const _) (by norm_num)
  have hc : DifferentiableAt ℝ (fun _ : Chart => (1:ℝ)) x := differentiableAt_const _
  unfold massField
  erw [D_mul _ (diffAt_div hr (differentiableAt_const (2:ℝ)) (by norm_num)) ((hc.add (ht.pow 2)).sub (hu.pow 2)),
    D_div _ hr (differentiableAt_const _) (by norm_num),D_const,
    D_sub _ (hc.add (ht.pow 2)) (hu.pow 2),D_add _ hc (ht.pow 2),D_const,
    D_pow _ 2 ht,D_pow _ 2 hu,
    D_div _ (hr.fun_mul hp) (differentiableAt_const _) (by norm_num),
    D_div _ (hr.fun_mul hH) (differentiableAt_const _) (by norm_num),D_const,
    D_mul _ hr hp,D_mul _ hr hH,normal_radius]
  simp only [Pi.add_apply,Pi.sub_apply,Pi.pow_apply]
  ring

end
end CKSFrame

end

end OAI
