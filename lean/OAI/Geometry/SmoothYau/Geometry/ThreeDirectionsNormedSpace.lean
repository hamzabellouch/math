import Mathlib
import OAI.Geometry.SmoothYau.Spectrum.ThreeCoupledNormedSpace

namespace OAI

noncomputable section
open Set Filter Function Manifold Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
local instance threeDirectionsNormedSpace : NormedSpace ℝ ThreeModel := inferInstance
local instance threeDirectionsContinuousSMul : ContinuousSMul ℝ ThreeModel := IsBoundedSMul.continuousSMul
local instance threeDirections_dimension_fact (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1))=n+1) := ⟨by simp [Euclidean]⟩
lemma productAxis_coord_le (p : Sphere 2) (i : Fin 3) : |(p:Euclidean 3) i| ≤ 1 := by
  have hn : ‖(p:Euclidean 3)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using p.property
  have h := abs_real_inner_le_norm (productAxis i) (p:Euclidean 3)
  simpa only [productAxis_coord,productAxis_norm,hn,one_mul] using h
lemma sphereCoordinates_norm_le {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A=n+1)]
    (p : Metric.sphere (0:A) 1) (a : A) : ‖unitSphereCoordinates (n:=n) p a‖ ≤ ‖a‖ := by
  have h := unitSphereCoordinates_inner (n:=n) p a a
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at h
  nlinarith [sq_nonneg (inner ℝ (p:A) a),norm_nonneg (unitSphereCoordinates (n:=n) p a),norm_nonneg a]
lemma productA_projection (p : Sphere 2) (a : Euclidean 3) :
    productA (unitSphereProjection p a)=productA a-(inner ℝ (p:Euclidean 3) a:ℝ)*productA p := by
  simp [productA,unitSphereProjection,map_sub,map_smul,Complex.real_smul]
lemma productB_projection (p : Sphere 2) (a : Euclidean 3) :
    productB (unitSphereProjection p a)=productB a-(inner ℝ (p:Euclidean 3) a:ℝ)*productB p := by
  simp [productB,unitSphereProjection,map_sub,map_smul,Complex.real_smul]
lemma productA_axis (i : Fin 3) : productA (productAxis i) =
    (if i=0 then 1 else 0)+(if i=1 then Complex.I else 0) := by
  fin_cases i <;> apply Complex.ext <;> norm_num [productA_re,productA_im,productAxis,PiLp.single_apply,Fin.ext_iff]
lemma productB_axis (i : Fin 3) : productB (productAxis i) =
    (if i=0 then 1 else 0)+(if i=2 then Complex.I else 0) := by
  fin_cases i <;> apply Complex.ext <;> norm_num [productB_re,productB_im,productAxis,PiLp.single_apply,Fin.ext_iff]
def threeSphereDirection (p : ThreeManifold) (i : Fin 3) : ThreeModel :=
  WithLp.toLp 2 (unitSphereCoordinates (n:=2) p.1 (productAxis i),0)
lemma threeSphereDirection_norm (p : ThreeManifold) (i : Fin 3) : ‖threeSphereDirection p i‖ ≤ 1 := by
  change ‖WithLp.toLp 2 (unitSphereCoordinates (n:=2) p.1 (productAxis i),(0:Euclidean 1))‖≤1
  rw [WithLp.norm_toLp_fst]
  exact (sphereCoordinates_norm_le p.1 (productAxis i)).trans_eq (productAxis_norm i)
def threeCircleDirection (p : ThreeManifold) : ThreeModel :=
  WithLp.toLp 2 (0,unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))
lemma threeCircleDirection_norm (p : ThreeManifold) : ‖threeCircleDirection p‖ ≤ 1 := by
  have hn : ‖(p.2:ℂ)‖=1 := p.2.norm_coe
  change ‖WithLp.toLp 2 ((0:Euclidean 2),unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))‖≤1
  rw [WithLp.norm_toLp_snd]
  exact (sphereCoordinates_norm_le p.2 _).trans_eq (by simp [hn])
lemma productCircle_projection (p : Circle) :
    unitSphereProjection p (Complex.I*(p:ℂ))=Complex.I*(p:ℂ) := by
  have hi : inner ℝ (p:ℂ) (Complex.I*(p:ℂ))=0 := by
    simp [Complex.inner,Complex.mul_re,Complex.mul_im]; ring
  simp [unitSphereProjection,hi]
lemma threeCoupled_sphere_direction (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) (i : Fin 3) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 (threeSphereDirection p i)=
      (k:ℝ)*(((p.2:ℂ)^k*productA p.1^(k-1)*productA (productAxis i)+
        (p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)*productB (productAxis i)).re-
        (p.1:Euclidean 3) i*threeCoupled r k p) := by
  rw [threeCoupled_chart_first]
  change ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 (unitSphereCoordinates (n:=2) p.1 (productAxis i)))+
    (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 (unitSphereCoordinates (n:=2) p.1 (productAxis i))))+
    (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 0*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  rw [map_zero,mul_zero,zero_mul,add_zero,unitSphereFrame_coordinates,productA_projection,productB_projection,real_inner_comm,productAxis_coord]
  have hp (z : ℂ) : z^(k-1)*z=z^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : (k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*(productA (productAxis i)-((p.1:Euclidean 3) i:ℂ)*productA p.1)+
    (r:ℂ)^k*productB p.1^(k-1)*(productB (productAxis i)-((p.1:Euclidean 3) i:ℂ)*productB p.1))=
    (k:ℂ)*((p.2:ℂ)^k*productA p.1^(k-1)*productA (productAxis i)+(p.2:ℂ)^k*(r:ℂ)^k*productB p.1^(k-1)*productB (productAxis i)-
      ((p.1:Euclidean 3) i:ℂ)*threeCoupledComplex r k p) := by
    dsimp only [threeCoupledComplex]
    rw [←hp (productA p.1),←hp (productB p.1)]
    ring
  rw [he]
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero,
    Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,threeCoupled]
lemma threeCoupled_circle_direction (r : ℝ) (k : ℕ) (hk : 1≤k) (p : ThreeManifold) :
    fderiv ℝ (threeCoupled r k ∘ (chartAt ThreeModel p).symm) 0 (threeCircleDirection p)=
      -(k:ℝ)*(threeCoupledComplex r k p).im := by
  rw [threeCoupled_chart_first]
  change ((k:ℂ)*(p.2:ℂ)^k*(productA p.1^(k-1)*productA (unitSphereFrame (n:=2) p.1 0)+
    (r:ℂ)^k*productB p.1^(k-1)*productB (unitSphereFrame (n:=2) p.1 0))+
    (k:ℂ)*(p.2:ℂ)^(k-1)*unitSphereFrame (n:=1) p.2 (unitSphereCoordinates (n:=1) p.2 (Complex.I*(p.2:ℂ)))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  simp only [map_zero,productA,productB,mul_zero,add_zero,zero_add]
  erw [unitSphereFrame_coordinates,productCircle_projection]
  have hp : (p.2:ℂ)^(k-1)*(p.2:ℂ)=(p.2:ℂ)^k := by rw [←pow_succ,Nat.sub_add_cancel hk]
  have he : (k:ℂ)*(p.2:ℂ)^(k-1)*(Complex.I*(p.2:ℂ))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)=
      (k:ℂ)*Complex.I*threeCoupledComplex r k p := by
    dsimp only [threeCoupledComplex]
    rw [←hp]
    ring
  change ((k:ℂ)*(p.2:ℂ)^(k-1)*(Complex.I*(p.2:ℂ))*(productA p.1^k+(r:ℂ)^k*productB p.1^k)).re = _
  rw [he]
  simp [Complex.mul_re,Complex.mul_im]
end YauCounterexamples
end

end OAI
