import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousJordanChannels
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousHarmonicEigenmode

namespace OAI

/-! The radial source equation of an actual finite Jordan chain. -/

open Set
open scoped ContDiff Laplacian
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

def IsHarmonicRadialSourcePair (a b : ℝ) (m : ℕ) (Q : ℝ → ℂ) (eta lam : ℂ)
    (f g F G : ℝ → ℂ) : Prop :=
  ∀ r : ℝ, 0<r →
    (lam*f r+F r=Complex.I*(deriv (deriv f) r+(11/r : ℝ)*deriv f r-
      eta/(r^2 : ℝ)*f r)-(r/2 : ℝ)*deriv f r+(-(a : ℂ)+Complex.I*(b : ℂ))*f r-
      Complex.I*((((m+1 : ℕ) : ℂ)*Q r^m*star (Q r)^m)*f r+
        ((m : ℂ)*Q r^(m+1)*star (Q r)^(m-1))*g r)) ∧
    (lam*g r+G r= -Complex.I*(deriv (deriv g) r+(11/r : ℝ)*deriv g r-
      eta/(r^2 : ℝ)*g r)-(r/2 : ℝ)*deriv g r+(-(a : ℂ)-Complex.I*(b : ℂ))*g r+
      Complex.I*(star (((m+1 : ℕ) : ℂ)*Q r^m*star (Q r)^m)*g r+
        star ((m : ℂ)*Q r^(m+1)*star (Q r)^(m-1))*f r))

theorem homogeneous_harmonic_smul_add (a k : ℝ)
    (ha : 0<a) (ha1 : a<1) (hk : 8<k) (u v : HomogeneousY a k) (Y : E → ℂ)
    (hY : Continuous (fun z : PhysicalUnitSphere => Y z.1)) (c : ℂ) (r : ℝ) :
    harmonicAngularCoefficient Y
      (fun x => homogeneousPhysicalCLM a k ha ha1 hk (c • u+v) x) r=
    c*harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk u x) r+
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk v x) r := by
  let P := fun w : HomogeneousY a k => fun x : E => homogeneousPhysicalCLM a k ha ha1 hk w x
  have hf : (fun x => homogeneousPhysicalCLM a k ha ha1 hk (c • u+v) x)=
      (fun x => c*P u x+1*P v x+0*P 0 x+0*P 0 x) := by
    funext x
    simp only [map_add,map_smul,ZeroAtInftyContinuousMap.add_apply,
      ZeroAtInftyContinuousMap.smul_apply,smul_eq_mul,zero_mul,one_mul,add_zero,P]
  rw [hf]
  simpa only [one_mul,zero_mul,add_zero] using harmonicAngularCoefficient_four
    Y (P u) (P v) (P 0) (P 0) hY
    (homogeneousPhysicalCLM a k ha ha1 hk u).continuous
    (homogeneousPhysicalCLM a k ha ha1 hk v).continuous
    (homogeneousPhysicalCLM a k ha ha1 hk 0).continuous
    (homogeneousPhysicalCLM a k ha ha1 hk 0).continuous c 1 0 0 r

theorem homogeneous_contour_jordan_radial (a b k : ℝ)
    (ha : 0<a) (ha1 : a<1) (hk : 8<k) (m : ℕ) (q : HomogeneousY a k)
    (Q : ℝ → ℂ) (hq : ∀ x : E, homogeneousPhysicalCLM a k ha ha1 hk q x=Q ‖x‖)
    (P : (HomogeneousY a k × HomogeneousY a k) →L[ℂ]
      (HomogeneousY a k × HomogeneousY a k))
    (hcomm : ∀ t, Commute (homogeneousComplexLinearizedStep a b k ha ha1 hk m q t) P)
    (hfin : FiniteDimensional ℂ P.range) (G : P.range →L[ℂ] P.range)
    (hG : ∀ t, projectionSemigroupRestriction
      (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) P hcomm t=
        NormedSpace.exp ((t : ℝ) • G))
    (lam : ℂ) (w v : P.range) (he : G w=lam • w+v)
    (Y : E → ℂ) (eta : ℂ)
    (hY : ∀ x : E, x≠0 → ContDiffAt ℝ ∞ Y x)
    (hRay : ∀ (x : E) (t : ℝ), 0<t → Y (t • x)=Y x)
    (hEigen : ∀ x : E, x≠0 → Δ Y x= -(eta/(‖x‖^2 : ℝ))*Y x) :
    let A := fun f : HomogeneousY a k =>
      harmonicAngularCoefficient Y (fun x => homogeneousPhysicalCLM a k ha ha1 hk f x)
    ContDiff ℝ 2 (A (w : HomogeneousY a k × HomogeneousY a k).1) ∧
      ContDiff ℝ 2 (A (w : HomogeneousY a k × HomogeneousY a k).2) ∧
      IsHarmonicRadialSourcePair a b m Q eta lam
        (A (w : HomogeneousY a k × HomogeneousY a k).1)
        (A (w : HomogeneousY a k × HomogeneousY a k).2)
        (A (v : HomogeneousY a k × HomogeneousY a k).1)
        (A (v : HomogeneousY a k × HomogeneousY a k).2) := by
  dsimp only
  have hd := projectionSemigroup_generator_domain
    (homogeneousComplexLinearizedStep a b k ha ha1 hk m q) P hcomm hfin G hG w
  obtain ⟨hf,hg,hEq⟩ := homogeneous_generator_harmonic_channels a b k ha ha1 hk m q Q hq
    (w : HomogeneousY a k × HomogeneousY a k)
    (G w : HomogeneousY a k × HomogeneousY a k) hd Y eta hY hRay hEigen
  have hval : (G w : HomogeneousY a k × HomogeneousY a k)=
      lam • (w : HomogeneousY a k × HomogeneousY a k)+
        (v : HomogeneousY a k × HomogeneousY a k) := congrArg Subtype.val he
  refine ⟨hf,hg,?_⟩
  intro r hr
  have hh := hEq r hr
  rw [hval] at hh
  simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
    homogeneous_harmonic_smul_add a k ha ha1 hk _ _ Y (continuous_harmonicSphere Y hY)] using hh

end DefocusingNLS

end OAI
