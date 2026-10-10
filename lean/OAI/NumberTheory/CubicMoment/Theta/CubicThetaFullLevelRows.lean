import OAI.NumberTheory.CubicMoment.Theta.CubicThetaScalarEisenstein
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimaryMassEuler

namespace OAI

/-! All level-three rows before the coprimality restriction. They form
one explicit affine lattice; primary common factors preserve the lattice. -/
noncomputable section
namespace CubicFirstMoment

@[ext] structure CubicThetaFullRow where
  c : Eisenstein
  d : Eisenstein
  c_three : (3:Eisenstein) ∣ c
  d_primary : primary d

def cubicThetaFullRowCoordinates (a b : Eisenstein) : CubicThetaFullRow where
  c := 3*a
  d := 1+3*b
  c_three := ⟨a,rfl⟩
  d_primary := ⟨b,by ring⟩

lemma cubicThetaFullRowCoordinates_injective :
    Function.Injective (fun p : Eisenstein × Eisenstein => cubicThetaFullRowCoordinates p.1 p.2) := by
  intro p q he
  have hc := congrArg CubicThetaFullRow.c he
  have hd := congrArg CubicThetaFullRow.d he
  apply Prod.ext
  · exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) hc
  · exact mul_left_cancel₀ (by norm_num : (3:Eisenstein)≠0) (add_left_cancel hd)

lemma cubicThetaFullRowCoordinates_surjective :
    Function.Surjective (fun p : Eisenstein × Eisenstein => cubicThetaFullRowCoordinates p.1 p.2) := by
  intro r
  obtain ⟨a,ha⟩ := r.c_three
  obtain ⟨b,hb⟩ := r.d_primary
  refine ⟨(a,b),?_⟩
  apply CubicThetaFullRow.ext
  · exact ha.symm
  · change 1+3*b=r.d
    linear_combination -hb

def cubicThetaFullRowEquiv : Eisenstein × Eisenstein ≃ CubicThetaFullRow :=
  Equiv.ofBijective (fun p => cubicThetaFullRowCoordinates p.1 p.2)
    ⟨cubicThetaFullRowCoordinates_injective,cubicThetaFullRowCoordinates_surjective⟩

def CubicThetaFullRow.height (r : CubicThetaFullRow) (p : ℂ × ℝ) : ℝ :=
  p.2/(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2)

def cubicThetaFullRowMultiply (g : PrimaryArgument) (r : CubicThetaBottomRow) : CubicThetaFullRow where
  c := g.val*r.c
  d := g.val*r.d
  c_three := dvd_mul_of_dvd_right r.c_three _
  d_primary := primary_mul g.property r.d_primary

lemma cubicThetaFullRowMultiply_height (g : PrimaryArgument) (r : CubicThetaBottomRow)
    (p : ℂ × ℝ) :
    (cubicThetaFullRowMultiply g r).height p=(norm g.val)⁻¹*r.height p := by
  unfold CubicThetaFullRow.height CubicThetaBottomRow.height cubicThetaFullRowMultiply
  simp only [Subalgebra.coe_mul]
  rw [show (g.val:ℂ)*(r.c:ℂ)*p.1+(g.val:ℂ)*(r.d:ℂ)=
    (g.val:ℂ)*((r.c:ℂ)*p.1+r.d) by ring,Complex.normSq_mul]
  change p.2/(norm g.val*Complex.normSq ((r.c:ℂ)*p.1+r.d)+
    norm (g.val*r.c)*p.2^2)=_
  rw [norm_mul_eq]
  rw [show norm g.val*Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm g.val*norm r.c*p.2^2=
    norm g.val*(Complex.normSq ((r.c:ℂ)*p.1+r.d)+norm r.c*p.2^2) by ring]
  rw [div_mul_eq_div_div]
  ring

end CubicFirstMoment

end

end OAI
