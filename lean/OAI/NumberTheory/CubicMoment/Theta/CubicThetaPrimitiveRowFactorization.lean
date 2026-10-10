import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFullLevelRows

namespace OAI

/-! Unique extraction of the primary common factor of a level-three row.
The inverse uses a Bezout identity for its actual gcd. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFullRowMultiply_surjective :
    Function.Surjective (fun p : PrimaryArgument × CubicThetaBottomRow =>
      cubicThetaFullRowMultiply p.1 p.2) := by
  classical
  let := EuclideanDomain.gcdMonoid Eisenstein
  intro r
  let d := GCDMonoid.gcd r.c r.d
  let g := primaryNormalize d
  have hgd : g ∣ r.d :=
    (primaryNormalize_associated d).symm.dvd.trans (GCDMonoid.gcd_dvd_right r.c r.d)
  have hg : primary g := primaryNormalize_primary
    (unit_residue_of_dvd_primary r.d_primary (GCDMonoid.gcd_dvd_right r.c r.d))
  have hg0 : g≠0 := primary_ne_zero hg
  have hgc : g ∣ r.c :=
    (primaryNormalize_associated d).symm.dvd.trans (GCDMonoid.gcd_dvd_left r.c r.d)
  obtain ⟨x,y,hxy⟩ := exists_gcd_eq_mul_add_mul r.c r.d
  obtain ⟨u,hu⟩ := primaryNormalize_associated d
  change d=r.c*x+r.d*y at hxy
  change d*(u:Eisenstein)=g at hu
  clear_value g d
  obtain ⟨a,ha⟩ := hgc
  obtain ⟨b,hb⟩ := hgd
  have hbprim : primary b := primary_of_mul hg (by rw [←hb]; exact r.d_primary)
  have ha3 : (3:Eisenstein) ∣ a :=
    (primary_coprime_three hg).symm.dvd_of_dvd_mul_left (by rw [←ha]; exact r.c_three)
  have hab : IsCoprime a b := by
    refine ⟨x*u,y*u,?_⟩
    apply mul_left_cancel₀ hg0
    calc
      g*(x*u*a+y*u*b)=(r.c*x+r.d*y)*u := by rw [ha,hb]; ring
      _ = g := by rw [←hxy]; exact hu
      _ = g*1 := (mul_one g).symm
  let q : CubicThetaBottomRow := ⟨a,b,ha3,hbprim,hab⟩
  refine ⟨(⟨g,hg⟩,q),?_⟩
  apply CubicThetaFullRow.ext
  · exact ha.symm
  · exact hb.symm

lemma cubicThetaFullRow_factor_dvd (g h : PrimaryArgument)
    (r s : CubicThetaBottomRow)
    (hc : g.val*r.c=h.val*s.c) (hd : g.val*r.d=h.val*s.d) :
    g.val ∣ h.val := by
  obtain ⟨x,y,hxy⟩ := s.coprime
  have he : h.val=(h.val*s.c)*x+(h.val*s.d)*y := by
    linear_combination -h.val*hxy
  rw [he,←hc,←hd]
  exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_right g.val r.c) x)
    (dvd_mul_of_dvd_left (dvd_mul_right g.val r.d) y)

lemma cubicThetaFullRowMultiply_injective :
    Function.Injective (fun p : PrimaryArgument × CubicThetaBottomRow =>
      cubicThetaFullRowMultiply p.1 p.2) := by
  rintro ⟨g,r⟩ ⟨h,s⟩ he
  have hc : g.val*r.c=h.val*s.c := congrArg CubicThetaFullRow.c he
  have hd : g.val*r.d=h.val*s.d := congrArg CubicThetaFullRow.d he
  have gh : g=h := Subtype.ext (primary_associated_eq g.property h.property
    (associated_of_dvd_dvd (cubicThetaFullRow_factor_dvd g h r s hc hd)
      (cubicThetaFullRow_factor_dvd h g s r hc.symm hd.symm)))
  subst h
  have hrs : r=s := CubicThetaBottomRow.ext
    (mul_left_cancel₀ (primary_ne_zero g.property) hc)
    (mul_left_cancel₀ (primary_ne_zero g.property) hd)
  subst s
  rfl

def cubicThetaPrimitiveRowEquiv : PrimaryArgument × CubicThetaBottomRow ≃ CubicThetaFullRow :=
  Equiv.ofBijective (fun p => cubicThetaFullRowMultiply p.1 p.2)
    ⟨cubicThetaFullRowMultiply_injective,cubicThetaFullRowMultiply_surjective⟩

end CubicFirstMoment

end

end OAI
