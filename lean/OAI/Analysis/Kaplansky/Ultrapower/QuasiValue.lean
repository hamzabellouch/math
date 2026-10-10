import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.NullIdeal

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder
open Kaplansky SpectralKernel
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

structure QuasiValue (A : Type*) [CStarAlgebra A] where
  val : A → ℝ
  zero : val 0=0
  one : val 1=1
  nonneg : ∀ ⦃a⦄, 0≤a → 0≤val a
  mono : ∀ ⦃a b⦄, 0≤a → a≤b → val a≤val b
  smul : ∀ (r:ℝ) a, val (r • a)=r*val a
  bound : ∀ a, |val a|≤‖a‖
  lipschitz_positive : ∀ ⦃a b⦄, 0≤a → 0≤b → |val a-val b|≤‖a-b‖
  square_swap : ∀ x, val (x*star x)=val (star x*x)
  weighted_add : ∀ ⦃a b⦄, 0≤a → 0≤b → ∀ (r:ℝ), r≠0 →
    val (a+b)≤(1+r^2)*val a+(1+r⁻¹^2)*val b
  add_commute : ∀ ⦃a b⦄, IsSelfAdjoint a → IsSelfAdjoint b → Commute a b →
    val (a+b)=val a+val b

namespace QuasiValue
variable {A : Type*} [CStarAlgebra A]

lemma spectral_commuting_add (d : CuntzDimensionState A) {n : ℕ}
    {a b : Mat A n} (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hc : Commute a b) :
    d.signedValue (a+b)=d.signedValue a+d.signedValue b := by
  let τ : OneQuasitrace (Mat A n) :=
    { toFun := d.complexValue
      square_nonneg := d.complexValue_square_nonneg
      square_swap := d.complexValue_square_swap
      real_imag := d.complexValue_real_imag
      abelian_linear := d.complexValue_abelian_linear n }
  have h := τ.map_add ha hb hc
  change d.complexValue (a+b)=d.complexValue a+d.complexValue b at h
  rw [d.complexValue_selfAdjoint (ha.add hb),d.complexValue_selfAdjoint ha,
    d.complexValue_selfAdjoint hb] at h
  exact_mod_cast h

def ofDimensionState (d : CuntzDimensionState A) : QuasiValue A := by
  let e := (CStarMatrix.toOneByOne (Fin 1) ℂ A).toStarAlgHom
  have hn (a : A) : ‖e a‖=‖a‖ :=
    NonUnitalStarAlgHom.norm_map e (CStarMatrix.toOneByOne (Fin 1) ℂ A).injective a
  exact
    { val := fun a => d.signedValue (e a)
      zero := by rw [map_zero]; exact d.signedValue_zero 1
      one := by rw [map_one]; exact_mod_cast val_one d 1
      nonneg := by intro a ha; exact val_nonneg d (map_nonneg e ha)
      mono := by
        intro a b ha hab
        exact val_mono d (map_nonneg e ha) (OrderHomClass.mono e hab)
      smul := by
        intro r a
        change d.signedValue (r • e a)=r*d.signedValue (e a)
        exact d.signedValue_smul _ _
      bound := by
        intro a
        simpa only [Nat.cast_one,mul_one,hn] using d.abs_signedValue_le (e a)
      lipschitz_positive := by
        intro a b ha hb
        have h := abs_val_sub_le d (map_nonneg e ha) (map_nonneg e hb)
        simpa only [← map_sub,Nat.cast_one,mul_one,hn] using h
      square_swap := by
        intro x
        simpa only [map_mul,map_star] using val_square_swap d (e x)
      weighted_add := by
        intro a b ha hb r hr
        simpa only [map_add] using val_add_le d (map_nonneg e ha) (map_nonneg e hb) r hr
      add_commute := by
        intro a b ha hb hc
        simpa only [map_add] using spectral_commuting_add d (ha.map e) (hb.map e) (hc.map e) }

variable (V : QuasiValue A)
def q (x : A) : ℝ := V.val (star x*x)

lemma q_nonneg (x : A) : 0≤V.q x := V.nonneg (star_mul_self_nonneg x)
@[simp] lemma q_zero : V.q 0=0 := by simp only [q,star_zero,zero_mul,V.zero]
@[simp] lemma q_star (x : A) : V.q (star x)=V.q x := by
  simp only [q,star_star,V.square_swap]
lemma q_bound (x : A) : V.q x≤‖x‖^2 := by
  simpa only [q,CStarRing.norm_star_mul_self,pow_two] using
    (le_abs_self (V.val (star x*x))).trans (V.bound _)

lemma val_scalar_sub {x : A} (hx : IsSelfAdjoint x) (r : ℝ) :
    V.val (r • 1-x)=r-V.val x := by
  have hn := V.smul (-1) x
  simp only [neg_one_smul,neg_mul,one_mul] at hn
  rw [sub_eq_add_neg,V.add_commute ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one A)) hx.neg
      (by change (r • (1:A)) * (-x)=(-x)*(r • (1:A)); simp),V.smul,V.one,hn]
  ring

lemma val_shift {x : A} (hx : IsSelfAdjoint x) (r : ℝ) :
    V.val (x+r • 1)=V.val x+r := by
  rw [V.add_commute hx ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one A))
    (by change x*(r • (1:A))=(r • (1:A))*x; simp),V.smul,V.one,mul_one]

end QuasiValue
end KaplanskyConsequences

end

end OAI
