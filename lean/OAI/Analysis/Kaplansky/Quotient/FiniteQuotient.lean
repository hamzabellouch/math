import OAI.Analysis.Kaplansky.Main
import OAI.Analysis.Kaplansky.Quotient.ClosedStarQuotient
import OAI.Analysis.Kaplansky.Quotient.NullIdeal

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped Matrix CStarAlgebra ComplexOrder
open Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
namespace SpectralKernel
variable (d : CuntzDimensionState A)

lemma finite_mod_null {n : ℕ} [NeZero n] (x : Mat A n)
    (hx : IsNull d (star x*x-1)) : IsNull d (x*star x-1) := by
  let I := nullIdeal d n
  let : SMulCommClass ℝ I.Quotient I.Quotient := Algebra.to_smulCommClass
  let : IsScalarTower ℝ I.Quotient I.Quotient := IsScalarTower.right
  let : NonUnitalContinuousFunctionalCalculus ℝ I.Quotient IsSelfAdjoint :=
    IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
  let : NonnegSpectrumClass ℝ I.Quotient := CStarAlgebra.instNonnegSpectrumClass
  let q := I.mkStarAlgHom
  have hsmul (r : ℝ) (a : Mat A n) : q (r • a) = r • q a :=
    q.toAlgHom.map_smul_of_tower r a
  have qzero (a : Mat A n) : q a = 0 ↔ IsNull d a := I.mk_eq_zero a
  have hiso : star (q x)*q x = 1 := by
    have h := (qzero _).2 hx
    simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using h
  have hp : IsStarProjection (q x*star (q x)) := by
    refine ⟨?_, (mul_star_self_nonneg _).isSelfAdjoint⟩
    change (q x*star (q x))*(q x*star (q x))=q x*star (q x)
    calc _ = q x*(star (q x)*q x)*star (q x) := by noncomm_ring
         _ = _ := by rw [hiso,mul_one]
  let w := 1-q x*star (q x)
  have hw : 0 ≤ w := hp.one_sub.nonneg
  obtain ⟨y, hy⟩ := I.mk_surjective (CFC.sqrt w)
  change q y = CFC.sqrt w at hy
  let u := star y*y
  have hu : 0 ≤ u := star_mul_self_nonneg y
  have hqu : q u = w := by
    simp only [u,map_mul,map_star,hy,(CFC.sqrt_nonneg w).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self w hw
  let c := ‖x*star x‖+1
  have hc : 0 ≤ c-1 := by dsimp [c]; linarith [norm_nonneg (x*star x)]
  have ha : 0 ≤ c • (1 : Mat A n)-x*star x := by
    apply sub_nonneg.mpr
    have ht := (mul_star_self_nonneg x).isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at ht
    have hc : ‖x * star x‖ ≤ c := by dsimp [c]; linarith
    have hsc := smul_nonneg (sub_nonneg.mpr hc) (show (0 : Mat A n) ≤ 1 from zero_le_one)
    rw [sub_smul, sub_nonneg] at hsc
    exact ht.trans hsc
  have hb : 0 ≤ u + (c-1) • (1 : Mat A n) := add_nonneg hu (smul_nonneg hc zero_le_one)
  have hab : IsNull d ((c • (1 : Mat A n)-x*star x) - (u+(c-1) • 1)) := by
    apply (qzero _).1
    simp only [map_sub,map_add,map_mul,map_star,map_one,hsmul,hqu]
    dsimp [w]
    rw [sub_smul,one_smul]
    abel
  have hvx : val d (x*star x) = n := by
    rw [val_square_swap]
    exact (val_eq_of_null_sub d (star_mul_self_nonneg x) zero_le_one hx).trans (val_one d n)
  have hv := val_eq_of_null_sub d ha hb hab
  rw [val_scalar_sub d (mul_star_self_nonneg x).isSelfAdjoint,
    val_shift d hu hc,hvx] at hv
  have hvu : val d u = 0 := by linarith
  have hnull := null_of_val_zero d hu hvu
  have hqu0 := (qzero _).2 hnull
  have hw0 : w=0 := hqu.symm.trans hqu0
  apply (qzero _).1
  simp only [map_sub,map_mul,map_star,map_one]
  exact sub_eq_zero.mpr (sub_eq_zero.mp hw0).symm

end SpectralKernel
end KaplanskyConsequences

end

end OAI
