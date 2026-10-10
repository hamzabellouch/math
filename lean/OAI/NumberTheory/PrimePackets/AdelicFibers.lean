import Mathlib
import OAI.NumberTheory.PrimePackets.AdelicContinuity

namespace OAI

noncomputable section
open scoped TensorProduct RestrictedProduct Topology Pointwise MatrixGroups
open Matrix Module Filter Set MeasureTheory
namespace PrimeDegreePackets.Adelic

lemma rational_commute_baseChange {n : ℕ} {K : Type*} [Field K] [NumberField K]
    {A : Type*} [CommRing A] [Algebra ℚ A] (b : Basis (Fin n) ℚ K)
    (c : Matrix (Fin n) (Fin n) ℚ) (hc : ∀ a : K, Commute c (rowRegular b a))
    (x : A ⊗[ℚ] K) : Commute (c.map (algebraMap ℚ A)) (rowRegular (b.baseChange A) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r a =>
    rw [rowRegular_tmul]
    exact ((hc a).map (algebraMap ℚ A).mapMatrix).smul_right r
  | add x y hx hy =>
    rw [map_add]
    exact hx.add_right hy

lemma rational_commutes_adelic_of_real {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (b : Basis (Fin n) ℚ K) (c : GL (Fin n) ℚ) (t : (TensorAdeles K)ˣ)
    (hc : ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) c) =
      (adelicRegular b t).1) (s : (TensorAdeles K)ˣ) :
    Commute (rationalProjectiveEmbedding n (ProjGenLinGroup.mk c)) (adelicRegular b s) := by
  let r : GL (Fin n) RationalAdeles := rowRegularUnits (b.baseChange RationalAdeles) t
  let rr : GL (Fin n) ℝ := GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles) r
  change ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) c) = ProjGenLinGroup.mk rr at hc
  obtain ⟨z,hz⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hc.symm
  have hcomm (a : K) : Commute c.val (rowRegular b a) := by
    have hr : Commute rr.val ((rowRegular b a).map (algebraMap ℚ ℝ)) := by
      have H := (Commute.all t.val (Algebra.TensorProduct.includeRight a)).map
        (rowRegular (b.baseChange RationalAdeles))
      have H' := H.map (RingHom.fst ℝ RationalFiniteAdeles).mapMatrix
      rw [rowRegular_baseChange] at H'
      change Commute ((rowRegular (b.baseChange RationalAdeles) t.val).map (RingHom.fst ℝ RationalFiniteAdeles))
        (((rowRegular b a).map (algebraMap ℚ RationalAdeles)).map (RingHom.fst ℝ RationalFiniteAdeles)) at H'
      exact H'
    have hrz : Commute (GeneralLinearGroup.map (algebraMap ℚ ℝ) c).val
        ((rowRegular b a).map (algebraMap ℚ ℝ)) := by
      rw [← hz]
      change Commute (rr.val * Matrix.diagonal (fun _ => z.val)) _
      rw [← Matrix.smul_one_eq_diagonal,Matrix.mul_smul,Matrix.mul_one]
      exact hr.smul_left z.val
    apply (Matrix.map_injective (algebraMap ℚ ℝ).injective)
    dsimp only
    rw [Matrix.map_mul,Matrix.map_mul]
    exact hrz.eq
  have H := rational_commute_baseChange b c.val hcomm s.val
  have HU : Commute (GeneralLinearGroup.map (algebraMap ℚ RationalAdeles) c)
      (rowRegularUnits (b.baseChange RationalAdeles) s) := by
    exact Units.ext H.eq
  have HP := HU.map
    (((ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.fst ℝ RationalFiniteAdeles))).prod
      (ProjGenLinGroup.mk.comp (GeneralLinearGroup.map (RingHom.snd ℝ RationalFiniteAdeles)))))
  exact HP

lemma adelicIdelePoint_fibers_mul {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles)
    {t s : (TensorAdeles K)ˣ} (hts : adelicIdelePoint hodd hn b σ g t =
      adelicIdelePoint hodd hn b σ g s) (q : (TensorAdeles K)ˣ) :
    adelicIdelePoint hodd hn b σ g (q*t) = adelicIdelePoint hodd hn b σ g (q*s) := by
  have he := congrArg (ambientEquiv hodd hn b) hts
  simp only [adelicIdelePoint,Equiv.apply_symm_apply] at he
  obtain ⟨a,⟨a,rfl⟩,k,hk,he⟩ := DoubleCoset.eq.mp he
  obtain ⟨c,rfl⟩ := ProjGenLinGroup.mk_surjective a
  have hk1 : k.1 = 1 := hk.1
  have hreal : ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) c) =
      (adelicRegular b (s*t⁻¹)).1 := by
    have H := congrArg Prod.fst he
    change (adelicRegular b s).1 * ProjGenLinGroup.mk (realBasisGL hn b σ) =
      (ProjGenLinGroup.mk (GeneralLinearGroup.map (algebraMap ℚ ℝ) c) *
        ((adelicRegular b t).1 * ProjGenLinGroup.mk (realBasisGL hn b σ))) * k.1 at H
    rw [hk1,mul_one,← mul_assoc] at H
    have H' := mul_right_cancel H
    rw [map_mul,map_inv,Prod.fst_mul,Prod.fst_inv]
    exact (eq_mul_inv_iff_mul_eq).mpr H'.symm
  have hc := rational_commutes_adelic_of_real b c (s*t⁻¹) hreal q
  apply (ambientEquiv hodd hn b).injective
  simp only [adelicIdelePoint,Equiv.apply_symm_apply]
  apply DoubleCoset.eq.mpr
  refine ⟨rationalProjectiveEmbedding n (ProjGenLinGroup.mk c),⟨_,rfl⟩,k,hk,?_⟩
  rw [map_mul,map_mul,mul_assoc,he,mul_assoc,hc.symm.left_comm]
  simp only [mul_assoc]

lemma adelicTorusPoint_fibers_mul {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (hodd : Odd n) (hn : finrank ℚ K = n) (b : Basis (Fin n) ℚ K)
    (σ : OrderedEmbeddings n K) (g : GL (Fin n) RationalFiniteAdeles)
    {t s : TorusQuotient K} (hts : adelicTorusPoint hodd hn b σ g t =
      adelicTorusPoint hodd hn b σ g s) (q : TorusQuotient K) :
    adelicTorusPoint hodd hn b σ g (q*t) = adelicTorusPoint hodd hn b σ g (q*s) := by
  induction t using QuotientGroup.induction_on with | H t =>
  induction s using QuotientGroup.induction_on with | H s =>
  induction q using QuotientGroup.induction_on with | H q =>
  exact adelicIdelePoint_fibers_mul hodd hn b σ g hts q

end PrimeDegreePackets.Adelic

end

end OAI
