import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.MatrixAlgebras.MatrixProjectionTests
import OAI.Analysis.JiangSu.CStarAlgebras.ContractionLift

namespace OAI

section

noncomputable section
namespace DirectPacking
open Pureness CurrentMain Filter Topology
open scoped ComplexOrder ENNReal

variable {A I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A] [Nonempty I] (T : I → TracialState A) (U : Ultrafilter ℕ)
local notation "D" => FamilyUltrapower T U
local notation "L" => familyLimitTrace T U
local notation "ι" => familyUltrapowerMap T U
local notation "J" => familyNullIdeal T (U : Filter ℕ)
local notation "q" => Pureness.ClosedStarIdeal.quotientStarHom (familyNullIdeal T (U : Filter ℕ))

lemma quotient_error_eventually (x : lp (fun _ : ℕ => A) ∞) {ε : ℝ}
    (hx : familyTwoNorm L (q x)<ε) :
    ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (x k)<ε :=
  (familyTwoNorm_limitTrace_tendsto T U x).eventually_lt_const hx

lemma matrix_star_lift_eventually (x y : lp (fun _ : ℕ => A) ∞) {ε : ℝ}
    (hs : familyTwoNorm L (star (q x)-q y)<ε) :
    ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (star (x k)-y k)<ε := by
  rw [←map_star,←map_sub] at hs
  exact quotient_error_eventually T U _ hs

lemma matrix_mul_lift_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞)
    (i j k l : Fin m) {ε : ℝ}
    (hm : familyTwoNorm L (q (x i j)*q (x k l)-if j=k then q (x i l) else 0)<ε) :
    ∀ᶠ t in (U : Filter ℕ),familyTwoNorm T (x i j t*x k l t-if j=k then x i l t else 0)<ε := by
  let b := if j=k then x i l else 0
  have hb : q b=if j=k then q (x i l) else 0 := by dsimp [b]; split_ifs <;> simp only [map_zero]
  have hh : familyTwoNorm L (q (x i j*x k l-b))<ε := by
    rw [map_sub,map_mul,hb]; exact hm
  have he := quotient_error_eventually T U _ hh
  filter_upwards [he] with t ht
  by_cases hjk : j=k
  · simpa only [b,hjk,ite_true,lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply] using ht
  · simpa only [b,hjk,ite_false,sub_zero,lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply,lp.coeFn_zero,Pi.zero_apply] using ht

lemma matrix_unit_lift_eventually {m : ℕ} (x : Fin m → Fin m → lp (fun _ : ℕ => A) ∞) {ε : ℝ}
    (hu : familyTwoNorm L ((∑ i,q (x i i))-1)<ε) :
    ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T ((∑ i,x i i k)-1)<ε := by
  have hh : familyTwoNorm L (q ((∑ i,x i i)-1))<ε := by
    rw [map_sub,map_sum,map_one]; exact hu
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.coeFn_sum,Finset.sum_apply,lp.infty_coeFn_one,Pi.one_apply]
    using quotient_error_eventually T U _ hh

lemma matrix_comm_lift_eventually (x : lp (fun _ : ℕ => A) ∞) (a : A) {ε : ℝ}
    (hc : familyTwoNorm L (q x*ι a-ι a*q x)<ε) :
    ∀ᶠ k in (U : Filter ℕ),familyTwoNorm T (x k*a-a*x k)<ε := by
  let c : lp (fun _ : ℕ => A) ∞ := boundedFamilyConstant a
  have hh : familyTwoNorm L (q (x*c-c*x))<ε := by
    rw [map_sub,map_mul,map_mul]; exact hc
  simpa only [lp.coeFn_sub,Pi.sub_apply,lp.infty_coeFn_mul,Pi.mul_apply,c,boundedFamilyConstant_apply]
    using quotient_error_eventually T U _ hh

lemma tracial_matrix_model_extract {m : ℕ} {K : Finset (unitary A)} {ε : ℝ}
    (M : TracialMatrixModel L ι m K ε) :
    Nonempty (TracialMatrixModel T (StarAlgHom.id ℂ A) m K ε) := by
  classical
  choose x hx hxn using fun i j => CStarLift.exists_contraction q (familyNullIdeal T (U : Filter ℕ)).quotientMap_surjective (M.norm_entry i j)
  have hs (i j : Fin m) := matrix_star_lift_eventually T U (x i j) (x j i) (by rw [hx,hx]; exact M.star_error i j)
  have hm (i j k l : Fin m) := matrix_mul_lift_eventually T U x i j k l (by simp only [hx]; exact M.mul_error i j k l)
  have hu := matrix_unit_lift_eventually T U x (by simp only [hx]; exact M.unit_error)
  have hc (i j : Fin m) (u : K) := matrix_comm_lift_eventually T U (x i j) (u.val:A) (by rw [hx]; exact M.comm_error i j u.val u.property)
  have hsall := eventually_all.mpr fun i => eventually_all.mpr fun j => hs i j
  have hmall := eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => eventually_all.mpr fun l => hm i j k l
  have hcall := eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun u => hc i j u
  obtain ⟨k,hks,hkm,hku,hkc⟩ := (hsall.and (hmall.and (hu.and hcall))).exists
  exact ⟨{
    entry := fun i j => x i j k
    norm_entry := fun i j => (lp.norm_apply_le_norm ENNReal.top_ne_zero (x i j) k).trans (hxn i j)
    star_error := hks
    mul_error := hkm
    unit_error := hku
    comm_error := fun i j u hu => hkc i j ⟨u,hu⟩}⟩

end DirectPacking

end
end

end OAI
