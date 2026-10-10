import OAI.MathematicalPhysics.RapidForcing.SyntaxComputable
import OAI.MathematicalPhysics.RapidForcing.JetControl

namespace OAI

open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveArithmetic

lemma computable_list_sum {S : Type} [Primcodable S] [AddMonoid S]
    (hadd : Computable (fun p : S × S => p.1 + p.2)) :
    Computable (List.sum : List S → S) := by
  have h := computable_list_foldr Computable.id (Computable.const (0 : S))
    (hadd.comp Computable.snd).to₂
  exact h.of_eq (fun _ => rfl)

lemma computable_list_flatMap {A B C : Type} [Primcodable A] [Primcodable B] [Primcodable C]
    {f : A → List B} {g : A → B → List C} (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) := by
  have h := computable_list_foldr hf (Computable.const ([] : List C))
    (h := fun a p => g a p.1 ++ p.2)
    ((Primrec.list_append.to_comp.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂)
  exact h.of_eq (fun a => by induction f a <;> simp [*])
end RapidForcing.EffectiveArithmetic

namespace RapidForcing
open EffectiveArithmetic EffectiveProfile
namespace EffectiveProfile.Formula
variable {d : ℕ}
attribute [local irreducible] diff Expr.diff bound Expr.bound

@[fun_prop] lemma computable_allDiff : Computable (@allDiff d) := by
  unfold allDiff
  apply computable_list_flatMap Computable.id
  unfold Computable₂
  apply computable_list_map (Computable.const (List.finRange d))
  exact (computable_diff.comp
    ((Computable.snd.comp Computable.fst).pair Computable.snd)).to₂

@[fun_prop] lemma computable_jetBound : Computable (fun p : Formula d × ℚ × ℕ =>
    p.1.jetBound p.2.1 p.2.2) := by
  unfold jetBound
  apply (computable_list_sum computable_rat_add).comp
  apply computable_list_map
  · apply computable_nat_iterate (by fun_prop)
      (Computable.list_cons.comp Computable.fst (Computable.const []))
    exact (computable_allDiff.comp Computable.snd).to₂
  · exact (computable_bound.comp (Computable.snd.pair
      ((Computable.fst.comp Computable.snd).comp Computable.fst))).to₂

attribute [local irreducible] jetBound scaledFormula
@[fun_prop] lemma computable_curlJetBound : Computable curlJetBound := by
  unfold curlJetBound
  apply computable_fin_sum computable_rat_add
  intro i
  exact computable_jetBound.comp ((Computable.const (scaledFormula i)).pair
    ((Computable.const 3).pair Computable.id))
end EffectiveProfile.Formula

attribute [local irreducible] ScaleData.δQ ScaleData.bQ ScaleData.s ScaleData.L
  ScaleData.C EffectiveProfile.Formula.curlJetBound

lemma ScaleData.computable_coefficientTerm : Computable
    (fun p : (ScaleData × ℕ × ℕ) × ℕ =>
      ((p.2:ℚ)+4)^p.1.2.1 * (p.1.1.bQ p.2 / p.1.1.δQ p.2 ^ p.1.2.2)) := by
  have hb := ScaleData.computable_bQ.comp (show Computable
    (fun p : (ScaleData × ℕ × ℕ) × ℕ => (p.1.1, p.2)) by fun_prop)
  have hd := ScaleData.computable_deltaQ.comp (show Computable
    (fun p : (ScaleData × ℕ × ℕ) × ℕ => (p.1.1, p.2)) by fun_prop)
  have he := computable_rat_pow.comp (hd.pair (show Computable
    (fun p : (ScaleData × ℕ × ℕ) × ℕ => p.1.2.2) by fun_prop))
  have hw : Computable (fun p : (ScaleData × ℕ × ℕ) × ℕ => ((p.2:ℚ)+4)^p.1.2.1) := by fun_prop
  exact (computable_rat_mul.comp (hw.pair (computable_rat_div.comp (hb.pair he)))).of_eq (fun _ => rfl)

lemma ScaleData.computable_coefficientSum : Computable
    (fun p : ScaleData × ℕ × ℕ =>
      ∑ n ∈ Finset.range (max p.2.1 p.2.2),
        ((n:ℚ)+4)^p.2.1 * (p.1.bQ n / p.1.δQ n ^ p.2.2)) := by
  exact computable_sum_range computable_rat_add
    (primrec_nat_max.to_comp.comp (show Computable
      (fun p : ScaleData × ℕ × ℕ => (p.2.1, p.2.2)) by fun_prop))
    ScaleData.computable_coefficientTerm.to₂

@[fun_prop] lemma ScaleData.computable_coefficientBound : Computable
    (fun p : ScaleData × ℕ × ℕ => p.1.coefficientBound p.2.1 p.2.2) := by
  unfold ScaleData.coefficientBound
  exact (computable_rat_add.comp (ScaleData.computable_coefficientSum.pair (Computable.const 2))).of_eq (fun _ => rfl)

attribute [local irreducible] ScaleData.coefficientBound
@[fun_prop] lemma computable_velocityJetBound : Computable
    (fun p : ScaleData × ℕ × ℕ => velocityJetBound p.1 p.2.1 p.2.2) := by
  unfold velocityJetBound
  fun_prop

attribute [local irreducible] velocityJetBound
@[fun_prop] lemma computable_forceJetBound : Computable
    (fun p : ScaleData × ℚ × ℕ × ℕ => forceJetBound p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have h : Computable (fun p : ScaleData × ℚ × ℕ × ℕ =>
      ∑ i ∈ Finset.range (p.2.2.2+1), velocityJetBound p.1 p.2.2.1 i *
        velocityJetBound p.1 0 (p.2.2.2-i+1)) := by
    apply computable_sum_range computable_rat_add (by fun_prop)
    unfold Computable₂
    fun_prop
  unfold forceJetBound
  fun_prop (disch := assumption)
end RapidForcing

end OAI
