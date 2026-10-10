import OAI.InformationTheory.Entanglement.CombinatorialNumbers
import OAI.InformationTheory.Entanglement.FiberBound
import OAI.InformationTheory.Entanglement.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators
namespace FiniteConstruction

abbrev Question := Base × (Base × Base)
abbrev Coordinate := Fin 1028 × (Fin 1028 × Fin 1028)
def sign (A : Base) (i : Fin 1028) : ℝ := if i ∈ A.val then 1 else -1
def s (A : Base) (i : Fin 1028) : ℝ := sign A i / Real.sqrt 1028
def u (q : Question) (i : Coordinate) : ℝ := s q.1 i.1 * (s q.2.1 i.2.1 * s q.2.2 i.2.2)
def baseOrth (A B : Base) : Prop := (A.val ∩ B.val).card = 257
lemma baseOrth_symm : ∀ ⦃left right⦄, baseOrth left right → baseOrth right left := by
  intro A B h
  simpa only [baseOrth,Finset.inter_comm] using h
lemma sign_sum (A B : Base) :
    ∑ i, sign A i * sign B i = 4*((A.val ∩ B.val).card : ℝ)-1028 := by
  have he (i : Fin 1028) : sign A i* sign B i=
      4*(if i ∈ A.val ∩ B.val then (1:ℝ) else 0)-
      2*(if i ∈ A.val then (1:ℝ) else 0)-
      2*(if i ∈ B.val then (1:ℝ) else 0)+1 := by
    by_cases ha : i ∈ A.val <;> by_cases hb : i ∈ B.val <;> norm_num [sign,ha,hb]
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
  have hi (T : Finset (Fin 1028)) :
      (∑ i : Fin 1028, if i ∈ T then (1:ℝ) else 0)=(T.card : ℝ) := by
    simp only [Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,
      nsmul_eq_mul,mul_one]
  rw [hi,hi,hi,A.property.1,B.property.1]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  norm_num
lemma base_gram (A B : Base) :
    ∑ i, s A i*s B i = ((A.val ∩ B.val).card : ℝ)/257-1 := by
  have hs : (Real.sqrt 1028)^2=(1028:ℝ) := Real.sq_sqrt (by norm_num)
  calc
    _ = (∑ i, sign A i*sign B i)/(Real.sqrt 1028)^2 := by
      simp only [s,div_mul_div_comm,← pow_two,Finset.sum_div]
    _ = _ := by rw [sign_sum,hs]; ring
lemma base_unit (A : Base) : ∑ i, s A i*s A i=1 := by
  rw [base_gram,Finset.inter_self,A.property.1]
  norm_num
lemma question_gram (q r : Question) :
    ProjectionCriterion.correlation u q r=
      (((q.1.val ∩ r.1.val).card : ℝ)/257-1)*
      ((((q.2.1.val ∩ r.2.1.val).card : ℝ)/257-1)*
        (((q.2.2.val ∩ r.2.2.val).card : ℝ)/257-1)) := by
  unfold ProjectionCriterion.correlation u
  simp only [Fintype.sum_prod_type]
  conv_lhs => arg 2; intro a; arg 2; intro b; arg 2; intro c; rw [show
    s q.1 a*(s q.2.1 b*s q.2.2 c)*(s r.1 a*(s r.2.1 b*s r.2.2 c))=
    (s q.1 a*s r.1 a)*((s q.2.1 b*s r.2.1 b)*(s q.2.2 c*s r.2.2 c)) by ring]
  simp only [← Finset.mul_sum,← Finset.sum_mul,base_gram]
lemma question_unit (q : Question) : ∑ i, u q i*u q i=1 := by
  change ProjectionCriterion.correlation u q q=1
  rw [question_gram]
  simp only [Finset.inter_self,q.1.property.1,q.2.1.property.1,q.2.2.property.1]
  norm_num
lemma question_card : Fintype.card Question=Q := by
  simp only [Question,Fintype.card_prod,base_card,Q]
  ring
lemma coordinate_card : Fintype.card Coordinate=K := by norm_num [Coordinate,K]
lemma base_gram_zero_iff (A B : Base) :
    ((A.val ∩ B.val).card : ℝ)/257-1=0 ↔ baseOrth A B := by
  unfold baseOrth
  constructor
  · intro h
    have he : ((A.val ∩ B.val).card : ℝ)=257 := by linarith
    exact_mod_cast he
  · intro h
    rw [h]
    norm_num
lemma question_orth_iff (q r : Question) :
    ProjectionCriterion.correlation u q r=0 ↔
      orRelation baseOrth (orRelation baseOrth baseOrth) q r := by
  rw [question_gram]
  simp only [mul_eq_zero,base_gram_zero_iff,orRelation]
lemma no_orthogonal_eight_bound (J : Finset Question)
    (hJ : ¬ HasClique (fun q r => ProjectionCriterion.correlation u q r=0) J 8) :
    J.card ≤ κ := by
  have hbase (G : Finset Base)
      (hG : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → ¬ baseOrth x y) : G.card ≤ a₀ :=
    restricted_intersections G hG
  have htwo (U : Finset Base) (hU : ¬ HasClique baseOrth U 2) : U.card ≤ a₀ :=
    hbase U (no_pair_of_no_clique_two baseOrth_symm hU)
  have hfour (U : Finset (Base × Base))
      (hU : ¬ HasClique (orRelation baseOrth baseOrth) U 4) : U.card ≤ 2*a₀*b := by
    have hh := amplification_bound baseOrth_symm a₀ a₀ 2 hbase htwo U hU
    simpa only [base_card,show a₀*b+b*a₀=2*a₀*b by ring] using hh
  have he : ¬ HasClique (orRelation baseOrth (orRelation baseOrth baseOrth)) J (2*4) := by
    intro hh
    apply hJ
    obtain ⟨T,hT,cT,pT⟩ := hh
    exact ⟨T,hT,cT,fun q hq r hr hqr => (question_orth_iff q r).mpr (pT q hq r hr hqr)⟩
  have hh := amplification_bound baseOrth_symm a₀ (2*a₀*b) 4 hbase hfour J he
  simpa only [Fintype.card_prod,base_card,κ,show a₀*(b*b)+b*(2*a₀*b)=3*a₀*b^2 by ring] using hh

end FiniteConstruction

end

end OAI
