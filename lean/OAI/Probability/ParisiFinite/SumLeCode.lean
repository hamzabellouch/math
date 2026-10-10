import Mathlib
import OAI.Probability.ParisiFinite.Labels

namespace OAI

/-! Sum Le Code. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped BigOperators

namespace FiniteWeightedCode
attribute [local instance] Classical.propDecidable

 

theorem sum_le_code {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (good : A → Prop) (first : A → B) (second : A → C) (allowed : B → Finset C)
    (f : A → ℝ) (g : B → C → ℝ)
    (hg : ∀b c, 0≤g b c)
    (hmem : ∀a,good a → second a∈allowed (first a))
    (hinj : ∀a,good a → ∀a',good a' → first a=first a' → second a=second a' → a=a')
    (hbound : ∀a,good a → f a≤g (first a) (second a)) :
    (∑a : A with good a,f a)≤∑b : B,∑c∈allowed b,g b c := by
  classical
  let target : Finset (B × C) := Finset.univ.filter (fun z => z.2∈allowed z.1)
  have htarget : (∑z∈target,g z.1 z.2)=∑b : B,∑c∈allowed b,g b c := by
    simp only [target,Finset.sum_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro b hb
    rw [←Finset.sum_filter]
    simp
  rw [←htarget]
  let code (a : A) : B × C := (first a,second a)
  let source : Finset A := Finset.univ.filter good
  have hi : Set.InjOn code (↑source : Set A) := by
    intro a ha a' ha' he
    exact hinj a (Finset.mem_filter.mp ha).2 a' (Finset.mem_filter.mp ha').2
      (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hs : source.image code⊆target := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hmem a (Finset.mem_filter.mp ha).2⟩
  calc
    _ ≤ ∑a∈source,g (first a) (second a) :=
      Finset.sum_le_sum (fun a ha => hbound a (Finset.mem_filter.mp ha).2)
    _ = ∑z∈source.image code,g z.1 z.2 := (Finset.sum_image (f := fun z : B × C => g z.1 z.2) hi).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun z _ _ => hg z.1 z.2)

end FiniteWeightedCode

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
open BoundedBranch Locality FiniteGraph
variable {n : ℕ}

def internalEdges (U : Finset (Fin n)) : Finset (Edge n) :=
  Finset.univ.filter (fun e => e.1.1∈U ∧ e.1.2∈U)

lemma card_internalEdges_le (U : Finset (Fin n)) : (internalEdges U).card≤U.card*n := by
  calc
    (internalEdges U).card = ((internalEdges U).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (U ×ˢ Finset.univ).card := by
      apply Finset.card_le_card
      rintro q hq
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_product.mpr ⟨(Finset.mem_filter.mp he).2.1,Finset.mem_univ _⟩
    _ = U.card*n := by simp

lemma forestVertices_card_le {p : ℕ} (r : Edge n) (b : Forest n p) :
    (forestVertices r b).card≤forestSize b+2 := by
  have hr : (roots r).card=2 := by simp [roots,ne_of_lt r.2]
  calc
    _ ≤ (roots r).card+(forestLabels b).toFinset.card := Finset.card_union_le _ _
    _ ≤ (roots r).card+(forestLabels b).card := Nat.add_le_add_left (Multiset.toFinset_card_le _) _
    _ = _ := by rw [hr,card_forestLabels]; omega

lemma sum_powerset_pow (E : Finset (Edge n)) (x : ℝ) :
    (∑T∈E.powerset,x^T.card)=(1+x)^E.card := by
  simpa only [Finset.prod_const] using (Finset.prod_one_add (f := fun _ : Edge n => x) E).symm

 

lemma sum_extras_bound {p : ℕ} (r : Edge n) (b : Forest n p) {x : ℝ} (hx : 0≤x) :
    (∑T∈(internalEdges (forestVertices r b)).powerset,(x/(n:ℝ))^T.card)≤
      Real.exp (x*(forestSize b+2)) := by
  have hn : 0<n := lt_of_le_of_lt (Nat.zero_le _) r.1.2.isLt
  have hnR : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hm : ((internalEdges (forestVertices r b)).card:ℝ)≤(forestSize b+2:ℝ)*(n:ℝ) := by
    exact_mod_cast (card_internalEdges_le (forestVertices r b)).trans
      (Nat.mul_le_mul_right n (forestVertices_card_le r b))
  rw [sum_powerset_pow]
  calc
    _ ≤ (Real.exp (x/(n:ℝ)))^(internalEdges (forestVertices r b)).card := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (x/(n:ℝ))
    _ = Real.exp ((internalEdges (forestVertices r b)).card*(x/(n:ℝ))) := by
      rw [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ((forestSize b+2:ℝ)*(n:ℝ))*(x/(n:ℝ)) :=
          mul_le_mul_of_nonneg_right hm (div_nonneg hx hnR.le)
        _ = _ := by field_simp

lemma weighted_extras_bound {p : ℕ} (r : Edge n) (b : Forest n p) {x : ℝ} (hx : 0≤x) :
    forestWeight x b*(∑T∈(internalEdges (forestVertices r b)).powerset,(x/(n:ℝ))^T.card)≤
      Real.exp (2*x)*forestWeight (Real.exp x*x) b := by
  calc
    _ ≤ forestWeight x b*Real.exp (x*(forestSize b+2)) :=
      mul_le_mul_of_nonneg_left (sum_extras_bound r b hx) (forestWeight_nonneg hx b)
    _ = _ := by
      rw [forestWeight_scale]
      have he : Real.exp (x*(forestSize b+2))=Real.exp (2*x)*(Real.exp x)^forestSize b := by
        rw [←Real.exp_nat_mul,←Real.exp_add]
        congr 1
        ring
      rw [he]
      ring

 

lemma forest_extra_injective (r : Edge n) (p : ℕ) (H K : Finset (Edge n))
    (hb : forestCode r H p=forestCode r K p)
    (he : H\forestEdges r (forestCode r H p)=K\forestEdges r (forestCode r K p)) : H=K := by
  have hH := Finset.union_sdiff_of_subset (forestCode_edges_subset r H p)
  have hK := Finset.union_sdiff_of_subset (forestCode_edges_subset r K p)
  rw [←hH,←hK,he,hb]

lemma extras_internal (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n) (H : Finset (Edge n))
    (hcone : H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)) :
    H\forestEdges r (forestCode r H p)⊆internalEdges (forestVertices r (forestCode r H p)) := by
  have hv : forestVertices r (forestCode r H p)=usedVertices r H := by
    rw [forestCode_vertices]
    exact (used_eq_ball p γ β r H hcone).symm
  rw [hv]
  intro e he
  have heH := (Finset.mem_sdiff.mp he).1
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fst_mem_usedVertices r H (Finset.mem_union_left _ heH),
    snd_mem_usedVertices r H (Finset.mem_union_left _ heH)⟩

lemma code_weight (r : Edge n) (p : ℕ) (H : Finset (Edge n)) (x : ℝ) :
    (x/(n:ℝ))^H.card=forestWeight x (forestCode r H p)*
      (x/(n:ℝ))^(H\forestEdges r (forestCode r H p)).card := by
  rw [forestWeight_eq_pow,←forestCode_edges_card,←pow_add,
    Nat.add_comm,Finset.card_sdiff_add_card_eq_card (forestCode_edges_subset r H p)]

 

theorem cone_graph_tail (p L : ℕ) (γ β : Fin p → ℝ) (r : Edge n) {x : ℝ} (hx : 0≤x) :
    (∑H : Finset (Edge n) with
      H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r) ∧ L≤forestSize (forestCode r H p),
        (x/(n:ℝ))^H.card)≤
          Real.exp (2*x)*(tower (2*(Real.exp x*x)) p)^2/(2:ℝ)^L := by
  let allowed (b : Forest n p) : Finset (Finset (Edge n)) :=
    if L≤forestSize b then (internalEdges (forestVertices r b)).powerset else ∅
  have hc := FiniteWeightedCode.sum_le_code
    (fun H : Finset (Edge n) => H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r) ∧
      L≤forestSize (forestCode r H p))
    (fun H => forestCode r H p) (fun H => H\forestEdges r (forestCode r H p)) allowed
    (fun H => (x/(n:ℝ))^H.card) (fun b T => forestWeight x b*(x/(n:ℝ))^T.card)
    (fun b T => mul_nonneg (forestWeight_nonneg hx b) (pow_nonneg (div_nonneg hx (Nat.cast_nonneg n)) _))
    (fun H hH => by simpa only [allowed,ite_eq_left hH.2] using
      Finset.mem_powerset.mpr (extras_internal p γ β r H hH.1))
    (fun H _ K _ hb he => forest_extra_injective r p H K hb he)
    (fun H _ => (code_weight r p H x).le)
  calc
    _ ≤ ∑b : Forest n p,∑T∈allowed b,forestWeight x b*(x/(n:ℝ))^T.card := by
      convert hc using 1
      simp only [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro H hH
      split_ifs <;> rfl
    _ = ∑b : Forest n p with L≤forestSize b,
        forestWeight x b*∑T∈(internalEdges (forestVertices r b)).powerset,(x/(n:ℝ))^T.card := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hL : L≤forestSize b <;> simp [allowed,hL,Finset.mul_sum]
    _ ≤ ∑b : Forest n p with L≤forestSize b,Real.exp (2*x)*forestWeight (Real.exp x*x) b :=
      Finset.sum_le_sum (fun b _ => weighted_extras_bound r b hx)
    _ ≤ Real.exp (2*x)*((tower (2*(Real.exp x*x)) p)^2/(2:ℝ)^L) := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (forest_tail_bound n p L (mul_nonneg (Real.exp_pos x).le hx))
        (Real.exp_pos _).le
    _ = _ := (mul_div_assoc _ _ _).symm

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
open Locality BoundedBranch
variable {n : ℕ}

lemma roots_subset_used (r : Edge n) (H : Finset (Edge n)) : roots r⊆usedVertices r H := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl|hv
  · exact fst_mem_usedVertices r H (by simp)
  · obtain rfl := Finset.mem_singleton.mp hv
    exact snd_mem_usedVertices r H (by simp)

lemma used_card_eq_forestSize_add_two (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n))
    (hc : H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)) :
    (usedVertices r H).card=forestSize (forestCode r H p)+2 := by
  rw [forestCode_size]
  have hu := used_eq_ball p γ β r H hc
  change usedVertices r H=reached r H p at hu
  rw [←hu]
  have hr : (roots r).card=2 := by simp [roots,ne_of_lt r.2]
  simpa only [hr] using (Finset.card_sdiff_add_card_eq_card (roots_subset_used r H)).symm

lemma cluster_zero_of_not_cone (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n))
    (hc : ¬H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)) :
    cluster p γ β r H=0 := by
  obtain ⟨e,he,he'⟩ := Finset.not_subset.mp hc
  exact cluster_eq_zero p γ β r he he'

 

lemma cluster_zero_of_edge_deficit (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) (hh : H.card+2<(usedVertices r H).card) :
    cluster p γ β r H=0 := by
  apply cluster_zero_of_not_cone
  intro hc
  have hu := used_card_eq_forestSize_add_two p γ β r H hc
  have he := Finset.card_le_card (forestCode_edges_subset r H p)
  rw [forestCode_edges_card] at he
  omega

def tailConstant (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  markedBound p γ β*Real.exp (2*activity p γ β)*
    (tower (2*(Real.exp (activity p γ β)*activity p γ β)) p)^2

lemma tailConstant_nonneg (p : ℕ) (γ β : Fin p → ℝ) : 0≤tailConstant p γ β := by
  unfold tailConstant
  exact mul_nonneg (mul_nonneg (markedBound_nonneg p γ β) (Real.exp_pos _).le) (sq_nonneg _)

 

theorem sum_norm_cluster_tail (p L : ℕ) (γ β : Fin p → ℝ) (r : Edge n) :
    (∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,‖cluster p γ β r H‖)≤
      (Real.sqrt (n:ℝ))⁻¹*tailConstant p γ β/(2:ℝ)^L := by
  classical
  let cone (H : Finset (Edge n)) := H⊆relevantEdges (H∪{r}) (qaoaWord p γ β) (roots r)
  have he : (∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,‖cluster p γ β r H‖)=
      ∑H : Finset (Edge n) with cone H ∧ L≤forestSize (forestCode r H p),‖cluster p γ β r H‖ := by
    simp only [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro H hH
    by_cases hc : cone H
    · have hu := used_card_eq_forestSize_add_two p γ β r H hc
      simp only [hu,hc,true_and,Nat.add_le_add_iff_right]
    · simp only [cluster_zero_of_not_cone p γ β r H hc,norm_zero,ite_self,hc,false_and]
  rw [he]
  calc
    _ ≤ ∑H : Finset (Edge n) with cone H ∧ L≤forestSize (forestCode r H p),
        markedBound p γ β*(Real.sqrt (n:ℝ))⁻¹*(activity p γ β/(n:ℝ))^H.card :=
      Finset.sum_le_sum (fun H _ => norm_cluster_le p γ β r H)
    _ ≤ markedBound p γ β*(Real.sqrt (n:ℝ))⁻¹*
        (Real.exp (2*activity p γ β)*(tower (2*(Real.exp (activity p γ β)*activity p γ β)) p)^2/(2:ℝ)^L) := by
      rw [←Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (cone_graph_tail p L γ β r (activity_nonneg p γ β))
        (mul_nonneg (markedBound_nonneg p γ β) (by positivity))
    _ = _ := by unfold tailConstant; ring

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
variable {n : ℕ}

 

def clusterEnergy (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n) (H : Finset (Edge n)) : ℂ :=
  (n:ℂ)⁻¹*((Real.sqrt (n:ℝ))⁻¹:ℂ)*cluster p γ β r H

def complexEnergy (n p : ℕ) (γ β : Fin p → ℝ) : ℂ :=
  ∑r : Edge n,∑H : Finset (Edge n),clusterEnergy p γ β r H

 
theorem expectedEnergy_eq_complexEnergy (n p : ℕ) (γ β : Fin p → ℝ) :
    expectedEnergy n p γ β=(complexEnergy n p γ β).re := by
  have hm (r : Edge n) : (∑H : Finset (Edge n),cluster p γ β r H)=
      Locality.averagedMarkedWord r (qaoaWord p γ β) Finset.univ := by
    simpa only [Finset.powerset_univ] using (marked_eq_sum_clusters p γ β r Finset.univ).symm
  have hc : complexEnergy n p γ β=(n:ℂ)⁻¹*((Real.sqrt (n:ℝ))⁻¹:ℂ)*
      ∑r : Edge n, Locality.averagedMarkedWord r (qaoaWord p γ β) Finset.univ := by
    simp only [complexEnergy,clusterEnergy,←Finset.mul_sum,hm]
  rw [hc,expectedEnergy_history]
  simp only [averagedMarkedWord_history,maskPhase,Finset.mem_union,Finset.mem_univ,true_or,ite_true]
  rw [Finset.sum_comm]
  have he : (∑r : Edge n,∑σ : Configuration n,(skCoeff n σ r:ℂ)*
      (∑a:History n p,∑b:History n p,pairedMix n p β σ a b*pairedPhase n p γ a b r*
        Complex.exp (∑e,(pairedPhase n p γ a b e)^2/2)))=
      ((Real.sqrt (n:ℝ))⁻¹:ℂ)*
        (∑r : Edge n,∑σ : Configuration n,∑a:History n p,∑b:History n p,
          (spin σ r.1.1:ℂ)*(spin σ r.1.2:ℂ)*pairedMix n p β σ a b*pairedPhase n p γ a b r*
            Complex.exp (∑e,(pairedPhase n p γ a b e)^2/2)) := by
    simp only [skCoeff,Complex.ofReal_mul,Complex.ofReal_inv,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro σ hσ
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  rw [he]
  have hn : (n:ℂ)⁻¹=(((n:ℝ)⁻¹:ℝ):ℂ) := by simp
  rw [mul_assoc,hn,Complex.re_ofReal_mul]
  ring

lemma clusterEnergy_eq_scaled (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    clusterEnergy p γ β r H=(n:ℂ)⁻¹^(H.card+2)*graphCoefficient n n p γ β r H := by
  have hn : (n:ℝ)≠0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) r.1.2.isLt))
  have hs : ((Real.sqrt (n:ℝ))⁻¹:ℂ)^2=(n:ℂ)⁻¹ := by
    rw [inv_pow,←Complex.ofReal_pow,Real.sq_sqrt (Nat.cast_nonneg n),Complex.ofReal_natCast]
  rw [clusterEnergy,cluster_eq_scaled,pow_add,pow_two]
  calc
    _ = (((Real.sqrt (n:ℝ))⁻¹:ℂ)^2)*(n:ℂ)⁻¹*(n:ℂ)⁻¹^H.card*graphCoefficient n n p γ β r H := by ring
    _ = _ := by rw [hs]; ring

lemma norm_clusterEnergy (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    ‖clusterEnergy p γ β r H‖=(n:ℝ)⁻¹*(Real.sqrt (n:ℝ))⁻¹*‖cluster p γ β r H‖ := by
  simp only [clusterEnergy,norm_mul,norm_inv,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

lemma sum_norm_clusterEnergy_tail (n p L : ℕ) (γ β : Fin p → ℝ) :
    (∑r : Edge n,∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,
      ‖clusterEnergy p γ β r H‖)≤tailConstant p γ β/(2:ℝ)^L := by
  have hi : (Real.sqrt (n:ℝ))⁻¹^2=(n:ℝ)⁻¹ := by
    rw [inv_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
  have he (r : Edge n) : (∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,
      ‖clusterEnergy p γ β r H‖)≤(n:ℝ)⁻¹^2*(tailConstant p γ β/(2:ℝ)^L) := by
    simp only [norm_clusterEnergy,←Finset.mul_sum]
    calc
      _ ≤ (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))⁻¹*((Real.sqrt (n:ℝ))⁻¹*tailConstant p γ β/(2:ℝ)^L) :=
        mul_le_mul_of_nonneg_left (sum_norm_cluster_tail p L γ β r) (by positivity)
      _ = (n:ℝ)⁻¹*(Real.sqrt (n:ℝ))⁻¹^2*(tailConstant p γ β/(2:ℝ)^L) := by ring
      _ = _ := by rw [hi]; ring
  calc
    _ ≤ ∑r : Edge n,(n:ℝ)⁻¹^2*(tailConstant p γ β/(2:ℝ)^L) := Finset.sum_le_sum (fun r _ => he r)
    _ = (Fintype.card (Edge n):ℝ)*(n:ℝ)⁻¹^2*(tailConstant p γ β/(2:ℝ)^L) := by simp; ring
    _ ≤ 1*(tailConstant p γ β/(2:ℝ)^L) := by
      apply mul_le_mul_of_nonneg_right _ (div_nonneg (tailConstant_nonneg p γ β) (by positivity))
      have hc : (Fintype.card (Edge n):ℝ)≤(n:ℝ)^2 := by
        exact_mod_cast (show Fintype.card (Edge n)≤n^2 from
          (Fintype.card_subtype_le _).trans_eq (by simp [pow_two]))
      calc
        _ ≤ (n:ℝ)^2*(n:ℝ)⁻¹^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
        _ ≤ 1 := by
          rw [←mul_pow]
          by_cases hn : (n:ℝ)=0 <;> simp [hn]
    _ = _ := one_mul _

end SKQAOA.SiteHistories

 

open scoped Topology
open Filter Asymptotics

namespace FiniteLabelCount

 
lemma tendsto_choose_inv_pow (m : ℕ) :
    Tendsto (fun n : ℕ => (n.choose m:ℝ)*(n:ℝ)⁻¹^m) atTop (𝓝 ((m.factorial:ℝ)⁻¹)) := by
  have hz : ∀ᶠn : ℕ in atTop,(n:ℝ)^m≠0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  have ht := (isEquivalent_iff_tendsto_one hz).mp (isEquivalent_descFactorial m)
  have hf : (m.factorial:ℝ)≠0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
  convert ht.const_mul (m.factorial:ℝ)⁻¹ using 1
  · funext n
    simp only [Pi.div_apply,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,div_eq_mul_inv,
      inv_pow]
    simp only [←mul_assoc,inv_mul_cancel₀ hf,one_mul]
  · simp

 

lemma tendsto_choose_inv_pow_of_le (m k : ℕ) (hmk : m≤k) :
    Tendsto (fun n : ℕ => (n.choose m:ℝ)*(n:ℝ)⁻¹^k) atTop
      (𝓝 (if m=k then (m.factorial:ℝ)⁻¹ else 0)) := by
  by_cases h : m=k
  · subst k
    simpa using tendsto_choose_inv_pow m
  · have hk : k-m≠0 := by omega
    have ht := (tendsto_choose_inv_pow m).mul
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow (k-m))
    simpa only [ite_eq_right h,zero_pow hk,mul_zero,mul_assoc,←pow_add,Nat.add_sub_of_le hmk] using ht

lemma tendsto_choose_inv_pow_complex (m k : ℕ) (hmk : m≤k) :
    Tendsto (fun n : ℕ => (n.choose m:ℂ)*(n:ℂ)⁻¹^k) atTop
      (𝓝 (if m=k then (m.factorial:ℂ)⁻¹ else 0)) := by
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_choose_inv_pow_of_le m k hmk)
  convert ht using 1
  · simp [Function.comp_def]
  · split_ifs <;> simp

end FiniteLabelCount

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories
attribute [local instance] Classical.propDecidable

 
def energySlice (n m p : ℕ) (γ β : Fin p → ℝ) : ℂ :=
  ∑g : MarkedGraph n with (usedVertices g.1 g.2).card=m,clusterEnergy p γ β g.1 g.2

def shapeTerm (N m p : ℕ) (γ β : Fin p → ℝ) (g : FullGraph m) : ℂ :=
  if m≤g.1.2.card+2 then (N:ℂ)⁻¹^(g.1.2.card+2)*graphCoefficient N m p γ β g.1.1 g.1.2 else 0

def shapeTermLimit (m p : ℕ) (γ β : Fin p → ℝ) (g : FullGraph m) : ℂ :=
  if m=g.1.2.card+2 then (m.factorial:ℂ)⁻¹*graphCoefficientLimit m p γ β g.1.1 g.1.2 else 0

 

theorem energySlice_eq_shapes (n m p : ℕ) (γ β : Fin p → ℝ) :
    energySlice n m p γ β=(n.choose m:ℂ)*∑g : FullGraph m,shapeTerm n m p γ β g := by
  let F (g : MarkedGraph n) :=
    if m≤g.2.card+2 then clusterEnergy p γ β g.1 g.2 else 0
  have he : energySlice n m p γ β=
      ∑g : MarkedGraph n with (usedVertices g.1 g.2).card=m,F g := by
    apply Finset.sum_congr rfl
    intro g hg
    have hc := (Finset.mem_filter.mp hg).2
    by_cases h : m≤g.2.card+2
    · simp only [F,ite_eq_left h]
    · have hd : g.2.card+2<(usedVertices g.1 g.2).card := by omega
      simp only [F,ite_eq_right h,clusterEnergy,cluster_zero_of_edge_deficit p γ β g.1 g.2 hd,mul_zero]
  rw [he,sum_full_graphs]
  have hF (U : SupportSet n m) (g : FullGraph m) :
      F (graphMap (U.1.orderEmbOfFin U.2) g.1)=shapeTerm n m p γ β g := by
    dsimp only [F,graphMap,shapeTerm]
    simp only [Finset.card_map]
    split_ifs
    · rw [clusterEnergy_eq_scaled,Finset.card_map,graphCoefficient_relabel]
    · rfl
  simp_rw [hF]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card_supportSet]

def energySliceLimit (m p : ℕ) (γ β : Fin p → ℝ) : ℂ :=
  ∑g : FullGraph m,shapeTermLimit m p γ β g

 
theorem tendsto_energySlice (m p : ℕ) (γ β : Fin p → ℝ) :
    Tendsto (fun n => energySlice n m p γ β) atTop (𝓝 (energySliceLimit m p γ β)) := by
  simp only [energySlice_eq_shapes,Finset.mul_sum,energySliceLimit]
  apply tendsto_finsetSum
  intro g hg
  by_cases hm : m≤g.1.2.card+2
  · have ht := (FiniteLabelCount.tendsto_choose_inv_pow_complex m (g.1.2.card+2) hm).mul
      (tendsto_graphCoefficient m p γ β g.1.1 g.1.2)
    by_cases he : m=g.1.2.card+2
    · simpa only [shapeTerm,shapeTermLimit,ite_eq_left hm,ite_eq_left he,mul_assoc] using ht
    · simpa only [shapeTerm,shapeTermLimit,ite_eq_left hm,ite_eq_right he,zero_mul,mul_assoc] using ht
  · have he : m≠g.1.2.card+2 := by omega
    simp only [shapeTerm,shapeTermLimit,ite_eq_right hm,ite_eq_right he,mul_zero]
    exact tendsto_const_nhds

 
def truncatedEnergy (n p L : ℕ) (γ β : Fin p → ℝ) : ℂ :=
  ∑g : MarkedGraph n with (usedVertices g.1 g.2).card<L+2,clusterEnergy p γ β g.1 g.2

lemma truncatedEnergy_eq_slices (n p L : ℕ) (γ β : Fin p → ℝ) :
    truncatedEnergy n p L γ β=∑m∈Finset.range (L+2),energySlice n m p γ β := by
  unfold energySlice truncatedEnergy
  simpa only [Finset.mem_range] using (Finset.sum_fiberwise_eq_sum_filter Finset.univ
    (Finset.range (L+2)) (fun g : MarkedGraph n => (usedVertices g.1 g.2).card)
    (fun g => clusterEnergy p γ β g.1 g.2)).symm

theorem tendsto_truncatedEnergy (p L : ℕ) (γ β : Fin p → ℝ) :
    Tendsto (fun n => truncatedEnergy n p L γ β) atTop
      (𝓝 (∑m∈Finset.range (L+2),energySliceLimit m p γ β)) := by
  simp only [truncatedEnergy_eq_slices]
  exact tendsto_finsetSum _ (fun m _ => tendsto_energySlice m p γ β)

end SKQAOA.SiteHistories

 

open scoped Topology
open Filter

namespace UniformApproximation

 

theorem cauchySeq_of_approximants {E : Type*} [PseudoMetricSpace E]
    (f : ℕ → E) (a : ℕ → ℕ → E) (c : ℕ → E) (b : ℕ → ℝ)
    (ha : ∀L,Tendsto (a L) atTop (𝓝 (c L)))
    (hb : Tendsto b atTop (𝓝 0))
    (hd : ∀L n,dist (f n) (a L n)≤b L) : CauchySeq f := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hε3 : 0<ε/3 := by positivity
  obtain ⟨L,hL⟩ := (hb.eventually (gt_mem_nhds hε3)).exists
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (ha L).cauchySeq (ε/3) hε3
  refine ⟨N,fun m hm n hn => ?_⟩
  have ht : dist (f m) (f n)≤dist (f m) (a L m)+dist (a L m) (a L n)+dist (a L n) (f n) :=
    (dist_triangle (f m) (a L m) (f n)).trans
      (by linarith [dist_triangle (a L m) (a L n) (f n)])
  have hd₁ := hd L m
  have hd₂ := hd L n
  rw [dist_comm (f n)] at hd₂
  have hmn := hN m hm n hn
  linarith

end UniformApproximation

 

open scoped BigOperators Topology
open Filter

namespace SKQAOA.SiteHistories
attribute [local instance] Classical.propDecidable

lemma norm_complexEnergy_sub_truncated (n p L : ℕ) (γ β : Fin p → ℝ) :
    ‖complexEnergy n p γ β-truncatedEnergy n p L γ β‖≤tailConstant p γ β/(2:ℝ)^L := by
  have he : complexEnergy n p γ β-truncatedEnergy n p L γ β=
      ∑g : MarkedGraph n with L+2≤(usedVertices g.1 g.2).card,clusterEnergy p γ β g.1 g.2 := by
    have h := Finset.sum_filter_add_sum_filter_not (s:=Finset.univ)
      (p:=fun g : MarkedGraph n => (usedVertices g.1 g.2).card<L+2)
      (f:=fun g => clusterEnergy p γ β g.1 g.2)
    simp only [not_lt] at h
    rw [complexEnergy,truncatedEnergy]
    rw [Fintype.sum_prod_type] at h
    exact sub_eq_iff_eq_add.mpr (h.symm.trans (add_comm _ _))
  rw [he]
  calc
    _ ≤ ∑g : MarkedGraph n with L+2≤(usedVertices g.1 g.2).card,‖clusterEnergy p γ β g.1 g.2‖ := norm_sum_le _ _
    _ = ∑r : Edge n,∑H : Finset (Edge n) with L+2≤(usedVertices r H).card,‖clusterEnergy p γ β r H‖ := by
      simp only [Finset.sum_filter,Fintype.sum_prod_type]
    _ ≤ _ := sum_norm_clusterEnergy_tail n p L γ β

theorem exists_complexEnergy_limit (p : ℕ) (γ β : Fin p → ℝ) :
    ∃ z : ℂ,Tendsto (fun n => complexEnergy n p γ β) atTop (𝓝 z) := by
  apply cauchySeq_tendsto_of_complete
  apply UniformApproximation.cauchySeq_of_approximants
    (a:=fun L n => truncatedEnergy n p L γ β)
    (c:=fun L => ∑m∈Finset.range (L+2),energySliceLimit m p γ β)
    (b:=fun L => tailConstant p γ β/(2:ℝ)^L)
  · exact fun L => tendsto_truncatedEnergy p L γ β
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(2:ℝ)⁻¹)
        (by norm_num : (2:ℝ)⁻¹<1)).const_mul (tailConstant p γ β)
    simpa only [div_eq_mul_inv,inv_pow,mul_zero] using ht
  · intro L n
    simpa only [dist_eq_norm] using norm_complexEnergy_sub_truncated n p L γ β

end SKQAOA.SiteHistories

namespace SKQAOA

 

theorem exists_expectedEnergy_limit (p : ℕ) (γ β : Fin p → ℝ) :
    ∃ v : ℝ,Tendsto (fun n => expectedEnergy n p γ β) atTop (𝓝 v) := by
  obtain ⟨z,hz⟩ := SiteHistories.exists_complexEnergy_limit p γ β
  refine ⟨z.re,?_⟩
  simpa only [SiteHistories.expectedEnergy_eq_complexEnergy,Function.comp_def] using
    Complex.continuous_re.continuousAt.tendsto.comp hz

 
theorem tendsto_expectedEnergy_value (p : ℕ) (γ β : Fin p → ℝ) :
    Tendsto (fun n => expectedEnergy n p γ β) atTop (𝓝 (value p γ β)) := by
  exact tendsto_nhds_limUnder (exists_expectedEnergy_limit p γ β)

end SKQAOA

 

open scoped Topology
open Filter

namespace SKQAOA

theorem abs_value_le_Pstar (p : ℕ) (γ β : Fin p → ℝ) : |value p γ β|≤Pstar := by
  exact le_of_tendsto_of_tendsto (tendsto_expectedEnergy_value p γ β).abs tendsto_expectedGround
    (Eventually.of_forall fun n => abs_expectedEnergy_le_expectedGround n p γ β)

theorem value_le_Pstar (p : ℕ) (γ β : Fin p → ℝ) : value p γ β≤Pstar :=
  (le_abs_self _).trans (abs_value_le_Pstar p γ β)

theorem valueSet_bddAbove (p : ℕ) :
    BddAbove (Set.range fun θ : (Fin p → ℝ)×(Fin p → ℝ) => value p θ.1 θ.2) := by
  refine ⟨Pstar,?_⟩
  rintro x ⟨θ,rfl⟩
  exact value_le_Pstar p θ.1 θ.2

theorem value_le_Q (p : ℕ) (γ β : Fin p → ℝ) : value p γ β≤Q p :=
  le_csSup (valueSet_bddAbove p) (Set.mem_range_self (γ,β))

theorem Q_le_Pstar (p : ℕ) : Q p≤Pstar := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨θ,rfl⟩
  exact value_le_Pstar p θ.1 θ.2

theorem monotone_Q : Monotone Q := by
  intro p q hpq
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hpq
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨⟨γ,β⟩,rfl⟩
  simpa only [value_extendAngles] using value_le_Q (p+k) (extendAngles γ k) (extendAngles β k)

 

def attainableEnergy : ℝ := sSup (Set.range Q)

theorem attainableEnergy_le_Pstar : attainableEnergy≤Pstar := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨p,rfl⟩
  exact Q_le_Pstar p

theorem tendsto_Q_attainableEnergy : Tendsto Q atTop (𝓝 attainableEnergy) := by
  simpa only [attainableEnergy, iSup] using tendsto_atTop_ciSup monotone_Q ⟨Pstar,fun x ⟨p,hp⟩ => hp ▸ Q_le_Pstar p⟩

end SKQAOA

end

end OAI
