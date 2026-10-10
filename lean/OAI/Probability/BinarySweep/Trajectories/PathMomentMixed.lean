import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseKernel
import OAI.Probability.BinarySweep.Trajectories.EndpointFactors
import OAI.Probability.BinarySweep.Trajectories.PathTelescope

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse

lemma centeredLineMoment_mixed {m h u v : ℕ} {η : ℝ}
    (hm : 0 < m) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : 0<u → (h:ℝ)+u+v ≤ m*η) :
    0≤centeredLineMoment m h u v ∧
    centeredLineMoment m h u v ≤
      Real.exp ((h:ℝ)+u+v) * 2^v * (4*Real.sqrt η)^u := by
  by_cases hu : u=0
  · subst u
    simp only [centeredLineMoment_zero,pow_zero,mul_one,Nat.cast_zero,add_zero]
    refine ⟨fallingMoment_nonneg _ _ _,(fallingMoment_le_exp hm).trans ?_⟩
    exact le_mul_of_one_le_right (Real.exp_pos _).le (one_le_pow₀ (by norm_num))
  · have hb := centeredLineMoment_light hm hη0 hη (hl (Nat.pos_of_ne_zero hu))
    refine ⟨hb.1,hb.2.trans ?_⟩
    have he : 1≤Real.exp ((h:ℝ)+u+v) := Real.one_le_exp (by positivity)
    have hn : 0≤(2:ℝ)^v*(4*Real.sqrt η)^u := by positivity
    simpa only [mul_assoc] using le_mul_of_one_le_left hn he

variable {L A B : Type*} [Fintype L] [Fintype A] [Fintype B]

theorem occurrenceMoment_mixed (m h : L → ℕ) (f : A → L) (g : B → L)
    {η : ℝ} (hm : ∀l, 0 < m l) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀l, 0<occurrences f l → (h l:ℝ)+occurrences f l+occurrences g l ≤ m l*η) :
    let P := ((∏a, ((MvPolynomial.X (f a) : MvPolynomial L ℝ)-1)) *
      ∏b, MvPolynomial.X (g b))
    0 ≤ multilineMoment m h P ∧ multilineMoment m h P ≤
      Real.exp ((∑l, (h l:ℝ)) + Fintype.card A+Fintype.card B) *
        2^Fintype.card B*(4*Real.sqrt η)^Fintype.card A := by
  dsimp only
  rw [occurrenceMoment_eq]
  have hb (l : L) := centeredLineMoment_mixed (hm l) hη0 hη (hl l)
  refine ⟨Finset.prod_nonneg (fun l _ => (hb l).1),?_⟩
  calc
    _ ≤ ∏l, Real.exp ((h l:ℝ)+occurrences f l+occurrences g l) *
        2^occurrences g l * (4*Real.sqrt η)^occurrences f l :=
      Finset.prod_le_prod₀ (fun l _ => (hb l).1) (fun l _ => (hb l).2)
    _ = _ := by
      rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,← Real.exp_sum,
        Finset.prod_pow_eq_pow_sum,Finset.prod_pow_eq_pow_sum,
        sum_occurrences,sum_occurrences]
      congr 2
      simp only [Finset.sum_add_distrib,← Nat.cast_sum,sum_occurrences]

theorem pathMoment_mixed {b : ℕ} (m h : L → ℕ) (f : A → Fin b → L) (g : B → L)
    {η : ℝ} (hm : ∀l, 0 < m l) (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀a j, (h (f a j):ℝ)+
      occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) (f a j) ≤ m (f a j)*η) :
    let P := (∏a, ((∏j, (MvPolynomial.X (f a j) : MvPolynomial L ℝ))-1)) *
      (∏k, MvPolynomial.X (g k))
    0 ≤ multilineMoment m h P ∧ multilineMoment m h P ≤
      (b:ℝ)^Fintype.card A *
      (Real.exp ((∑l, (h l:ℝ))+Fintype.card A+Fintype.card B+Fintype.card A*b) *
        2^(Fintype.card B+Fintype.card A*b)*(4*Real.sqrt η)^Fintype.card A) := by
  dsimp only
  rw [path_telescope_expansion,map_sum]
  have hb (c : A → Fin b) := occurrenceMoment_mixed m h (centeredLine f c)
    (Sum.elim g (suffixLine f c)) hm hη0 hη (fun l hlu => by
      obtain ⟨a,ha⟩ := (Fintype.card_pos_iff.mp hlu)
      have hn := telescope_occurrences_le f g c l
      have hn' : (occurrences (centeredLine f c) l:ℝ)+
        occurrences (Sum.elim g (suffixLine f c)) l ≤
        occurrences (Sum.elim g (fun a : A × Fin b => f a.1 a.2)) l := by exact_mod_cast hn
      have hx := hl a (c a)
      change f a (c a)=l at ha
      rw [ha] at hx
      linarith)
  refine ⟨Finset.sum_nonneg (fun c _ => (hb c).1),?_⟩
  calc
    _ ≤ ∑c : A → Fin b,
      Real.exp ((∑l, (h l:ℝ))+Fintype.card A+Fintype.card B+Fintype.card A*b) *
        2^(Fintype.card B+Fintype.card A*b)*(4*Real.sqrt η)^Fintype.card A := by
      apply Finset.sum_le_sum
      intro c _
      apply (hb c).2.trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        have hc : (Fintype.card (Suffixes c):ℝ)≤Fintype.card A*b := by
          exact_mod_cast card_suffixes_le c
        simp only [Fintype.card_sum,Nat.cast_add]
        linarith
      · apply pow_le_pow_right₀ (by norm_num)
        simpa using Nat.add_le_add_left (card_suffixes_le c) (Fintype.card B)
      · positivity
      · positivity
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fun,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]

end BinaryCoordinateSweeps.Sparse

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)
variable {I : Type*} [Fintype I] [DecidableEq I]

def endpointPathPolynomial (e : I → GridSlot bits × GridSlot bits) (i : I) :
    MvPolynomial (EndpointLineIndex bits) ℝ := ∏j, MvPolynomial.X (endpointPathLine e i j)

def vertexIsolated (e : I → GridSlot bits × GridSlot bits) (i : I) : Prop :=
  (∀t a, independentPosition (e i) t≠H.position t a) ∧
  (∀t a, a≠i → independentPosition (e a) t≠independentPosition (e i) t)

omit [Fintype I] in
lemma endpointValid_union_isolated (e : I → GridSlot bits × GridSlot bits)
    (G J : Finset I) (hi : ∀i∈G, vertexIsolated H e i) :
    EndpointValid H (J∪G) e ↔ EndpointValid H J e := by
  induction G using Finset.induction_on with
  | empty => simp only [Finset.union_empty]
  | @insert i G hn ih =>
    rw [Finset.union_insert,endpointValid_insert H _ e i
      (hi i (Finset.mem_insert_self _ _)).1 (hi i (Finset.mem_insert_self _ _)).2]
    exact ih (fun a ha => hi a (Finset.mem_insert_of_mem ha))

lemma endpoint_subset_polynomial (x : Placement H k 0) (y : Placement H k (Fin.last b))
    (A : Finset (Fin k)) :
    (gridSize bits:ℝ)^A.card * endpointProbability H 0 A (fun i => ((x i).val,(y i).val)) =
      if EndpointValid H A (fun i => ((x i).val,(y i).val)) then
        multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
          (fun l => lineHoles H l.1 l.2)
          (∏i∈A, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
      else 0 := by
  rw [endpointProbability_zero_polynomial]
  congr 1
  apply congrArg (multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
    (fun l => lineHoles H l.1 l.2))
  exact Finset.prod_coe_sort A (endpointPathPolynomial (fun i => ((x i).val,(y i).val)))

lemma centeredEndpointKernel_scaled (z : ℝ) (e : I → GridSlot bits × GridSlot bits) :
    (gridSize bits:ℝ)^Fintype.card I * centeredEndpointKernel H z e =
      mobiusSum Finset.univ (fun A => (gridSize bits:ℝ)^A.card * endpointProbability H z A e) := by
  unfold centeredEndpointKernel alternatingSubsetSum mobiusSum
  rw [← mul_assoc,← mul_pow,mul_inv_cancel₀ (show (gridSize bits:ℝ)≠0 by
    exact_mod_cast (gridSize_pos bits).ne'),one_pow,one_mul]
  apply Finset.sum_congr rfl
  intro A _
  ring

theorem centeredEndpointKernel_good_expansion (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (G : Finset (Fin k))
    (hi : ∀i∈G, vertexIsolated H (fun i => ((x i).val,(y i).val)) i) :
    (gridSize bits:ℝ)^k * centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)) =
      mobiusSum (Finset.univ\G) (fun J =>
        if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
          multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
            (fun l => lineHoles H l.1 l.2)
            ((∏i∈G, (endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i-1)) *
              ∏i∈J, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
        else 0) := by
  have hs := centeredEndpointKernel_scaled H 0 (fun i => ((x i).val,(y i).val))
  simp only [Fintype.card_fin] at hs
  rw [hs]
  conv_lhs => rw [show (Finset.univ : Finset (Fin k))=G∪(Finset.univ\G) by ext i; simp]
  rw [mobiusSum_union _ _ Finset.disjoint_sdiff]
  apply mobiusSum_congr
  intro J hJ
  have hJG : Disjoint J G := (Finset.disjoint_sdiff.symm).mono_left hJ
  trans mobiusSum G (fun A => if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
    multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1)
      (fun l => lineHoles H l.1 l.2)
      ((∏i∈J, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)*
        ∏i∈A, endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i) else 0)
  · apply mobiusSum_congr
    intro A hA
    rw [endpoint_subset_polynomial,endpointValid_union_isolated H _ A J (fun i hiA => hi i (hA hiA))]
    rw [Finset.prod_union (hJG.mono_right hA)]
  · by_cases hv : EndpointValid H J (fun i => ((x i).val,(y i).val))
    · simp only [ite_eq_left hv]
      rw [mobiusSum_linear_product,mul_comm]
    · simp only [ite_eq_right hv,mobiusSum,mul_zero,Finset.sum_const_zero]

end BinaryCoordinateSweeps

end

end OAI
