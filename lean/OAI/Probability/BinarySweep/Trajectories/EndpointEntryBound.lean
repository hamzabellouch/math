import Mathlib
import OAI.Probability.BinarySweep.Trajectories.PathMomentMixed

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

lemma Sparse.mobiusSum_abs_le {I : Type*} [DecidableEq I]
    (U : Finset I) (f : Finset I → ℝ) (B : ℝ)
    (hb : ∀A⊆U, |f A|≤B) : |mobiusSum U f|≤(2:ℝ)^U.card*B := by
  unfold mobiusSum
  calc
    _ ≤ ∑A∈U.powerset, |(-1:ℝ)^(U.card-A.card)*f A| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑A∈U.powerset, B := by
      apply Finset.sum_le_sum
      intro A hA
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hb A (Finset.mem_powerset.mp hA)
    _ = _ := by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]

lemma occurrences_injective_le {I J L : Type*} [Fintype I] [Fintype J]
    (f : I → L) (g : J → L) (e : I → J) (hi : Function.Injective e)
    (he : ∀i, g (e i)=f i) (l : L) : occurrences f l≤occurrences g l := by
  apply Fintype.card_le_of_injective
    (fun a : {i // f i=l} => (⟨e a.val,(he a.val).trans a.property⟩ : {j // g j=l}))
  intro a c hac
  exact Subtype.ext (hi (congrArg Subtype.val hac))

lemma endpoint_mixed_occurrences_le (e : Fin k → GridSlot bits × GridSlot bits)
    (G J : Finset (Fin k)) (hd : Disjoint J G) (l : EndpointLineIndex bits) :
    occurrences (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
      (fun a : G × Fin b => endpointPathLine e a.1 a.2)) l ≤
      endpointLineCount Finset.univ e l.1 l.2 := by
  let emb : (J × Fin b) ⊕ (G × Fin b) → ↥(Finset.univ : Finset (Fin k)) × Fin b :=
    Sum.elim (fun a => (⟨a.1.val,Finset.mem_univ _⟩,a.2))
      (fun a => (⟨a.1.val,Finset.mem_univ _⟩,a.2))
  have hi : Function.Injective emb := by
    intro a c hac
    cases a with
    | inl a => cases c with
      | inl c => exact congrArg Sum.inl (Prod.ext (Subtype.ext (congrArg (fun x => x.1.val) hac)) (congrArg (fun v : ↥(Finset.univ : Finset (Fin k)) × Fin b => v.2) hac))
      | inr c =>
        have he : a.1.val=c.1.val := congrArg (fun x => x.1.val) hac
        exact False.elim (Finset.disjoint_left.mp hd a.1.property (he.symm ▸ c.1.property))
    | inr a => cases c with
      | inl c =>
        have he : a.1.val=c.1.val := congrArg (fun x => x.1.val) hac
        exact False.elim (Finset.disjoint_left.mp hd c.1.property (he ▸ a.1.property))
      | inr c => exact congrArg Sum.inr (Prod.ext (Subtype.ext (congrArg (fun x => x.1.val) hac)) (congrArg (fun v : ↥(Finset.univ : Finset (Fin k)) × Fin b => v.2) hac))
  have ht := occurrences_injective_le
    (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
      (fun a : G × Fin b => endpointPathLine e a.1 a.2)) (fun a : ↥(Finset.univ : Finset (Fin k)) × Fin b =>
    endpointPathLine e a.1 a.2) emb hi (fun a => by cases a <;> rfl) l
  rcases l with ⟨j,y⟩
  simpa only [pathLine_occurrences] using ht

def endpointLight (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits)
    (l : EndpointLineIndex bits) : Prop :=
  (lineHoles H l.1 l.2:ℝ)+endpointLineCount Finset.univ e l.1 l.2 ≤ (2^bits l.1:ℕ)*η

lemma endpoint_pathMoment_bound (e : Fin k → GridSlot bits × GridSlot bits)
    (G J : Finset (Fin k)) (hd : Disjoint J G) {η : ℝ} (hη0 : 0≤η) (hη : η≤1/4)
    (hl : ∀i∈G, ∀j, endpointLight H η e (endpointPathLine e i j)) :
    let P := (∏i∈G, (endpointPathPolynomial e i-1))*∏i∈J,endpointPathPolynomial e i
    0 ≤ multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2) P ∧
    multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2) P ≤
      Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card := by
  dsimp only
  have hb := pathMoment_mixed
    (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2)
    (fun i : G => endpointPathLine e i) (fun a : J × Fin b => endpointPathLine e a.1 a.2)
    (η:=η) (fun _ => by positivity) hη0 hη (fun i j => by
      have hn := endpoint_mixed_occurrences_le e G J hd (endpointPathLine e i j)
      have hn' : (occurrences (Sum.elim (fun a : J × Fin b => endpointPathLine e a.1 a.2)
        (fun a : G × Fin b => endpointPathLine e a.1 a.2)) (endpointPathLine e i j):ℝ) ≤
        endpointLineCount Finset.univ e j (endpointLine (e i) j) := by exact_mod_cast hn
      have ht := hl i i.property j
      change (lineHoles H j (endpointLine (e i) j):ℝ)+_≤_ at ht ⊢
      dsimp only [endpointPathLine] at ht hn' ⊢
      linarith only [hn',ht])
  dsimp only at hb
  have hp1 : (∏i : G, ((∏j, (MvPolynomial.X (endpointPathLine e i j) : MvPolynomial (EndpointLineIndex bits) ℝ))-1)) =
      ∏i∈G, (endpointPathPolynomial e i-1) :=
    Finset.prod_coe_sort G (fun i => endpointPathPolynomial e i-1)
  have hp2 : (∏a : J × Fin b, (MvPolynomial.X (endpointPathLine e a.1 a.2) : MvPolynomial (EndpointLineIndex bits) ℝ)) =
      ∏i∈J, endpointPathPolynomial e i :=
    (Fintype.prod_prod_type _).trans (Finset.prod_coe_sort J (endpointPathPolynomial e))
  rw [hp1,hp2] at hb
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin] at hb
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hc : J.card+G.card≤k := by
    rw [← Finset.card_union_of_disjoint hd]
    exact (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_fin k)
  have hg : G.card≤k := by omega
  have hpow : J.card*b+G.card*b≤k*b := by nlinarith
  have hh : (∑l : EndpointLineIndex bits, (lineHoles H l.1 l.2:ℝ))=(b*h:ℕ) := by
    rw [Fintype.sum_sigma]
    simp only [← Nat.cast_sum,sum_lineHoles,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  rw [hh]
  calc
    _ ≤ (b:ℝ)^G.card * (Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*Real.sqrt η)^G.card) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        exact_mod_cast (show b*h+G.card+(J.card*b)+G.card*b≤b*h+k+k*b by omega)
      · exact pow_le_pow_right₀ (by norm_num) hpow
      · positivity
      · positivity
    _ = _ := by rw [show 4*(b:ℝ)*Real.sqrt η=b*(4*Real.sqrt η) by ring,mul_pow]; ring

theorem centeredEndpointKernel_good_bound (x : Placement H k 0)
    (y : Placement H k (Fin.last b)) (G : Finset (Fin k)) {η : ℝ}
    (hη0 : 0≤η) (hη : η≤1/4)
    (hi : ∀i∈G, vertexIsolated H (fun i => ((x i).val,(y i).val)) i)
    (hl : ∀i∈G, ∀j, endpointLight H η (fun i => ((x i).val,(y i).val))
      (endpointPathLine (fun i => ((x i).val,(y i).val)) i j)) :
    |(gridSize bits:ℝ)^k*centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val))| ≤
      (2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^G.card := by
  rw [centeredEndpointKernel_good_expansion H x y G hi]
  have hc : (Finset.univ\G).card≤k := (Finset.card_le_card (Finset.sdiff_subset)).trans_eq (Finset.card_fin k)
  have hb := mobiusSum_abs_le (Finset.univ\G) (fun J =>
    if EndpointValid H J (fun i => ((x i).val,(y i).val)) then
      multilineMoment (fun l : EndpointLineIndex bits => 2^bits l.1) (fun l => lineHoles H l.1 l.2)
        ((∏i∈G,(endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i-1))*
          ∏i∈J,endpointPathPolynomial (fun i => ((x i).val,(y i).val)) i)
    else 0) (Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card) (fun J hJ => by
      have hd : Disjoint J G := Finset.disjoint_sdiff.symm.mono_left hJ
      have he := endpoint_pathMoment_bound H (fun i => ((x i).val,(y i).val)) G J hd hη0 hη hl
      split_ifs
      · rw [abs_of_nonneg he.1]; exact he.2
      · simp only [abs_zero]; positivity)
  apply hb.trans
  calc
    _ ≤ (2:ℝ)^k*(Real.exp ((b*h+k+k*b:ℕ):ℝ)*2^(k*b)*(4*b*Real.sqrt η)^G.card) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (by positivity)
    _ = _ := by rw [pow_add]; ring

end BinaryCoordinateSweeps

end

end OAI
