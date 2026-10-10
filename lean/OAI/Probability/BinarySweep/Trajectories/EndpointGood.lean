import Mathlib
import OAI.Probability.BinarySweep.SparseBounds.SparseAmplitude
import OAI.Probability.BinarySweep.Trajectories.EndpointOccupancy

namespace OAI

noncomputable section

section

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
lemma Sparse.productProbability_or_le {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀u, 0≤p u) (E F : (I → Ω) → Prop) :
    productProbability p (fun x => E x ∨ F x) ≤ productProbability p E+productProbability p F := by
  unfold productProbability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hx := productWeight_nonneg hp x
  by_cases he : E x <;> by_cases hf : F x <;> simp [he,hf,hx]

variable {b h k : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

def endpointVertexIncident (e : Fin k → GridSlot bits × GridSlot bits) : Finset (Fin k) :=
  incidentSet shareVertex (fun a => (H.position 0 a,H.position (Fin.last b) a)) e

lemma vertexIsolated_of_not_incident (e : Fin k → GridSlot bits × GridSlot bits) (i : Fin k)
    (hi : i∉endpointVertexIncident H e) : vertexIsolated H e i := by
  have hh (a : Fin h) (t : Fin (b+1)) :
      independentPosition (H.position 0 a,H.position (Fin.last b) a) t=H.position t a :=
    independentPosition_of_path (fun t => H.position t a) (fun j i hi => H.changes_only_stage j a i hi) t
  have hn : ¬((∃j,i≠j ∧ shareVertex (e i) (e j)) ∨
      ∃a, shareVertex (e i) (H.position 0 a,H.position (Fin.last b) a)) := by
    simpa only [endpointVertexIncident,incidentSet,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  constructor
  · intro t a he
    exact hn (Or.inr ⟨a,t,he.trans (hh a t).symm⟩)
  · intro t a ha he
    exact hn (Or.inl ⟨a,ha.symm,t,he.symm⟩)

def endpointGoodSet (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i∉endpointVertexIncident H e ∧
    ∀j, endpointLight H η e (endpointPathLine e i j))

def endpointHoleBad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => endpointLine (e i) j∈holeHeavyLines H j η)

def endpointParticleBad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) (j : Fin b) : Finset (Fin k) :=
  Finset.univ.filter (fun i => endpointLine (e i) j∈particleHeavyLines e j η)

lemma endpointGood_cover (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits) :
    k ≤ (endpointGoodSet H η e).card+(endpointVertexIncident H e).card+
      (∑j, (endpointHoleBad H η e j).card)+(∑j, (endpointParticleBad η e j).card) := by
  let G := endpointGoodSet H η e
  let V := endpointVertexIncident H e
  let S := Finset.univ.biUnion (endpointHoleBad H η e)
  let T := Finset.univ.biUnion (endpointParticleBad η e)
  have hc : (Finset.univ : Finset (Fin k))⊆((G∪V)∪S)∪T := by
    intro i _
    by_cases hv : i∈V
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hv))
    by_cases hl : ∀j, endpointLight H η e (endpointPathLine e i j)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv,hl⟩)))
    push Not at hl
    obtain ⟨j,hj⟩ := hl
    obtain hh | ht := endpoint_not_light H e j (endpointLine (e i) j) η hj
    · apply Finset.mem_union_left
      apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩
    · apply Finset.mem_union_right
      exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht⟩⟩
  have h1 := Finset.card_le_card hc
  have h2 := Finset.card_union_le ((G∪V)∪S) T
  have h3 := Finset.card_union_le (G∪V) S
  have h4 := Finset.card_union_le G V
  have h5 := Finset.card_biUnion_le (s:=Finset.univ) (t:=endpointHoleBad H η e)
  have h6 := Finset.card_biUnion_le (s:=Finset.univ) (t:=endpointParticleBad η e)
  simp only [Finset.card_univ,Fintype.card_fin] at h1
  dsimp [G,V,S,T] at h1 h2 h3 h4
  omega

lemma few_good_implies_bad (η : ℝ) (e : Fin k → GridSlot bits × GridSlot bits)
    (wv wl : ℕ) (hb : 2*(wv-1+2*b*(wl-1))≤k)
    (hg : 2*(endpointGoodSet H η e).card<k) :
    wv≤(endpointVertexIncident H e).card ∨
      ∃j, wl≤(endpointHoleBad H η e j).card ∨ wl≤(endpointParticleBad η e j).card := by
  by_contra hn
  push Not at hn
  have hv : (endpointVertexIncident H e).card≤wv-1 := by omega
  have hh : (∑j, (endpointHoleBad H η e j).card)≤b*(wl-1) := by
    calc
      _ ≤ ∑j : Fin b, (wl-1) := Finset.sum_le_sum (fun j _ => by have := (hn.2 j).1; omega)
      _ = _ := by simp
  have ht : (∑j, (endpointParticleBad η e j).card)≤b*(wl-1) := by
    calc
      _ ≤ ∑j : Fin b, (wl-1) := Finset.sum_le_sum (fun j _ => by have := (hn.2 j).2; omega)
      _ = _ := by simp
  have hc := endpointGood_cover H η e
  have hm : 2*b*(wl-1)=b*(wl-1)+b*(wl-1) := by ring
  omega

lemma few_good_probability_bound {η : ℝ} (hη : 0<η) (wv wl : ℕ)
    (hb : 2*(wv-1+2*b*(wl-1))≤k)
    (hv : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits)≤1)
    (hh : 2*h/((gridSize bits:ℝ)*η)≤1) (hk : 2*k/((gridSize bits:ℝ)*η)≤1) :
    productProbability uniformWeight (fun e : Fin k → GridSlot bits × GridSlot bits =>
      2*(endpointGoodSet H η e).card<k) ≤
      (2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) +
      ∑j : Fin b, ((2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl) := by
  let V (e : Fin k → GridSlot bits × GridSlot bits) := wv≤(endpointVertexIncident H e).card
  let B (j : Fin b) (e : Fin k → GridSlot bits × GridSlot bits) :=
    wl≤(endpointHoleBad H η e j).card ∨ wl≤(endpointParticleBad η e j).card
  have h1 := productProbability_mono uniformWeight_nonneg (fun e he => few_good_implies_bad H η e wv wl hb he)
  have h2 := productProbability_or_le uniformWeight uniformWeight_nonneg V (fun e => ∃j, B j e)
  have h3 := productProbability_union_le uniformWeight_nonneg B
  have h4 : productProbability uniformWeight V≤
      (2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) :=
    independent_trajectory_sharing (fun a => (H.position 0 a,H.position (Fin.last b) a)) wv hv
  have h5 : ∀j, productProbability uniformWeight (B j)≤
      (2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl := by
    intro j
    exact (productProbability_or_le uniformWeight uniformWeight_nonneg _ _).trans
      (add_le_add (holeHeavy_occupancy_bound H j hη hh wl) (particleHeavy_occupancy_bound j hη hk wl))
  exact h1.trans (h2.trans (add_le_add h4 (h3.trans (Finset.sum_le_sum (fun j _ => h5 j)))))

end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Sparse
attribute [local instance] Classical.propDecidable
variable {P Ω : Type*} [Fintype P] [Fintype Ω]

lemma sum_square_le_uniform_split (f : P → Ω) (hi : Function.Injective f)
    (Q : Ω → ℝ) (E : Ω → Prop) (a C B : ℝ) (ha : 0<a)
    (hN : (Fintype.card Ω:ℝ)=a^2)
    (hc : ∀i, ¬E (f i) → |a*Q (f i)|≤C) (hb : ∀i, |a*Q (f i)|≤B) :
    ∑i, (Q (f i))^2 ≤ C^2+B^2*finiteProbability uniformWeight E := by
  have hcard : (Fintype.card Ω:ℝ)≠0 := by rw [hN]; positivity
  have hp : (Fintype.card Ω:ℝ)*finiteProbability uniformWeight E =
      ∑u : Ω, if E u then (1:ℝ) else 0 := by
    unfold finiteProbability uniformWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    rw [← mul_assoc,mul_one_div_cancel hcard,one_mul]
  have hle : a^2*(∑i, (Q (f i))^2) ≤ ∑u : Ω, (C^2+if E u then B^2 else 0) := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum (fun i _ => ?_)).trans
      (sum_injective_le f hi (fun u => C^2+if E u then B^2 else 0)
        (fun u => by split_ifs <;> positivity))
    by_cases hE : E (f i)
    · rw [ite_eq_left hE,← mul_pow]
      have hs := pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
      rw [sq_abs] at hs
      linarith [sq_nonneg C]
    · rw [ite_eq_right hE,add_zero,← mul_pow]
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc i hE) 2
  have he : (∑u : Ω, (C^2+if E u then B^2 else 0)) =
      (Fintype.card Ω:ℝ)*(C^2+B^2*finiteProbability uniformWeight E) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_add,mul_left_comm _ (B^2),hp,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro u _
    split_ifs <;> simp
  rw [he,hN] at hle
  exact (mul_le_mul_iff_right₀ (sq_pos_of_pos ha)).mp hle

end BinaryCoordinateSweeps.Sparse
namespace BinaryCoordinateSweeps
open Sparse

attribute [local instance] Classical.propDecidable
variable {b h k r : ℕ} {bits : Fin b → ℕ} (H : PathFamily bits h)

theorem centeredEndpointKernel_few_hs (hd : ∀j, bits j≤2*r) {η : ℝ}
    (hη : 0<η) (hη1 : η≤1/4) (hηb : 4*(b:ℝ)*Real.sqrt η≤1)
    (wv wl : ℕ) (ht : 2*(wv-1+2*b*(wl-1))≤k)
    (hv : ((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits)≤1)
    (hh : 2*h/((gridSize bits:ℝ)*η)≤1) (hk : 2*k/((gridSize bits:ℝ)*η)≤1) :
    (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
      (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) ≤
      ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^((k+1)/2))^2 +
      ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*(((k+h:ℕ):ℝ)*((b+1:ℝ)/gridSize bits))^((wv+1)/2) +
      ∑j : Fin b, ((2:ℝ)^k*(2*h/((gridSize bits:ℝ)*η))^wl +
        (Fintype.card (GridOutside bits j)+1:ℕ)^⌊2*(k:ℝ)/((2^bits j:ℕ)*η)⌋₊ *
          (2:ℝ)^k*(2*k/((gridSize bits:ℝ)*η))^wl)) := by
  let f := placementEndpointArray (k:=k) H
  let E (e : Fin k → GridSlot bits × GridSlot bits) := 2*(endpointGoodSet H η e).card<k
  have hs : (0:ℝ)<gridSize bits := by exact_mod_cast gridSize_pos bits
  have hN : (Fintype.card (Fin k → GridSlot bits × GridSlot bits):ℝ)=((gridSize bits:ℝ)^k)^2 := by
    simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_prod,card_gridSlot,Nat.cast_pow,Nat.cast_mul,mul_pow,pow_two]
  have he := sum_square_le_uniform_split f (placementEndpointArray_injective H)
    (centeredEndpointKernel H 0) E ((gridSize bits:ℝ)^k)
    ((2:ℝ)^(k+k*b)*Real.exp ((b*h+k+k*b:ℕ):ℝ)*(4*b*Real.sqrt η)^((k+1)/2))
    ((2:ℝ)^k*Real.exp ((b:ℝ)*(h+k)+Real.log 4*k*b)) (pow_pos hs _) hN
    (fun xy hE => ?_) (fun xy => centeredEndpointKernel_amplitude H hd (le_refl 0)
      (linePerturbationRadius_pos r).le (by norm_num) xy.1 xy.2)
  · rw [← productProbability_uniform] at he
    have hp := few_good_probability_bound H hη wv wl ht hv hh hk
    have heq : (∑x : Placement H k 0, ∑y : Placement H k (Fin.last b),
        (centeredEndpointKernel H 0 (fun i => ((x i).val,(y i).val)))^2) =
        ∑xy : Placement H k 0 × Placement H k (Fin.last b),
          (centeredEndpointKernel H 0 (f xy))^2 := by
      rw [Fintype.sum_prod_type]
      rfl
    rw [heq]
    exact he.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp (sq_nonneg _)))
  · have hi : ∀i∈endpointGoodSet H η (f xy), vertexIsolated H (f xy) i := by
      intro i hi
      exact vertexIsolated_of_not_incident H (f xy) i (Finset.mem_filter.mp hi).2.1
    have hl := fun i (hi : i∈endpointGoodSet H η (f xy)) => (Finset.mem_filter.mp hi).2.2
    have hh := centeredEndpointKernel_good_bound H xy.1 xy.2 (endpointGoodSet H η (f xy)) hη.le hη1 hi hl
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_of_le_one (by positivity) hηb
    dsimp [E] at hE
    omega

end BinaryCoordinateSweeps

end

end OAI
