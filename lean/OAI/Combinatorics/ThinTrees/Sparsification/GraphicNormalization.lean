import Mathlib
import OAI.Combinatorics.ThinTrees.Normalization.Parameters
import OAI.Combinatorics.ThinTrees.Signing.Realization

namespace OAI

/-! Graphic normalization. -/

section

namespace AlgorithmicThinTrees.Normalization
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
variable {d m q : ℕ}

def dropRoot (d : ℕ) : zeroSumSpace (d+1) ≃ₗ[ℝ] (Fin d → ℝ) where
  toFun x i := x.val i.succ
  invFun y := ⟨Fin.cases (-(∑i, y i)) y,by
    rw [mem_zeroSumSpace,Fin.sum_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,neg_add_cancel]⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => rfl) i
    have hh := (mem_zeroSumSpace x.val).mp x.property
    rw [Fin.sum_univ_succ] at hh
    change -(∑i : Fin d, x.val i.succ)=x.val 0
    linarith only [hh]
  right_inv y := rfl
  map_add' x y := rfl
  map_smul' c x := rfl

def integerColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) : Fin m → Fin d → ℤ :=
  fun e i => if e ∈ B then (if G.left e=i.succ then 1 else 0)-(if G.right e=i.succ then 1 else 0) else 0

def graphColumns (G : MultiGraph (d+1) m) (B : Finset (Fin m)) : Fin m → Fin d → ℚ :=
  fun e i => (integerColumns G B e i:ℚ)

lemma graphColumns_cast (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (e : Fin m) :
    realColumns (graphColumns G B) e = if e ∈ B then
      dropRoot d ⟨G.incidence e,G.incidence_zeroSum e⟩ else 0 := by
  funext i
  by_cases he : e ∈ B
  · rw [ite_eq_left he]
    change ((integerColumns G B e i : ℚ):ℝ) = G.incidence e i.succ
    simp only [integerColumns,ite_eq_left he,Int.cast_sub,incidence,
      point,Pi.sub_apply,Pi.single_apply,eq_comm (a:=i.succ)]
    split_ifs <;> norm_num
  · simp [he,realColumns,graphColumns,integerColumns]

lemma graphColumns_norm (G : MultiGraph (d+1) m) (B : Finset (Fin m)) (e : Fin m) :
    realColumns (graphColumns G B) e ⬝ᵥ realColumns (graphColumns G B) e ≤ 2 := by
  rw [graphColumns_cast]
  split_ifs with he
  · have hh := G.eval_incidence (G.incidence e) e
    have hnorm : G.incidence e ⬝ᵥ G.incidence e=2 := by
      rw [dotProduct,hh]
      norm_num [incidence,point,G.loopless e,Ne.symm (G.loopless e)]
    rw [dotProduct,Fin.sum_univ_succ] at hnorm
    change (∑i : Fin d, G.incidence e i.succ*G.incidence e i.succ) ≤ 2
    nlinarith only [hnorm,sq_nonneg (G.incidence e 0)]
  · simp

lemma integral_det_bound (v : Fin d → Fin d → ℤ)
    (hv : IsUnit (Matrix.of (fun i j => (v i j:ℝ)))) :
    1 ≤ (Matrix.det (fun i j => (v i j:ℝ)))^2 := by
  have hdet : (Matrix.of v).det ≠ 0 := by
    intro hh
    have hR : (Matrix.of (fun i j => (v i j:ℝ))).det=0 := by
      have hc := (Int.cast_det (R := ℝ) (Matrix.of v)).symm
      rw [hh,Int.cast_zero] at hc
      exact hc
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hv)) hR
  have hpos : (0:ℤ) < (Matrix.of v).det^2 := sq_pos_of_ne_zero hdet
  have h1 : (1:ℤ) ≤ (Matrix.of v).det^2 := by omega
  have hR : (1:ℝ) ≤ ((Matrix.of v).det:ℝ)^2 := by exact_mod_cast h1
  rw [Int.cast_det] at hR
  exact hR

lemma integral_containedPacking {E : Type*} [DecidableEq E]
    (v : E → Fin d → ℤ) (F : Fin q → Finset E) (hq : 0 < q)
    (hF : ∀t, LinearIndepOn ℝ (fun e i => (v e i:ℝ)) (F t : Set E))
    (hc : ∀t, (F t).card=d) (hd : Pairwise (fun i j => Disjoint (F i) (F j))) :
    Nonempty (ContainedPacking (fun e i => (v e i:ℝ)) q) := by
  classical
  let en (t : Fin q) : Fin d ≃ ↥(F t) := Fintype.equivOfCardEq (by simp [hc])
  let f : Fin q × Fin d → E :=fun x => en x.1 x.2
  have hinj : Function.Injective f := by
    rintro ⟨t,i⟩ ⟨u,j⟩ hh
    have hev : (en t i:E)=(en u j:E) := hh
    have htu : t=u := by
      by_contra h
      exact Finset.disjoint_left.mp (hd h) (en t i).property (hev ▸ (en u j).property)
    subst u
    have hij := (en t).injective (Subtype.ext hev)
    subst j
    rfl
  have hb (t : Fin q) : IsUnit (Matrix.of (fun i j => (v (en t j) i:ℝ))) := by
    apply Matrix.mulVec_injective_iff_isUnit.mp
    apply Matrix.mulVec_injective_iff.mpr
    exact (hF t).linearIndependent.comp (en t) (en t).injective
  exact ⟨⟨hq,⟨f,hinj⟩,hb,fun t => integral_det_bound (fun i j => v (en t j) i) (hb t)⟩⟩

lemma graph_containedPacking (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    (hq : 0 < q) (hp : G.TreePackable B q) :
    Nonempty (ContainedPacking (realColumns (graphColumns G B)) q) := by
  obtain ⟨F,hF,hd⟩ := hp
  have hv : realColumns (graphColumns G B) =
      fun e i => (integerColumns G B e i:ℝ) := by
    funext e i
    simp only [realColumns,graphColumns,Rat.cast_intCast]
  rw [hv]
  apply integral_containedPacking _ F hq ?_ ?_ hd
  · intro t
    have hf := ((G.spanningTree_iff_independent (F t)).mp (hF t).2).2.linearIndependent
    have hf' : LinearIndependent ℝ (fun e : ↥(F t) =>
        (⟨G.incidence e,G.incidence_zeroSum e⟩ : zeroSumSpace (d+1))) :=
      hf.of_comp (zeroSumSpace (d+1)).subtype
    have hl := hf'.map' (dropRoot d).toLinearMap (dropRoot d).ker
    change LinearIndependent ℝ (fun (e : ↥(F t)) (i : Fin d) => (integerColumns G B e i:ℝ))
    have hvec : (fun (e : ↥(F t)) (i : Fin d) => (integerColumns G B e i:ℝ)) =
        (dropRoot d).toLinearMap ∘ (fun e : ↥(F t) =>
          (⟨G.incidence e,G.incidence_zeroSum e⟩ : zeroSumSpace (d+1))) := by
      funext e i
      have he := graphColumns_cast G B e.val
      rw [hv,ite_eq_left ((hF t).1 e.property)] at he
      exact congrFun he i
    rw [hvec]
    exact hl
  · intro t
    simpa only [Nat.add_sub_cancel] using G.spanningTree_card (by omega : 0 < d+1) (hF t).2

theorem graphic_normalization (G : MultiGraph (d+1) m) (B : Finset (Fin m))
    {q r : ℕ} (hq : 0 < q) (hqr : q ≤ r) (hp : G.TreePackable B q) :
    let s := normalizedScales q r (graphColumns G B)
    (∀e, 0 < s e ∧ s e ≤ 1) ∧
    (∀e, leverage (realColumns (graphColumns G B)) (realWeights s) e ≤ (1+4/(r:ℝ))/(q:ℝ)) ∧
    (∀e, CurrentKS.RationalBits.Parts (normalizationLength m r*(5+2*r.size)) (s e)) := by
  obtain ⟨packing⟩ := graph_containedPacking G B hq hp
  exact normalizedScales_correct _ packing hqr (graphColumns_norm G B)

end AlgorithmicThinTrees.Normalization
end

end OAI
