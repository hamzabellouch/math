import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.CoordinateRow

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility PolytopeCertificate
open scoped BigOperators

lemma finalFace_injective {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Function.Injective (fun u : Fin n → ℝ =>
      (fun i j => (rowMatrix (finalFace rows B) i j:ℝ)) *ᵥ u) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply finalFace_kernel rows B hfeas
  intro q hq
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hq
  have hh := congrFun huv ⟨i,hi⟩
  change (∑ j, ((finalFace rows B)[i].coeff j:ℝ)*u j)=
    (∑ j, ((finalFace rows B)[i].coeff j:ℝ)*v j) at hh
  rw [he] at hh
  simpa only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,sub_eq_zero] using hh

lemma finalFace_rat_injective {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Function.Injective (rowMatrix (finalFace rows B)).mulVec := by
  intro u v huv
  have he := finalFace_injective rows B hfeas (a₁:=fun j => (u j:ℝ)) (a₂:=fun j => (v j:ℝ)) ?_
  · funext j
    exact_mod_cast congrFun he j
  · ext i
    have hh := congrFun huv i
    change (∑ j, (rowMatrix (finalFace rows B) i j:ℝ)*(u j:ℝ))=
      (∑ j, (rowMatrix (finalFace rows B) i j:ℝ)*(v j:ℝ))
    exact_mod_cast hh

def facePoint {n : ℕ} (rows : List (Row n)) (B : ℕ) : Fin n → ℚ :=
  let picked := finalFace rows B
  let C := rowMatrix picked
  let G := PositiveSolve.freezeMat (Cᵀ*C)
  let d := PositiveSolve.freezeVec (Cᵀ *ᵥ rowBounds picked)
  PositiveSolve.solve n G d

theorem facePoint_correct {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    Face (withBox rows B) (finalFace rows B) B (fun j => (facePoint rows B j:ℝ)) := by
  let picked := finalFace rows B
  let C := rowMatrix picked
  let Cr : Matrix (Fin picked.length) (Fin n) ℝ := fun i j => (C i j:ℝ)
  have hC : Function.Injective C.mulVec := finalFace_rat_injective rows B hfeas
  have hCr : Function.Injective Cr.mulVec := finalFace_injective rows B hfeas
  have hG : (Cᵀ*C).PosDef := by simpa using PosDef.conjTranspose_mul_self C hC
  have hGr : (Crᵀ*Cr).PosDef := by simpa using PosDef.conjTranspose_mul_self Cr hCr
  obtain ⟨x,hx⟩ := finalFace_feasible rows B hfeas
  have hxe : Cr *ᵥ x=fun i => (rowBounds picked i:ℝ) := by
    ext i
    exact hx.2.1 _ (List.getElem_mem _)
  have hy : (Cᵀ*C) *ᵥ facePoint rows B=Cᵀ *ᵥ rowBounds picked := by
    simpa only [facePoint,PositiveSolve.freezeMat_eq,PositiveSolve.freezeVec_eq] using
      PositiveSolve.solve_correct n (Cᵀ*C) (Cᵀ *ᵥ rowBounds picked) hG
  have hye : (Crᵀ*Cr) *ᵥ (fun j => (facePoint rows B j:ℝ))=
      Crᵀ *ᵥ (fun i => (rowBounds picked i:ℝ)) := by
    ext i
    have hh := congrFun hy i
    change (∑ j, (∑ k, (C k i:ℝ)*(C k j:ℝ))*(facePoint rows B j:ℝ))=
      (∑ k, (C k i:ℝ)*(rowBounds picked k:ℝ))
    exact_mod_cast hh
  have he : (fun j => (facePoint rows B j:ℝ))=x := by
    apply mulVec_injective_of_isUnit hGr.isUnit
    rw [hye,←mulVec_mulVec,hxe]
  rwa [he]

def exactSolve {n : ℕ} (rows : List (Row n)) (B : ℕ) : Option (Fin n → ℚ) :=
  if boundedRationalDecide rows B then some (facePoint rows B) else none

theorem exactSolve_some {n : ℕ} (rows : List (Row n)) (B : ℕ) (x : Fin n → ℚ)
    (hx : exactSolve rows B=some x) :
    (∀ q∈rows,q.Holds x) ∧ (∀ j,|x j|≤(B:ℚ)) := by
  unfold exactSolve at hx
  split at hx
  next hd =>
    have he := Option.some.inj hx
    subst x
    have hh := facePoint_correct rows B ((boundedRationalDecide_correct rows B).mp hd)
    refine ⟨?_,?_⟩
    · intro q hq
      exact (Row.realHolds_cast _ _).mp (hh.1 q (List.mem_append_left _ hq))
    · intro j
      have hj : |(facePoint rows B j:ℝ)|≤(B:ℝ) := hh.2.2 j
      exact_mod_cast hj
  next => contradiction

theorem exactSolve_complete {n : ℕ} (rows : List (Row n)) (B : ℕ)
    (hfeas : ∃ x : Fin n → ℝ, (∀ q∈rows,q.RealHolds x) ∧ (∀ j,|x j|≤(B:ℝ))) :
    ∃ x, exactSolve rows B=some x := by
  exact ⟨facePoint rows B,ite_eq_left ((boundedRationalDecide_correct rows B).mpr hfeas)⟩

end MetricKMedianRecovery.Ellipsoid

namespace MetricKMedianRecovery.OpenabilityLinearization
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X]

theorem normalize_bounded (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hz : 0 ≤ z) (tau : D → ℝ) (y : F → D → D → ℝ)
    (h : Feasible loc F W v z lam eta i tau y) :
    ∃ tau' : D → ℝ, ∃ y' : F → D → D → ℝ,
      Feasible loc F W v z lam eta i tau' y' ∧
      (∀ j, 0 ≤ tau' j ∧ tau' j ≤ (1+v^2)*z) ∧
      (∀ f a j, 0 ≤ y' f a j ∧ y' f a j ≤ (1+v^2)*z) := by
  classical
  let tau' : D → ℝ := fun j => if activeAt loc (1-3*v) z W j then tau j else 0
  let y' : F → D → D → ℝ := fun f a j => if activeAt loc (1-3*v) z W a then
    max (dualTerm loc (1-3*v) z W f tau' a j) 0 else 0
  have hK : 0 ≤ (1+v^2)*z := mul_nonneg (by positivity) hz
  have hbid : admissibleBids loc (1-3*v) (1+v^2) v z W i tau' := by
    intro j hj
    simpa only [tau',ite_eq_left hj] using h.1 j hj
  have ht : ∀ j, 0 ≤ tau' j ∧ tau' j ≤ (1+v^2)*z := by
    intro j
    by_cases ha : activeAt loc (1-3*v) z W j
    · simp only [tau',ite_eq_left ha]
      exact ⟨hz.trans (h.1 j ha).1,(h.1 j ha).2.1⟩
    · simp only [tau',ite_eq_right ha]
      exact ⟨le_rfl,hK⟩
  have hp : linearPayment loc (1-3*v) v z W i tau' = linearPayment loc (1-3*v) v z W i tau := by
    unfold linearPayment
    apply Finset.sum_congr rfl
    intro j _
    by_cases ha : activeAt loc (1-3*v) z W j
    · simp only [ite_eq_left ha,tau']
    · simp only [ite_eq_right ha]
  have hd : ∀ f : F, ∀ a, activeAt loc (1-3*v) z W a → ∀ j,
      dualTerm loc (1-3*v) z W f tau' a j = dualTerm loc (1-3*v) z W f tau a j := by
    intro f a ha j
    unfold dualTerm
    by_cases hj : activeAt loc (1-3*v) z W j
    · simp only [ite_eq_left hj,tau']
    · simp only [ite_eq_right hj,tau']
      rw [ite_eq_left ha]
  refine ⟨tau',y',⟨hbid,?_,?_⟩,ht,?_⟩
  · rw [hp]
    exact h.2.1
  · intro f a ha
    refine ⟨?_,?_⟩
    · intro j
      simp only [y',ite_eq_left ha]
      exact ⟨le_max_right _ _,le_max_left _ _⟩
    · calc
        ∑ j, y' f a j ≤ ∑ j, y f a j := by
          apply Finset.sum_le_sum
          intro j _
          simp only [y',ite_eq_left ha,hd f a ha]
          exact max_le ((h.2.2 f a ha).1 j).2 ((h.2.2 f a ha).1 j).1
        _ ≤ lam := (h.2.2 f a ha).2
  · intro f a j
    by_cases ha : activeAt loc (1-3*v) z W a
    · simp only [y',ite_eq_left ha]
      refine ⟨le_max_right _ _,max_le ?_ hK⟩
      unfold dualTerm
      split_ifs with hj
      · exact (sub_le_self _ dist_nonneg).trans (ht j).2
      · have hh := (ht a).2
        have h1 : 0 ≤ dist (f:X) (loc j) := dist_nonneg
        have h2 : 0 ≤ dist (f:X) (loc a) := dist_nonneg
        linarith
    · simp only [y',ite_eq_right ha]
      exact ⟨le_rfl,hK⟩

theorem openable_iff_bounded (loc : D → X) (F W : Finset X) (v z lam eta : ℝ) (i : X)
    (hv : 0<v) (hv1 : v<1/6) (hz : 0≤z) :
    etaOpenable loc F W (1-3*v) (1+v^2) v z lam eta i ↔
      ∃ tau : D → ℝ, ∃ y : F → D → D → ℝ,
        Feasible loc F W v z lam eta i tau y ∧
        (∀ j, 0 ≤ tau j ∧ tau j ≤ (1+v^2)*z) ∧
        (∀ f a j, 0 ≤ y f a j ∧ y f a j ≤ (1+v^2)*z) := by
  rw [openable_iff_linear_feasible loc F W v z lam eta i hv hv1 hz]
  constructor
  · rintro ⟨tau,y,h⟩
    exact normalize_bounded loc F W v z lam eta i hz tau y h
  · rintro ⟨tau,y,h,_,_⟩
    exact ⟨tau,y,h⟩

end MetricKMedianRecovery.OpenabilityLinearization

end OAI
