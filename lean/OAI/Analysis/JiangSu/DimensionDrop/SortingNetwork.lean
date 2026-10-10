import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.ContinuousBlockSort

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

 def liftNetwork {n : ℕ} (cs : List (Fin n×Fin n)) : List (Fin (n+1)×Fin (n+1)) :=
   cs.map (fun c => (c.1.succ,c.2.succ))

lemma networkCoordinateMap_append {n : ℕ} (cs ds : List (Fin n×Fin n))
    (z : Fin n → Interval) :
    networkCoordinateMap (cs++ds) z=networkCoordinateMap ds (networkCoordinateMap cs z) := by
  induction cs generalizing z with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    exact ih _

lemma compareCoordinates_lift_zero {n : ℕ} (i j : Fin n) (z : Fin (n+1) → Interval) :
    compareCoordinates i.succ j.succ z 0=z 0 := by
  have hi : (0 : Fin (n+1)) ≠ i.succ := by
    intro h
    have hh := congrArg Fin.val h
    simp at hh
  have hj : (0 : Fin (n+1)) ≠ j.succ := by
    intro h
    have hh := congrArg Fin.val h
    simp at hh
  simp [compareCoordinates,hi,hj]

lemma compareCoordinates_lift_succ {n : ℕ} (i j : Fin n) (z : Fin (n+1) → Interval) :
    (fun k => compareCoordinates i.succ j.succ z k.succ)=
      compareCoordinates i j (fun k => z k.succ) := by
  funext k
  simp [compareCoordinates]

lemma networkCoordinateMap_lift_zero {n : ℕ} (cs : List (Fin n×Fin n))
    (z : Fin (n+1) → Interval) : networkCoordinateMap (liftNetwork cs) z 0=z 0 := by
  induction cs generalizing z with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    change networkCoordinateMap (liftNetwork cs) (compareCoordinateMap i.succ j.succ z) 0=z 0
    rw [ih]
    exact compareCoordinates_lift_zero i j z

lemma networkCoordinateMap_lift_succ {n : ℕ} (cs : List (Fin n×Fin n))
    (z : Fin (n+1) → Interval) :
    (fun k => networkCoordinateMap (liftNetwork cs) z k.succ)=
      networkCoordinateMap cs (fun k => z k.succ) := by
  induction cs generalizing z with
  | nil => rfl
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    change (fun k : Fin n => networkCoordinateMap (liftNetwork cs)
      (compareCoordinateMap i.succ j.succ z) k.succ)=_
    rw [ih]
    change networkCoordinateMap cs (fun k : Fin n => compareCoordinates i.succ j.succ z k.succ)=_
    rw [compareCoordinates_lift_succ]
    rfl

lemma networkCoordinateMap_lower {n : ℕ} (cs : List (Fin n×Fin n))
    (z : Fin n → Interval) (l : Interval) (hz : ∀ k,l≤z k) :
    ∀ k,l≤networkCoordinateMap cs z k := by
  induction cs generalizing z with
  | nil => exact hz
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    apply ih
    intro k
    change l≤compareCoordinates i j z k
    unfold compareCoordinates
    split_ifs
    · exact le_min (hz i) (hz j)
    · exact (hz i).trans (le_max_left _ _)
    · exact hz k

 def sortingNetwork : (n : ℕ) → List (Fin n×Fin n)
  | 0 => []
  | 1 => []
  | n+2 => let cs := liftNetwork (sortingNetwork (n+1))
      cs ++ [(0,1)] ++ cs

lemma monotone_of_head_tail {n : ℕ} (z : Fin (n+2) → Interval)
    (ht : Monotone (fun k : Fin (n+1) => z k.succ)) (hh : z 0≤z 1) : Monotone z := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  obtain rfl | ⟨i,rfl⟩ := i.eq_zero_or_eq_succ
  · simpa using hh
  · simpa using ht i.castSucc_le_succ

lemma sortingNetwork_sorts (n : ℕ) (z : Fin n → Interval) :
    Monotone (networkCoordinateMap (sortingNetwork n) z) := by
  induction n using Nat.twoStepInduction with
  | zero => exact fun i => Fin.elim0 i
  | one => intro i j _; have : i=j := Subsingleton.elim _ _; simp [this]
  | more n _ ih =>
    let cs := liftNetwork (sortingNetwork (n+1))
    let w := networkCoordinateMap cs z
    let v := compareCoordinates (0 : Fin (n+2)) 1 w
    let r := networkCoordinateMap cs v
    have ht : Monotone (fun k : Fin (n+1) => w k.succ) := by
      change Monotone (fun k : Fin (n+1) => networkCoordinateMap (liftNetwork (sortingNetwork (n+1))) z k.succ)
      rw [networkCoordinateMap_lift_succ]
      exact ih _
    have hv0 : v 0=min (w 0) (w 1) := by simp [v,compareCoordinates]
    have hv1 : v 1=max (w 0) (w 1) := by simp [v,compareCoordinates]
    have hv : ∀ k : Fin (n+1),v 0≤v k.succ := by
      intro k
      obtain rfl | ⟨k,rfl⟩ := k.eq_zero_or_eq_succ
      · rw [hv0]; exact (min_le_left _ _).trans (le_max_left _ _)
      · have hk : k.succ.succ≠(1 : Fin (n+2)) := by
          intro h; have hh := congrArg Fin.val h; simp at hh
        have hvk : v k.succ.succ=w k.succ.succ := by simp [v,compareCoordinates,hk]
        rw [hv0,hvk]
        exact (min_le_right _ _).trans (ht (Fin.zero_le k.succ))
    have hr0 : r 0=v 0 := networkCoordinateMap_lift_zero _ _
    have hrt : Monotone (fun k : Fin (n+1) => r k.succ) := by
      change Monotone (fun k : Fin (n+1) => networkCoordinateMap (liftNetwork (sortingNetwork (n+1))) v k.succ)
      rw [networkCoordinateMap_lift_succ]
      exact ih _
    have hr1 : v 0≤r 1 := by
      have h := networkCoordinateMap_lower (sortingNetwork (n+1)) (fun k => v k.succ) (v 0) hv 0
      rw [←networkCoordinateMap_lift_succ] at h
      exact h
    have hm : Monotone r := monotone_of_head_tail r hrt (hr0 ▸ hr1)
    simpa only [sortingNetwork,networkCoordinateMap_append,networkCoordinateMap,
      ContinuousMap.comp_apply,compareCoordinateMap,ContinuousMap.coe_mk,ContinuousMap.id_apply,cs,w,v,r] using hm

lemma networkCoordinateMap_permutation {n : ℕ} (cs : List (Fin n×Fin n))
    (z : Fin n → Interval) :
    ∃ e : Equiv.Perm (Fin n),networkCoordinateMap cs z=z ∘ e := by
  induction cs generalizing z with
  | nil => exact ⟨Equiv.refl _,rfl⟩
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    obtain ⟨e,he⟩ := ih (compareCoordinates i j z)
    change networkCoordinateMap cs (compareCoordinates i j z)=_ at he
    change ∃ e' : Equiv.Perm (Fin n),networkCoordinateMap cs (compareCoordinates i j z)=z ∘ e'
    rw [he,compareCoordinates_eq]
    split_ifs with hz
    · exact ⟨e,rfl⟩
    · exact ⟨e.trans (Equiv.swap i j).symm,rfl⟩

lemma sortingNetwork_eq_sort (n : ℕ) (z : Fin n → Interval) :
    networkCoordinateMap (sortingNetwork n) z=z ∘ Tuple.sort z := by
  obtain ⟨e,he⟩ := networkCoordinateMap_permutation (sortingNetwork n) z
  have hm := sortingNetwork_sorts n z
  rw [he] at hm ⊢
  exact Tuple.comp_sort_eq_comp_iff_monotone.mpr hm

theorem continuous_sort_unitary_control (p n : ℕ) {δ : ℝ} (hδ : 0<δ)
    (f : Interval → Mat p) {η : ℝ} (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η) (z : Fin n → Interval) :
    ‖unitaryConjugation (networkUnitary p n δ (sortingNetwork n) z)
        (blockDiagonalHom (f ∘ z))-
      blockDiagonalHom (f ∘ (z ∘ Tuple.sort z))‖≤
        3*((sortingNetwork n).length:ℝ)*η := by
  simpa only [sortingNetwork_eq_sort] using
    networkUnitary_control p n hδ (sortingNetwork n) f hη hf z

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

lemma interval_sorted_displacement {n : ℕ} (x y : Fin n → Interval) (δ : ℝ)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => (x i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (y i:ℝ)≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => (y i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (x i:ℝ)≤t+δ).card) (j : Fin n) :
    dist (x (Tuple.sort x j)) (y (Tuple.sort y j))≤δ := by
  have castsort (z : Fin n → Interval) :
      (fun i => (z i:ℝ)) ∘ Tuple.sort z=
        (fun i => (z i:ℝ)) ∘ Tuple.sort (fun i => (z i:ℝ)) := by
    apply Tuple.unique_monotone
    · exact fun i j hij => Tuple.monotone_sort z hij
    · exact Tuple.monotone_sort _
  have hx := FiniteSpectralMatching.sorted_le_of_cumulative
    (fun i => (x i:ℝ)) (fun i => (y i:ℝ)) δ hxy j
  have hy := FiniteSpectralMatching.sorted_le_of_cumulative
    (fun i => (y i:ℝ)) (fun i => (x i:ℝ)) δ hyx j
  have hxx := congrFun (castsort x) j
  have hyy := congrFun (castsort y) j
  simp only [Function.comp_apply] at hxx hyy
  rw [←hxx,←hyy] at hx hy
  change |(x (Tuple.sort x j):ℝ)-(y (Tuple.sort y j):ℝ)|≤δ
  exact abs_le.mpr ⟨by linarith,by linarith⟩

 def continuousMatchingUnitary (p n : ℕ) (δ : ℝ) :
    C((Fin n → Interval)×(Fin n → Interval),unitary (TensorMat p n)) :=
  ⟨fun z => (networkUnitary p n δ (sortingNetwork n) z.2)⁻¹ *
    networkUnitary p n δ (sortingNetwork n) z.1,by fun_prop⟩

theorem continuous_matching_control (p n : ℕ) {δ : ℝ} (hδ : 0<δ)
    (x y : Fin n → Interval)
    (hxy : ∀ t : ℝ,(Finset.univ.filter fun i => (x i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (y i:ℝ)≤t+δ).card)
    (hyx : ∀ t : ℝ,(Finset.univ.filter fun i => (y i:ℝ)≤t).card≤
      (Finset.univ.filter fun i => (x i:ℝ)≤t+δ).card)
    (f : Interval → Mat p) {η : ℝ} (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η) :
    ‖unitaryConjugation (continuousMatchingUnitary p n δ (x,y))
        (blockDiagonalHom (f ∘ x))-blockDiagonalHom (f ∘ y)‖≤
      (6*((sortingNetwork n).length:ℝ)+1)*η := by
  let ux := networkUnitary p n δ (sortingNetwork n) x
  let uy := networkUnitary p n δ (sortingNetwork n) y
  let X := blockDiagonalHom (f ∘ x)
  let Y := blockDiagonalHom (f ∘ y)
  let SX := blockDiagonalHom (f ∘ (x ∘ Tuple.sort x))
  let SY := blockDiagonalHom (f ∘ (y ∘ Tuple.sort y))
  have hx : ‖unitaryConjugation ux X-SX‖≤3*((sortingNetwork n).length:ℝ)*η :=
    continuous_sort_unitary_control p n hδ f hη hf x
  have hy : ‖unitaryConjugation uy Y-SY‖≤3*((sortingNetwork n).length:ℝ)*η :=
    continuous_sort_unitary_control p n hδ f hη hf y
  have hs : ‖SX-SY‖≤η := by
    change ‖blockDiagonalHom _-blockDiagonalHom _‖≤_
    rw [←map_sub]
    apply (NonUnitalStarAlgHom.norm_apply_le
      (blockDiagonalHom : (Fin n → Mat p) →⋆ₐ[ℂ] TensorMat p n) _).trans
    apply (pi_norm_le_iff_of_nonneg hη).mpr
    intro i
    exact hf _ _ (interval_sorted_displacement x y δ hxy hyx i)
  have hcancel : unitaryConjugation uy⁻¹ (unitaryConjugation uy Y)=Y := by
    rw [←unitaryConjugation_mul,inv_mul_cancel,unitaryConjugation_one]
  have hb : ‖unitaryConjugation ux X-unitaryConjugation uy Y‖≤
      (6*((sortingNetwork n).length:ℝ)+1)*η := by
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation ux X) SX SY
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (unitaryConjugation ux X) SY
      (unitaryConjugation uy Y)
    rw [norm_sub_rev SY] at h₂
    linarith
  change ‖unitaryConjugation (uy⁻¹*ux) X-Y‖≤_
  rw [unitaryConjugation_mul,←hcancel,←map_sub]
  exact (NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation uy⁻¹) _).trans hb

lemma continuous_finite_family_modulus (p k : ℕ) (f : Fin k → C(Interval,Mat p))
    {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ,0<δ ∧ ∀ j s t,dist s t≤δ → ‖f j s-f j t‖≤η := by
  let g : Interval → (Fin k → Mat p) := fun t j => f j t
  have hg : Continuous g := continuous_pi (fun j => (f j).continuous)
  have hu := CompactSpace.uniformContinuous_of_continuous hg
  obtain ⟨δ,hδ,hgδ⟩ := Metric.uniformContinuous_iff.mp hu η hη
  refine ⟨δ/2,by positivity,?_⟩
  intro j s t hst
  have ht : dist s t<δ := lt_of_le_of_lt hst (by linarith)
  have hb := (dist_le_pi_dist (g s) (g t) j).trans (hgδ ht).le
  simpa only [g,dist_eq_norm] using hb

theorem exists_continuous_matching_finite {X : Type*} [TopologicalSpace X]
    (p n k : ℕ) (f : Fin k → C(Interval,Mat p)) (ε : ℝ) (hε : 0<ε) :
    ∃ δ : ℝ,0<δ ∧ ∀ x y : C(X,Fin n → Interval),
      (∀ z t,(Finset.univ.filter fun i => (x z i:ℝ)≤t).card≤
        (Finset.univ.filter fun i => (y z i:ℝ)≤t+δ).card) →
      (∀ z t,(Finset.univ.filter fun i => (y z i:ℝ)≤t).card≤
        (Finset.univ.filter fun i => (x z i:ℝ)≤t+δ).card) →
      ∃ u : C(X,unitary (TensorMat p n)),∀ j z,
        ‖unitaryConjugation (u z) (blockDiagonalHom ((f j) ∘ (x z)))-
          blockDiagonalHom ((f j) ∘ (y z))‖<ε := by
  let c : ℝ := 6*((sortingNetwork n).length:ℝ)+1
  have hc : 0<c := by dsimp [c]; positivity
  let η : ℝ := ε/(2*c)
  have hη : 0<η := by dsimp [η]; positivity
  obtain ⟨δ,hδ,hf⟩ := continuous_finite_family_modulus p k f hη
  refine ⟨δ,hδ,?_⟩
  intro x y hxy hyx
  let xy : C(X,(Fin n → Interval)×(Fin n → Interval)) :=
    ⟨fun z => (x z,y z),x.continuous.prodMk y.continuous⟩
  refine ⟨(continuousMatchingUnitary p n δ).comp xy,?_⟩
  intro j z
  have hb := continuous_matching_control p n hδ (x z) (y z)
    (hxy z) (hyx z) (f j) hη.le (hf j)
  have he : c*η=ε/2 := by
    dsimp [η]
    field_simp
  have hlt : c*η<ε := he ▸ (by linarith)
  exact hb.trans_lt hlt

end JiangSuConstruction

end

end OAI
