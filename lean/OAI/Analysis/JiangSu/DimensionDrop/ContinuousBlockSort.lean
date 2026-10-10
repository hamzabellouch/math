import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SoftSwap

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

lemma blockDiagonal_dist {p n : ℕ} (x y : Fin n → Mat p) {η : ℝ}
    (hη : 0≤η) (h : ∀ k,‖x k-y k‖≤η) :
    ‖blockDiagonalHom x-blockDiagonalHom y‖≤η := by
  rw [←map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le
    (blockDiagonalHom : (Fin n → Mat p) →⋆ₐ[ℂ] TensorMat p n) _).trans
  exact (pi_norm_le_iff_of_nonneg hη).mpr h

lemma block_swap_distance {p n : ℕ} (i j : Fin n) (f : Interval → Mat p)
    (z : Fin n → Interval) {η : ℝ} (hη : 0≤η) (hij : ‖f (z i)-f (z j)‖≤η) :
    ‖blockDiagonalHom (f ∘ z)-
      blockDiagonalHom (fun k => f (z ((Equiv.swap i j).symm k)))‖≤η := by
  apply blockDiagonal_dist _ _ hη
  intro k
  by_cases hki : k=i
  · subst k; simpa using hij
  by_cases hkj : k=j
  · subst k; simpa [norm_sub_rev] using hij
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj,hη]

 def blockSortUnitary (p n : ℕ) (i j : Fin n) (δ : ℝ) :
    C((Fin n → Interval),unitary (TensorMat p n)) :=
  ⟨fun z => blockSwapPath p n i j (softParameter δ (z i:ℝ) (z j:ℝ)), by
    apply (blockSwapPath p n i j).continuous.comp
    exact (softParameter_continuous δ).comp
      ((continuous_subtype_val.comp (continuous_apply i)).prodMk
        (continuous_subtype_val.comp (continuous_apply j)))⟩

lemma blockSortUnitary_left (p n : ℕ) (i j : Fin n) {δ : ℝ} (hδ : 0<δ)
    (z : Fin n → Interval) (h : (z i:ℝ)≤(z j:ℝ)-δ) :
    blockSortUnitary p n i j δ z=1 := by
  change blockSwapPath p n i j (softParameter δ (z i:ℝ) (z j:ℝ))=1
  rw [softParameter_zero hδ h]
  exact (blockSwapPath p n i j).source

lemma blockSortUnitary_right (p n : ℕ) (i j : Fin n) {δ : ℝ} (hδ : 0<δ)
    (z : Fin n → Interval) (h : (z j:ℝ)+δ≤(z i:ℝ)) :
    blockSortUnitary p n i j δ z=
      amplifiedUnitary p n (permutationUnitary (Equiv.swap i j)) := by
  change blockSwapPath p n i j (softParameter δ (z i:ℝ) (z j:ℝ))=_
  rw [softParameter_one hδ h]
  exact (blockSwapPath p n i j).target

theorem continuous_block_sort (p n : ℕ) (i j : Fin n) {δ : ℝ} (hδ : 0<δ)
    (f : Interval → Mat p) {η : ℝ} (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η) (z : Fin n → Interval) :
    ‖unitaryConjugation (blockSortUnitary p n i j δ z) (blockDiagonalHom (f ∘ z))-
      (if z i≤z j then blockDiagonalHom (f ∘ z) else
        blockDiagonalHom (fun k => f (z ((Equiv.swap i j).symm k))))‖≤3*η := by
  by_cases h0 : (z i:ℝ)≤(z j:ℝ)-δ
  · have hst : z i≤z j := by change (z i:ℝ)≤(z j:ℝ); linarith
    rw [blockSortUnitary_left p n i j hδ z h0,unitaryConjugation_one,ite_eq_left hst,
      sub_self,norm_zero]
    positivity
  by_cases h1 : (z j:ℝ)+δ≤(z i:ℝ)
  · have hst : ¬z i≤z j := by change ¬(z i:ℝ)≤(z j:ℝ); linarith
    rw [blockSortUnitary_right p n i j hδ z h1,amplified_permutation_conjugation,
      ite_eq_right hst]
    simp [hη]
  have hd : dist (z j) (z i)≤δ := by
    change |(z j:ℝ)-(z i:ℝ)|≤δ
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hc := blockSwapPath_control p n i j (f ∘ z)
    (softParameter δ (z i:ℝ) (z j:ℝ))
  have hc' : ‖unitaryConjugation (blockSortUnitary p n i j δ z)
      (blockDiagonalHom (f ∘ z))-blockDiagonalHom (f ∘ z)‖≤2*η := by
    exact hc.trans (mul_le_mul_of_nonneg_left (hf _ _ hd) (by norm_num))
  by_cases hs : z i≤z j
  · rw [ite_eq_left hs]; linarith
  · rw [ite_eq_right hs]
    have hb := block_swap_distance i j f z hη
      (hf _ _ (by simpa only [dist_comm] using hd))
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (unitaryConjugation (blockSortUnitary p n i j δ z) (blockDiagonalHom (f ∘ z)))
      (blockDiagonalHom (f ∘ z))
      (blockDiagonalHom (fun k => f (z ((Equiv.swap i j).symm k))))
    linarith

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

 def compareCoordinates {n : ℕ} (i j : Fin n) (z : Fin n → Interval) : Fin n → Interval :=
   fun k => if k=i then min (z i) (z j) else if k=j then max (z i) (z j) else z k

lemma compareCoordinates_eq {n : ℕ} (i j : Fin n) (z : Fin n → Interval) :
    compareCoordinates i j z=if z i≤z j then z else fun k => z ((Equiv.swap i j).symm k) := by
  funext k
  by_cases hz : z i≤z j
  · rw [ite_eq_left hz]
    unfold compareCoordinates
    rw [min_eq_left hz,max_eq_right hz]
    split_ifs with hi hj
    · subst k; rfl
    · subst k; rfl
    · rfl
  · rw [ite_eq_right hz]
    have hz' : z j≤z i := le_of_lt (lt_of_not_ge hz)
    have hij : i≠j := by intro h; subst j; exact hz le_rfl
    by_cases hi : k=i
    · subst k; simp [compareCoordinates,min_eq_right hz']
    by_cases hj : k=j
    · subst k; simp [compareCoordinates,max_eq_left hz',hij.symm]
    simp [compareCoordinates,hi,hj,Equiv.swap_apply_of_ne_of_ne hi hj]

 def compareCoordinateMap {n : ℕ} (i j : Fin n) :
    C((Fin n → Interval),(Fin n → Interval)) :=
  ⟨compareCoordinates i j, by
    apply continuous_pi
    intro k
    unfold compareCoordinates
    split_ifs <;> fun_prop⟩

lemma compareCoordinateMap_control (p n : ℕ) (i j : Fin n) {δ : ℝ} (hδ : 0<δ)
    (f : Interval → Mat p) {η : ℝ} (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η) (z : Fin n → Interval) :
    ‖unitaryConjugation (blockSortUnitary p n i j δ z) (blockDiagonalHom (f ∘ z))-
      blockDiagonalHom (f ∘ compareCoordinateMap i j z)‖≤3*η := by
  have h := continuous_block_sort p n i j hδ f hη hf z
  change ‖_-blockDiagonalHom (f ∘ compareCoordinates i j z)‖≤_
  rw [compareCoordinates_eq]
  split_ifs with hz <;> simpa [hz,Function.comp_def] using h

 def networkCoordinateMap {n : ℕ} : List (Fin n×Fin n) →
    C((Fin n → Interval),(Fin n → Interval))
  | [] => ContinuousMap.id _
  | (i,j)::cs => (networkCoordinateMap cs).comp (compareCoordinateMap i j)

 def networkUnitary (p n : ℕ) (δ : ℝ) : List (Fin n×Fin n) →
    C((Fin n → Interval),unitary (TensorMat p n))
  | [] => 1
  | (i,j)::cs => ((networkUnitary p n δ cs).comp (compareCoordinateMap i j)) *
      blockSortUnitary p n i j δ

lemma unitaryConjugation_mul {A : Type*} [CStarAlgebra A]
    (u v : unitary A) (a : A) :
    unitaryConjugation (u*v) a=unitaryConjugation u (unitaryConjugation v a) := by
  change ((u:A)*(v:A))*a*star ((u:A)*(v:A))=(u:A)*((v:A)*a*star (v:A))*star (u:A)
  simp only [star_mul,mul_assoc]

theorem networkUnitary_control (p n : ℕ) {δ : ℝ} (hδ : 0<δ)
    (cs : List (Fin n×Fin n)) (f : Interval → Mat p) {η : ℝ} (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η) (z : Fin n → Interval) :
    ‖unitaryConjugation (networkUnitary p n δ cs z) (blockDiagonalHom (f ∘ z))-
      blockDiagonalHom (f ∘ networkCoordinateMap cs z)‖≤3*(cs.length:ℝ)*η := by
  induction cs generalizing z with
  | nil => simp [networkUnitary,networkCoordinateMap,unitaryConjugation_one]
  | cons c cs ih =>
    rcases c with ⟨i,j⟩
    let w := networkUnitary p n δ cs (compareCoordinateMap i j z)
    let a := unitaryConjugation (blockSortUnitary p n i j δ z) (blockDiagonalHom (f ∘ z))
    let b := blockDiagonalHom (f ∘ compareCoordinateMap i j z)
    let c := blockDiagonalHom (f ∘ networkCoordinateMap cs (compareCoordinateMap i j z))
    have hprev : ‖unitaryConjugation w b-c‖≤3*(cs.length:ℝ)*η := ih _
    have hlocal : ‖a-b‖≤3*η := compareCoordinateMap_control p n i j hδ f hη hf z
    have hc : ‖unitaryConjugation w a-unitaryConjugation w b‖≤3*η := by
      rw [←map_sub]
      exact (NonUnitalStarAlgHom.norm_apply_le (unitaryConjugation w) (a-b)).trans hlocal
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (unitaryConjugation w a) (unitaryConjugation w b) c
    change ‖unitaryConjugation (w*blockSortUnitary p n i j δ z)
      (blockDiagonalHom (f ∘ z))-c‖≤_
    rw [unitaryConjugation_mul]
    change ‖unitaryConjugation w a-c‖≤_
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    linarith

end JiangSuConstruction

end

end OAI
