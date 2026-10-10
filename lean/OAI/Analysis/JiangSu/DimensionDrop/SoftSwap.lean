import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.PointwiseMatching

namespace OAI

noncomputable section


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

lemma amplified_permutation (p n : ℕ) (e : Equiv.Perm (Fin n)) :
    amplifiedUnitary p n (permutationUnitary e)=
      permutationUnitary (Equiv.prodCongr (Equiv.refl (Fin p)) e) := by
  apply Subtype.ext
  ext ⟨i,k⟩ ⟨j,l⟩
  change ((1 : Matrix (Fin p) (Fin p) ℂ) ⊗ₖ (e⁻¹).permMatrix ℂ) (i,k) (j,l)=
    (Equiv.Perm.permMatrix ℂ ((Equiv.prodCongr (Equiv.refl (Fin p)) e)⁻¹)) (i,k) (j,l)
  simp only [Matrix.kroneckerMap_apply,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,
    Equiv.Perm.inv_def,Equiv.toPEquiv_apply,Option.mem_def,Option.some.injEq,
    Equiv.prodCongr_symm,Equiv.refl_symm,Equiv.prodCongr_apply,Matrix.one_apply]
  split_ifs <;> simp_all

lemma amplified_permutation_conjugation (p n : ℕ) (e : Equiv.Perm (Fin n))
    (x : Fin n → Mat p) :
    unitaryConjugation (amplifiedUnitary p n (permutationUnitary e)) (blockDiagonalHom x)=
      blockDiagonalHom (fun i => x (e.symm i)) := by
  rw [amplified_permutation,permutationUnitary_conjugation,reindex_blockDiagonal]

 def softParameter (δ : ℝ) (s t : ℝ) : Interval :=
   ⟨min 1 (max 0 ((s-t+δ)/(2*δ))),le_min (by norm_num) (le_max_left _ _),min_le_left _ _⟩

lemma softParameter_continuous (δ : ℝ) :
    Continuous (fun z : ℝ×ℝ => softParameter δ z.1 z.2) := by
  apply Continuous.subtype_mk
  fun_prop

lemma softParameter_zero {δ s t : ℝ} (hδ : 0<δ) (h : s≤t-δ) :
    softParameter δ s t=leftEndpoint := by
  apply Subtype.ext
  change min 1 (max 0 ((s-t+δ)/(2*δ)))=0
  have hh : (s-t+δ)/(2*δ)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [max_eq_left hh,min_eq_right (by norm_num)]

lemma softParameter_one {δ s t : ℝ} (hδ : 0<δ) (h : t + δ ≤ s) :
    softParameter δ s t=rightEndpoint := by
  apply Subtype.ext
  change min 1 (max 0 ((s-t+δ)/(2*δ)))=1
  have hh : 1≤(s-t+δ)/(2*δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  exact min_eq_left (hh.trans (le_max_right _ _))

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

 def mergeBlocks {p n : ℕ} (i j : Fin n) (x : Fin n → Mat p) : Fin n → Mat p :=
   fun k => if k=j then x i else x k

lemma mergeBlocks_swap {p n : ℕ} (i j : Fin n) (x : Fin n → Mat p) (k : Fin n) :
    mergeBlocks i j x ((Equiv.swap i j).symm k)=mergeBlocks i j x k := by
  by_cases hij : i=j
  · subst j; simp
  by_cases hki : k=i
  · subst k; simp [mergeBlocks,hij]
  by_cases hkj : k=j
  · subst k; simp [mergeBlocks,hij]
  simp [Equiv.swap_apply_of_ne_of_ne hki hkj,mergeBlocks,hkj]

lemma mergeBlocks_dist {p n : ℕ} (i j : Fin n) (x : Fin n → Mat p) :
    ‖blockDiagonalHom x-blockDiagonalHom (mergeBlocks i j x)‖≤‖x j-x i‖ := by
  rw [←map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le
    (blockDiagonalHom : (Fin n → Mat p) →⋆ₐ[ℂ] TensorMat p n) _).trans
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  change ‖x k-mergeBlocks i j x k‖≤‖x j-x i‖
  by_cases hk : k=j
  · subst k; simp [mergeBlocks]
  · simp [mergeBlocks,hk]

lemma commute_of_unitaryConjugation_eq {A : Type*} [CStarAlgebra A]
    (u : unitary A) (b : A) (h : unitaryConjugation u b=b) : Commute (u:A) b := by
  change (u:A)*b=b*(u:A)
  change (u:A)*b*star (u:A)=b at h
  have hh := congrArg (fun x : A => x*(u:A)) h
  simpa only [mul_assoc,u.2.1,mul_one] using hh

lemma mergeBlocks_commute {p n : ℕ} (i j : Fin n) (x : Fin n → Mat p) :
    Commute (amplifiedUnitary p n (permutationUnitary (Equiv.swap i j)) : TensorMat p n)
      (blockDiagonalHom (mergeBlocks i j x)) := by
  apply commute_of_unitaryConjugation_eq
  rw [amplified_permutation_conjugation]
  congr 1
  funext k
  exact mergeBlocks_swap i j x k

 def blockSwapPath (p n : ℕ) (i j : Fin n) :
    Path 1 (amplifiedUnitary p n (permutationUnitary (Equiv.swap i j))) :=
  finiteSpectrumLogPath _ (matrix_finite_spectrum _)

theorem blockSwapPath_control (p n : ℕ) (i j : Fin n) (x : Fin n → Mat p)
    (t : unitInterval) :
    ‖unitaryConjugation (blockSwapPath p n i j t) (blockDiagonalHom x)-
      blockDiagonalHom x‖≤2*‖x j-x i‖ := by
  apply (finiteSpectrumLogPath_control _ _ _ _ (mergeBlocks_commute i j x) t).trans
  exact mul_le_mul_of_nonneg_left (mergeBlocks_dist i j x) (by norm_num)

end JiangSuConstruction


namespace JiangSuConstruction
open scoped CStarAlgebra ComplexOrder Kronecker

 def pairBlocks (p : ℕ) (a b : Mat p) : TensorMat p 2 :=
   blockDiagonalHom ![a,b]

lemma pairBlocks_dist (p : ℕ) (a b c d : Mat p) {η : ℝ}
    (hη : 0≤η) (hac : ‖a-c‖≤η) (hbd : ‖b-d‖≤η) :
    ‖pairBlocks p a b-pairBlocks p c d‖≤η := by
  change ‖blockDiagonalHom ![a,b]-blockDiagonalHom ![c,d]‖≤η
  rw [←map_sub]
  apply (NonUnitalStarAlgHom.norm_apply_le
    (blockDiagonalHom : (Fin 2 → Mat p) →⋆ₐ[ℂ] TensorMat p 2) _).trans
  apply (pi_norm_le_iff_of_nonneg hη).mpr
  intro i
  fin_cases i <;> simpa using (by assumption : ‖_‖≤η)

lemma pairBlocks_swap (p : ℕ) (a b : Mat p) :
    unitaryConjugation (amplifiedUnitary p 2 (permutationUnitary (Equiv.swap 0 1)))
      (pairBlocks p a b)=pairBlocks p b a := by
  unfold pairBlocks
  rw [amplified_permutation_conjugation]
  congr 1
  funext i
  fin_cases i <;> simp

lemma amplifiedUnitary_one (p n : ℕ) : amplifiedUnitary p n 1=1 := by
  apply Subtype.ext
  exact map_one (rightAmplification p n)

lemma unitaryConjugation_one {A : Type*} [CStarAlgebra A] (a : A) :
    unitaryConjugation (1 : unitary A) a=a := by
  change (1:A)*a*star (1:A)=a
  simp

abbrev PairSortPath (p : ℕ) :=
  Path (amplifiedUnitary p 2 (1 : unitary (Mat 2)))
    (amplifiedUnitary p 2 (permutationUnitary (Equiv.swap 0 1)))

 def pairSortUnitary {p : ℕ} (γ : PairSortPath p) (δ : ℝ) :
    C(Interval×Interval,unitary (TensorMat p 2)) :=
  ⟨fun z => γ (softParameter δ (z.1:ℝ) (z.2:ℝ)),
    γ.continuous.comp ((softParameter_continuous δ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))⟩

lemma pairSortUnitary_left {p : ℕ} (γ : PairSortPath p) {δ : ℝ} (hδ : 0<δ)
    (s t : Interval) (h : (s:ℝ)≤(t:ℝ)-δ) : pairSortUnitary γ δ (s,t)=1 := by
  change γ (softParameter δ (s:ℝ) (t:ℝ))=1
  rw [softParameter_zero hδ h]
  exact γ.source.trans (amplifiedUnitary_one p 2)

lemma pairSortUnitary_right {p : ℕ} (γ : PairSortPath p) {δ : ℝ} (hδ : 0<δ)
    (s t : Interval) (h : (t:ℝ)+δ≤(s:ℝ)) :
    pairSortUnitary γ δ (s,t)=
      amplifiedUnitary p 2 (permutationUnitary (Equiv.swap 0 1)) := by
  change γ (softParameter δ (s:ℝ) (t:ℝ))=_
  rw [softParameter_one hδ h]
  exact γ.target

lemma pair_sort_error (p : ℕ) (f : Interval → Mat p) (s t : Interval)
    (u : unitary (TensorMat p 2)) {δ η : ℝ} (hδ : 0<δ) (hη : 0≤η)
    (hf : ∀ s t,dist s t≤δ → ‖f s-f t‖≤η)
    (hu0 : (s:ℝ)≤(t:ℝ)-δ → u=1)
    (hu1 : (t:ℝ)+δ≤(s:ℝ) →
      u=amplifiedUnitary p 2 (permutationUnitary (Equiv.swap 0 1)))
    (hcontrol : dist s t≤δ →
      ‖unitaryConjugation u (pairBlocks p (f s) (f t))-pairBlocks p (f s) (f t)‖≤2*η) :
    ‖unitaryConjugation u (pairBlocks p (f s) (f t))-
      (if s≤t then pairBlocks p (f s) (f t) else pairBlocks p (f t) (f s))‖≤3*η := by
  by_cases h0 : (s:ℝ)≤(t:ℝ)-δ
  · have hst : s≤t := by change (s:ℝ)≤(t:ℝ); linarith
    rw [hu0 h0,unitaryConjugation_one,ite_eq_left hst,sub_self,norm_zero]
    positivity
  by_cases h1 : (t:ℝ)+δ≤(s:ℝ)
  · have hst : ¬s≤t := by change ¬(s:ℝ)≤(t:ℝ); linarith
    rw [hu1 h1,pairBlocks_swap,ite_eq_right hst,sub_self,norm_zero]
    positivity
  have hd : dist s t≤δ := by
    change |(s:ℝ)-(t:ℝ)|≤δ
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hc := hcontrol hd
  by_cases hs : s≤t
  · rw [ite_eq_left hs]
    linarith
  · rw [ite_eq_right hs]
    have hb := pairBlocks_dist p (f s) (f t) (f t) (f s) hη (hf s t hd)
      (hf t s (by simpa only [dist_comm] using hd))
    have ht := norm_sub_le_norm_sub_add_norm_sub
      (unitaryConjugation u (pairBlocks p (f s) (f t)))
      (pairBlocks p (f s) (f t)) (pairBlocks p (f t) (f s))
    linarith

lemma pairBlocks_self (p : ℕ) (a : Mat p) :
    pairBlocks p a a=leftAmplification p 2 a := by
  rw [←blockDiagonal_constant]
  unfold pairBlocks
  congr 1
  funext i
  fin_cases i <;> rfl

lemma pair_cluster_control (p : ℕ) (u : unitary (Mat 2)) (a b : Mat p)
    {η : ℝ} (hη : 0≤η) (hba : ‖b-a‖≤η) :
    ‖unitaryConjugation (amplifiedUnitary p 2 u) (pairBlocks p a b)-
      pairBlocks p a b‖≤2*η := by
  have hc := amplification_commute p 2 a (u : Mat 2)
  apply (conjugation_near_commuting (amplifiedUnitary p 2 u) _ _ hc).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  rw [←pairBlocks_self]
  exact pairBlocks_dist p a b a a hη (by simpa using hη) hba

lemma exists_pair_sort_path (p : ℕ) :
    ∃ γ : PairSortPath p,∀ (f : Interval → Mat p) (s t : Interval) (η : ℝ),
      0≤η → ‖f t-f s‖≤η → ∀ r,
      ‖unitaryConjugation (γ r) (pairBlocks p (f s) (f t))-
        pairBlocks p (f s) (f t)‖≤2*η := by
  let v := finiteMatrixUnitaryPath (1 : unitary (Mat 2))
    (permutationUnitary (Equiv.swap (0 : Fin 2) 1))
  let γ := v.map (amplifiedUnitary_continuous p 2)
  refine ⟨γ,?_⟩
  intro f s t η hη hts r
  exact pair_cluster_control p (v r) (f s) (f t) hη hts

theorem continuous_pair_sort (p : ℕ) {δ : ℝ} (hδ : 0<δ) :
    ∃ u : C(Interval×Interval,unitary (TensorMat p 2)),
      (∀ (s t : Interval),(s:ℝ)≤(t:ℝ)-δ → u (s,t)=1) ∧
      (∀ (s t : Interval),(t:ℝ)+δ≤(s:ℝ) →
        u (s,t)=amplifiedUnitary p 2 (permutationUnitary (Equiv.swap 0 1))) ∧
      ∀ (f : Interval → Mat p) (η : ℝ),0≤η →
        (∀ s t,dist s t≤δ → ‖f s-f t‖≤η) → ∀ s t,
        ‖unitaryConjugation (u (s,t)) (pairBlocks p (f s) (f t))-
          (if s≤t then pairBlocks p (f s) (f t) else pairBlocks p (f t) (f s))‖≤3*η := by
  obtain ⟨γ,hγ⟩ := exists_pair_sort_path p
  refine ⟨pairSortUnitary γ δ,pairSortUnitary_left γ hδ,pairSortUnitary_right γ hδ,?_⟩
  intro f η hη hf s t
  apply pair_sort_error p f s t _ hδ hη hf
    (pairSortUnitary_left γ hδ s t) (pairSortUnitary_right γ hδ s t)
  intro hd
  exact hγ f s t η hη (hf t s (by simpa only [dist_comm] using hd)) _

end JiangSuConstruction

end

end OAI
