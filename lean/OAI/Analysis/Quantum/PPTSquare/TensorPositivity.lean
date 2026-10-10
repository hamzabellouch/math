import OAI.Analysis.Quantum.PPTSquare.TensorModel

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype n] [Fintype m] in
lemma cp_sum {r : Type} [Fintype r] (F : r → Map n m) (hF : ∀ i, CP (F i)) :
    CP (∑ i, F i) := by
  classical
  induction (Finset.univ : Finset r) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro k _ X _
    exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact cp_add (hF a) ih

omit [Fintype m] in
lemma ad_single_apply [DecidableEq n] (W : Matrix m n ℂ) (i j : n) (a b : m) :
    ad W (Matrix.single i j 1) a b = W a i * star (W b j) := by
  have hm (r : n) : (W * Matrix.single i j (1 : ℂ)) a r =
      if r = j then W a i else 0 := by
    by_cases hr : r = j
    · subst r; simp
    · simp [hr, Matrix.mul_single_apply_of_ne]
  rw [ad_apply, Matrix.mul_apply]
  simp_rw [hm]
  simp [ite_mul, Matrix.conjTranspose_apply]

lemma cp_of_choi [DecidableEq n] {F : Map n m} (hF : (choi F).PosSemidef) : CP F := by
  classical
  let Q : Mat (n × m) := CFC.sqrt (choi F)
  let A (r : n × m) : Matrix m n ℂ := Matrix.of fun a i => Q (i,a) r
  have hQh : Q.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (choi F))).isHermitian
  have hQ : Q * Qᴴ = choi F := by
    rw [hQh.eq]
    exact CFC.sqrt_mul_sqrt_self _ hF.nonneg
  have hb (i j : n) : F (Matrix.single i j 1) = (∑ r, ad (A r)) (Matrix.single i j 1) := by
    ext a b
    have hh := congrArg (fun C : Mat (n × m) => C (i,a) (j,b)) hQ
    simpa only [LinearMap.sum_apply, Matrix.sum_apply, ad_single_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, choi, A, Matrix.of_apply] using hh.symm
  have he : F = ∑ r, ad (A r) := by
    apply LinearMap.ext
    intro X
    induction X using Matrix.induction_on' with
    | h_zero => simp
    | h_add X Y hX hY => simp only [map_add, hX, hY]
    | h_std_basis i j c =>
      have hc : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by simp
      rw [hc, map_smul, map_smul, hb]
  rw [he]
  exact cp_sum _ (fun r => cp_ad _)

omit [Fintype n] [Fintype m] in
lemma choi_simultaneous_transpose [DecidableEq n] (F : Map n m) :
    choi (transposeMap.comp (F.comp transposeMap)) = (choi F)ᵀ := by
  ext ⟨i,a⟩ ⟨j,b⟩
  simp [choi, LinearMap.comp_apply, transposeMap_apply, Matrix.transpose_single]

lemma cp_simultaneous_transpose [DecidableEq n] {F : Map n m} (hF : CP F) :
    CP (transposeMap.comp (F.comp transposeMap)) := by
  apply cp_of_choi
  rw [choi_simultaneous_transpose]
  exact (cp_choi hF).transpose

lemma ppt_input_transpose [DecidableEq n] {F : Map n m} (hF : PPT F) :
    PPT (F.comp transposeMap) := by
  refine ⟨?_, cp_simultaneous_transpose hF.1⟩
  exact cp_simultaneous_transpose hF.2

lemma hsAdjoint_single [DecidableEq n] [DecidableEq m] (F : Map n m) (a b : m) (i j : n) :
    hsAdjoint F (Matrix.single a b 1) i j = star (F (Matrix.single i j 1) a b) := by
  simp [hsAdjoint, Matrix.single_apply, ite_and, mul_ite]

lemma choi_hsAdjoint [DecidableEq n] [DecidableEq m] {F : Map n m} (hF : CP F) :
    choi (hsAdjoint F) = ((choi F)ᵀ).submatrix Prod.swap Prod.swap := by
  ext ⟨a,i⟩ ⟨b,j⟩
  change hsAdjoint F (Matrix.single a b 1) i j = _
  rw [hsAdjoint_single]
  exact (cp_choi hF).isHermitian.apply (j,b) (i,a)

lemma cp_hsAdjoint [DecidableEq n] [DecidableEq m] {F : Map n m} (hF : CP F) :
    CP (hsAdjoint F) := by
  apply cp_of_choi
  rw [choi_hsAdjoint hF]
  exact (cp_choi hF).transpose.submatrix _

lemma hsAdjoint_input_transpose [DecidableEq n] (F : Map n m) :
    hsAdjoint (F.comp transposeMap) = transposeMap.comp (hsAdjoint F) := by
  ext X i j
  simp [hsAdjoint, LinearMap.comp_apply, transposeMap_apply]

lemma ppt_hsAdjoint [DecidableEq n] [DecidableEq m] {F : Map n m} (hF : PPT F) :
    PPT (hsAdjoint F) := by
  refine ⟨cp_hsAdjoint hF.1, ?_⟩
  rw [← hsAdjoint_input_transpose]
  exact cp_hsAdjoint (ppt_input_transpose hF).1

end TensorCriterion

namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
variable {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]

lemma tensorMap_kronecker (F : Map n m) (G : Map p q) (A : Mat n) (B : Mat p) :
    tensorMap F G (A ⊗ₖ B) = F A ⊗ₖ G B := by
  ext ⟨a,c⟩ ⟨b,d⟩
  change F (Matrix.of fun i j => G (A i j • B) c d) a b = F A a b * G B c d
  simp only [map_smul, Matrix.smul_apply, smul_eq_mul]
  have he : (Matrix.of fun i j => A i j * G B c d) = G B c d • A := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he, map_smul]
  change G B c d * F A a b = F A a b * G B c d
  ring

lemma choi_tensorMap [DecidableEq n] [DecidableEq p] (F : Map n m) (G : Map p q) :
    choi (tensorMap F G) = (choi F ⊗ₖ choi G).submatrix
      (fun a => ((a.1.1,a.2.1),(a.1.2,a.2.2)))
      (fun a => ((a.1.1,a.2.1),(a.1.2,a.2.2))) := by
  ext ⟨⟨i,k⟩,⟨a,c⟩⟩ ⟨⟨j,l⟩,⟨b,d⟩⟩
  have he : Matrix.single (i,k) (j,l) (1 : ℂ) =
      Matrix.single i j 1 ⊗ₖ Matrix.single k l 1 := by
    rw [Matrix.single_kronecker_single, one_mul]
  change tensorMap F G (Matrix.single (i,k) (j,l) 1) (a,c) (b,d) = _
  rw [he, tensorMap_kronecker]
  rfl

lemma cp_tensorMap [DecidableEq n] [DecidableEq p] {F : Map n m} {G : Map p q}
    (hF : CP F) (hG : CP G) : CP (tensorMap F G) := by
  apply cp_of_choi
  rw [choi_tensorMap]
  exact ((cp_choi hF).kronecker (cp_choi hG)).submatrix _

lemma transpose_tensorMap (F : Map n m) (G : Map p q) :
    transposeMap.comp (tensorMap F G) =
      tensorMap (transposeMap.comp F) (transposeMap.comp G) := rfl

lemma ppt_tensorMap [DecidableEq n] [DecidableEq p] {F : Map n m} {G : Map p q}
    (hF : PPT F) (hG : PPT G) : PPT (tensorMap F G) := by
  refine ⟨cp_tensorMap hF.1 hG.1, ?_⟩
  rw [transpose_tensorMap]
  exact cp_tensorMap hF.2 hG.2

omit [Fintype n] [Fintype m] [Fintype p] in
lemma ppt_comp_cp {F : Map n m} {G : Map m p} (hG : PPT G) (hF : CP F) :
    PPT (G.comp F) := by
  refine ⟨cp_comp hG.1 hF, ?_⟩
  change CP ((transposeMap.comp G).comp F)
  exact cp_comp hG.2 hF

omit [Fintype n] [Fintype p] in
lemma transpose_ad_comp (W : Matrix p m ℂ) (F : Map n m) :
    transposeMap.comp ((ad W).comp F) = (ad (Wᴴ)ᵀ).comp (transposeMap.comp F) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, transposeMap_apply, ad_apply, Matrix.transpose_mul,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

omit [Fintype n] in
lemma ppt_ad_comp {F : Map n m} (hF : PPT F) (W : Matrix p m ℂ) : PPT ((ad W).comp F) := by
  refine ⟨cp_comp (cp_ad _) hF.1, ?_⟩
  rw [transpose_ad_comp]
  exact cp_comp (cp_ad _) hF.2

omit [Fintype n] [Fintype m] in
lemma ppt_output_transpose {F : Map n m} (hF : PPT F) : PPT (transposeMap.comp F) :=
  ⟨hF.2, hF.1⟩

lemma S_ppt {L : Map (Fin 4) (Fin 4)} (hL : PPT L) : PPT (S L) := by
  apply ppt_ad_comp
  exact ppt_comp_cp (ppt_tensorMap hL hL) (cp_ad U)

lemma R_ppt {L : Map (Fin 4) (Fin 4)} (hL : PPT L) : PPT (R L) := by
  exact ppt_ad_comp (ppt_output_transpose (S_ppt hL)) K

lemma Phi1_ppt {L : Map (Fin 4) (Fin 4)} (hL : PPT L) : PPT (Phi1 L) := by
  exact ppt_ad_comp (ppt_input_transpose (S_ppt hL)) E

lemma Phi2_ppt {L : Map (Fin 4) (Fin 4)} (hL : PPT L) : PPT (Phi2 L) := by
  exact ppt_comp_cp (ppt_hsAdjoint (R_ppt hL)) (cp_ad Eᴴ)

omit [Fintype n] [Fintype m] in
lemma cp_positive {F : Map n m} (hF : CP F) {X : Mat n} (hX : X.PosSemidef) :
    (F X).PosSemidef := by
  have h := hF Unit (X.submatrix Prod.snd Prod.snd) (hX.submatrix Prod.snd)
  exact h.submatrix (fun i => ((),i))

lemma trace_hsAdjoint [DecidableEq n] {F : Map n m} (hF : CP F) (X : Mat n) (Y : Mat m) :
    Matrix.trace (X * hsAdjoint F Y) = Matrix.trace (F X * Y) := by
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X X' hX hX' => simp [Matrix.add_mul, hX, hX']
  | h_std_basis i j c =>
    have hc : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by simp
    have hb : Matrix.trace (Matrix.single i j (1 : ℂ) * hsAdjoint F Y) =
        Matrix.trace (F (Matrix.single i j 1) * Y) := by
      rw [Matrix.trace_single_mul, one_smul]
      change (∑ a, ∑ b, star (F (Matrix.single j i 1) a b) * Y a b) = _
      have hentry (a b : m) : star (F (Matrix.single j i 1) a b) =
          F (Matrix.single i j 1) b a := (cp_choi hF).isHermitian.apply (i,b) (j,a)
      simp_rw [hentry]
      rw [Finset.sum_comm]
      rfl
    rw [hc, Matrix.smul_mul, Matrix.trace_smul, map_smul, Matrix.smul_mul,
      Matrix.trace_smul, hb]

end TensorCriterion

end

end OAI
