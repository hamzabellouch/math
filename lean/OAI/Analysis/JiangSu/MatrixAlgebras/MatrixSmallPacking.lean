import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nuclearity.MatrixNuclearPacking

namespace OAI

noncomputable section
namespace DirectPacking
open CurrentMain Pureness DirectComparison
open scoped ComplexOrder

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [TraceFamily D]

lemma exists_small_matrix_packing
    (hA : IsNuclear A) (ι : A →⋆ₐ[ℂ] D)
    (hsupply : SpectralProjectionSupply (fun τ : RestrictedTracialState D => (τ : TracialState D)))
    (hT : Nonempty (TracialState D)) (hcoef : CoefficientSupply (D := D))
    (hinsert : InsertionSupply (D := D)) {m : ℕ} (hm : 0 < m)
    (hmat : ∀ e : D,IsStarProjection e → ∃ p : D,∃ V : ProjectionRow (Fin m) p,V.sample p=e)
    (K : Finset (unitary A)) {δ : ℝ} (hδ : 0<δ) :
    ∃ z : D, IsStarProjection z ∧ ∃ C : MatrixPackingCertificate z m,
      (∀ τ : RestrictedTracialState D,(τ.functional (1-z)).re<δ) ∧
      (∀ τ : RestrictedTracialState D,C.gap τ<δ) ∧
      (∀ P : CStarMatrix (Fin m) (Fin m) ℂ,IsStarProjection P →
        Matrix.trace (CStarMatrix.ofMatrixStarAlgEquiv.symm P)=1 →
        ∀ x∈K,∀ τ : RestrictedTracialState D,C.energy τ (ι (x:A)) P<δ) := by
  obtain ⟨η,n,hη,hη1,hE,hB⟩ := exists_packing_parameters
    (lt_min (Real.sqrt_pos.mpr hδ) (by positivity : 0<δ/2))
  obtain ⟨Q,C,hQ,_,hgap,henergy⟩ := matrix_packing_from_nuclearity hA.small ι hsupply hT hcoef hinsert hm hmat hη hη1 n K ∅
  have hEn : packingEnergy η n<δ := by
    have he := hE.trans_le (min_le_left _ _)
    have hs0 := Real.sqrt_nonneg (packingEnergy η n)
    have hs1 := Real.sqrt_nonneg δ
    have hs2 := Real.sq_sqrt (packingEnergy_nonneg hη.le n)
    have hs3 := Real.sq_sqrt hδ.le
    nlinarith
  have hBn : packingRemainder η n<δ := by
    have h := hB.trans_le (min_le_right _ _)
    have hb0 : 0≤packingBalance η n := by dsimp [packingBalance]; positivity
    linarith
  refine ⟨Q.total,Q.total_projection,C,?_,?_,?_⟩
  · intro τ; exact (hQ.remaining τ).trans_lt hBn
  · intro τ; exact (hgap τ).trans_lt hEn
  · intro P hP htr x hx τ; exact (henergy P hP htr x hx τ).trans_lt hEn

end DirectPacking

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type} {I : Type*} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Fintype I]

omit [PartialOrder D] [StarOrderedRing D] in
lemma orthogonal_sum_star_mul (a : I → D) (ha : Pairwise (fun i j => star (a i)*a j=0)) :
    star (∑ i,a i)*(∑ i,a i)=∑ i,star (a i)*a i := by
  classical
  rw [star_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_eq_single i (fun j _ hji => ha (Ne.symm hji)) (by simp)

lemma orthogonal_sum_twoNorm_sq (τ : TracialState D) (a : I → D)
    (ha : Pairwise (fun i j => star (a i)*a j=0)) :
    traceTwoNorm τ (∑ i,a i)^2=∑ i,traceTwoNorm τ (a i)^2 := by
  simp only [traceTwoNorm_sq,orthogonal_sum_star_mul a ha,map_sum,Complex.re_sum]

omit [PartialOrder D] [StarOrderedRing D] [Fintype I] in
lemma supported_orthogonal {t a : I → D} (ht : ∀ i,IsStarProjection (t i))
    (ho : Pairwise (fun i j => t i*t j=0)) (hl : ∀ i,t i*a i=a i) :
    Pairwise (fun i j => star (a i)*a j=0) := by
  intro i j hij
  have hs : star (a i)*t i=star (a i) := by
    simpa only [star_mul,(ht i).isSelfAdjoint.star_eq] using congrArg star (hl i)
  calc
    star (a i)*a j=(star (a i)*t i)*(t j*a j) := by rw [hs,hl]
    _=0 := by rw [mul_assoc,←mul_assoc (t i),ho hij,zero_mul,mul_zero]

lemma twoNorm_compress_le (τ : TracialState D) {t : D} (ht : IsStarProjection t) (a : D) :
    traceTwoNorm τ (t*a*t)≤traceTwoNorm τ a := by
  apply (traceTwoNorm_mul_right τ t (t*a)).trans
  apply (mul_le_mul_of_nonneg_right ht.norm_le (traceTwoNorm_nonneg τ _)).trans
  rw [one_mul]
  exact (traceTwoNorm_mul_left τ t a).trans
    ((mul_le_mul_of_nonneg_right ht.norm_le (traceTwoNorm_nonneg τ _)).trans_eq (one_mul _))

lemma supported_sum_norm_le_one {z : D} (hz : IsStarProjection z)
    (t a : I → D) (ht : ∀ i,IsStarProjection (t i))
    (ho : Pairwise (fun i j => t i*t j=0)) (hs : ∑ i,t i=z)
    (hl : ∀ i,t i*a i=a i) (hr : ∀ i,a i*t i=a i) (hn : ∀ i,‖a i‖≤1) :
    ‖∑ i,a i‖≤1 := by
  have hb (i : I) : star (a i)*a i≤t i := by
    have h1 : star (a i)*a i≤(1:D) :=
      (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mp (by
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg (a i),hn i])
    have hh := (ht i).isSelfAdjoint.conjugate_le_conjugate h1
    have hstar : t i*star (a i)=star (a i) := by
      simpa only [star_mul,(ht i).isSelfAdjoint.star_eq] using congrArg star (hr i)
    have hh' : t i*(star (a i)*a i)*t i≤t i := by
      simpa only [mul_one,(ht i).isIdempotentElem.eq] using hh
    calc
      star (a i)*a i=t i*(star (a i)*a i)*t i := by rw [←mul_assoc,hstar,mul_assoc,hr]
      _≤t i := hh'
  have hb' : star (∑ i,a i)*(∑ i,a i)≤1 := by
    rw [orthogonal_sum_star_mul _ (supported_orthogonal ht ho hl)]
    exact (Finset.sum_le_sum fun i _ => hb i).trans (hs ▸ hz.le_one)
  have hn' := (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _)).mpr hb'
  rw [CStarRing.norm_star_mul_self] at hn'
  nlinarith [norm_nonneg (∑ i,a i)]

namespace MatrixPackingCertificate
variable {z : D} {m : ℕ} (C : MatrixPackingCertificate z m)

def compress (M : CStarMatrix (Fin m) (Fin m) ℂ) : D :=
  ∑ i,C.piece i*C.hom i M*C.piece i

omit [PartialOrder D] [StarOrderedRing D] in
lemma compress_star (M : CStarMatrix (Fin m) (Fin m) ℂ) :
    C.compress (star M)=star (C.compress M) := by
  simp only [compress,star_sum,star_mul,←map_star,
    fun i => (C.projection i).isSelfAdjoint.star_eq,mul_assoc]

lemma compress_add (M N : CStarMatrix (Fin m) (Fin m) ℂ) :
    C.compress (M+N)=C.compress M+C.compress N := by
  simp only [compress,map_add,mul_add,add_mul,Finset.sum_add_distrib]

lemma compress_smul (c : ℂ) (M : CStarMatrix (Fin m) (Fin m) ℂ) :
    C.compress (c • M)=c • C.compress M := by
  simp only [compress,map_smul,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

lemma compress_norm_le_one (hz : IsStarProjection z) {M : CStarMatrix (Fin m) (Fin m) ℂ}
    (hM : ‖M‖≤1) : ‖C.compress M‖≤1 := by
  apply supported_sum_norm_le_one hz C.piece _ C.projection C.orthogonal C.sum_eq
  · intro i; simp only [←mul_assoc,(C.projection i).isIdempotentElem.eq]
  · intro i; simp only [mul_assoc,(C.projection i).isIdempotentElem.eq]
  · intro i
    apply (norm_mul_le _ _).trans
    have hn : ‖C.hom i M‖≤1 := NonUnitalStarAlgHom.norm_apply_le (C.hom i) M |>.trans hM
    have ht := (C.projection i).norm_le
    have hi : ‖C.piece i*C.hom i M‖≤1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg (C.piece i),norm_nonneg (C.hom i M)])
    nlinarith [norm_nonneg (C.piece i),norm_nonneg (C.piece i*C.hom i M)]

end MatrixPackingCertificate
end DirectPacking

namespace DirectPacking
open Pureness CurrentMain
open scoped ComplexOrder

variable {D : Type} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma twoNorm_mul_left_contraction (τ : TracialState D) {a : D} (ha : ‖a‖≤1) (b : D) :
    traceTwoNorm τ (a*b)≤traceTwoNorm τ b :=
  (traceTwoNorm_mul_left τ a b).trans ((mul_le_mul_of_nonneg_right ha (traceTwoNorm_nonneg τ b)).trans_eq (one_mul _))
lemma twoNorm_mul_right_contraction (τ : TracialState D) {a : D} (ha : ‖a‖≤1) (b : D) :
    traceTwoNorm τ (b*a)≤traceTwoNorm τ b :=
  (traceTwoNorm_mul_right τ a b).trans ((mul_le_mul_of_nonneg_right ha (traceTwoNorm_nonneg τ b)).trans_eq (one_mul _))
omit [PartialOrder D] [StarOrderedRing D] in
lemma norm_mul_contractions {a b : D} (ha : ‖a‖≤1) (hb : ‖b‖≤1) : ‖a*b‖≤1 :=
  (norm_mul_le _ _).trans (by nlinarith [norm_nonneg a,norm_nonneg b])

omit [PartialOrder D] [StarOrderedRing D] in
lemma orthogonal_sum_mul {I : Type*} [Fintype I] (t a b : I → D)
    (ho : Pairwise (fun i j => t i*t j=0))
    (hr : ∀ i,a i*t i=a i) (hl : ∀ i,t i*b i=b i) :
    (∑ i,a i)*(∑ i,b i)=∑ i,a i*b i := by
  classical
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    calc
      a i*b j=(a i*t i)*(t j*b j) := by rw [hr,hl]
      _=0 := by rw [mul_assoc,←mul_assoc (t i),ho (Ne.symm hji),zero_mul,mul_zero]
  · simp

namespace MatrixPackingCertificate
variable {z : D} {m : ℕ} (C : MatrixPackingCertificate z m)

omit [PartialOrder D] [StarOrderedRing D] in
lemma compress_left (M : CStarMatrix (Fin m) (Fin m) ℂ) (i : C.Index) :
    C.piece i*(C.piece i*C.hom i M*C.piece i)=C.piece i*C.hom i M*C.piece i := by
  simp only [←mul_assoc,(C.projection i).isIdempotentElem.eq]
omit [PartialOrder D] [StarOrderedRing D] in
lemma compress_right (M : CStarMatrix (Fin m) (Fin m) ℂ) (i : C.Index) :
    (C.piece i*C.hom i M*C.piece i)*C.piece i=C.piece i*C.hom i M*C.piece i := by
  simp only [mul_assoc,(C.projection i).isIdempotentElem.eq]

lemma compress_unit_gap (τ : TracialState D) :
    traceTwoNorm τ (C.compress 1-z)^2≤C.gap τ := by
  have he : C.compress 1-z=∑ i,C.piece i*(C.hom i 1-C.piece i)*C.piece i := by
    calc
      C.compress 1-z=C.compress 1-∑ i,C.piece i := congrArg (C.compress 1-·) C.sum_eq.symm
      _=_ := ?_
    rw [compress,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    noncomm_ring [(C.projection i).isIdempotentElem.eq]
  rw [he,orthogonal_sum_twoNorm_sq τ _ (supported_orthogonal C.projection C.orthogonal (by
    intro i; simp only [←mul_assoc,(C.projection i).isIdempotentElem.eq]))]
  apply Finset.sum_le_sum
  intro i _
  apply (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _)).mpr
  exact (twoNorm_compress_le τ (C.projection i) _).trans_eq (traceTwoNorm_sub_swap τ _ _)

lemma compress_mul_gap (τ : TracialState D) {M N : CStarMatrix (Fin m) (Fin m) ℂ}
    (hM : ‖M‖≤1) (hN : ‖N‖≤1) :
    traceTwoNorm τ (C.compress (M*N)-C.compress M*C.compress N)^2≤C.gap τ := by
  let d (i : C.Index) := C.piece i*C.hom i (M*N)*C.piece i-
    (C.piece i*C.hom i M*C.piece i)*(C.piece i*C.hom i N*C.piece i)
  have hd : C.compress (M*N)-C.compress M*C.compress N=∑ i,d i := by
    rw [compress,compress,compress,orthogonal_sum_mul C.piece _ _ C.orthogonal
      (C.compress_right M) (C.compress_left N),←Finset.sum_sub_distrib]
  have hs : ∀ i,C.piece i*d i=d i := by
    intro i
    dsimp [d]
    simp only [mul_sub,←mul_assoc,(C.projection i).isIdempotentElem.eq]
  have hn (i : C.Index) : traceTwoNorm τ (d i)≤traceTwoNorm τ (C.piece i-C.hom i 1) := by
    have hM' : ‖C.hom i M‖≤1 := (NonUnitalStarAlgHom.norm_apply_le (C.hom i) M).trans hM
    have hN' : ‖C.hom i N‖≤1 := (NonUnitalStarAlgHom.norm_apply_le (C.hom i) N).trans hN
    have hy : C.hom i 1*C.hom i N=C.hom i N := by rw [←map_mul,one_mul]
    have he : d i=(C.piece i*C.hom i M)*((1-C.piece i)*(C.hom i 1-C.piece i))*(C.hom i N*C.piece i) := by
      dsimp [d]
      rw [map_mul]
      noncomm_ring [(C.projection i).isIdempotentElem.eq,hy]
      simp only [←mul_assoc (C.piece i) (C.piece i),(C.projection i).isIdempotentElem.eq,
        ←mul_assoc (C.hom i 1) (C.hom i N),hy]
    rw [he]
    apply (twoNorm_mul_right_contraction τ (norm_mul_contractions hN' (C.projection i).norm_le) _).trans
    apply (twoNorm_mul_left_contraction τ (norm_mul_contractions (C.projection i).norm_le hM') _).trans
    exact (twoNorm_mul_left_contraction τ (C.projection i).one_sub.norm_le _).trans_eq (traceTwoNorm_sub_swap τ _ _)
  rw [hd,orthogonal_sum_twoNorm_sq τ _ (supported_orthogonal C.projection C.orthogonal hs)]
  exact Finset.sum_le_sum fun i _ => (sq_le_sq₀ (traceTwoNorm_nonneg τ _) (traceTwoNorm_nonneg τ _)).mpr (hn i)

end MatrixPackingCertificate
end DirectPacking

end

end OAI
