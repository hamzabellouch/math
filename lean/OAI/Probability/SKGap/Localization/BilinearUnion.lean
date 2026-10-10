import Mathlib
import OAI.Probability.SKGap.Localization.Bilinear2

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

def bilinearPathGood {n : ℕ} (j A : ℝ) (a : Fin n → ℝ)
    (g : MatrixCoordinates (Fin n) → ℝ) : Prop :=
  ∀ z ∈ Icc (0:ℝ) 1, g ∈ truncationGoodSet (j/(n:ℝ))
    (2*sqrt j+1+1) ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
    (pathDiagonal a z) (pathShift z ((j/(n:ℝ))*∑ b,a b))

theorem bilinear_deterministic_equivalents {j A U ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
    (hU : 0 ≤ U) (hε : 0 < ε) (m : ℕ) :
    ∃ (c : ℝ) (N : ℕ), 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
      ∀ v : Fin m → EuclideanSpace ℝ (Fin n), (∀ r, ‖v r‖ ≤ U) →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
          ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|} ≤
        (3+6*(m:ℝ)^2)*exp (-c*(n:ℝ)) := by
  have hD : 0 ≤ A+1+j*A^2 := by positivity
  obtain ⟨f,R,hR,lo,hi,c₀,N₀,hReq,hloeq,hhieq,hlo,hf,hc₀,hN₀,htail⟩ :=
    actual_path_affine_tail hj hA hs hD hU (by norm_num : (0:ℝ)≤1) hε
  obtain ⟨N₁,hN₁⟩ := eventually_atTop.mp (path_size_eventually hs)
  refine ⟨min c₀ (pathRate j A),max N₀ N₁,lt_min hc₀ (pathRate_pos hj hA hs),
    hN₀.trans_le (le_max_left _ _),?_⟩
  intro n hn a ha haA v hv
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hn₁ := (le_max_right N₀ N₁).trans hn
  have hnpos := hN₀.trans_le hn₀
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  let μ := Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)
  let B : Set (MatrixCoordinates (Fin n) → ℝ) := {g | ¬bilinearPathGood j A a g}
  let T (p : Fin m × Fin m × Fin 3) : Set (MatrixCoordinates (Fin n) → ℝ) :=
    {g | ε ≤ |matrixBilinear (affineRight (pathFeature (decide (p.2.2=2)) f R hR j a)
      (bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a) (bilinearDataE p.2.2) (bilinearDataW p.2.2)
      (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
        (if p.2.2=2 then (j/(n:ℝ))*∑ b,a b else 1)*
          bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a i-bilinearDataE p.2.2 i)) (v p.1) (v p.2.1)|}
  have hb : μ.real B ≤ 3*exp (-pathRate j A*(n:ℝ)) := by
    have hh := path_all_good_exponential hj hA ha haA hs (by simpa only [Fintype.card_fin] using hN₁ n hn₁)
    simpa only [B,μ,bilinearPathGood,not_forall,exists_prop,Fintype.card_fin] using hh
  have ht (p : Fin m × Fin m × Fin 3) : μ.real (T p) ≤ 2*exp (-c₀*(n:ℝ)) := by
    have hh := htail n hn₀ a ha haA (decide (p.2.2=2))
      (bilinearDataD p.2.2 ((j/(n:ℝ))*∑ b,a b) a) (bilinearDataE p.2.2) (bilinearDataW p.2.2)
      (fun i => by simpa only [Fintype.card_fin] using bilinearData_bound hj.le hA.le ha haA p.2.2 i)
      (bilinearDataW_bound p.2.2) (v p.1) (v p.2.1) (hv p.1) (hv p.2.1)
    simpa only [T,μ,decide_eq_true_eq] using hh
  have hsub : {g | ¬bilinearPathGood j A a g ∨ ∃ r s k,
        ε < |matrixBilinear (bilinearError k j a (goeMatrix (j/(n:ℝ)) g)) (v r) (v s)|} ⊆ B ∪ ⋃ p,T p := by
    intro g hg
    by_cases hgood : bilinearPathGood j A a g
    · rcases hg with hb | ⟨r,s,k,hk⟩
      · exact (hb hgood).elim
      · apply Or.inr
        refine mem_iUnion.mpr ⟨(r,s,k),?_⟩
        have hg₁ := hgood 1 (by constructor <;> norm_num)
        change opNorm _ < _ ∧ _ < _ ∧ _ < _ at hg₁
        have he := bilinearError_agrees f hlo hf hR j ha
          (goeMatrix (j/(n:ℝ)) g) (goeMatrix_transpose _ g)
          (by simpa only [hReq] using hg₁.1.le)
          (by simpa only [hloeq,Fintype.card_fin] using hg₁.2.1.le)
          (by simpa only [hhieq,Fintype.card_fin] using hg₁.2.2.le) k
        dsimp only at he
        simp only [Fintype.card_fin] at he
        change ε ≤ |matrixBilinear _ (v r) (v s)|
        rw [← he]
        exact hk.le
    · exact Or.inl hgood
  have hbound := (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le B (⋃ p,T p)).trans (add_le_add hb
      ((measureReal_iUnion_fintype_le T).trans (Finset.sum_le_sum (fun p _ => ht p)))))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat] at hbound
  have hnr : (0:ℝ) ≤ n := Nat.cast_nonneg _
  have he₀ : exp (-c₀*(n:ℝ)) ≤ exp (-min c₀ (pathRate j A)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) hnr)
  have he₁ : exp (-pathRate j A*(n:ℝ)) ≤ exp (-min c₀ (pathRate j A)*(n:ℝ)) :=
    exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) hnr)
  apply hbound.trans
  have hh₀ := mul_le_mul_of_nonneg_left he₀ (show 0 ≤ (m:ℝ)*((m:ℝ)*3)*2 by positivity)
  linarith
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
variable {ι κ : Type*} [Fintype ι]

def matrixPair (G : Matrix ι ι ℝ) (x y : ι → ℝ) := x ⬝ᵥ (G*ᵥy)

lemma matrixPair_sub (G H : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair (G-H) x y=matrixPair G x y-matrixPair H x y := by
  simp [matrixPair,Matrix.sub_mulVec,dotProduct_sub]
lemma matrixPair_smul (a : ℝ) (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair (a • G) x y=a*matrixPair G x y := by
  simp [matrixPair,Matrix.smul_mulVec,smul_eq_mul]
lemma matrixPair_sub_right (G : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    matrixPair G x (y-z)=matrixPair G x y-matrixPair G x z := by
  simp [matrixPair,Matrix.mulVec_sub,dotProduct_sub]
lemma matrixPair_sub_left (G : Matrix ι ι ℝ) (x y z : ι → ℝ) :
    matrixPair G (x-y) z=matrixPair G x z-matrixPair G y z := by
  simp [matrixPair,sub_dotProduct]
lemma matrixPair_smul_right (G : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    matrixPair G x (a • y)=a*matrixPair G x y := by
  simp [matrixPair,Matrix.mulVec_smul,smul_eq_mul]
lemma matrixPair_smul_left (G : Matrix ι ι ℝ) (a : ℝ) (x y : ι → ℝ) :
    matrixPair G (a • x) y=a*matrixPair G x y := by
  simp [matrixPair,smul_eq_mul]
lemma matrixPair_mul_right (G W : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair G x (W*ᵥy)=matrixPair (G*W) x y := by
  simp [matrixPair,Matrix.mulVec_mulVec]
lemma matrixPair_symm {G : Matrix ι ι ℝ} (hG : Gᵀ=G) (x y : ι → ℝ) :
    matrixPair G x y=matrixPair G y x := by
  simpa only [hG,matrixPair] using Matrix.dotProduct_transpose_mulVec G x y
lemma matrixPair_mul_left {W : Matrix ι ι ℝ} (hW : Wᵀ=W)
    (G : Matrix ι ι ℝ) (x y : ι → ℝ) :
    matrixPair G (W*ᵥx) y=matrixPair (W*G) x y := by
  calc
    _ = (G*ᵥy) ⬝ᵥ (W*ᵥx) := dotProduct_comm _ _
    _ = x ⬝ᵥ (W*ᵥ(G*ᵥy)) := by
      simpa only [hW] using Matrix.dotProduct_transpose_mulVec W (G*ᵥy) x
    _ = _ := by rw [matrixPair,Matrix.mulVec_mulVec]

def residualGramVector (B : ℝ) (W : Matrix ι ι ℝ) (u : ι → ℝ) :=
  (Real.sqrt B)⁻¹ • (W*ᵥu-B • u)

lemma centered_gram_mixed (G W A : Matrix ι ι ℝ) (B : ℝ) (x u : ι → ℝ) :
    matrixPair G x (residualGramVector B W u)=
      (Real.sqrt B)⁻¹*(matrixPair (G*W-B • A) x u-B*matrixPair (G-A) x u) := by
  simp only [residualGramVector,matrixPair_smul_right,matrixPair_sub_right,
    matrixPair_mul_right,matrixPair_sub,matrixPair_smul]
  ring

lemma centered_gram_diagonal [DecidableEq ι] {G W : Matrix ι ι ℝ} (hG : Gᵀ=G) (hW : Wᵀ=W)
    (A : Matrix ι ι ℝ) {B : ℝ} (hB : 0 < B) (u : ι → ℝ) (hu : u⬝ᵥu=1) :
    matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1=
      B⁻¹*(matrixPair (W*G*W-B • 1-B^2 • A) u u-
        2*B*matrixPair (G*W-B • A) u u+B^2*matrixPair (G-A) u u) := by
  have hs : (Real.sqrt B)⁻¹*(Real.sqrt B)⁻¹=B⁻¹ := by
    rw [← mul_inv,← pow_two,Real.sq_sqrt hB.le]
  have hx : matrixPair G (W*ᵥu) u=matrixPair (G*W) u u := by
    rw [matrixPair_symm hG,matrixPair_mul_right]
  simp only [residualGramVector,matrixPair_smul_left,matrixPair_smul_right,
    matrixPair_sub_left,matrixPair_sub_right,matrixPair_mul_right,
    matrixPair_sub,matrixPair_smul]
  rw [matrixPair_mul_left hW,hx,← Matrix.mul_assoc]
  have hi : matrixPair (1 : Matrix ι ι ℝ) u u=1 := by simp [matrixPair,hu]
  rw [hi]
  calc
    _ = ((Real.sqrt B)⁻¹*(Real.sqrt B)⁻¹)*
        (matrixPair (W*G*W) u u-2*B*matrixPair (G*W) u u+B^2*matrixPair G u u)-1 := by ring
    _ = _ := by rw [hs]; field_simp; ring

lemma centered_gram_mixed_bound (G W A : Matrix ι ι ℝ) {B ε : ℝ}
    (hB : 0 < B) (x u : ι → ℝ)
    (h0 : |matrixPair (G-A) x u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) x u| ≤ ε) :
    |matrixPair G x (residualGramVector B W u)| ≤ (Real.sqrt B)⁻¹*(1+B)*ε := by
  rw [centered_gram_mixed G W A B x u,abs_mul,abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hB))]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  calc
    _ ≤ |matrixPair (G*W-B • A) x u|+|B*matrixPair (G-A) x u| := abs_sub _ _
    _ ≤ ε+B*ε := by rw [abs_mul,abs_of_pos hB]; exact add_le_add h1 (mul_le_mul_of_nonneg_left h0 hB.le)
    _ = _ := by ring

lemma centered_gram_diagonal_bound [DecidableEq ι] {G W : Matrix ι ι ℝ} (hG : Gᵀ=G) (hW : Wᵀ=W)
    (A : Matrix ι ι ℝ) {B ε : ℝ} (hB : 0 < B) (u : ι → ℝ) (hu : u⬝ᵥu=1)
    (h0 : |matrixPair (G-A) u u| ≤ ε)
    (h1 : |matrixPair (G*W-B • A) u u| ≤ ε)
    (h2 : |matrixPair (W*G*W-B • 1-B^2 • A) u u| ≤ ε) :
    |matrixPair G (residualGramVector B W u) (residualGramVector B W u)-1| ≤
      B⁻¹*(1+2*B+B^2)*ε := by
  rw [centered_gram_diagonal hG hW A hB u hu,abs_mul,abs_of_pos (inv_pos.mpr hB)]
  conv_rhs => rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hB.le)
  calc
    _ ≤ |matrixPair (W*G*W-B • 1-B^2 • A) u u-2*B*matrixPair (G*W-B • A) u u|+
        |B^2*matrixPair (G-A) u u| := abs_add_le _ _
    _ ≤ (ε+2*B*ε)+B^2*ε := by
      apply add_le_add
      · apply (abs_sub _ _).trans
        rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2*B)]
        exact add_le_add h2 (mul_le_mul_of_nonneg_left h1 (by positivity))
      · rw [abs_mul,abs_of_nonneg (sq_nonneg B)]
        exact mul_le_mul_of_nonneg_left h0 (sq_nonneg B)
    _ = _ := by ring
end SKGap
end
end

end OAI
