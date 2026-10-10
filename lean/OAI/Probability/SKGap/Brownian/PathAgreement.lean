import Mathlib
import OAI.Probability.SKGap.Brownian.PathCutoff
import OAI.Probability.SKGap.Localization.AffineBilinear

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap ComplexOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pathDiagonal_square {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) :
    pathDiagonal a 1*pathDiagonal a 1=diagonal a := by
  simp only [pathDiagonal,sqrt_one,one_mul,diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_self_sqrt (ha i)

omit [Fintype ι] in
lemma pathShift_one (q : ℝ) : pathShift (ι := ι) 1 q=q • 1 := by
  ext i k
  by_cases h : i=k <;> simp [pathShift,h]

lemma symmetric_isUnit_of_lower [Nonempty ι] (S : Matrix ι ι ℝ) (hS : Sᵀ=S)
    {lo : ℝ} (hlo : 0 < lo) (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix S)) : IsUnit S := by
  apply (liftMatrix_isUnit_iff S).mp
  have hh : (liftMatrix S).IsHermitian := liftMatrix_hermitian S hS
  exact (hh.posDef_iff_eigenvalues_pos.mpr (fun i => hlo.trans_le
    (hl.trans (ComplexSpectral.eigenvalue_lower_bound hh i)))).isUnit

lemma pathK_agrees [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1))) :
    pathK f R hR j a 1 M=(1-diagonal a*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1))⁻¹ := by
  change realTruncatedK f R hR (pathDiagonal a 1)
    (pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M = _
  have he := realTruncatedK_eq_inverse f hlo hf hR (pathDiagonal a 1)
    (pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b)) M
    (diagonal_transpose _) (diagonal_transpose _) hM hMR hl hu
  simpa only [pathDiagonal_square ha,pathShift_one] using he

lemma inverse_resolvent_relations (D M : Matrix ι ι ℝ) (q : ℝ)
    (hS : IsUnit (1-D*(M-q • 1)*D)) :
    let K := (1-D*D*(M-q • 1))⁻¹
    let G := D*(1-D*(M-q • 1)*D)⁻¹*D
    K*(D*D)=G ∧ G*M=K*(1+q • (D*D))-1 ∧
      M*G*M=(M*K)*(1+q • (D*D))-M := by
  dsimp only
  have hunit := ResolventIdentity.inverse_one_sub_square_mul_unit D (M-q • 1) hS
  have hKG := ResolventIdentity.inverse_one_sub_square_mul_square D (M-q • 1) hS
  have hKK := Matrix.nonsing_inv_mul (1-D*D*(M-q • 1))
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)
  have hd : D*D*(q • (1:Matrix ι ι ℝ))=q • (D*D) := by simp
  have hGW : (D*(1-D*(M-q • 1)*D)⁻¹*D)*M=
      (1-D*D*(M-q • 1))⁻¹*(1+q • (D*D))-1 := by
    rw [← hKG]
    have hid : (1-D*D*(M-q • 1))⁻¹*(1+q • (D*D))-
        (1-D*D*(M-q • 1))⁻¹*(D*D)*M=
        (1-D*D*(M-q • 1))⁻¹*(1-D*D*(M-q • 1)) := by
      rw [mul_sub,hd]
      noncomm_ring
    rw [hKK] at hid
    exact sub_eq_iff_eq_add.mp hid |>.symm |> (fun h => eq_sub_of_add_eq (by simpa only [add_comm] using h))
  refine ⟨hKG,hGW,?_⟩
  rw [mul_assoc M _ M,hGW,mul_sub,mul_one]
  simp only [mul_assoc]

lemma path_bilinear_agreement [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {lo hi : ℝ} (hlo : 0 < lo)
    (hf : ∀ x ∈ Set.Icc lo hi, f x=(x:ℂ)⁻¹) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (M : Matrix ι ι ℝ)
    (hM : Mᵀ=M) (hMR : opNorm M ≤ R)
    (hl : lo ≤ ComplexSpectral.lowerRayleigh (liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1)))
    (hu : -hi ≤ ComplexSpectral.lowerRayleigh (-liftMatrix
      (1-pathDiagonal a 1*(M-pathShift 1 ((j/(Fintype.card ι:ℝ))*∑ b,a b))*pathDiagonal a 1))) :
    let q := (j/(Fintype.card ι:ℝ))*∑ b,a b
    let G := pathDiagonal a 1*(1-pathDiagonal a 1*(M-q • 1)*pathDiagonal a 1)⁻¹*pathDiagonal a 1
    affineRight (pathK f R hR j a 1) a 0 0 M=G ∧
    affineRight (pathK f R hR j a 1) (fun i => 1+q*a i) 1 0 M=G*M ∧
    affineRight (fun Q => realProject R hR Q*pathK f R hR j a 1 Q)
      (fun i => 1+q*a i) 0 1 M=M*G*M := by
  dsimp only
  have hl' := hl
  rw [pathShift_one] at hl'
  have hsym : (1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1)ᵀ=
      1-pathDiagonal a 1*(M-((j/(Fintype.card ι:ℝ))*∑ b,a b) • 1)*pathDiagonal a 1 := by
    simp only [transpose_sub,transpose_one,transpose_mul,transpose_smul,hM,
      show (pathDiagonal a 1)ᵀ=pathDiagonal a 1 from diagonal_transpose _,mul_assoc]
  have hS := symmetric_isUnit_of_lower _ hsym hlo hl'
  have hh := inverse_resolvent_relations (pathDiagonal a 1) M
    ((j/(Fintype.card ι:ℝ))*∑ b,a b) hS
  dsimp only at hh
  rw [pathDiagonal_square ha] at hh
  have hid : diagonal (fun i => 1+((j/(Fintype.card ι:ℝ))*∑ b,a b)*a i)=
      1+((j/(Fintype.card ι:ℝ))*∑ b,a b) • diagonal a := by
    ext i k
    by_cases h : i=k <;> simp [h]
  simp only [affineRight,pathK_agrees f hlo hf hR j ha M hM hMR hl hu,
    zero_smul,one_smul,sub_zero,
    realProject_eq_self hR M hM hMR,hid]
  have hz : (diagonal (0 : ι → ℝ))=(0 : Matrix ι ι ℝ) := by ext i k; simp
  have ho : (diagonal (1 : ι → ℝ))=(1 : Matrix ι ι ℝ) := by ext i k; simp [Matrix.diagonal_apply,Matrix.one_apply]
  simpa only [hz,ho,sub_zero] using And.intro hh.1 (And.intro hh.2.1.symm hh.2.2.symm)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathFeature (p : Bool) (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (M : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  if p then realProject R hR M*pathK f R hR j a 1 M else pathK f R hR j a 1 M

def pathFeatureLip (f : 𝓢(ℝ,ℂ)) (R j A : ℝ) : ℝ :=
  pathLip f R j A+pathBound f R j A+R*pathLip f R j A

lemma pathFeatureLip_nonneg (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) : 0 ≤ pathFeatureLip f R j A := by
  obtain ⟨hb,hl⟩ := path_constants_nonneg f hR hj hA
  unfold pathFeatureLip
  positivity

lemma pathFeature_lip [Nonempty ι] (p : Bool) (f : 𝓢(ℝ,ℂ)) {R j A : ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA : 0 ≤ A) {a : ι → ℝ}
    (ha : ∀ i, 0 ≤ a i) (haA : ∀ i, a i ≤ A) (M N : Matrix ι ι ℝ) :
    ‖pathFeature p f R hR j a M-pathFeature p f R hR j a N‖ ≤ pathFeatureLip f R j A*‖M-N‖ := by
  have hb := pathK_bounds f hR hj hA ha haA (z := 1) (by constructor <;> norm_num)
  obtain ⟨hB,hL⟩ := path_constants_nonneg f hR hj hA
  cases p
  · exact (hb.2 M N).trans (mul_le_mul_of_nonneg_right
      (show pathLip f R j A ≤ pathFeatureLip f R j A by unfold pathFeatureLip; nlinarith)
      (norm_nonneg _))
  · exact (realProjectedProduct_sub_norm hR _ hb.1 hb.2 M N).trans
      (mul_le_mul_of_nonneg_right
        (show pathBound f R j A+R*pathLip f R j A ≤ pathFeatureLip f R j A by unfold pathFeatureLip; linarith)
        (norm_nonneg _))

lemma pathFeature_sign (p : Bool) (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R)
    (j : ℝ) (a : ι → ℝ) (s : ι → ℝ) (hs : ∀ i, s i^2=1) (M : Matrix ι ι ℝ) :
    pathFeature p f R hR j a (signConjugate s M)=signConjugate s (pathFeature p f R hR j a M) := by
  cases p <;> simp only [pathFeature,Bool.false_eq_true,ite_false,ite_true,
    pathK_sign f hR j a 1 s hs,realProject_sign hR s hs,signConjugate_mul s hs]

theorem actual_path_affine_tail {j A D U W ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi c : ℝ) (N : ℕ),
      R=2*sqrt j+1+1 ∧ lo=(1-sqrt j*A)^2/4 ∧ hi=2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
      ∀ (p : Bool) (d e : Fin n → ℝ) (w : ℝ), (∀ i, |d i| ≤ D) → |w| ≤ W →
      ∀ (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ ≤ U → ‖v‖ ≤ U →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
          (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
            (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤ 2*exp (-c*(n:ℝ)) := by
  obtain ⟨f,R,hR,lo,hi,C,N₀,hReq,hloeq,hhieq,hlo,hf,_hfr,hC,hN₀,hEquiv⟩ :=
    actual_projected_path_equivalents hj hA hs
  let L := pathFeatureLip f R j A
  let denom := π^2*((L*D+W+1)*(U+1)^2)^2*j
  let c := (ε/2)^2/denom
  have hL : 0 ≤ L := pathFeatureLip_nonneg f hR hj.le hA.le
  have hdenom : 0 < denom := by dsimp [denom]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N₁,hN₁⟩ := exists_nat_gt (2*C*D*U^2/ε)
  refine ⟨f,R,hR,lo,hi,c,max N₀ N₁,hReq,hloeq,hhieq,hlo,hf,hc,
    lt_of_lt_of_le hN₀ (le_max_left _ _),?_⟩
  intro n hn a ha haA p d e w hd hw u v hu hv
  have hn₀ := (le_max_left N₀ N₁).trans hn
  have hnpos := hN₀.trans_le hn₀
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hnpos
  have hnr : (0:ℝ) < n := Nat.cast_pos.mpr hnpos
  have hn₁ : (N₁:ℝ) ≤ n := by exact_mod_cast (le_max_right N₀ N₁).trans hn
  have hbias : (C/(n:ℝ)*D)*U^2 ≤ ε/2 := by
    have h := ((div_lt_iff₀ hε).mp (hN₁.trans_le hn₁)).le
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
    have he : C/(n:ℝ)*D*U^2*2=(2*C*D*U^2)/(n:ℝ) := by ring
    rw [he,div_le_iff₀ hnr]
    nlinarith
  have hk (i : Fin n) : |(∫ g, pathFeature p f R hR j a (goeMatrix (j/(n:ℝ)) g) i i
      ∂Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1))-
      (if p then (j/(n:ℝ))*∑ b,a b else 1)| ≤ C/(n:ℝ) := by
    have heq := hEquiv n hn₀ a ha haA 1 (by constructor <;> norm_num) i
    cases p
    · simpa only [pathFeature,Bool.false_eq_true,ite_false,pathExpected,expectedCutoff,pathK,Fintype.card_fin] using heq.1
    · simpa only [pathFeature,ite_true,one_mul,Fintype.card_fin] using heq.2
  have hp := affineRight_concentration hj hL hU (div_nonneg hC.le hnr.le) hD
    (show 0 ≤ ε/2 by positivity) (pathFeature p f R hR j a) d e
    (fun _ => if p then (j/(n:ℝ))*∑ b,a b else 1) w hd
    (pathFeature_sign p f hR j a) (pathFeature_lip p f hR hj.le hA.le ha haA)
    (by simpa only [Fintype.card_fin] using hk) u v hu hv
  simp only [Fintype.card_fin] at hp
  have hmono : (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
        (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
          (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
      {g | (C/(n:ℝ)*D)*U^2+ε/2 ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
        (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
          (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} := by
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro g hg
    change ε ≤ _ at hg
    change (C/(n:ℝ)*D)*U^2+ε/2 ≤ _
    linarith
  apply hmono.trans (hp.trans ?_)
  apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr ?_) (by norm_num)
  have hden : π^2*((L*D+|w|+1)*(U+1)^2)^2*j ≤ denom := by
    dsimp [denom]
    gcongr
  have hdenpos : 0 < π^2*((L*D+|w|+1)*(U+1)^2)^2*j := by positivity
  have hrat := div_le_div_of_nonneg_left (show 0 ≤ (n:ℝ)*(ε/2)^2 by positivity) hdenpos hden
  dsimp only [c]
  calc
    _ = -((n:ℝ)*(ε/2)^2/(π^2*((L*D+|w|+1)*(U+1)^2)^2*j)) := by ring
    _ ≤ -((n:ℝ)*(ε/2)^2/denom) := neg_le_neg hrat
    _ = -((ε/2)^2/denom)*(n:ℝ) := by ring
end SKGap
end
end

end OAI
