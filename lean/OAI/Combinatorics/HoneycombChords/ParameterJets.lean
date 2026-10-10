import OAI.Combinatorics.HoneycombChords.TransformSurjectivity
import OAI.Combinatorics.HoneycombChords.SechResidual

namespace OAI

/-! Parameter jet spans and confluent hyperbolic secant coefficients.

The development follows OpenAI, *Uniform marked-polygon estimates and sharp finite bridge moments*
(2026), Sections 6 and 7. -/

section


namespace CriticalHoneycomb.FiniteFunctional
open Finset Filter Topology
open StripAsymptotic Analytic

lemma C_eq_beta_square (t x : ℝ) : C t x = (cosineKernelJet 0 0 (t^2) x : ℂ) := by
  rw [cosineKernelJet_eq_C (sq_nonneg t),Real.sqrt_sq_eq_abs]
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht)]
    unfold C
    split_ifs <;> simp only [neg_mul,Real.cosh_neg,Real.cos_neg]

noncomputable def composeCoeff : ℕ → ℕ → ℝ → ℝ
  | 0,0 => 1
  | 0,_+1 => 0
  | n+1,0 => deriv (composeCoeff n 0)
  | n+1,k+1 => fun t => deriv (composeCoeff n (k+1)) t +
      2*t*(k+1:ℕ)*composeCoeff n k t

lemma composeCoeff_smooth (n k : ℕ) : ContDiff ℝ ⊤ (composeCoeff n k) := by
  induction n generalizing k with
  | zero => cases k <;> exact contDiff_const
  | succ n ih =>
    cases k with
    | zero => exact (ih 0).deriv'
    | succ k =>
      exact (ih (k+1)).deriv'.add
        (((contDiff_const.mul contDiff_id).mul contDiff_const).mul (ih k))

lemma composeCoeff_zero {n k : ℕ} (h : n < k) : composeCoeff n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> first | omega | rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k =>
      ext t
      simp [composeCoeff,ih (show n<k+1 by omega),ih (show n<k by omega)]

lemma composeCoeff_diagonal {t : ℝ} (ht : t ≠ 0) (n : ℕ) :
    composeCoeff n n t ≠ 0 := by
  induction n with
  | zero => exact one_ne_zero
  | succ n ih =>
    change deriv (composeCoeff n (n+1)) t + 2*t*(n+1:ℕ)*composeCoeff n n t ≠ 0
    rw [composeCoeff_zero (by omega)]
    rw [show deriv (0:ℝ→ℝ) t = 0 from deriv_const t 0,zero_add]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ht)
      (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) ih

lemma beta_square_hasDerivAt (k : ℕ) (t x : ℝ) :
    HasDerivAt (fun s => (cosineKernelJet k 0 (s^2) x : ℂ))
      ((2*t*(k+1:ℕ)*cosineKernelJet (k+1) 0 (t^2) x : ℝ) : ℂ) t := by
  have h := (cosineKernelJet_hasDerivAt_left k 0 (t^2) x).comp t
    ((hasDerivAt_id t).pow 2)
  convert h.ofReal_comp using 1 <;> try rfl
  push_cast
  simp only [id_eq,pow_one]
  ring

lemma C_parameter_jet_expansion (n : ℕ) (t x : ℝ) :
    iteratedDeriv n (fun s => C s x) t =
      ∑ k ∈ range (n+1), (composeCoeff n k t : ℂ) *
        (cosineKernelJet k 0 (t^2) x : ℂ) := by
  induction n generalizing t with
  | zero => simp [composeCoeff,C_eq_beta_square]
  | succ n ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv n (fun s=>C s x) =
      (fun t=>∑ k ∈ range (n+1),(composeCoeff n k t:ℂ)*(cosineKernelJet k 0 (t^2) x:ℂ))
      from funext ih]
    have hd (k : ℕ) :=
      (((composeCoeff_smooth n k).differentiable (by simp)).differentiableAt.hasDerivAt.ofReal_comp).mul
        (beta_square_hasDerivAt k t x)
    have hds := HasDerivAt.fun_sum (fun k (_ : k ∈ range (n+1)) => hd k)
    simp only [Pi.mul_apply] at hds
    rw [hds.deriv]
    let A := fun k => ((deriv (composeCoeff n k) t : ℝ) : ℂ) * (cosineKernelJet k 0 (t^2) x : ℂ)
    have hz : A (n+1) = 0 := by simp [A,composeCoeff_zero (show n<n+1 by omega)]
    have hshift : (∑ k ∈ range (n+1), A k) = A 0 + ∑ k ∈ range (n+1), A (k+1) := by
      have h1 := sum_range_succ A (n+1)
      have h2 := sum_range_succ' A (n+1)
      rw [hz,add_zero] at h1
      rw [h1] at h2
      exact h2.trans (add_comm _ _)
    simp only [Complex.ofReal_mul]
    rw [sum_add_distrib]
    change (∑ k ∈ range (n+1),A k) + _ = _
    rw [hshift,add_assoc,← sum_add_distrib]
    conv_rhs => rw [sum_range_succ']
    rw [add_comm (∑ _ ∈ _, _)]
    congr 1
    apply sum_congr rfl
    intro k hk
    simp only [A,composeCoeff,Complex.ofReal_add,Complex.ofReal_mul]
    ring

lemma parameter_jet_span (t : ℝ) (ht : t ≠ 0) (N : ℕ) :
    Submodule.span ℂ ((fun k : ℕ => fun x : ℝ => (cosineKernelJet k 0 (t^2) x : ℂ)) '' Set.Iio N) =
      Submodule.span ℂ ((fun k : ℕ => fun x : ℝ => iteratedDeriv k (fun s=>C s x) t) '' Set.Iio N) := by
  apply triangular_span _ _ (fun n k => (composeCoeff n k t : ℂ))
  · intro k
    ext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact C_parameter_jet_expansion k t x
  · intro k
    exact Complex.ofReal_ne_zero.mpr (composeCoeff_diagonal ht k)

end CriticalHoneycomb.FiniteFunctional

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 Matrix Finset MeasureTheory

lemma A_eq_jet (c m x : ℝ) : A c m x=Real.cos (alpha c*m)*cosineKernelJet 0 0 (m^2) x := by
  rw [A,C_eq_beta_square,Complex.ofReal_re]

lemma A_eq_jet_fun (c m : ℝ) : A c m=fun x ↦ Real.cos (alpha c*m)*cosineKernelJet 0 0 (m^2) x :=
  funext (A_eq_jet c m)

lemma cos_alpha_pos {c m : ℝ} (hc : 0<c) (hm : |m|<c) : 0<Real.cos (alpha c*m) := by
  apply Real.cos_pos_of_mem_Ioo
  apply abs_lt.mp
  have h:=alpha_pair_bound hc (m:=m) (n:=0) (by simpa using hm)
  simpa using h

lemma sech_ordinary_pair_integrable {m n : ℝ} (hm : 0 ≤ m ∧ m ≤ 3*angle/2) (hn : 0 ≤ n ∧ n ≤ angle) :
    IntegrableOn (fun p ↦ cosineKernelJet 0 0 (m^2) (p^2)*cosineKernelJet 0 0 (n^2) (p^2)*
      sechProbDensity (3*angle) p) (Set.Ioi 0) := by
  exact sech_jet_pair_integrable (sq_nonneg _) (sq_nonneg _)
    ((sq_le_sq₀ hm.1 (by linarith [strip_angle_pos] : 0 ≤ 3*angle/2)).mpr hm.2)
    ((sq_le_sq₀ hn.1 strip_angle_pos.le).mpr hn.2) 0 0

/-- Separated-knot coefficient estimate for the actual cosine families. The
Gram invertibility here will be discharged by the sorted positive jet flag. -/
theorem sech_ordinary_coefficient_lower (N : ℕ) (q : Fin (2*N) → ℝ) (u t : ℝ)
    (hq : ∀ i,0 ≤ q i ∧ q i ≤ angle) (hu : 0 ≤ u ∧ u ≤ angle) (ht : 0 ≤ t ∧ t ≤ angle)
    (hinj : Function.Injective (Fin.lastCases t q))
    (hd : (familyGram (sechProbDensity (3*angle))
      (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases u q i)^2))
      (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases t q i)^2))).det≠0) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1))  ≤  -meanResidualRatio (sechProbDensity (3*angle))
      (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases u q i)^2))
      (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases t q i)^2))
      (cosineKernelJet 0 0 ((3*angle/2)^2)) 0 := by
  have hangle:=strip_angle_pos
  let c:=3*angle
  have hc : 0<c := by dsimp [c]; positivity
  let b : Fin (2*N+1) → ℝ:=Fin.lastCases u q
  let d : Fin (2*N+1) → ℝ:=Fin.lastCases t q
  have hb (i : Fin (2*N+1)) : 0 ≤ b i ∧ b i ≤ angle := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa [b] using hu
    · simpa [b] using hq i
  have hd' (i : Fin (2*N+1)) : 0 ≤ d i ∧ d i ≤ angle := by
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa [d] using ht
    · simpa [d] using hq i
  let F:=fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((b i)^2)
  let G:=fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((d i)^2)
  let H:=cosineKernelJet 0 0 ((c/2)^2)
  have hpair i j : |b i|+|d j|<c := by rw [abs_of_nonneg (hb i).1,abs_of_nonneg (hd' j).1]; dsimp [c]; linarith [(hb i).2,(hd' j).2]
  have htarget j : |c/2|+|d j|<c := by rw [abs_of_pos (half_pos hc),abs_of_nonneg (hd' j).1]; dsimp [c]; linarith [(hd' j).2]
  have hi i j : IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*sechProbDensity c p) (Set.Ioi 0) :=
    sech_ordinary_pair_integrable ⟨(hb i).1,by linarith [(hb i).2]⟩ (hd' j)
  have hH j : IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*sechProbDensity c p) (Set.Ioi 0) :=
    sech_ordinary_pair_integrable ⟨by dsimp [c]; positivity,le_rfl⟩ (hd' j)
  have hpF i : 0<Real.cos (alpha c*b i) := cos_alpha_pos hc (by rw [abs_of_nonneg (hb i).1]; dsimp [c]; linarith [(hb i).2])
  have hpG i : 0<Real.cos (alpha c*d i) := cos_alpha_pos hc (by rw [abs_of_nonneg (hd' i).1]; dsimp [c]; linarith [(hd' i).2])
  have hGram : (familyGram (sechProbDensity c) (fun i ↦ A c (b i)) (fun i ↦ A c (d i))).det≠0 := by
    simp_rw [A_eq_jet_fun]
    rw [familyGram_scalars _ F G _ _ hi,Matrix.det_mul,Matrix.det_mul,Matrix.det_diagonal,Matrix.det_diagonal]
    exact mul_ne_zero (mul_ne_zero (prod_ne_zero_iff.mpr (fun i _ ↦ (hpF i).ne')) hd)
      (prod_ne_zero_iff.mpr (fun i _ ↦ (hpG i).ne'))
  have hwq i := w_bounds_third hc (hq i).1 (show q i ≤ c/3 by dsimp [c]; linarith [(hq i).2])
  have hwu := w_bounds_third hc hu.1 (show u ≤ c/3 by dsimp [c]; linarith [hu.2])
  have hwt := w_bounds_third hc ht.1 (show t ≤ c/3 by dsimp [c]; linarith [ht.2])
  have he (v : ℝ) (i : Fin (2*N+1)) : Fin.lastCases (w c v) (fun j ↦ w c (q j)) i=w c (Fin.lastCases v q i) := by
    refine Fin.lastCases ?_ (fun _ ↦ ?_) i <;> simp
  have hinj' : Function.Injective (Fin.lastCases (w c t) (fun j ↦ w c (q j))) := by
    intro i j h
    simp only [he] at h
    apply hinj
    exact w_injectiveOn_third hc ⟨(hd' i).1,by dsimp [c]; linarith [(hd' i).2]⟩
      ⟨(hd' j).1,by dsimp [c]; linarith [(hd' j).2]⟩ h
  have hbound:=cauchyGram_coefficient_lower N (fun i ↦ w c (q i)) (w c u) (w c t)
    (sechProbDensity c) (fun i ↦ A c (b i)) (fun i ↦ A c (d i)) (A c (c/2)) hwq hwu hwt hinj'
    (fun i j ↦ A_pair_prob_integrable hc (hpair i j))
    (fun j ↦ A_pair_prob_integrable hc (htarget j)) hGram
    (fun i j ↦ by rw [he,he]; exact A_pair_prob_integral hc (hpair i j))
    (fun j ↦ by rw [he]; rw [A_pair_prob_integral hc (htarget j),w_half hc.ne',one_mul])
    (fun i ↦ by rw [he]; exact A_zero hc (by rw [abs_of_nonneg (hb i).1]; dsimp [c]; linarith [(hb i).2]))
    (by rw [A_zero hc (by rw [abs_of_pos (half_pos hc)]; linarith),w_half hc.ne']; norm_num)
  have heq : meanResidualRatio (sechProbDensity c) (fun i ↦ A c (b i)) (fun i ↦ A c (d i)) (A c (c/2)) 0=
      meanResidualRatio (sechProbDensity c) F G H 0 := by
    simp_rw [A_eq_jet_fun]
    rw [meanResidualRatio_scale_target _ _ _ H _ _ (cos_alpha_pos hc (by rw [abs_of_pos (half_pos hc)]; linarith)).ne']
    exact meanResidualRatio_scalars _ F G H 0 _ _ (fun i ↦ (hpF i).ne') (fun i ↦ (hpG i).ne') hi hH
  rw [heq,A_zero hc (by rw [abs_of_pos (half_pos hc)]; linarith),w_half hc.ne'] at hbound
  have hs : 0<1/Real.sqrt ((1:ℝ)+1) := by positivity
  have hs1 : 1/Real.sqrt ((1:ℝ)+1) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    exact Real.one_le_sqrt.mpr (by norm_num)
  have hpos : 0<1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) := by positivity
  have hn : 0  ≤  -meanResidualRatio (sechProbDensity c) F G H 0 := by nlinarith
  change _  ≤  -meanResidualRatio (sechProbDensity c) F G H 0
  nlinarith

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory

lemma sech_approximate_coefficient_lower (N : ℕ) {u t ε : ℝ}
    (hu : 0<u) (huL : u<angle) (ht : 0<t) (htL : t<angle)
    (he : 0<ε) (heu : ε<u^2) (heu' : u^2<angle^2-ε)
    (het : ε<t^2) (het' : t^2<angle^2-ε) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤
      -meanResidualRatio (sechProbDensity (3*angle))
        (fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder (interiorApproach N (u^2) ε) i) 0
          (interiorApproach N (u^2) ε i))
        (fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder (interiorApproach N (t^2) ε) i) 0
          (interiorApproach N (t^2) ε i)) (cosineKernelJet 0 0 ((3*angle/2)^2)) 0 := by
  have hangle:=strip_angle_pos
  have heL : ε ≤ angle^2 := by nlinarith [sq_nonneg u]
  let b:=interiorApproach N (u^2) ε
  let c:=interiorApproach N (t^2) ε
  have hb:=interiorApproach_strictMono N he heu heu'
  have hc:=interiorApproach_strictMono N he het het'
  have hb0 k := interiorApproach_bounds N k he.le heL ⟨sq_nonneg u,(sq_le_sq₀ hu.le hangle.le).mpr huL.le⟩
  have hc0 k := interiorApproach_bounds N k he.le heL ⟨sq_nonneg t,(sq_le_sq₀ ht.le hangle.le).mpr htL.le⟩
  let F:=fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder b i) 0 (b i)
  let G:=fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder c i) 0 (c i)
  let q:=fun i : Fin (2*N) ↦ Real.sqrt (commonApproach N ε i)
  have hq i : 0 ≤ q i ∧ q i ≤ angle := by
    constructor
    · exact Real.sqrt_nonneg _
    · apply Real.sqrt_le_iff.mpr
      exact ⟨hangle.le,(commonApproach_bounds N i he.le heL).2⟩
  have hEq (v : ℝ) (i : Fin (2*N+1)) :
      (Fin.lastCases v q i)^2=interiorApproach N (v^2) ε (knotPermutation N i) := by
    rw [interiorApproach_permutation]
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp only [Fin.lastCases_castSucc,q]
      exact Real.sq_sqrt (commonApproach_bounds N j he.le heL).1
  have hEF : (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases u q i)^2))=F ∘ knotPermutation N := by
    funext i x
    change _=cosineKernelJet (nodalOrder b (knotPermutation N i)) 0 (b (knotPermutation N i)) x
    rw [nodalOrder_eq_zero_of_strictMono_prefix hb,hEq]
  have hEG : (fun i : Fin (2*N+1) ↦ cosineKernelJet 0 0 ((Fin.lastCases t q i)^2))=G ∘ knotPermutation N := by
    funext i x
    change _=cosineKernelJet (nodalOrder c (knotPermutation N i)) 0 (c (knotPermutation N i)) x
    rw [nodalOrder_eq_zero_of_strictMono_prefix hc,hEq]
  have hinj : Function.Injective (Fin.lastCases t q) := by
    intro i j hij
    have hsq:=congrArg (fun z : ℝ ↦ z^2) hij
    rw [hEq,hEq] at hsq
    exact (knotPermutation N).injective (hc.injective hsq)
  have hdet : 0<(familyGram (sechProbDensity (3*angle)) F G).det := by
    apply sech_jet_gram_det_pos b c hb.monotone hc.monotone
      (fun i ↦ (hb0 i).1) (fun i ↦ (hc0 i).1) _ (fun i ↦ (hc0 i).2)
    intro i
    nlinarith [(hb0 i).2,sq_nonneg angle]
  have hd : (familyGram (sechProbDensity (3*angle)) (F ∘ knotPermutation N) (G ∘ knotPermutation N)).det≠0 := by
    change ((familyGram (sechProbDensity (3*angle)) F G).submatrix (knotPermutation N) (knotPermutation N)).det≠0
    rw [Matrix.det_submatrix_equiv_self]
    exact hdet.ne'
  have h:=sech_ordinary_coefficient_lower N q u t hq ⟨hu.le,huL.le⟩ ⟨ht.le,htL.le⟩ hinj
    (by rw [hEF,hEG]; exact hd)
  rw [hEF,hEG,meanResidualRatio_reindex] at h
  exact h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix MeasureTheory

lemma jetFamily_as_newton {n : ℕ} (b : ℕ → ℝ) {R : ℝ} (hb : ∀ i,0 ≤ b i ∧ b i ≤ R) :
    (fun i : Fin n ↦ cosineKernelJet (nodalOrder b i) 0 (b i))=
      fun i ↦ finiteFamilyCombination (fun j : Fin n ↦ fun x ↦ newtonKernel b x 0 j) ((newtonJetMatrix n b)ᵀ i) := by
  have hR : 0 ≤ R := (hb 0).1.trans (hb 0).2
  funext i x
  simpa only [finiteFamilyCombination,Matrix.transpose_apply,mul_comm] using
    cosineKernelJet_newton (R:=R+1) (by linarith)
      (fun j ↦ by rw [abs_of_nonneg (hb j).1]; linarith [(hb j).2]) x 0 i

lemma newtonFamilyGram_det_ne_zero {n : ℕ} (b c : ℕ → ℝ) {R S : ℝ}
    (hb : ∀ i,0 ≤ b i ∧ b i ≤ R) (hc : ∀ i,0 ≤ c i ∧ c i ≤ S)
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ p,0<p → 0 ≤ w p)
    (hi : ∀ r s,IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hd : (jetGram (n:=n) w b c).det≠0) :
    (familyGram w (fun i : Fin n ↦ fun x ↦ newtonKernel b x 0 i)
      (fun i : Fin n ↦ fun x ↦ newtonKernel c x 0 i)).det≠0 := by
  intro hz
  apply hd
  change (familyGram w (fun i : Fin n ↦ cosineKernelJet (nodalOrder b i) 0 (b i))
    (fun i : Fin n ↦ cosineKernelJet (nodalOrder c i) 0 (c i))).det=0
  rw [jetFamily_as_newton b hb,jetFamily_as_newton c hc,
    familyGram_bichange _ _ _ (fun i j ↦ newton_pair_integrable hb hc w hw hw0 i j (hi i j))]
  rw [Matrix.det_mul,Matrix.det_mul,hz,mul_zero,zero_mul]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix Filter Topology MeasureTheory

lemma tendsto_jet_meanResidualRatio {n : ℕ} {b c : ℕ → ℕ → ℝ} {B C : ℕ → ℝ} {R S T : ℝ}
    (hb : ∀ k i,0 ≤ b k i ∧ b k i ≤ R) (hc : ∀ k i,0 ≤ c k i ∧ c k i ≤ S)
    (hB : ∀ i,0 ≤ B i ∧ B i ≤ R) (hC : ∀ i,0 ≤ C i ∧ C i ≤ S)
    (htb : Tendsto b atTop (𝓝 B)) (htc : Tendsto c atTop (𝓝 C))
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀ p,0<p → 0 ≤ w p) (hT : 0 ≤ T)
    (hi : ∀ r s,IntegrableOn (fun p ↦ cosineKernelJet r 0 R (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hH : ∀ s,IntegrableOn (fun p ↦ cosineKernelJet 0 0 T (p^2)*cosineKernelJet s 0 S (p^2)*w p) (Set.Ioi 0))
    (hd : (jetGram (n:=n) w B C).det≠0) :
    Tendsto (fun k ↦ meanResidualRatio w
      (fun i : Fin n ↦ cosineKernelJet (nodalOrder (b k) i) 0 (b k i))
      (fun i : Fin n ↦ cosineKernelJet (nodalOrder (c k) i) 0 (c k i)) (cosineKernelJet 0 0 T) 0)
      atTop (𝓝 (meanResidualRatio w
        (fun i : Fin n ↦ cosineKernelJet (nodalOrder B i) 0 (B i))
        (fun i : Fin n ↦ cosineKernelJet (nodalOrder C i) 0 (C i)) (cosineKernelJet 0 0 T) 0)) := by
  have hHi (d : ℕ → ℝ) (hd : ∀ i,0 ≤ d i ∧ d i ≤ S) (j : Fin n) :
      IntegrableOn (fun p ↦ cosineKernelJet 0 0 T (p^2)*newtonKernel d (p^2) 0 j*w p) (Set.Ioi 0) := by
    simpa only [newtonKernel_const] using
      newton_pair_integrable (fun _ ↦ ⟨hT,le_rfl⟩) hd w hw hw0 0 j (hH j)
  have he k:=jet_meanResidualRatio_eq_newton (n:=n) (b k) (c k) (hb k) (hc k) w hw hw0
    (cosineKernelJet 0 0 T) 0 hi (hHi (c k) (hc k))
  have he0:=jet_meanResidualRatio_eq_newton (n:=n) B C hB hC w hw hw0
    (cosineKernelJet 0 0 T) 0 hi (hHi C hC)
  simp_rw [he,he0]
  exact tendsto_newton_meanResidualRatio hb hc hB hC htb htc w hw hw0 hT hi hH
    (newtonFamilyGram_det_ne_zero B C hB hC w hw hw0 hi hd)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Filter Topology MeasureTheory

/-- Quantitative coefficient noncancellation for the exact two-cluster jet
flags under the sech comparison measure. The systems remain nonsymmetric. -/
theorem sech_confluent_coefficient_lower (N : ℕ) {u t : ℝ}
    (hu : 0<u) (huL : u<angle) (ht : 0<t) (htL : t<angle) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤
      -meanResidualRatio (sechProbDensity (3*angle))
        (fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder (interiorKnotLabels N u) i) 0
          (interiorKnotLabels N u i))
        (fun i : Fin (2*N+1) ↦ cosineKernelJet (nodalOrder (interiorKnotLabels N t) i) 0
          (interiorKnotLabels N t i)) (cosineKernelJet 0 0 ((3*angle/2)^2)) 0 := by
  have hangle:=strip_angle_pos
  have hu2 : 0<u^2 := sq_pos_of_pos hu
  have ht2 : 0<t^2 := sq_pos_of_pos ht
  have hu2L : u^2<angle^2 := (sq_lt_sq₀ hu.le hangle.le).mpr huL
  have ht2L : t^2<angle^2 := (sq_lt_sq₀ ht.le hangle.le).mpr htL
  let δ:=min (u^2/2) (min ((angle^2-u^2)/2) (min (t^2/2) ((angle^2-t^2)/2)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδu : δ<u^2 := (min_le_left _ _).trans_lt (by linarith)
  have hδu' : δ<angle^2-u^2 := (min_le_right _ _ |>.trans (min_le_left _ _)).trans_lt (by linarith)
  have hδt : δ<t^2 := (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_left _ _)).trans_lt (by linarith)
  have hδt' : δ<angle^2-t^2 := (min_le_right _ _ |>.trans (min_le_right _ _) |>.trans (min_le_right _ _)).trans_lt (by linarith)
  let ε:=fun k : ℕ ↦ δ/((k:ℝ)+1)
  have he k : 0<ε k := by dsimp [ε]; positivity
  have heδ k : ε k ≤ δ := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0<(k:ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have heu k : ε k<u^2 := (heδ k).trans_lt hδu
  have heu' k : u^2<angle^2-ε k := by linarith [heδ k,hδu']
  have het k : ε k<t^2 := (heδ k).trans_lt hδt
  have het' k : t^2<angle^2-ε k := by linarith [heδ k,hδt']
  have heL k : ε k ≤ angle^2 := (heu k).le.trans hu2L.le
  have he0 : Tendsto ε atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop)
  let b:=fun k ↦ interiorApproach N (u^2) (ε k)
  let c:=fun k ↦ interiorApproach N (t^2) (ε k)
  have hb k j := interiorApproach_bounds N j (he k).le (heL k) ⟨hu2.le,hu2L.le⟩
  have hc k j := interiorApproach_bounds N j (he k).le (heL k) ⟨ht2.le,ht2L.le⟩
  have hB j : 0 ≤ interiorKnotLabels N u j ∧ interiorKnotLabels N u j ≤ angle^2 :=
    ⟨interiorKnot_nonneg N j u,interiorKnot_le N j hu huL⟩
  have hC j : 0 ≤ interiorKnotLabels N t j ∧ interiorKnotLabels N t j ≤ angle^2 :=
    ⟨interiorKnot_nonneg N j t,interiorKnot_le N j ht htL⟩
  have hR : angle^2 ≤ (3*angle/2)^2 := by nlinarith [sq_nonneg angle]
  have hi r s := sech_jet_pair_integrable (sq_nonneg angle) (sq_nonneg angle) hR le_rfl r s
  have hH s := sech_jet_pair_integrable (sq_nonneg (3*angle/2)) (sq_nonneg angle) le_rfl le_rfl 0 s
  have hd : (jetGram (n:=2*N+1) (sechProbDensity (3*angle)) (interiorKnotLabels N u) (interiorKnotLabels N t)).det≠0 := by
    apply ne_of_gt
    exact sech_jet_gram_det_pos _ _
      ((interiorKnot_monotone N hu huL).comp (fun _ _ h ↦ h))
      ((interiorKnot_monotone N ht htL).comp (fun _ _ h ↦ h))
      (fun i ↦ (hB i).1) (fun i ↦ (hC i).1) (fun i ↦ (hB i).2.trans hR) (fun i ↦ (hC i).2)
  have hlim:=tendsto_jet_meanResidualRatio (n:=2*N+1) hb hc hB hC
    (tendsto_interiorApproach N u he0) (tendsto_interiorApproach N t he0)
    (sechProbDensity (3*angle)) (by unfold sechProbDensity; fun_prop)
    (fun p hp ↦ by unfold sechProbDensity; positivity) (sq_nonneg (3*angle/2)) hi hH hd
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim.neg
    (fun k ↦ sech_approximate_coefficient_lower N hu huL ht htL (he k) (heu k) (heu' k) (het k) (het' k))

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
