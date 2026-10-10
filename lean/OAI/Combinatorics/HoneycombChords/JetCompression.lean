import OAI.Combinatorics.HoneycombChords.JetApproximation

namespace OAI

/-!
# Polynomial compression of complete jet Gram matrices

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open MeasureTheory
lemma scalar_young_abs {t:ℝ} (ht:0<t) (a b:ℝ) : |2*a*b|≤t*a^2+b^2/t := by
  have he:(t*a^2+b^2/t)*t=t^2*a^2+b^2 := by field_simp
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_left₀ ht).mp
    rw [neg_mul,he]
    nlinarith [sq_nonneg (t*a+b)]
  · apply (mul_le_mul_iff_left₀ ht).mp
    rw [he]
    nlinarith [sq_nonneg (t*a-b)]
lemma scalar_square_perturbation {t:ℝ} (ht:0<t) (a b:ℝ) :
    |b^2-a^2|≤t*a^2+(1+1/t)*(a-b)^2 := by
  have h:=scalar_young_abs ht a (b-a)
  obtain ⟨h1,h2⟩:=abs_le.mp h
  have hdiv:(b-a)^2/t=(1/t)*(a-b)^2 := by ring
  rw [hdiv] at h1 h2
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (a-b)]
lemma familySquaredNorm_sub_integrable (w f g:ℝ→ℝ)
    (hf:IntegrableOn (fun p=>f (p^2)^2*w p) (Set.Ioi 0))
    (hg:IntegrableOn (fun p=>g (p^2)^2*w p) (Set.Ioi 0))
    (hfg:IntegrableOn (fun p=>f (p^2)*g (p^2)*w p) (Set.Ioi 0)) :
    IntegrableOn (fun p=>(f (p^2)-g (p^2))^2*w p) (Set.Ioi 0) := by
  apply ((hf.add hg).sub (hfg.const_mul 2)).congr
  filter_upwards with p
  simp only [Pi.add_apply,Pi.sub_apply]
  ring
lemma familySquaredNorm_young (w f g:ℝ→ℝ) (hw:∀ p,0<p→0≤w p)
    (hf:IntegrableOn (fun p=>f (p^2)^2*w p) (Set.Ioi 0))
    (hg:IntegrableOn (fun p=>g (p^2)^2*w p) (Set.Ioi 0))
    (hfg:IntegrableOn (fun p=>f (p^2)*g (p^2)*w p) (Set.Ioi 0))
    {t:ℝ} (ht:0<t) :
    |familySquaredNorm w g-familySquaredNorm w f|≤
      t*familySquaredNorm w f+(1+1/t)*familySquaredNorm w (fun x=>f x-g x) := by
  have he:=familySquaredNorm_sub_integrable w f g hf hg hfg
  have hb:IntegrableOn (fun p=>t*(f (p^2)^2*w p)+(1+1/t)*((f (p^2)-g (p^2))^2*w p)) (Set.Ioi 0):=
    (hf.const_mul _).add (he.const_mul _)
  have hbound: (∫ p in Set.Ioi 0,t*(f (p^2)^2*w p)+(1+1/t)*((f (p^2)-g (p^2))^2*w p))=
      t*familySquaredNorm w f+(1+1/t)*familySquaredNorm w (fun x=>f x-g x) := by
    rw [integral_add (hf.const_mul _) (he.const_mul _),integral_const_mul,integral_const_mul]
    rfl
  apply abs_le.mpr
  constructor
  · have hm:(∫ p in Set.Ioi 0,f (p^2)^2*w p-g (p^2)^2*w p)≤
        ∫ p in Set.Ioi 0,t*(f (p^2)^2*w p)+(1+1/t)*((f (p^2)-g (p^2))^2*w p) := by
      apply integral_mono_ae (hf.sub hg) hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      have hh:=mul_le_mul_of_nonneg_right (abs_le.mp (scalar_square_perturbation ht (f (p^2)) (g (p^2)))).1 (hw p hp)
      simp only [Pi.sub_apply]
      nlinarith
    rw [hbound,integral_sub hf hg] at hm
    change familySquaredNorm w f-familySquaredNorm w g≤_ at hm
    linarith
  · have hm:(∫ p in Set.Ioi 0,g (p^2)^2*w p-f (p^2)^2*w p)≤
        ∫ p in Set.Ioi 0,t*(f (p^2)^2*w p)+(1+1/t)*((f (p^2)-g (p^2))^2*w p) := by
      apply integral_mono_ae (hg.sub hf) hb
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
      have hh:=mul_le_mul_of_nonneg_right (abs_le.mp (scalar_square_perturbation ht (f (p^2)) (g (p^2)))).2 (hw p hp)
      simp only [Pi.sub_apply]
      nlinarith
    rw [hbound,integral_sub hg hf] at hm
    exact hm
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Polynomial Finset MeasureTheory Matrix
lemma stripSpan_mono {A B:ℝ} (h:A≤B) : stripKernelSpan A ≤ stripKernelSpan B := by
  apply Submodule.span_mono
  rintro f ⟨b,r,hb,hA,rfl⟩
  exact ⟨b,r,hb,hA.trans h,rfl⟩
lemma stripSpan_actual_pair {f g:ℝ→ℝ}
    (hf:f∈stripKernelSpan (angle^2)) (hg:g∈stripKernelSpan (angle^2)) :
    IntegrableOn (fun p=>f (p^2)*g (p^2)*stripDensity p) (Set.Ioi 0) := by
  have hb:angle^2≤(3*angle/2)^2:=by nlinarith [sq_nonneg angle]
  have hi2:=stripSpan_pair_integrable (by norm_num : (0:ℝ)<1) 2 (stripSpan_mono hb hf) hg
  have hi0:=stripSpan_pair_integrable (by norm_num : (0:ℝ)<1) 0 (stripSpan_mono hb hf) hg
  apply (hi2.add hi0).congr
  filter_upwards with p
  dsimp only [Pi.add_apply,poleAdjustedDensity]
  have hd:(p^2+(1:ℝ)^2)≠0:=by positivity
  field_simp
lemma stripSpan_tilt_pair {f g:ℝ→ℝ}
    (hf:f∈stripKernelSpan (angle^2)) (hg:g∈stripKernelSpan (angle^2))
    (y:ℝ) {z:ℝ} (hz:0<z) :
    IntegrableOn (fun p=>f (p^2)*g (p^2)*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0) := by
  have hb:angle^2≤(3*angle/2)^2:=by nlinarith [sq_nonneg angle]
  have hi2:=stripSpan_pair_integrable hz 2 (stripSpan_mono hb hf) hg
  have hi0:=stripSpan_pair_integrable hz 0 (stripSpan_mono hb hf) hg
  apply (hi2.add (hi0.const_mul (y^2))).congr
  filter_upwards with p
  dsimp only [Pi.add_apply,poleAdjustedDensity,characteristicRatio]
  ring
lemma monomial_mem_stripSpan (k:ℕ) : (fun x:ℝ=>x^k)∈stripKernelSpan (angle^2) := by
  have h:=(stripKernelSpan (angle^2)).smul_mem ((2*k).factorial:ℝ)
    (kernel_mem_stripSpan le_rfl (sq_nonneg angle) k)
  have he:((2*k).factorial:ℝ) • cosineKernelJet k 0 0=(fun x:ℝ=>x^k) := by
    funext x
    simp only [Pi.smul_apply,smul_eq_mul,cosineKernelJet_at_zero]
    have hn : ((2*k).factorial:ℝ)≠0:=by positivity
    field_simp
  rwa [he] at h
lemma polynomial_mem_stripSpan (P:Polynomial ℝ) : (fun x=>P.eval x)∈stripKernelSpan (angle^2) := by
  classical
  have he:(fun x=>P.eval x)=∑ k∈P.support,P.coeff k • (fun x:ℝ=>x^k):=by
    funext x
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    exact Polynomial.eval_eq_sum
  rw [he]
  exact Submodule.sum_mem _ fun k _=>(stripKernelSpan (angle^2)).smul_mem _ (monomial_mem_stripSpan k)
noncomputable def twoJetFamily (N:ℕ) (i:Fin (2*N)) : ℝ→ℝ :=
  cosineKernelJet (nodalOrder (twoKnotLabels N) i) 0 (twoKnotLabels N i)
lemma twoJetFamily_mem (N:ℕ) (i:Fin (2*N)) : twoJetFamily N i∈stripKernelSpan (angle^2) :=
  kernel_mem_stripSpan (twoKnot_nonneg N _) (twoKnot_le N _) _
lemma finiteFamilyCombination_mem_stripSpan {n:ℕ} {F:Fin n→ℝ→ℝ}
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (a:Fin n→ℝ) :
    finiteFamilyCombination F a∈stripKernelSpan (angle^2) := by
  have he:finiteFamilyCombination F a=∑ i,a i • F i:=by ext x;simp [finiteFamilyCombination]
  rw [he]
  exact Submodule.sum_mem _ fun i _=>(stripKernelSpan (angle^2)).smul_mem _ (hF i)
lemma twoJetFamily_posDef (N:ℕ) : (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).PosDef := by
  apply jetGram_posDef stripDensity (twoKnotLabels N)
    (fun i j hij=>(twoKnot_monotone N) hij) (fun i=>twoKnot_nonneg N i) (fun _ hp=>stripDensity_pos hp)
  intro i j
  exact stripSpan_actual_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Filter Topology
/-- Fixed-parameter determinant compression for the complete jet family. -/
def TwoJetPolynomialCompression : Prop :=
  ∃ C:ℕ,0<C ∧ ∀ y z:ℝ,0<y→y<z→∀ᶠ N:ℕ in atTop,
    let w := fun p=>characteristicRatio y z p*stripDensity p
    let J := (familyGram w (twoJetFamily N) (twoJetFamily N)).det /
      (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).det
    (monomialGram (C*N) w).det/(monomialGram (C*N) stripDensity).det/4 ≤ J ∧
    J≤(monomialGram N w).det/(monomialGram N stripDensity).det
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Finset Matrix MeasureTheory
/-- An integral perturbation bound for polynomial compression. -/
theorem familyGram_error_from_norm {n:ℕ} (w:ℝ→ℝ) (F G:Fin n→ℝ→ℝ)
    (hw:∀ p,0<p→0≤w p)
    (hFF:∀ i j,IntegrableOn (fun p=>F i (p^2)*F j (p^2)*w p) (Set.Ioi 0))
    (hGG:∀ i j,IntegrableOn (fun p=>G i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hFG:∀ i j,IntegrableOn (fun p=>F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    {δ t:ℝ} (ht:0<t)
    (herr:∀ v:Fin n→ℝ,
      familySquaredNorm w (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
        δ*familySquaredNorm w (finiteFamilyCombination F v)) :
    ∀ v:Fin n→ℝ,
      |v ⬝ᵥ (familyGram w G G *ᵥ v)-v ⬝ᵥ (familyGram w F F *ᵥ v)|≤
        (t+(1+1/t)*δ)*(v ⬝ᵥ (familyGram w F F *ᵥ v)) := by
  intro v
  rw [familyGram_quad w F hFF,familyGram_quad w G hGG]
  have hF:=finiteFamilyCombination_pair_integrable w F F hFF v v
  have hG:=finiteFamilyCombination_pair_integrable w G G hGG v v
  have hfg:=finiteFamilyCombination_pair_integrable w F G hFG v v
  have hy:=familySquaredNorm_young w (finiteFamilyCombination F v) (finiteFamilyCombination G v) hw
    (by simpa only [pow_two] using hF) (by simpa only [pow_two] using hG) hfg ht
  calc
    _≤t*familySquaredNorm w (finiteFamilyCombination F v)+(1+1/t)*
      familySquaredNorm w (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x):=hy
    _≤t*familySquaredNorm w (finiteFamilyCombination F v)+(1+1/t)*
      (δ*familySquaredNorm w (finiteFamilyCombination F v)):=add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left (herr v) (show 0≤1+1/t by positivity))
    _=_:=by ring
lemma familySquaredNorm_weight_bounds (w r f:ℝ→ℝ) {l u:ℝ}
    (hw:∀ p,0<p→0≤w p) (hr:∀ p,0<p→l≤r p ∧ r p≤u)
    (hf:IntegrableOn (fun p=>f (p^2)^2*w p) (Set.Ioi 0))
    (hrf:IntegrableOn (fun p=>f (p^2)^2*(r p*w p)) (Set.Ioi 0)) :
    l*familySquaredNorm w f≤familySquaredNorm (fun p=>r p*w p) f ∧
    familySquaredNorm (fun p=>r p*w p) f≤u*familySquaredNorm w f := by
  unfold familySquaredNorm
  rw [←integral_const_mul,←integral_const_mul]
  constructor
  · apply integral_mono_ae (hf.const_mul l) hrf
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have h:=mul_le_mul_of_nonneg_right (hr p hp).1 (mul_nonneg (sq_nonneg (f (p^2))) (hw p hp))
    nlinarith
  · apply integral_mono_ae hrf (hf.const_mul u)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have h:=mul_le_mul_of_nonneg_right (hr p hp).2 (mul_nonneg (sq_nonneg (f (p^2))) (hw p hp))
    nlinarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Polynomial Finset MeasureTheory
/-- The genuine complete-jet space admits one simultaneous polynomial
approximation on an orthonormal basis; constants do not depend on its vectors. -/
theorem twoJet_orthonormal_polynomial_approximation :
    ∃ C N₀:ℕ,0<C ∧ ∀ N:ℕ,N₀≤N→0<N→
      ∃ (T:Matrix (Fin (2*N)) (Fin (2*N)) ℝ) (P:Fin (2*N)→Polynomial ℝ),
        IsUnit T.det ∧
        (let F:=fun i=>finiteFamilyCombination (twoJetFamily N) (T i)
         familyGram stripDensity F F=1 ∧
         (∀ i,(P i).natDegree<C*N) ∧
         ∀ i,familySquaredNorm stripDensity (fun x=>F i x-(P i).eval x)≤Real.exp (-2*(N:ℝ))) := by
  classical
  obtain ⟨C,N₀,hC,happ⟩:=twoJetPolynomialApproximation
  refine ⟨C,N₀,hC,?_⟩
  intro N hNN hN
  let J:=twoJetFamily N
  let B:=familyGram stripDensity J J
  have hB:B.PosDef:=twoJetFamily_posDef N
  obtain ⟨S,e,hS,hBS,_⟩:=positive_pencil_normal_form B B hB.isHermitian hB
  let T:=Sᵀ
  let F:=fun i=>finiteFamilyCombination J (T i)
  have hi i j:IntegrableOn (fun p=>J i (p^2)*J j (p^2)*stripDensity p) (Set.Ioi 0):=
    stripSpan_actual_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j)
  have hF:familyGram stripDensity F F=1:=by
    rw [show familyGram stripDensity F F=T*B*Tᵀ from familyGram_congruence stripDensity J hi T]
    simpa only [T,transpose_transpose,conjTranspose_eq_transpose_of_trivial] using hBS
  have hFp:∀ i,familySquaredNorm stripDensity (F i)=1:=by
    intro i
    have h:=congrArg (fun M:Matrix (Fin (2*N)) (Fin (2*N)) ℝ=>M i i) hF
    simpa only [familyGram,familySquaredNorm,pow_two,Matrix.one_apply_eq] using h
  have hPick:∀ i:Fin (2*N),∃ P:Polynomial ℝ,P.natDegree<C*N ∧
      familySquaredNorm stripDensity (fun x=>F i x-P.eval x)≤Real.exp (-2*(N:ℝ)) := by
    intro i
    obtain ⟨P,hP,herr⟩:=happ N hNN hN (T i)
    refine ⟨P,hP,?_⟩
    change familySquaredNorm stripDensity (fun x=>F i x-P.eval x)≤
      Real.exp (-2*(N:ℝ))*familySquaredNorm stripDensity (F i) at herr
    simpa only [hFp,mul_one] using herr
  choose P hP using hPick
  refine ⟨T,P,?_,hF,fun i=>(hP i).1,fun i=>(hP i).2⟩
  simpa only [T,det_transpose] using hS
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma orthonormal_family_error {n:ℕ} (F G:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (hG:∀ i,G i∈stripKernelSpan (angle^2))
    (hI:familyGram stripDensity F F=1) {δ:ℝ}
    (hE:∀ i,familySquaredNorm stripDensity (fun x=>F i x-G i x)≤δ)
    (v:Fin n→ℝ) :
    familySquaredNorm stripDensity (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
      ((n:ℝ)*δ)*familySquaredNorm stripDensity (finiteFamilyCombination F v) := by
  let E:Fin n→ℝ→ℝ:=fun i=>F i-G i
  have hmem i:E i∈stripKernelSpan (angle^2):=(stripKernelSpan (angle^2)).sub_mem (hF i) (hG i)
  have h:=familySquaredNorm_error_bound stripDensity E (fun _ hp=>(stripDensity_pos hp).le)
    (fun i j=>stripSpan_actual_pair (hmem i) (hmem j)) hE v
  have he:finiteFamilyCombination E v=(fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x):=by
    funext x
    simp [finiteFamilyCombination,E,mul_sub,sum_sub_distrib]
  rw [he] at h
  have hn:familySquaredNorm stripDensity (finiteFamilyCombination F v)=∑ i,v i^2:=by
    rw [←familyGram_quad stripDensity F (fun i j=>stripSpan_actual_pair (hF i) (hF j)),hI,one_mulVec]
    simp only [dotProduct,pow_two]
  rwa [hn]
lemma orthonormal_family_tilt_error {n:ℕ} (F G:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (hG:∀ i,G i∈stripKernelSpan (angle^2))
    (hI:familyGram stripDensity F F=1) {δ:ℝ} (hδ:0≤δ)
    (hE:∀ i,familySquaredNorm stripDensity (fun x=>F i x-G i x)≤δ)
    {y z:ℝ} (hy:0<y) (hyz:y<z) (v:Fin n→ℝ) :
    familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
      (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
      (((n:ℝ)*δ)/(y^2/z^2))*familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
        (finiteFamilyCombination F v) := by
  have hz:0<z:=hy.trans hyz
  let l:=y^2/z^2
  have hl:0<l:=by dsimp [l];positivity
  have hlt:l≤1:=by dsimp [l];apply (div_le_one (by positivity)).mpr;nlinarith
  have hr p (_:0<p):l≤characteristicRatio y z p ∧ characteristicRatio y z p≤1:=by
    have h:=characteristicRatio_bounds y hz p
    change l≤characteristicRatio y z p ∧ characteristicRatio y z p≤1
    change min 1 l≤characteristicRatio y z p ∧ characteristicRatio y z p≤ max 1 l at h
    simpa only [min_eq_right hlt,max_eq_left hlt] using h
  let f:=finiteFamilyCombination F v
  let e:=fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x
  have hf:f∈stripKernelSpan (angle^2):=finiteFamilyCombination_mem_stripSpan hF v
  have he:e∈stripKernelSpan (angle^2):=(stripKernelSpan (angle^2)).sub_mem hf (finiteFamilyCombination_mem_stripSpan hG v)
  have heint:IntegrableOn (fun p=>e (p^2)^2*stripDensity p) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_actual_pair he he
  have herint:IntegrableOn (fun p=>e (p^2)^2*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_tilt_pair he he y hz
  have hfint:IntegrableOn (fun p=>f (p^2)^2*stripDensity p) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_actual_pair hf hf
  have hfrint:IntegrableOn (fun p=>f (p^2)^2*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_tilt_pair hf hf y hz
  have hne:familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) e≤familySquaredNorm stripDensity e:=by
    simpa only [one_mul] using (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) e
      (fun _ hp=>(stripDensity_pos hp).le) hr heint herint).2
  have hnf: l*familySquaredNorm stripDensity f≤familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) f:=
    (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) f
      (fun _ hp=>(stripDensity_pos hp).le) hr hfint hfrint).1
  have hn:=orthonormal_family_error F G hF hG hI hE v
  change familySquaredNorm stripDensity e≤((n:ℝ)*δ)*familySquaredNorm stripDensity f at hn
  calc
    _≤familySquaredNorm stripDensity e:=hne
    _≤((n:ℝ)*δ)*familySquaredNorm stripDensity f:=hn
    _=(((n:ℝ)*δ)/l)*(l*familySquaredNorm stripDensity f):=by field_simp
    _≤_:=mul_le_mul_of_nonneg_left hnf (by positivity)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Polynomial Finset MeasureTheory
lemma posDef_real_congruence {n:ℕ} (A C:Matrix (Fin n) (Fin n) ℝ)
    (hA:A.PosDef) (hC:IsUnit C.det) : (C*A*Cᵀ).PosDef := by
  have ht:IsUnit Cᵀ.det:=by simpa only [det_transpose] using hC
  have h:=hA.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit (Cᵀ.isUnit_iff_isUnit_det.mpr ht))
  simpa only [conjTranspose_eq_transpose_of_trivial,transpose_transpose] using h
lemma determinant_quotient_congruence {n:ℕ} (A B C:Matrix (Fin n) (Fin n) ℝ)
    (hC:IsUnit C.det) : (C*A*Cᵀ).det/(C*B*Cᵀ).det=A.det/B.det := by
  have hc:C.det≠0:=isUnit_iff_ne_zero.mp hC
  simp only [det_mul,det_transpose]
  by_cases hb:B.det=0
  · simp [hb]
  · field_simp
lemma posDef_of_relative_error {n:ℕ} (A D:Matrix (Fin n) (Fin n) ℝ)
    (hA:A.PosDef) (hD:D.IsHermitian) {η:ℝ} (hη:η<1)
    (herr:∀ v:Fin n→ℝ,|v ⬝ᵥ (D *ᵥ v)-v ⬝ᵥ (A *ᵥ v)|≤η*(v ⬝ᵥ (A *ᵥ v))) : D.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hD
  intro v hv
  have hp:=hA.dotProduct_mulVec_pos hv
  have hh:=(abs_le.mp (herr v)).1
  simp only [star_trivial] at hp ⊢
  nlinarith
lemma polynomial_family_compression {n d:ℕ} (P:Fin n→Polynomial ℝ) (hP:∀ i,(P i).natDegree<d)
    (w:ℝ→ℝ) (hi:∀ k:ℕ,IntegrableOn (fun p=>p^k*w p) (Set.Ioi 0)) :
    familyGram w (fun i x=>(P i).eval x) (fun i x=>(P i).eval x)=
      (Matrix.of fun i (j:Fin d)=>(P i).coeff j)*monomialGram d w*(Matrix.of fun i (j:Fin d)=>(P i).coeff j)ᵀ := by
  let C:Matrix (Fin n) (Fin d) ℝ:=fun i j=>(P i).coeff j
  let V:Fin d→ℝ→ℝ:=fun j x=>x^j.val
  have hV:∀ i,finiteFamilyCombination V (C i)=(fun x=>(P i).eval x):=by
    intro i
    funext x
    rw [Polynomial.eval_eq_sum_range' (hP i)]
    simp only [finiteFamilyCombination,V,C]
    exact Fin.sum_univ_eq_sum_range (fun k=>(P i).coeff k*x^k) d
  have hh:=familyGram_congruence w V (fun i j=>monomial_pair_integrable w hi i.val j.val) C
  simp only [hV] at hh
  exact hh
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real Filter Topology
noncomputable def compressionError (l:ℝ) (N:ℕ) : ℝ :=
  Real.exp (-(N:ℝ))+(1+1/Real.exp (-(N:ℝ)))*((2*(N:ℝ))*Real.exp (-2*(N:ℝ))/l)
lemma compressionError_nonneg {l:ℝ} (hl:0<l) (N:ℕ) : 0≤compressionError l N:=by
  unfold compressionError;positivity
lemma compressionError_eventually_small {l:ℝ} (hl:0<l) :
    ∀ᶠ N:ℕ in atTop,compressionError l N≤1/2 ∧
      (2*(N:ℝ))*compressionError l N≤1/2 := by
  have hc:Tendsto (fun N:ℕ=>(N:ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop
  have h1:Tendsto (fun N:ℕ=>(N:ℝ)*Real.exp (-(N:ℝ))) atTop (𝓝 0):=by
    simpa only [Function.comp_def,pow_one] using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hc
  have h2:Tendsto (fun N:ℕ=>(N:ℝ)^2*Real.exp (-(N:ℝ))) atTop (𝓝 0):=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hc
  have hh:Tendsto (fun N:ℕ=>2*((N:ℝ)*Real.exp (-(N:ℝ)))+(8/l)*((N:ℝ)^2*Real.exp (-(N:ℝ)))) atTop (𝓝 0):=by
    simpa using (h1.const_mul 2).add (h2.const_mul (8/l))
  have hb:=hh.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  filter_upwards [hb,eventually_ge_atTop (1:ℕ)] with N hN hN1
  have hn:(1:ℝ)≤N:=by exact_mod_cast hN1
  have he: Real.exp (-2*(N:ℝ))=Real.exp (-(N:ℝ))^2:=by
    rw [sq,←Real.exp_add];congr 1;ring
  have he1:Real.exp (-(N:ℝ))≤1:=Real.exp_le_one_iff.mpr (by linarith)
  have hx:1/Real.exp (-(N:ℝ))*Real.exp (-2*(N:ℝ))=Real.exp (-(N:ℝ)):=by
    rw [he];field_simp
  have hs:(2*(N:ℝ))*compressionError l N≤
      2*((N:ℝ)*Real.exp (-(N:ℝ)))+(8/l)*((N:ℝ)^2*Real.exp (-(N:ℝ))) := by
    have hp:Real.exp (-2*(N:ℝ))≤Real.exp (-(N:ℝ)):=Real.exp_le_exp.mpr (by linarith)
    have hm:=mul_le_mul_of_nonneg_left hp (show 0≤4*(N:ℝ)^2/l by positivity)
    unfold compressionError
    have hxs:(1+1/Real.exp (-(N:ℝ)))*Real.exp (-2*(N:ℝ))=
        Real.exp (-2*(N:ℝ))+Real.exp (-(N:ℝ)):=by rw [add_mul,one_mul,hx]
    calc
      _=2*((N:ℝ)*Real.exp (-(N:ℝ)))+(4*(N:ℝ)^2/l)*(Real.exp (-2*(N:ℝ))+Real.exp (-(N:ℝ))):=by
        rw [←hxs];ring
      _≤_:=by ring_nf at hm ⊢;linarith
  have hsmall: (2*(N:ℝ))*compressionError l N≤1/2:=hs.trans hN.le
  refine ⟨?_,hsmall⟩
  have h0:=compressionError_nonneg hl N
  nlinarith
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma orthonormal_stripGram_transfer {N:ℕ} (F G:Fin (2*N)→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (hG:∀ i,G i∈stripKernelSpan (angle^2))
    (hI:familyGram stripDensity F F=1)
    (hE:∀ i,familySquaredNorm stripDensity (fun x=>F i x-G i x)≤Real.exp (-2*(N:ℝ)))
    {y z:ℝ} (hy:0<y) (hyz:y<z)
    (hA:(familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F).PosDef)
    (hsmall:compressionError (y^2/z^2) N≤1/2 ∧ (2*(N:ℝ))*compressionError (y^2/z^2) N≤1/2) :
    (familyGram stripDensity G G).PosDef ∧
    (familyGram (fun p=>characteristicRatio y z p*stripDensity p) G G).det/(familyGram stripDensity G G).det≤
      4*((familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F).det/(familyGram stripDensity F F).det) := by
  have hz:=hy.trans hyz
  let l:=y^2/z^2
  have hl:0<l:=by dsimp [l];positivity
  have hl1:l≤1:=by dsimp [l];apply (div_le_one (by positivity)).mpr;nlinarith
  let η:=compressionError l N
  let δ:ℝ:=(2*(N:ℝ))*Real.exp (-2*(N:ℝ))/l
  let t:=Real.exp (-(N:ℝ))
  have ht:0<t:=Real.exp_pos _
  have hδ:0≤δ:=by dsimp [δ];positivity
  have hFF i j:=stripSpan_actual_pair (hF i) (hF j)
  have hGG i j:=stripSpan_actual_pair (hG i) (hG j)
  have hFG i j:=stripSpan_actual_pair (hF i) (hG j)
  have hbase:∀ v:Fin (2*N)→ℝ,
      familySquaredNorm stripDensity (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
        δ*familySquaredNorm stripDensity (finiteFamilyCombination F v):=by
    intro v
    have h:=orthonormal_family_error F G hF hG hI hE v
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (familySquaredNorm_nonneg stripDensity _ (fun _ hp=>(stripDensity_pos hp).le))
    change (2*(N:ℝ))*Real.exp (-2*(N:ℝ))≤(2*(N:ℝ))*Real.exp (-2*(N:ℝ))/l
    apply (le_div_iff₀ hl).mpr
    exact mul_le_of_le_one_right (by positivity) hl1
  have hBE:=familyGram_error_from_norm stripDensity F G (fun _ hp=>(stripDensity_pos hp).le)
    hFF hGG hFG ht hbase
  change ∀ v,|v ⬝ᵥ (familyGram stripDensity G G *ᵥ v)-v ⬝ᵥ (familyGram stripDensity F F *ᵥ v)|≤
    η*(v ⬝ᵥ (familyGram stripDensity F F *ᵥ v)) at hBE
  have htilt:∀ v:Fin (2*N)→ℝ,
      familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
        (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
      δ*familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) (finiteFamilyCombination F v):=by
    intro v
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      orthonormal_family_tilt_error F G hF hG hI (Real.exp_pos _).le hE hy hyz v
  have hAD:=familyGram_error_from_norm (fun p=>characteristicRatio y z p*stripDensity p) F G
    (fun p hp=>(mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp)).le)
    (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz)
    (fun i j=>stripSpan_tilt_pair (hG i) (hG j) y hz)
    (fun i j=>stripSpan_tilt_pair (hF i) (hG j) y hz) ht htilt
  change ∀ v,|v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) G G *ᵥ v)-
    v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v)|≤
    η*(v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v)) at hAD
  have hB:(familyGram stripDensity F F).PosDef:=by rw [hI];exact Matrix.PosDef.one
  have hn:((2*N:ℕ):ℝ)*η≤1/2:=by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hsmall.2
  have hη:0≤η:=compressionError_nonneg hl N
  refine ⟨posDef_of_relative_error _ _ hB (familyGram_hermitian _ G) (by linarith only [hsmall.1]) hBE,?_⟩
  exact (gram_quotient_small_relative_error _ _ _ _ hA hB
    (familyGram_hermitian _ G) (familyGram_hermitian _ G) hη hsmall.1 hn hAD hBE).2
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma characteristicRatio_le_one {y z:ℝ} (hy:0<y) (hyz:y<z) (p:ℝ) :
    characteristicRatio y z p≤1 := by
  have hz:=hy.trans hyz
  have ht:y^2/z^2≤1:=by apply (div_le_one (by positivity)).mpr;nlinarith
  simpa only [max_eq_left ht] using (characteristicRatio_bounds y hz p).2
lemma twoJetFamily_tilt_posDef (N:ℕ) {y z:ℝ} (hy:0<y) (hz:0<z) :
    (familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)).PosDef := by
  apply jetGram_posDef _ (twoKnotLabels N)
    (fun i j hij=>(twoKnot_monotone N) hij) (fun i=>twoKnot_nonneg N i)
    (fun p hp=>mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp))
  intro i j
  exact stripSpan_tilt_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j) y hz
lemma familyGram_tilt_contraction {n:ℕ} (F:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) {y z:ℝ} (hy:0<y) (hyz:y<z) (v:Fin n→ℝ) :
    v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v)≤
      v ⬝ᵥ (familyGram stripDensity F F *ᵥ v) := by
  rw [familyGram_quad _ F (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y (hy.trans hyz)),
    familyGram_quad _ F (fun i j=>stripSpan_actual_pair (hF i) (hF j))]
  have hf:=finiteFamilyCombination_mem_stripSpan hF v
  apply integral_mono_ae
  · simpa only [IntegrableOn,pow_two] using stripSpan_tilt_pair hf hf y (hy.trans hyz)
  · simpa only [IntegrableOn,pow_two] using stripSpan_actual_pair hf hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hh:=mul_le_mul_of_nonneg_right (characteristicRatio_le_one hy hyz p)
      (mul_nonneg (sq_nonneg (finiteFamilyCombination F v (p^2))) (stripDensity_pos hp).le)
    nlinarith
lemma twoJet_contains_monomials (N:ℕ) :
    ∃ C:Matrix (Fin N) (Fin (2*N)) ℝ,∀ i,finiteFamilyCombination (twoJetFamily N) (C i)=(fun x=>x^i.val) := by
  classical
  let ix:Fin N→Fin (2*N):=fun i=>⟨i.val,by omega⟩
  let C:Matrix (Fin N) (Fin (2*N)) ℝ:=fun i j=>if j=ix i then ((2*i.val).factorial:ℝ) else 0
  refine ⟨C,?_⟩
  intro i
  funext x
  unfold finiteFamilyCombination
  rw [sum_eq_single (ix i)]
  · simp only [C,ite_eq_left rfl,twoJetFamily,ix,twoKnot_nodalOrder,twoKnotLabels,ite_eq_left i.isLt,cosineKernelJet_at_zero]
    have hn:((2*i.val).factorial:ℝ)≠0:=by positivity
    field_simp
  · intro j _ hj
    simp only [C,ite_eq_right hj,zero_mul]
  · simp
/-- A containment inequality for polynomial compression at every natural index. -/
theorem twoJet_polynomial_compression_upper (N:ℕ) {y z:ℝ} (hy:0<y) (hyz:y<z) :
    (familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)).det /
      (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).det≤
    (monomialGram N (fun p=>characteristicRatio y z p*stripDensity p)).det/(monomialGram N stripDensity).det := by
  obtain ⟨C,hC⟩:=twoJet_contains_monomials N
  have he (w:ℝ→ℝ) (hi:∀ i j,IntegrableOn
      (fun p=>twoJetFamily N i (p^2)*twoJetFamily N j (p^2)*w p) (Set.Ioi 0)) :
      C*familyGram w (twoJetFamily N) (twoJetFamily N)*Cᵀ=monomialGram N w:=by
    rw [←familyGram_congruence w (twoJetFamily N) hi C]
    simp only [hC]
    rfl
  have heB:=he stripDensity (fun i j=>stripSpan_actual_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j))
  have heA:=he (fun p=>characteristicRatio y z p*stripDensity p)
    (fun i j=>stripSpan_tilt_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j) y (hy.trans hyz))
  have hcb:(C*familyGram stripDensity (twoJetFamily N) (twoJetFamily N)*Cᵀ).PosDef:=by
    rw [heB]
    exact monomialGram_posDef N stripDensity (fun _ hp=>stripDensity_pos hp) stripDensity_moments
  have h:=positive_contraction_compression _ _ C (twoJetFamily_tilt_posDef N hy (hy.trans hyz))
    (twoJetFamily_posDef N) hcb (familyGram_tilt_contraction _ (twoJetFamily_mem N) hy hyz)
  simpa only [heA,heB] using h
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Topology Polynomial
/-- Determinant compression for the complete jet family with the strip weight. -/
theorem twoJetPolynomialCompression : TwoJetPolynomialCompression := by
  classical
  obtain ⟨C,N₀,hC,happrox⟩:=twoJet_orthonormal_polynomial_approximation
  refine ⟨C,hC,?_⟩
  intro y z hy hyz
  have hz:=hy.trans hyz
  have hl:0<y^2/z^2:=by positivity
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop (1:ℕ),compressionError_eventually_small hl] with N hNN hN hsmall
  obtain ⟨T,P,hT,hI,hP,hE⟩:=happrox N hNN (by omega)
  let w:ℝ→ℝ:=fun p=>characteristicRatio y z p*stripDensity p
  let J:=twoJetFamily N
  let F:=fun i=>finiteFamilyCombination J (T i)
  let G:Fin (2*N)→ℝ→ℝ:=fun i x=>(P i).eval x
  have hFm i:F i∈stripKernelSpan (angle^2):=finiteFamilyCombination_mem_stripSpan (twoJetFamily_mem N) (T i)
  have hGm i:G i∈stripKernelSpan (angle^2):=polynomial_mem_stripSpan (P i)
  have hcongB:familyGram stripDensity F F=T*familyGram stripDensity J J*Tᵀ:=
    familyGram_congruence stripDensity J (fun i j=>stripSpan_actual_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j)) T
  have hcongA:familyGram w F F=T*familyGram w J J*Tᵀ:=
    familyGram_congruence w J (fun i j=>stripSpan_tilt_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j) y hz) T
  have hAF:(familyGram w F F).PosDef:=by
    rw [hcongA]
    exact posDef_real_congruence _ T (twoJetFamily_tilt_posDef N hy hz) hT
  have htrans:=orthonormal_stripGram_transfer F G hFm hGm hI hE hy hyz hAF hsmall
  have hInv:(familyGram w F F).det/(familyGram stripDensity F F).det=
      (familyGram w J J).det/(familyGram stripDensity J J).det:=by
    rw [hcongA,hcongB]
    exact determinant_quotient_congruence _ _ T hT
  let Q:Matrix (Fin (2*N)) (Fin (C*N)) ℝ:=fun i j=>(P i).coeff j
  have hwint k:IntegrableOn (fun p=>p^k*w p) (Set.Ioi 0):=by
    simpa only [pow_one] using characteristic_tilt_moments hy hz 1 k
  have hpA:familyGram w G G=Q*monomialGram (C*N) w*Qᵀ:=polynomial_family_compression P hP w hwint
  have hpB:familyGram stripDensity G G=Q*monomialGram (C*N) stripDensity*Qᵀ:=
    polynomial_family_compression P hP stripDensity stripDensity_moments
  have hPolyA:(monomialGram (C*N) w).PosDef:=monomialGram_posDef _ w
    (fun p hp=>mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp)) hwint
  have hPolyB:(monomialGram (C*N) stripDensity).PosDef:=monomialGram_posDef _ stripDensity
    (fun _ hp=>stripDensity_pos hp) stripDensity_moments
  have hQB:(Q*monomialGram (C*N) stripDensity*Qᵀ).PosDef:=by rw [←hpB];exact htrans.1
  have hContract:∀ v:Fin (C*N)→ℝ,v ⬝ᵥ (monomialGram (C*N) w *ᵥ v)≤v ⬝ᵥ (monomialGram (C*N) stripDensity *ᵥ v):=by
    intro v
    exact familyGram_tilt_contraction (fun i:Fin (C*N)=>fun x:ℝ=>x^i.val) (fun i=>monomial_mem_stripSpan i.val) hy hyz v
  have hlow:=positive_contraction_compression _ _ Q hPolyA hPolyB hQB hContract
  rw [←hpA,←hpB] at hlow
  have hu:=htrans.2
  change (familyGram w G G).det/(familyGram stripDensity G G).det≤
    4*((familyGram w F F).det/(familyGram stripDensity F F).det) at hu
  rw [hInv] at hu
  constructor
  · change (monomialGram (C*N) w).det/(monomialGram (C*N) stripDensity).det/4≤
      (familyGram w J J).det/(familyGram stripDensity J J).det
    linarith [hlow.trans hu]
  · exact twoJet_polynomial_compression_upper N hy hyz
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma orthonormal_family_expansion_error {n:ℕ} (F G:Fin n→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (hG:∀ i,G i∈stripKernelSpan (angle^2))
    (hI:familyGram stripDensity F F=1) {δ:ℝ} (hδ:0≤δ)
    (hE:∀ i,familySquaredNorm stripDensity (fun x=>F i x-G i x)≤δ)
    {y z:ℝ} (hz:0<z) (hr:∀ p,0<p→(1:ℝ)≤characteristicRatio y z p ∧ characteristicRatio y z p≤2) (v:Fin n→ℝ) :
    familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
      (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
      (2*((n:ℝ)*δ))*familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
        (finiteFamilyCombination F v) := by
  let f:=finiteFamilyCombination F v
  let e:=fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x
  have hf:f∈stripKernelSpan (angle^2):=finiteFamilyCombination_mem_stripSpan hF v
  have he:e∈stripKernelSpan (angle^2):=(stripKernelSpan (angle^2)).sub_mem hf (finiteFamilyCombination_mem_stripSpan hG v)
  have heint:IntegrableOn (fun p=>e (p^2)^2*stripDensity p) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_actual_pair he he
  have herint:IntegrableOn (fun p=>e (p^2)^2*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_tilt_pair he he y hz
  have hfint:IntegrableOn (fun p=>f (p^2)^2*stripDensity p) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_actual_pair hf hf
  have hfrint:IntegrableOn (fun p=>f (p^2)^2*(characteristicRatio y z p*stripDensity p)) (Set.Ioi 0):=by
    simpa only [pow_two] using stripSpan_tilt_pair hf hf y hz
  have hne:familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) e≤2*familySquaredNorm stripDensity e:=by
    exact (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) e
      (fun _ hp=>(stripDensity_pos hp).le) hr heint herint).2
  have hnf: 1*familySquaredNorm stripDensity f≤familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) f:=
    (familySquaredNorm_weight_bounds stripDensity (characteristicRatio y z) f
      (fun _ hp=>(stripDensity_pos hp).le) hr hfint hfrint).1
  have hn:=orthonormal_family_error F G hF hG hI hE v
  change familySquaredNorm stripDensity e≤((n:ℝ)*δ)*familySquaredNorm stripDensity f at hn
  calc
    _≤2*familySquaredNorm stripDensity e:=hne
    _≤2*(((n:ℝ)*δ)*familySquaredNorm stripDensity f):=mul_le_mul_of_nonneg_left hn (by norm_num)
    _=(2*((n:ℝ)*δ))*(1*familySquaredNorm stripDensity f):=by ring
    _≤_:=mul_le_mul_of_nonneg_left hnf (by positivity)
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory
lemma orthonormal_stripGram_expansion_transfer {N:ℕ} (F G:Fin (2*N)→ℝ→ℝ)
    (hF:∀ i,F i∈stripKernelSpan (angle^2)) (hG:∀ i,G i∈stripKernelSpan (angle^2))
    (hI:familyGram stripDensity F F=1)
    (hE:∀ i,familySquaredNorm stripDensity (fun x=>F i x-G i x)≤Real.exp (-2*(N:ℝ)))
    {y z:ℝ} (hy:0<y) (hz:0<z)
    (hr:∀ p,0<p→(1:ℝ)≤characteristicRatio y z p ∧ characteristicRatio y z p≤2)
    (hA:(familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F).PosDef)
    (hsmall:compressionError ((1:ℝ)/2) N≤1/2 ∧ (2*(N:ℝ))*compressionError ((1:ℝ)/2) N≤1/2) :
    (familyGram stripDensity G G).PosDef ∧
    ((familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F).det/(familyGram stripDensity F F).det)/4≤
      (familyGram (fun p=>characteristicRatio y z p*stripDensity p) G G).det/(familyGram stripDensity G G).det := by
  let l:ℝ:=1/2
  have hl:0<l:=by norm_num [l]
  have hl1:l≤1:=by norm_num [l]
  let η:=compressionError l N
  let δ:ℝ:=(2*(N:ℝ))*Real.exp (-2*(N:ℝ))/l
  let t:=Real.exp (-(N:ℝ))
  have ht:0<t:=Real.exp_pos _
  have hδ:0≤δ:=by dsimp [δ];positivity
  have hFF i j:=stripSpan_actual_pair (hF i) (hF j)
  have hGG i j:=stripSpan_actual_pair (hG i) (hG j)
  have hFG i j:=stripSpan_actual_pair (hF i) (hG j)
  have hbase:∀ v:Fin (2*N)→ℝ,
      familySquaredNorm stripDensity (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
        δ*familySquaredNorm stripDensity (finiteFamilyCombination F v):=by
    intro v
    have h:=orthonormal_family_error F G hF hG hI hE v
    simp only [Nat.cast_mul,Nat.cast_ofNat] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (familySquaredNorm_nonneg stripDensity _ (fun _ hp=>(stripDensity_pos hp).le))
    change (2*(N:ℝ))*Real.exp (-2*(N:ℝ))≤(2*(N:ℝ))*Real.exp (-2*(N:ℝ))/l
    apply (le_div_iff₀ hl).mpr
    exact mul_le_of_le_one_right (by positivity) hl1
  have hBE:=familyGram_error_from_norm stripDensity F G (fun _ hp=>(stripDensity_pos hp).le)
    hFF hGG hFG ht hbase
  change ∀ v,|v ⬝ᵥ (familyGram stripDensity G G *ᵥ v)-v ⬝ᵥ (familyGram stripDensity F F *ᵥ v)|≤
    η*(v ⬝ᵥ (familyGram stripDensity F F *ᵥ v)) at hBE
  have htilt:∀ v:Fin (2*N)→ℝ,
      familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p)
        (fun x=>finiteFamilyCombination F v x-finiteFamilyCombination G v x)≤
      δ*familySquaredNorm (fun p=>characteristicRatio y z p*stripDensity p) (finiteFamilyCombination F v):=by
    intro v
    have h:=orthonormal_family_expansion_error F G hF hG hI (Real.exp_pos _).le hE hz hr v
    convert h using 1; dsimp [δ,l]; push_cast; ring
  have hAD:=familyGram_error_from_norm (fun p=>characteristicRatio y z p*stripDensity p) F G
    (fun p hp=>(mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp)).le)
    (fun i j=>stripSpan_tilt_pair (hF i) (hF j) y hz)
    (fun i j=>stripSpan_tilt_pair (hG i) (hG j) y hz)
    (fun i j=>stripSpan_tilt_pair (hF i) (hG j) y hz) ht htilt
  change ∀ v,|v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) G G *ᵥ v)-
    v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v)|≤
    η*(v ⬝ᵥ (familyGram (fun p=>characteristicRatio y z p*stripDensity p) F F *ᵥ v)) at hAD
  have hB:(familyGram stripDensity F F).PosDef:=by rw [hI];exact Matrix.PosDef.one
  have hn:((2*N:ℕ):ℝ)*η≤1/2:=by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hsmall.2
  have hη:0≤η:=compressionError_nonneg hl N
  refine ⟨posDef_of_relative_error _ _ hB (familyGram_hermitian _ G) (by linarith only [hsmall.1]) hBE,?_⟩
  exact (gram_quotient_small_relative_error _ _ _ _ hA hB
    (familyGram_hermitian _ G) (familyGram_hermitian _ G) hη hsmall.1 hn hAD hBE).1
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Equiv
lemma diagonal_compression_codimension {n m:ℕ} (C:Matrix (Fin n) (Fin m) ℝ) (e:Fin m→ℝ)
    {l:ℝ} (hl:0≤l) (he:∀ i,l≤e i) :
    l^(m-n)*(C*diagonal e*Cᵀ).det≤(∏ i,e i)*(C*Cᵀ).det := by
  classical
  have hn:0<(Fintype.card (Perm (Fin n)):ℝ):=by exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hn).mp
  have hbase:=rectangular_diagonal_gram_det C (fun _=>1)
  simp only [Matrix.diagonal_one,Matrix.mul_one,prod_const_one,one_mul] at hbase
  have hweight:=rectangular_diagonal_gram_det C e
  calc
    (Fintype.card (Perm (Fin n)):ℝ)*(l^(m-n)*(C*diagonal e*Cᵀ).det)=
      l^(m-n)*((Fintype.card (Perm (Fin n)):ℝ)*(C*diagonal e*Cᵀ).det):=by ring
    _=l^(m-n)*(∑ f:Fin n→Fin m,(∏ i,e (f i))*(C.submatrix id f).det^2):=by rw [hweight]
    _≤(∏ i,e i)*(∑ f:Fin n→Fin m,(C.submatrix id f).det^2):=by
      rw [mul_sum,mul_sum]
      apply sum_le_sum
      intro f _
      by_cases hf:Function.Injective f
      · let S:Finset (Fin m):=univ.image f
        have hcard:(univ\S).card=m-n:=by
          rw [card_sdiff]
          simp only [inter_univ]
          simp [S,card_image_iff.mpr (fun i _ j _ h=>hf h)]
        have hc:l^(m-n)≤∏ i∈univ\S,e i:=by
          rw [←hcard,←prod_const]
          exact prod_le_prod₀ (fun _ _=>hl) (fun i _=>he i)
        have hp:(∏ i,e i)=(∏ i∈univ\S,e i)*(∏ i,e (f i)):=by
          rw [←prod_image (fun i _ j _ h=>hf h)]
          exact (prod_sdiff (subset_univ S)).symm
        have hh:=mul_le_mul_of_nonneg_right hc (show 0≤∏ i,e (f i) from prod_nonneg (fun i _=>hl.trans (he (f i))))
        rw [←hp] at hh
        nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg (C.submatrix id f).det)]
      · obtain ⟨i,j,hij,heq⟩:=Function.not_injective_iff.mp hf
        have hz:(C.submatrix id f).det=0:=Matrix.det_zero_of_column_eq heq (fun k=>by simp [hij])
        simp [hz]
    _=(Fintype.card (Perm (Fin n)):ℝ)*((∏ i,e i)*(C*Cᵀ).det):=by rw [←hbase];ring
/-- The matching compression bound with the codimension factor. -/
theorem positive_compression_codimension {n m:ℕ}
    (A B:Matrix (Fin m) (Fin m) ℝ) (C:Matrix (Fin n) (Fin m) ℝ)
    (hA:A.PosDef) (hB:B.PosDef) (hCB:(C*B*Cᵀ).PosDef) {l:ℝ} (hl:0≤l)
    (hAB:∀ v:Fin m→ℝ,l*(v ⬝ᵥ (B *ᵥ v))≤v ⬝ᵥ (A *ᵥ v)) :
    l^(m-n)*((C*A*Cᵀ).det/(C*B*Cᵀ).det)≤A.det/B.det := by
  obtain ⟨P,e,hP,hPB,hPA⟩:=positive_pencil_normal_form A B hA.1 hB
  have hPP:P*P⁻¹=1:=Matrix.mul_nonsing_inv P hP
  have hPP':P⁻¹*P=1:=Matrix.nonsing_inv_mul P hP
  have he (i:Fin m):l≤e i := by
    have hh:=hAB (P *ᵥ Pi.single i 1)
    have hquad (T:Matrix (Fin m) (Fin m) ℝ) (v:Fin m→ℝ) :
        (P *ᵥ v) ⬝ᵥ (T *ᵥ (P *ᵥ v))=v ⬝ᵥ ((Pᴴ*T*P) *ᵥ v) := by
      simp only [Matrix.conjTranspose_eq_transpose_of_trivial,←mulVec_mulVec]
      exact (dotProduct_comm _ _).trans (Matrix.dotProduct_transpose_mulVec P v (T *ᵥ (P *ᵥ v))).symm
    rw [hquad,hquad,hPA,hPB] at hh
    simpa [Matrix.mulVec_diagonal] using hh
  have hnormal (T U:Matrix (Fin m) (Fin m) ℝ) (h:Pᴴ*T*P=U) : T=P⁻¹ᵀ*U*P⁻¹ := by
    have hl':P⁻¹ᵀ*Pᵀ=1:=by rw [←Matrix.transpose_mul,hPP,Matrix.transpose_one]
    rw [←h,Matrix.conjTranspose_eq_transpose_of_trivial]
    calc
      T=(P⁻¹ᵀ*Pᵀ)*T*(P*P⁻¹) := by rw [hl',hPP];simp
      _=P⁻¹ᵀ*(Pᵀ*T*P)*P⁻¹ := by simp only [Matrix.mul_assoc]
  let D:Matrix (Fin n) (Fin m) ℝ:=C*P⁻¹ᵀ
  have hDA:C*A*Cᵀ=D*diagonal e*Dᵀ := by
    rw [hnormal A _ hPA]
    dsimp [D]
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  have hDB:C*B*Cᵀ=D*Dᵀ := by
    rw [hnormal B _ hPB]
    dsimp [D]
    rw [Matrix.transpose_mul,Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc,Matrix.mul_one]
  have hr:A.det/B.det=∏ i,e i := by
    have ha:=congrArg Matrix.det hPA
    have hb:=congrArg Matrix.det hPB
    simp only [det_mul,det_conjTranspose,star_trivial,det_diagonal,det_one] at ha hb
    apply (div_eq_iff hB.det_pos.ne').mpr
    nlinarith [congrArg (fun x:ℝ=>x*B.det) ha,congrArg (fun x:ℝ=>x*A.det) hb]
  rw [←mul_div_assoc]
  apply (div_le_iff₀ hCB.det_pos).mpr
  rw [hr,hDA,hDB]
  exact diagonal_compression_codimension D e hl he
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset MeasureTheory Filter Topology Polynomial
/-- One uniform polynomial compression bound for every parameter pair with
1≤(y/z)²≤2, including the moving pair in strip-asymptotics:107. -/
theorem twoJet_polynomial_expansion_uniform :
    ∃ C:ℕ,0<C ∧ ∀ᶠ N:ℕ in atTop,∀ y z:ℝ,0<z→z≤y→y^2≤2*z^2→
      (familyGram (fun p=>characteristicRatio y z p*stripDensity p) (twoJetFamily N) (twoJetFamily N)).det /
        (familyGram stripDensity (twoJetFamily N) (twoJetFamily N)).det ≤
      4*((monomialGram (C*N) (fun p=>characteristicRatio y z p*stripDensity p)).det /
        (monomialGram (C*N) stripDensity).det) := by
  classical
  obtain ⟨C,N₀,hC,happrox⟩:=twoJet_orthonormal_polynomial_approximation
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop N₀,eventually_ge_atTop (1:ℕ),
    compressionError_eventually_small (by norm_num : 0<(1:ℝ)/2)] with N hNN hN' hsmall
  intro y z hz hzy hyz2
  have hN:0<N:=by omega
  have hy:=hz.trans_le hzy
  have hr1:1≤y^2/z^2:=by apply (le_div_iff₀ (by positivity)).mpr;nlinarith
  have hr2:y^2/z^2≤2:=by apply (div_le_iff₀ (by positivity)).mpr;linarith
  have hr p (_:0<p):(1:ℝ)≤characteristicRatio y z p ∧ characteristicRatio y z p≤2:=by
    have h:=characteristicRatio_bounds y hz p
    rw [min_eq_left hr1,max_eq_right hr1] at h
    exact ⟨h.1,h.2.trans hr2⟩
  obtain ⟨T,P,hT,hI,hP,hE⟩:=happrox N hNN hN
  let w:ℝ→ℝ:=fun p=>characteristicRatio y z p*stripDensity p
  let J:=twoJetFamily N
  let F:=fun i=>finiteFamilyCombination J (T i)
  let G:Fin (2*N)→ℝ→ℝ:=fun i x=>(P i).eval x
  have hFm i:F i∈stripKernelSpan (angle^2):=finiteFamilyCombination_mem_stripSpan (twoJetFamily_mem N) (T i)
  have hGm i:G i∈stripKernelSpan (angle^2):=polynomial_mem_stripSpan (P i)
  have hcongB:familyGram stripDensity F F=T*familyGram stripDensity J J*Tᵀ:=
    familyGram_congruence stripDensity J (fun i j=>stripSpan_actual_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j)) T
  have hcongA:familyGram w F F=T*familyGram w J J*Tᵀ:=
    familyGram_congruence w J (fun i j=>stripSpan_tilt_pair (twoJetFamily_mem N i) (twoJetFamily_mem N j) y hz) T
  have hAF:(familyGram w F F).PosDef:=by
    rw [hcongA]
    exact posDef_real_congruence _ T (twoJetFamily_tilt_posDef N hy hz) hT
  have htrans:=orthonormal_stripGram_expansion_transfer F G hFm hGm hI hE hy hz hr hAF hsmall
  have hInv:(familyGram w F F).det/(familyGram stripDensity F F).det=
      (familyGram w J J).det/(familyGram stripDensity J J).det:=by
    rw [hcongA,hcongB]
    exact determinant_quotient_congruence _ _ T hT
  let Q:Matrix (Fin (2*N)) (Fin (C*N)) ℝ:=fun i j=>(P i).coeff j
  have hwint k:IntegrableOn (fun p=>p^k*w p) (Set.Ioi 0):=by
    simpa only [pow_one] using characteristic_tilt_moments hy hz 1 k
  have hpA:familyGram w G G=Q*monomialGram (C*N) w*Qᵀ:=polynomial_family_compression P hP w hwint
  have hpB:familyGram stripDensity G G=Q*monomialGram (C*N) stripDensity*Qᵀ:=
    polynomial_family_compression P hP stripDensity stripDensity_moments
  have hPolyA:(monomialGram (C*N) w).PosDef:=monomialGram_posDef _ w
    (fun p hp=>mul_pos (characteristicRatio_pos hy hz p) (stripDensity_pos hp)) hwint
  have hPolyB:(monomialGram (C*N) stripDensity).PosDef:=monomialGram_posDef _ stripDensity
    (fun _ hp=>stripDensity_pos hp) stripDensity_moments
  have hQB:(Q*monomialGram (C*N) stripDensity*Qᵀ).PosDef:=by rw [←hpB];exact htrans.1
  have hExpand:∀ v:Fin (C*N)→ℝ,(1:ℝ)*(v ⬝ᵥ (monomialGram (C*N) stripDensity *ᵥ v))≤v ⬝ᵥ (monomialGram (C*N) w *ᵥ v):=by
    intro v
    rw [one_mul,monomialGram_quadratic _ stripDensity_moments,monomialGram_quadratic _ hwint]
    apply integral_mono_ae (weightedPolynomialNorm_integrable _ stripDensity_moments _)
      (weightedPolynomialNorm_integrable _ hwint _)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
    have hh:=mul_le_mul_of_nonneg_right (hr p hp).1
      (mul_nonneg (sq_nonneg ((Polynomial.ofFn (C*N) v).eval (p^2))) (stripDensity_pos hp).le)
    change _≤_*(characteristicRatio y z p*stripDensity p)
    nlinarith only [hh]
  have hpoly:=positive_compression_codimension _ _ Q hPolyA hPolyB hQB (by norm_num : (0:ℝ)≤1) hExpand
  simp only [one_pow,one_mul] at hpoly
  rw [←hpA,←hpB] at hpoly
  have hu:=htrans.2
  change ((familyGram w F F).det/(familyGram stripDensity F F).det)/4≤
    (familyGram w G G).det/(familyGram stripDensity G G).det at hu
  rw [hInv] at hu
  change (familyGram w J J).det/(familyGram stripDensity J J).det≤
    4*((monomialGram (C*N) w).det/(monomialGram (C*N) stripDensity).det)
  linarith [hu.trans hpoly]
end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end

end OAI
