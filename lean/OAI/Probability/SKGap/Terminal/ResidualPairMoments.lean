import Mathlib
import OAI.Probability.SKGap.Terminal.FieldGibbs

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix.Norms.Frobenius
namespace SKGapCutoff.Static
open Primary Recipe
variable {n : ℕ}

lemma varianceEnergy_gradient_bound (P : Observables n) (hP : ∀x,0≤P x)
    (hp : ∑x,P x=1) (f : Observables n) {L : ℝ}
    (hd : ∀x,∑i,(halfDiff i f x)^2≤L^2) : varianceEnergy P f≤L^2 := by
  calc
    _ ≤ ∑x,P x*L^2 := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hP x)
      exact (Finset.sum_le_sum (fun i _=>mul_le_of_le_one_left (sq_nonneg _) (conditionalVariance_le_one P x i))).trans (hd x)
    _ = _ := by rw [←Finset.sum_mul,hp,one_mul]

lemma weak_selftest (P F : Observables n) (hP : ∀x,0≤P x) (hp : ∑x,P x=1)
    {C L : ℝ} (hC : 0≤C)
    (hw : ∀G,|∑x,P x*G x*F x|≤C*starNorm P G)
    (hd : ∀x,∑i,(halfDiff i F x)^2≤L^2) :
    (∑x,P x*(F x)^2)≤C^2+L^2 := by
  let X:=∑x,P x*(F x)^2
  have hX : 0≤X:=Finset.sum_nonneg (fun x _=>mul_nonneg (hP x) (sq_nonneg _))
  have he:=varianceEnergy_gradient_bound P hP hp F hd
  have hb : X≤C*Real.sqrt (X+L^2) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (show X+varianceEnergy P F≤X+L^2 by linarith)) hC)
    have hh : (∑x,P x*F x*F x)=X := by
      apply Finset.sum_congr rfl; intro x _; ring
    have hh' := hw F
    rw [hh,abs_of_nonneg hX] at hh'
    exact hh'
  have hy:=Real.sq_sqrt (add_nonneg hX (sq_nonneg L))
  change X≤_
  nlinarith [sq_nonneg (C-Real.sqrt (X+L^2))]

lemma square_selftest (hn : 0<n) (P F : Observables n) (_ : ∀x,0≤P x)
    {C : ℝ} (hs : ∀f,|∑x,P x*(f x)^2*(F x/Real.sqrt (n:ℝ))*F x|≤C*starSquared P f)
    (f : Observables n) :
    (∑x,P x*(f x)^2*(F x/Real.sqrt (n:ℝ))^2)≤C/Real.sqrt (n:ℝ)*starSquared P f := by
  have hnR : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  have he : (∑x,P x*(f x)^2*(F x/Real.sqrt (n:ℝ))^2)=
      (∑x,P x*(f x)^2*(F x/Real.sqrt (n:ℝ))*F x)/Real.sqrt (n:ℝ) := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro x _; ring
  rw [he]
  exact (div_le_div_of_nonneg_right ((le_abs_self _).trans (hs f)) hnR.le).trans_eq (by ring)

end SKGapCutoff.Static
namespace SKGapCutoff.Recipe
open Primary Static
variable {n : ℕ}

def primaryPair (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) : Observables n :=
  normalizedPair (residual j J h k) (mag j J h (k+1))

lemma mag_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (mag j J h k x)≤Real.sqrt (n:ℝ) := by
  apply nonneg_le_nonneg_of_sq_le_sq (Real.sqrt_nonneg _)
  simp only [←sq,vectorNorm_sq,Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    _ ≤ ∑_i:Fin n,(1:ℝ)^2 := Finset.sum_le_sum (fun i _=>by
      simpa only [sq_abs,mag] using pow_le_pow_left₀ (abs_nonneg _) (primaryState_mag_bounded j J h k x i) 2)
    _ = _ := by simp

lemma residual_vectorNorm (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    vectorNorm (residual j J h k x)≤2*Real.sqrt (n:ℝ) := by
  have he : vectorNorm (residual j J h k x)≤vectorNorm (mag j J h k x)+vectorNorm (mag j J h (k+1) x) :=
    norm_sub_le (WithLp.toLp 2 (mag j J h k x) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (mag j J h (k+1) x))
  exact he.trans ((add_le_add (mag_vectorNorm j J h k x) (mag_vectorNorm j J h (k+1) x)).trans_eq (by ring))

lemma primaryPair_size (hn : 0<n) (j : ℝ) (J : Interaction n) (h : Fin n→ℝ) (k : ℕ) (x : Spin n) :
    |primaryPair j J h k x|≤2*Real.sqrt (n:ℝ) := by
  have hs : 0<Real.sqrt (n:ℝ):=Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  rw [primaryPair,normalizedPair,abs_div,abs_of_pos hs]
  apply (div_le_iff₀ hs).mpr
  exact (vectorPair_abs _ _ x).trans (mul_le_mul (residual_vectorNorm j J h k x)
    (mag_vectorNorm j J h (k+1) x) (vectorNorm_nonneg _) (by positivity))

def primaryPairBudget (j R B : ℝ) (k : ℕ) : ℝ :=
  (differentiationBound j R B k+differentiationBound j R B (k+1))+
  differentiationBound j R B (k+1)*2+
  2*(differentiationBound j R B k+differentiationBound j R B (k+1))*differentiationBound j R B (k+1)

lemma primaryPairBudget_nonneg {j R B : ℝ} (hR : 0≤R) (hB : 0≤B) (k : ℕ) :
    0≤primaryPairBudget j R B k := by
  have h0:=differentiationBound_nonneg (j:=j) hR hB k
  have h1:=differentiationBound_nonneg (j:=j) hR hB (k+1)
  unfold primaryPairBudget; positivity

lemma primaryPair_gradient (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) :
    ∀x,‖derivativeVector (primaryPair j J h k) x‖≤primaryPairBudget j R B k := by
  let A:=differentiationBound j R B k
  let B':=differentiationBound j R B (k+1)
  have hA : 0≤A:=differentiationBound_nonneg hR hB k
  have hB' : 0≤B':=differentiationBound_nonneg hR hB (k+1)
  have hm (l : ℕ) (hl : l≤k+1) (x : Spin n) :
      SKGap.opNorm (derivativeMatrix (mag j J h l) x)≤differentiationBound j R B l :=
    (primary_differentiation J h x hn hR hB hJ l (fun t ht=>hformal x t (ht.trans hl))).2.2.1
  intro x
  change ‖derivativeVector (primaryPair j J h k) x‖≤(A+B')+B'*2+2*(A+B')*B'
  apply (normalizedPair_derivative_bound (Cu:=2) (Cv:=1) hn _ _ x (add_nonneg hA hB') hB' ?_
    (hm _ le_rfl x) (residual_vectorNorm j J h k x) (by simpa using mag_vectorNorm j J h (k+1) x)).trans_eq (by ring)
  rw [show derivativeMatrix (residual j J h k) x=
    derivativeMatrix (mag j J h k) x-derivativeMatrix (mag j J h (k+1)) x from derivativeMatrix_sub _ _ x]
  simp only [opNorm_eq,map_sub]
  exact (norm_sub_le _ _).trans (add_le_add (hm _ (by omega) x) (hm _ le_rfl x))

end SKGapCutoff.Recipe

end
end

section

noncomputable section
open scoped BigOperators
namespace SKGapCutoff.Recipe
open Primary Static
universe u
variable {Ω : Type u} {n : Ω→ℕ} {M : ℕ} {j R B W C : ℝ}
variable {J : ∀a,Interaction (n a)} {h : ∀a,Fin (n a)→ℝ}

lemma primaryPair_difference_sq {n : ℕ} (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    (∑i,(halfDiff i (primaryPair j J h k) x)^2)≤(primaryPairBudget j R B k)^2 := by
  have hd:=pow_le_pow_left₀ (norm_nonneg _) (primaryPair_gradient hn hR hB J h hJ k hformal x) 2
  simpa only [EuclideanSpace.real_norm_sq_eq,derivativeVector,WithLp.ofLp_toLp] using hd

lemma primaryPair_scaled_difference {n : ℕ} (hn : 0<n) {j R B : ℝ} (hR : 0≤R) (hB : 0≤B)
    (J : Interaction n) (h : Fin n→ℝ) (hJ : SKGap.opNorm J≤R) (k : ℕ)
    (hformal : ∀x l,l≤k+1→ShapeBound (formalField j J h x l) B) (x : Spin n) :
    (∑i,(halfDiff i (fun y=>primaryPair j J h k y/Real.sqrt (n:ℝ)) x)^2)≤(primaryPairBudget j R B k)^2 := by
  have ht (i : Fin n) : halfDiff i (fun y=>primaryPair j J h k y/Real.sqrt (n:ℝ)) x=
      halfDiff i (primaryPair j J h k) x/Real.sqrt (n:ℝ) := by unfold halfDiff; ring
  simp only [ht,div_pow,←Finset.sum_div,Real.sq_sqrt (Nat.cast_nonneg n)]
  exact (div_le_div_of_nonneg_right (primaryPair_difference_sq hn hR hB J h hJ k hformal x)
    (Nat.cast_nonneg n)).trans (div_le_self (sq_nonneg _) (by exact_mod_cast hn))

theorem gibbs_primary_pair_moments (k : ℕ) (hk : k+1<M)
    (hR : 0≤R) (hB : 0≤B) (hW : 0≤W) (hC : 0≤C)
    (hn : ∀a,0<n a) (hJ : ∀a,(J a).IsSymm) (hdiag : ∀a i,J a i i=0)
    (hevent : ∀a,RecipeMatrixEvent j R (residualCoefficientBudget j 2 k 0) B W C M (2*k) (J a)) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀a,
      (∑x,fieldGibbs (J a) (h a) x*(primaryPair j (J a) (h a) k x)^2)≤C₁ ∧
      ∀f : Observables (n a),
      (∑x,fieldGibbs (J a) (h a) x*(f x)^2*
        (primaryPair j (J a) (h a) k x/Real.sqrt (n a:ℝ))^2)≤
        C₂/Real.sqrt (n a:ℝ)*starSquared (fieldGibbs (J a) (h a)) f := by
  let q : Fin M:=⟨k,by omega⟩
  let D:=fun a=>(emptyRecipe j (J a) (h a) M).normalizedPrimary q
  have hD : FamilyRecipe j J h D 0 k 2:=
    (emptyRecipe_family j J h M).normalizedPrimary hn q k le_rfl
  have hcon (a : Ω) (x : Spin (n a)) :
      (∑i,residual j (J a) (h a) k x i*(D a).source 0 x i)=primaryPair j (J a) (h a) k x := by
    rw [show (D a).source 0=fun y i=>mag j (J a) (h a) (k+1) y i/Real.sqrt (n a:ℝ) from
      OrdinaryData.normalizedPrimary_magnetization _ q j (J a) (h a) k rfl]
    simp only [primaryPair,normalizedPair,vectorPair,mul_div_assoc,Finset.sum_div]
  obtain ⟨hw,hs⟩:=gibbs_ordinary_residuals k 0 (by norm_num : (2:ℝ)≤2) (by omega)
    hR hB hW hC hn hJ hdiag (by simpa using hevent) D hD
  have hw':=hw.congr hcon
  have hs':=hs.congr hcon
  obtain ⟨C₁,hC₁,hw'⟩:=hw'
  let L:=primaryPairBudget j R B k
  have hL : 0≤L:=primaryPairBudget_nonneg hR hB k
  obtain ⟨C₂,hC₂,hs'⟩:=hs' 2 L (by norm_num) hL
  refine ⟨C₁^2+L^2,C₂,by positivity,hC₂,fun a=>⟨?_,?_⟩⟩
  · exact weak_selftest _ _ (fun x=>(fieldGibbs_pos _ _ x).le) (sum_fieldGibbs _ _) hC₁ (hw' a)
      (primaryPair_difference_sq (hn a) hR hB (J a) (h a) (hevent a).1 k
        (fun x l hl=>(hevent a).2.1 (h a) x l (by omega)))
  · intro f
    apply square_selftest (hn a) _ _ (fun x=>(fieldGibbs_pos _ _ x).le) ?_ f
    intro g
    apply hs' a g _
    · intro x
      rw [abs_div,abs_of_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn a)))]
      exact (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hn a)))).mpr
        (primaryPair_size (hn a) j (J a) (h a) k x)
    · exact primaryPair_scaled_difference (hn a) hR hB (J a) (h a) (hevent a).1 k
        (fun x l hl=>(hevent a).2.1 (h a) x l (by omega))

end SKGapCutoff.Recipe

end
end

end OAI
