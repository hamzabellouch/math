import Mathlib
import OAI.Probability.SKGap.Entropy.WordUniformCost
import OAI.Probability.SKGap.Stability.WordPredictionStability

namespace OAI

section
noncomputable section
namespace SKGap
open Real Set
open scoped BigOperators

def wordBiasConstant (L : ℕ) (j B C : ℝ) : ℕ → ℝ
  | 0 => C
  | k+1 => C+(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k+
      wordBiasConstant L j B C k

lemma wordBiasConstant_nonneg (L : ℕ) {j B C : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (k : ℕ) :
    0≤wordBiasConstant L j B C k := by
  induction k with
  | zero => exact hC
  | succ k ih => simp only [wordBiasConstant];positivity

lemma wordBiasConstant_ge (L : ℕ) {j B C : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (k : ℕ) :
    C≤wordBiasConstant L j B C k := by
  cases k with
  | zero => exact le_rfl
  | succ k =>
    have hh := wordBiasConstant_nonneg L hj hB hC k
    change C≤C+(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k+wordBiasConstant L j B C k
    have hp : 0≤(L:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k := by positivity
    linarith

theorem word_bias_induction {ι : Type*} [Fintype ι] [Nonempty ι]
    {j B C D n z : ℝ} (hj : 0≤j) (hB : 0≤B) (hC : 0≤C) (hn : 1≤n)
    (hz : z∈Icc (0:ℝ) 1) (a : ι → ℝ) (ha : ∀ i,|a i|≤D) (L : ℕ)
    (e : List (WordLetter ι) → ι → ℝ)
    (hb : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ∀ i,|e F i|≤B)
    (hbase : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F=0 → ∀ i,|e F i-wordDiagonal F i|≤C/n)
    (hloop : ∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F≠0 → ∀ i,
        |e F i-wordRecursionValue j a z e F i|≤C/n) :
    ∀ k,∀ F : List (WordLetter ι),F.length≤L → (∀ l∈F,l.bounded D) →
      inverseCount F≤1 → ordinaryCount F≤k → ∀ i,
        |e F i-wordPrediction j a z F i|≤wordBiasConstant L j B C k/n := by
  intro k
  induction k with
  | zero =>
    intro F hlen hF hI hO i
    have ho : ordinaryCount F=0 := Nat.eq_zero_of_le_zero hO
    rw [wordPrediction_base j a z F i ho]
    exact hbase F hlen hF hI ho i
  | succ k ih =>
    intro F hlen hF hI hO i
    have hn0 : 0<n := zero_lt_one.trans_le hn
    by_cases ho : ordinaryCount F=0
    · rw [wordPrediction_base j a z F i ho]
      exact (hbase F hlen hF hI ho i).trans
        (div_le_div_of_nonneg_right (wordBiasConstant_ge L hj hB hC (k+1)) hn0.le)
    have he := wordBiasConstant_nonneg L hj hB hC k
    have hsub (t : WordRecursionTerm ι) (ht : t∈wordRecursionTerms a F) :
        t.outer.length≤L ∧ t.inner.length≤L ∧
        (∀ l∈t.outer,l.bounded D) ∧ (∀ l∈t.inner,l.bounded D) ∧
        inverseCount t.outer≤1 ∧ inverseCount t.inner≤1 ∧
        ordinaryCount t.outer≤k ∧ ordinaryCount t.inner≤k := by
      have h1 := wordRecursionTerms_lengths a F t ht
      have h2 := wordRecursionTerms_bounds ha F hF t ht
      have h3 := wordRecursionTerms_one_inverse a F hI t ht
      have h4 := wordRecursionTerms_decreases a F t ht
      exact ⟨h1.1.trans hlen,h1.2.trans hlen,h2.1,h2.2,h3.1,h3.2,by omega,by omega⟩
    have hreg := wordRecursionValue_stability hj hz hn hB he a F e (wordPrediction j a z)
      (by intro t ht u;have hh:=hsub t ht;exact ⟨hb _ hh.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1 u,hb _ hh.1 hh.2.2.1 hh.2.2.2.2.1 u⟩)
      (by intro t ht u;have hh:=hsub t ht;exact ⟨ih _ hh.2.1 hh.2.2.2.1 hh.2.2.2.2.2.1 hh.2.2.2.2.2.2.2 u,
        ih _ hh.1 hh.2.2.1 hh.2.2.2.2.1 hh.2.2.2.2.2.2.1 u⟩) i
    rw [wordPrediction_recursion j a z F i ho]
    apply (abs_sub_le (e F i) (wordRecursionValue j a z e F i)
      (wordRecursionValue j a z (wordPrediction j a z) F i)).trans
    apply (add_le_add (hloop F hlen hF hI ho i) hreg).trans
    have hl : (F.length:ℝ)≤L := by exact_mod_cast hlen
    have hmul := mul_le_mul_of_nonneg_right hl
      (show 0≤j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k by positivity)
    apply (div_le_div_of_nonneg_right (show C+(F.length:ℝ)*j*(2*B+wordBiasConstant L j B C k)*wordBiasConstant L j B C k≤
      wordBiasConstant L j B C (k+1) by
        simp only [wordBiasConstant]
        nlinarith only [hmul,he]) hn0.le).trans_eq'
    ring
end SKGap
end
end

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma wordExpected_abs_bound [Nonempty ι] (f : 𝓢(ℝ,ℂ)) {R j A D z : ℝ}
    (hR : 0≤R) (hj : 0≤j) (hA : 0≤A) (hD : 0≤D) {a : ι→ℝ}
    (ha : ∀ i,0≤a i) (haA : ∀ i,a i≤A) (hz : z∈Icc (0:ℝ) 1)
    (F : List (WordLetter ι)) (hF : ∀ l∈F,l.bounded D) (i : ι) :
    |wordExpected f hR j a z F i|≤(actualWordBound f R j A D)^F.length := by
  have hh := norm_integral_le_of_norm_le_const (μ:=Measure.pi (fun _ : MatrixCoordinates ι=>gaussianReal 0 1))
    (f:=fun g=>actualWord f R hR j a z F (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i)
    (C:=(actualWordBound f R j A D)^F.length) (Filter.Eventually.of_forall (fun g=>
      (matrix_entry_le_opNorm _ i i).trans ((actualWord_bounds f hR hj hA hD ha haA hz F hF).1 _)))
  simpa [wordExpected,Real.norm_eq_abs,Measure.real] using hh

lemma wordRecursionValue_split (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0≤R) (j : ℝ)
    (a : ι→ℝ) (z : ℝ) (F P Q : List (WordLetter ι)) (i : ι)
    (hs : firstNoiseSplit F=some (P,Q)) :
    wordRecursionValue j a z (wordExpected f hR j a z) F i=
      wordRecursionAtExpected f hR j a z P Q i := by
  simp only [wordRecursionValue,wordRecursionTerms,hs]
  rfl

theorem actual_word_uniform_bias {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0≤R) (C : ℝ) (N : ℕ),
      R=2*sqrt j+1+1 ∧
      (∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹) ∧
      (∀ x,star (f x)=f x) ∧ 0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ a : Fin n→ℝ,(∀ i,0≤a i) → (∀ i,a i≤A) →
        ∀ z∈Icc (0:ℝ) 1,∀ F : List (WordLetter (Fin n)),F.length≤L →
          (∀ l∈F,l.bounded D) → inverseCount F≤1 → ∀ i,
            |wordExpected f hR j a z F i-wordPrediction j a z F i|≤C/(n:ℝ) := by
  obtain ⟨f,R,hR,lo,hi,C0,N0,hRv,hlo,hhi,hlo0,hf,hfr,hC0,hN0,hbase⟩ := actual_path_bias hj hA hs
  subst R lo hi
  let R := 2*sqrt j+1+1
  have hD0 : 0≤D := zero_le_one.trans hD
  let B : NNReal := ⟨actualWordBound f R j A D,(actualWordBound_pos f hR hj.le hA.le hD0).le⟩
  have hB1 : (1:ℝ)≤B := by
    have hh := path_constants_nonneg f hR hj.le hA.le
    change 1≤1+R+D+pathBound f R j A+pathLip f R j A
    linarith
  obtain ⟨CM,hCM,hmarked⟩ := wordMarkedCost_uniform B j R A (pathRate j A) L
  obtain ⟨CL,hCL,hlead⟩ := finite_cost_bound (wordLeadingCost j B) L
  let Cbase := CM+(L:ℝ)*CL+D^L*C0+1
  have hCb : 0≤Cbase := by dsimp [Cbase];positivity
  obtain ⟨N1,hsize⟩ := eventually_atTop.mp (path_size_eventually hs)
  let C := wordBiasConstant L j ((B:ℝ)^L) Cbase L+1
  have hC : 0<C := by
    have hh := wordBiasConstant_nonneg L hj.le (pow_nonneg B.coe_nonneg L) hCb L
    dsimp [C]
    linarith
  refine ⟨f,R,hR,C,max N0 (N1+1),rfl,hf,hfr,hC,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro n hn a ha haA z hz F hlen hF hI i
  have hn0 : 0<n := lt_of_lt_of_le hN0 ((le_max_left _ _).trans hn)
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn0
  have hnr : (1:ℝ)≤n := by exact_mod_cast hn0
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn0
  have haD : ∀ i,|a i|≤D := fun i=>(abs_of_nonneg (ha i)).trans_le ((haA i).trans hAD)
  have hbnd (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (_hGI : inverseCount G≤1) (u : Fin n) :
      |wordExpected f hR j a z G u|≤(B:ℝ)^L := by
    exact (wordExpected_abs_bound f hR hj.le hA.le hD0 ha haA hz G hG u).trans
      (pow_le_pow_right₀ hB1 hGlen)
  have hbas (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (hGI : inverseCount G≤1) (hGO : ordinaryCount G=0) (u : Fin n) :
      |wordExpected f hR j a z G u-wordDiagonal G u|≤Cbase/(n:ℝ) := by
    have hh := word_base_bias f hR j a z G u hGO hGI hD hG (div_nonneg hC0.le hnpos.le)
      (hbase n ((le_max_left _ _).trans hn) a ha haA z hz u)
    apply hh.trans
    have hpow := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hD hGlen) hC0.le
    have hc : D^G.length*C0≤Cbase := by
      dsimp [Cbase]
      nlinarith [mul_nonneg (Nat.cast_nonneg L) hCL]
    simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hc hnpos.le
  have hloop (G : List (WordLetter (Fin n))) (hGlen : G.length≤L)
      (hG : ∀ l∈G,l.bounded D) (_hGI : inverseCount G≤1) (hGO : ordinaryCount G≠0) (u : Fin n) :
      |wordExpected f hR j a z G u-wordRecursionValue j a z (wordExpected f hR j a z) G u|≤Cbase/(n:ℝ) := by
    cases hsplit : firstNoiseSplit G with
    | none => exact False.elim (hGO ((firstNoiseSplit_none G).mp hsplit))
    | some pq =>
      rcases pq with ⟨P,Q⟩
      have he := firstNoiseSplit_some G P Q hsplit
      have hP : ∀ l∈P,l.bounded D := fun l hl=>hG l (by rw [he];exact List.mem_append_left _ hl)
      have hQ : ∀ l∈Q,l.bounded D := fun l hl=>hG l (by rw [he];exact List.mem_append_right _ (List.mem_cons_of_mem _ hl))
      have hlenPQ : P.length+1+Q.length≤L := by simpa [he,List.length_append,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hGlen
      have herr := hsize n (by have hh := (le_max_right N0 (N1+1)).trans hn;omega)
      have hh := actualWord_expected_recursion hn0 f hj hA hD0 hs hf herr ha haA haD hz P Q hP hQ u
      rw [wordRecursionValue_split f hR j a z G P Q u hsplit,he]
      apply hh.trans
      have hmc := hmarked z hz P.length (by omega) Q.length (by omega)
      have hlc := wordRecursionAtCost_uniform hz hCL L hlead a P Q hlenPQ
      have hcost : wordMarkedCost B j R A (pathRate j A) z P.length Q.length+
          wordRecursionAtCost j B z a P Q≤Cbase := by
        dsimp [Cbase]
        have hh0 : 0≤D^L*C0 := by positivity
        linarith
      exact div_le_div_of_nonneg_right hcost hnpos.le
  have hh := word_bias_induction hj.le (pow_nonneg B.coe_nonneg L) hCb hnr hz a haD L
    (wordExpected f hR j a z) hbnd hbas hloop L F hlen hF hI
    ((show ordinaryCount F≤F.length from List.countP_le_length).trans hlen) i
  apply hh.trans
  exact div_le_div_of_nonneg_right (by dsimp [C];linarith) hnpos.le
end SKGap
end
end

end OAI
