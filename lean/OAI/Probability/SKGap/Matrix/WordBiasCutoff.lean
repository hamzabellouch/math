import Mathlib
import OAI.Probability.SKGap.Matrix.WordBiasInduction
import OAI.Probability.SKGap.Stability.WordMeanSeminorm
import OAI.Probability.SKGap.Brownian.PathBiasCutoff

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix Real MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_uniform_bias_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ a : Fin n→ℝ,(∀ i,0≤a i) → (∀ i,a i≤A) →
        ∀ z∈Icc (0:ℝ) 1,∀ F : List (WordLetter (Fin n)),F.length≤L →
          (∀ l∈F,l.bounded D) → inverseCount F≤1 → ∀ i,
            |wordExpected f hR j a z F i-wordPrediction j a z F i|≤C/(n:ℝ) := by
  obtain ⟨C0,N0,hC0,hN0,hbase⟩ := actual_path_bias_of_cutoff hj hA hs f hf hR
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
  refine ⟨C,max N0 (N1+1),hC,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
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

section
noncomputable section
namespace SKGap
open Matrix Real Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix.Norms.Frobenius SchwartzMap Topology

theorem actual_word_simultaneous_prediction_of_cutoff {j A D : ℝ} (hj : 0<j) (hA : 0<A)
    (hs : sqrt j*A<1) (hD : 1≤D) (hAD : A≤D) (L : ℕ) (f : 𝓢(ℝ,ℂ))
    (hf : ∀ x∈Icc ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A)),f x=(x:ℂ)⁻¹)
    (hR : 0≤2*sqrt j+1+1) :
    ∃ (C : ℝ) (N : ℕ),0<C ∧ 0<N ∧
      ∀ n,N≤n → ∀ p : Bool,
        (Measure.pi (fun _ : MatrixCoordinates (Fin n)=>gaussianReal 0 1))
        {g | ∃ (a : Fin n→ℝ) (F : List (WordLetter (Fin n))),
          (∀ i,a i∈Icc 0 A) ∧ F.length≤L ∧ (∀ l∈F,l.bounded D) ∧ inverseCount F≤1 ∧
          C< matrixWordSeminorm p
            (actualWord f (2*sqrt j+1+1) hR j a 1 F (goeMatrix (j/n) g)-Matrix.diagonal (wordPrediction j a 1 F))} ≤
          (wordPatternSet L L).card*ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  obtain ⟨Cb,N,hCb,hN,hbias⟩ := actual_word_uniform_bias_of_cutoff hj hA hs hD hAD L f hf hR
  let R := 2*sqrt j+1+1
  obtain ⟨C0,hC0,hchain⟩ := all_actualWords_gaussian_chaining f hR hj.le hA (lt_of_lt_of_le zero_lt_one hD) L
  refine ⟨C0+Cb,N,by positivity,hN,?_⟩
  intro n hn p
  have hn0 : 1≤n := (Nat.succ_le_iff.mpr hN).trans hn
  apply (measure_mono ?_).trans (hchain n hn0 p)
  intro g hg
  obtain ⟨a,F,ha,hFL,hF,hFI,hg⟩ := hg
  refine ⟨a,F,ha,hFL,hF,?_⟩
  have hb : matrixWordSeminorm p (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))≤Cb := by
    cases p with
    | false =>
      exact diagonalSeminorm_diagonal_bound hn0 hCb.le
        (hbias n hn a (fun i=>(ha i).1) (fun i=>(ha i).2) 1 ⟨zero_le_one,le_rfl⟩ F hFL hF hFI)
    | true =>
      change offDiagonalSeminorm (Matrix.diagonal _)≤Cb
      rw [offDiagonalSeminorm_diagonal]
      exact hCb.le
  have hdecomp := actualWord_diagonal_prediction_decompose (j:=j) f hR a 1 F g
  simp only [Fintype.card_fin] at hdecomp
  rw [hdecomp] at hg
  have hh := matrixWordSeminorm_add p
    (matrixCentered (fun x : EuclideanSpace ℝ (MatrixCoordinates (Fin n))=>
      actualWord f R hR j a 1 F (goeMatrix (j/n) x)) (WithLp.toLp 2 g))
    (Matrix.diagonal (fun i=>wordExpected f hR j a 1 F i-wordPrediction j a 1 F i))
  linarith
end SKGap
end
end

end OAI
