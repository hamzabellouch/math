import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.FunctionGramMatrix
import OAI.Probability.CriticalPercolation.Criticality.PairedSparseScales
import OAI.Probability.CriticalPercolation.Growth.WordLengthGeometry
import OAI.Probability.CriticalPercolation.Harmonic.PolynomialHarmonicSpace
import OAI.Probability.CriticalPercolation.Growth.WordBallPacking

namespace OAI

section
noncomputable section
open scoped Classical Pointwise BigOperators Matrix

namespace CriticalPercolation.HarmonicAnalysis
variable {A ι : Type*} [Group A] [Fintype ι]

omit [Group A] in
lemma functionCombination_eq_linearCombination (v : ι → A → ℝ) (a : ι → ℝ) :
    functionCombination v a = Fintype.linearCombination ℝ v a := by
  funext x
  simp only [functionCombination,Fintype.linearCombination_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

namespace WordGeometry
variable (W : WordGeometry A)

lemma exists_posDef_functionGram (v : ι → A → ℝ) (hv : LinearIndependent ℝ v) :
    ∃ n₀ : ℕ, ∀ n≥n₀, (functionGram (W.ball n) v).PosDef := by
  let f := Fintype.linearCombination ℝ v
  obtain ⟨n₀,hn₀⟩ := exists_detecting_ball (fun n => (W.ball n:Set A))
    (fun i j h => W.ball_mono h) W.exists_mem_ball f.range
  refine ⟨n₀,?_⟩
  intro n hn
  apply functionGram_posDef
  intro a ha
  have hzero : f a=0 := by
    have hh := hn₀ ⟨f a,⟨a,rfl⟩⟩ (fun x hx => by
      change f a x=0
      rw [←functionCombination_eq_linearCombination]
      exact ha x (W.ball_mono hn hx))
    exact congrArg Subtype.val hh
  exact hv.fintypeLinearCombination_injective (by simpa only [map_zero] using hzero)

lemma gram_sparse_product_growth (d k : ℕ) (hg : SparseGrowth.HasDegree W.generators d)
    (v : ι → A → ℝ) (hv : ∀ i, W.HasPolynomialGrowth k (v i)) (n₀ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R, ∃ n≥R,
      ((W.ball (max n n₀)).card:ℝ)^(Fintype.card ι) *
          (functionGram (W.ball (max n n₀)) v).det ≤
        C*(n:ℝ)^((Fintype.card ι)*(2*d+2*k)) := by
  obtain ⟨C,hC⟩ := hg
  obtain ⟨M,hM,hvM⟩ := W.finite_family_growth_bound k v hv
  let m := Fintype.card ι
  let D : ℝ := (m.factorial:ℝ)*((C:ℝ)*M^2)^m
  refine ⟨(C:ℝ)^m*D,by dsimp [D]; positivity,?_⟩
  intro R
  obtain ⟨n,hn,hvn⟩ := hC (max R (max n₀ 1))
  have hnR : R ≤ n := by omega
  have hn₀ : n₀ ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hvol : ((W.ball n).card:ℝ) ≤ (C:ℝ)*(n:ℝ)^d := by exact_mod_cast hvn
  have hbase : ((W.ball n).card:ℝ)*(M*(n:ℝ)^k)^2 ≤
      ((C:ℝ)*M^2)*(n:ℝ)^(d+2*k) := by
    calc
      _ ≤ ((C:ℝ)*(n:ℝ)^d)*(M*(n:ℝ)^k)^2 :=
        mul_le_mul_of_nonneg_right hvol (sq_nonneg _)
      _ = _ := by rw [mul_pow,←pow_mul,pow_add]; ring_nf
  have hdet : (functionGram (W.ball n) v).det ≤ D*(n:ℝ)^(m*(d+2*k)) := by
    calc
      _ ≤ |(functionGram (W.ball n) v).det| := le_abs_self _
      _ ≤ (m.factorial:ℝ)*(((W.ball n).card:ℝ)*(M*(n:ℝ)^k)^2)^m :=
        functionGram_det_bound _ _ _ (mul_nonneg hM (by positivity)) (hvM n hn1)
      _ ≤ (m.factorial:ℝ)*(((C:ℝ)*M^2)*(n:ℝ)^(d+2*k))^m :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase m) (by positivity)
      _ = _ := by
        rw [mul_pow,←pow_mul (n:ℝ),Nat.mul_comm (d+2*k) m]
        dsimp [D]
        ring
  refine ⟨n,hnR,?_⟩
  rw [max_eq_left hn₀]
  calc
    _ ≤ ((W.ball n).card:ℝ)^m*(D*(n:ℝ)^(m*(d+2*k))) :=
      mul_le_mul_of_nonneg_left hdet (by positivity)
    _ ≤ ((C:ℝ)*(n:ℝ)^d)^m*(D*(n:ℝ)^(m*(d+2*k))) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hvol m)
        (by dsimp [D]; positivity)
    _ = _ := by
      rw [mul_pow,←pow_mul]
      calc
        _ = ((C:ℝ)^m*D)*((n:ℝ)^(d*m)*(n:ℝ)^(m*(d+2*k))) := by ring
        _ = _ := by rw [←pow_add]; congr 2; ring

theorem function_gram_paired_scales (d k : ℕ) (hg : SparseGrowth.HasDegree W.generators d)
    (v : ι → A → ℝ) (hv : ∀ i, W.HasPolynomialGrowth k (v i))
    (hli : LinearIndependent ℝ v) (hm : 0 < Fintype.card ι)
    (L : ℕ) (hL : 0 < L) (N : ℕ) :
    ∃ r R : ℕ, N ≤ r ∧ 1 ≤ R ∧ 6*r ≤ R ∧ 10^(2*L)*r ≤ R ∧
      (W.ball (7*r)).card ≤ 10^(4*(2*d+2*k+1))*(W.ball r).card ∧
      (functionGram (W.ball (5*R)) v).det ≤
        ((10:ℝ)^(4*(2*d+2*k+1)))^(Fintype.card ι)*(functionGram (W.ball R) v).det ∧
      (W.ball (R+r)).card ≤ (10^(4*(2*d+2*k+1)))^L*(W.ball r).card ∧
      (functionGram (W.ball R) v).PosDef := by
  obtain ⟨n₀,hn₀⟩ := W.exists_posDef_functionGram v hli
  let V : ℕ → ℝ := fun n => (W.ball (max n n₀)).card
  let D : ℕ → ℝ := fun n => (functionGram (W.ball (max n n₀)) v).det
  have hV : Monotone V := by
    intro i j hij
    dsimp [V]
    exact_mod_cast Finset.card_le_card (W.ball_mono (max_le_max hij (le_refl n₀)))
  have hD : Monotone D := by
    intro i j hij
    exact functionGram_det_mono (W.ball_mono (max_le_max hij le_rfl)) v
      (hn₀ _ (le_max_right _ _))
  have hVp : ∀ n, 0 < V n := by intro n; dsimp [V]; exact_mod_cast W.ball_card_pos (max n n₀)
  have hDp : ∀ n, 0 < D n := fun n => (hn₀ _ (le_max_right _ _)).det_pos
  obtain ⟨C,hC,hpoly⟩ := W.gram_sparse_product_growth d k hg v hv n₀
  obtain ⟨r,R,hr,hR,hrR,hscale,hvr,hdr,hvR⟩ := paired_sparse_scales V D hV hD hVp hDp
    (Fintype.card ι) (2*d+2*k) hm C hC hpoly L hL (max N n₀)
  have hr₀ : n₀ ≤ r := by omega
  have hR₀ : n₀ ≤ R := by omega
  simp only [V,D,max_eq_left hr₀,max_eq_left hR₀,
    max_eq_left (show n₀ ≤ 7*r by omega),max_eq_left (show n₀ ≤ 5*R by omega),
    max_eq_left (show n₀ ≤ R+r by omega)] at hvr hdr hvR
  refine ⟨r,R,by omega,hR,hrR,hscale,?_,hdr,?_,hn₀ R hR₀⟩
  · exact_mod_cast hvr
  · exact_mod_cast hvR

end WordGeometry
end CriticalPercolation.HarmonicAnalysis
end
end

end OAI
