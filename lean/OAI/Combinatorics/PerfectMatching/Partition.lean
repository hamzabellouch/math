import OAI.Combinatorics.PerfectMatching.EntropyUpper
import OAI.Combinatorics.PerfectMatching.DyadicEntropy

namespace OAI

universe u_1 u_2

section

noncomputable section
open Finset
namespace MatchingEntropy

variable {I : Type*} [Fintype I]

def expSum (a : I → ℝ) : ℝ := ∑ i, Real.exp (a i)
def expLaw (a : I → ℝ) (i : I) : ℝ := Real.exp (a i)/expSum a

lemma expSum_pos [Nonempty I] (a : I → ℝ) : 0<expSum a :=
  sum_pos (fun i _ => Real.exp_pos (a i)) univ_nonempty

lemma expLaw_simplex [Nonempty I] (a : I → ℝ) : expLaw a∈probabilitySimplex I := by
  refine ⟨fun i => (div_pos (Real.exp_pos _) (expSum_pos a)).le,?_⟩
  simp only [expLaw,←sum_div]
  exact div_self (expSum_pos a).ne'

lemma log_expLaw [Nonempty I] (a : I → ℝ) (i : I) :
    Real.log (expLaw a i)=a i-Real.log (expSum a) := by
  rw [expLaw,Real.log_div (Real.exp_ne_zero _) (expSum_pos a).ne',Real.log_exp]

lemma expLaw_cross [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) :
    -(∑ i,p i*Real.log (expLaw a i))=Real.log (expSum a)-∑ i,p i*a i := by
  simp only [log_expLaw,mul_sub,sum_sub_distrib,←sum_mul,hp.2,one_mul]
  ring

lemma expSum_variational_le [Nonempty I] (a : I → ℝ) {p : I → ℝ}
    (hp : p∈probabilitySimplex I) : entropy p+∑ i,p i*a i≤Real.log (expSum a) := by
  have hh := entropy_le_crossEntropy (expLaw_simplex a) hp
    (fun i hi => False.elim ((div_pos (Real.exp_pos _) (expSum_pos a)).ne' hi))
  rw [expLaw_cross a hp] at hh
  linarith

lemma expSum_variational_eq [Nonempty I] (a : I → ℝ) :
    entropy (expLaw a)+∑ i,expLaw a i*a i=Real.log (expSum a) := by
  rw [entropy_eq,expLaw_cross a (expLaw_simplex a)]
  ring

namespace LooplessGraph
variable {V : Type u_1} {E : Type u_2} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def score (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) : ℝ :=
  ∑ e∈M.val,β e

def weightedZ (G : LooplessGraph V E) (β : E → ℝ) : ℝ :=
  expSum (fun M => Real.log 2*G.score β M)

omit [Fintype V] [DecidableEq V] in
lemma score_indicator (G : LooplessGraph V E) (β : E → ℝ) (M : G.Matching) :
    G.score β M=∑ e, β e*G.indicator M e := by
  simp [score,indicator]

omit [Fintype V] [DecidableEq V] in
lemma mean_score (G : LooplessGraph V E) (β : E → ℝ) (p : G.Matching → ℝ) :
    (∑ M,p M*G.score β M)=∑ e,β e*G.mean p e := by
  simp only [score_indicator,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro e _
  simp only [mean,mul_sum]
  apply sum_congr rfl; intro M _; ring

omit [Fintype V] [DecidableEq V] in
lemma complement_entropy_le_mass (G : LooplessGraph V E) {x : E → ℝ}
    (hx : x∈G.polytope) : entropy (fun e => 1-x e)≤∑ e,x e := by
  apply sum_le_sum; intro e _
  have hh := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr (G.coordinate_mem_Icc hx e).2)
  simpa only [sub_sub_cancel] using hh

lemma entropy_binary_scale (G : LooplessGraph V E) (hPM : Nonempty G.Matching)
    {r : ℕ} (hV : Fintype.card V=2*r) {x : E → ℝ} (hx : x∈G.polytope) :
    entropy x/Real.log 2-4*(Fintype.card V:ℝ)≤ maxMatchingEntropy G x/Real.log 2 ∧
    maxMatchingEntropy G x/Real.log 2≤entropy x/Real.log 2+(Fintype.card V:ℝ) := by
  have hl := separable_lower G hPM x hx
  have hu := maxMatchingEntropy_le_binary G x hx
  have hc := G.complement_entropy_le_mass hx
  rw [G.marginal_sum hV hx] at hc
  have hv : (Fintype.card V:ℝ)=2*(r:ℝ) := by exact_mod_cast hV
  have hlog := BinaryMatching.Algorithm.half_le_log_two
  have hr : (0:ℝ)≤r := by positivity
  have hprod := mul_le_mul_of_nonneg_right hlog hr
  dsimp only [separableLower,binaryEntropy] at hl hu
  constructor
  · apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [sub_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith
  · apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
    rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne',hv]
    nlinarith

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_le (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) {x : E → ℝ} (hx : x∈G.polytope) :
    maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e≤Real.log (G.weightedZ β)/Real.log 2 := by
  obtain ⟨p,hp,hh⟩ := maxMatchingEntropy_attained G hx
  have h := expSum_variational_le (fun M => Real.log 2*G.score β M) hp.1
  have he : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*x e) := by
    rw [mul_sum]
    conv_lhs => arg 2; ext M; rw [mul_left_comm]
    rw [←mul_sum,G.mean_score,hp.2,mul_sum]
  rw [he,hh] at h
  apply (le_div_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  calc
    _ = maxMatchingEntropy G x+Real.log 2*(∑ e,β e*x e) := by
      rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
    _ ≤ _ := h

omit [Fintype V] [DecidableEq V] in
lemma weighted_variational_attained (G : LooplessGraph V E) [Nonempty G.Matching]
    (β : E → ℝ) : ∃ x∈G.polytope,
      Real.log (G.weightedZ β)/Real.log 2≤ maxMatchingEntropy G x/Real.log 2+∑ e,β e*x e := by
  let p := expLaw (fun M => Real.log 2*G.score β M)
  have hp := expLaw_simplex (fun M => Real.log 2*G.score β M)
  have hpx : p∈G.feasibleLaws (G.mean p) := ⟨hp,rfl⟩
  refine ⟨G.mean p,(G.mem_polytope_iff _).mpr ⟨p,hpx⟩,?_⟩
  have he := expSum_variational_eq (fun M => Real.log 2*G.score β M)
  have he' : (∑ M,p M*(Real.log 2*G.score β M))=Real.log 2*(∑ e,β e*G.mean p e) := by
    calc
      _ = Real.log 2*(∑ M,p M*G.score β M) := by
        rw [mul_sum]; apply sum_congr rfl; intro M _; ring
      _ = _ := by rw [G.mean_score]
  change entropy p+(∑ M,p M*(Real.log 2*G.score β M))=Real.log (G.weightedZ β) at he
  rw [he'] at he
  apply (div_le_iff₀ BinaryMatching.Algorithm.log_two_pos).2
  have hH := entropy_le_maxMatchingEntropy G hpx
  calc
    _ ≤ maxMatchingEntropy G (G.mean p)+Real.log 2*(∑ e,β e*G.mean p e) := by linarith
    _ = _ := by rw [add_mul,div_mul_cancel₀ _ BinaryMatching.Algorithm.log_two_pos.ne']; ring
end LooplessGraph
end MatchingEntropy
end
end

end OAI
