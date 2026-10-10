import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Expression
import OAI.Probability.LogConcave.Numerics.MeanTree
import OAI.Probability.LogConcave.OraclePrograms.SeedProgram

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def childNoise (n w : ℝ) : ℝ := n/(2*(w+1))

def reserve (n w : ℝ) {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  Real.sqrt (n^2-(childNoise n w)^2*∑i,a i^2)

def compileTerms (D : ℝ) : (k : ℕ) → (Fin k → ℝ) → (Fin k → Expression X d) →
    (Fin k → SeedProgram d) → Expression X d → Expression X d
  | 0,_,_,_,E => E
  | k+1,a,C,M,E =>
    .add (a 0) (C 0) (M 0).slots (M 0).calls (M 0).program
      ((M 0).damping D) ((M 0).measurable_damping D)
      (compileTerms D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E)

def compile (D : ℝ) (M : ℝ → ℝ → SeedProgram d) : MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    let w := ∑i,|a i|
    compileTerms D k a (fun i => compile D M (C i) (r i/(2*D)))
      (fun i => M (r i) (childNoise n w)) (.noise b hb (reserve n w a))

def compileRoot (D : ℝ) (Mfinal Minternal : ℝ → ℝ → SeedProgram d) :
    MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    let w := ∑i,|a i|
    compileTerms D k a (fun i => compile D Minternal (C i) (r i/(2*D)))
      (fun i => Mfinal (r i) (childNoise n w)) (.noise b hb (reserve n w a))

lemma calls_compileTerms (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    (compileTerms D k a C M E).calls=E.calls+∑i,((C i).calls+(M i).calls) := by
  induction k with
  | zero => simp [compileTerms]
  | succ k ih =>
    simp only [compileTerms,Expression.calls,ih,Fin.sum_univ_succ]
    omega

lemma slots_compileTerms (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d) :
    (compileTerms D k a C M E).slots=E.slots+∑i,((C i).slots+(M i).slots) := by
  induction k with
  | zero => simp [compileTerms]
  | succ k ih =>
    simp only [compileTerms,Expression.slots,ih,Fin.sum_univ_succ]
    omega

lemma calls_compile (D : ℝ) (M : ℝ → ℝ → SeedProgram d)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) :
    (compile D M (.node k b hb a r C) n).calls=
      ∑i,((compile D M (C i) (r i/(2*D))).calls+(M (r i) (childNoise n (∑j,|a j|))).calls) := by
  simp only [compile,calls_compileTerms,Expression.calls,zero_add]

lemma slots_compile (D : ℝ) (M : ℝ → ℝ → SeedProgram d)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) :
    (compile D M (.node k b hb a r C) n).slots=
      1+∑i,((compile D M (C i) (r i/(2*D))).slots+(M (r i) (childNoise n (∑j,|a j|))).slots) := by
  simp only [compile,slots_compileTerms,Expression.slots]

theorem compile_query_cap (D : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d)
    (E : MeanTree X d) (n : ℝ) :
    ∃q : ℕ,∃P : Program (X × (Fin (compileRoot D Mf Mi E n).slots → Point d)) d q (Point d),
      ∀V x z,P.run V (x,z)=(compileRoot D Mf Mi E n).eval V x z := by
  exact ⟨_,(compileRoot D Mf Mi E n).compile,(compileRoot D Mf Mi E n).compile_run⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

lemma coefficient_energy {k : ℕ} (a : Fin k → ℝ) :
    (∑i,a i^2)≤(∑i,|a i|)^2 := by
  simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
    (s:=Finset.univ) (fun i _ => abs_nonneg (a i))

lemma childNoise_energy {k : ℕ} (n : ℝ) (a : Fin k → ℝ) :
    (childNoise n (∑i,|a i|))^2*(∑i,a i^2)≤n^2/4 := by
  let w := ∑i,|a i|
  have hw : 0≤w := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hs : (∑i,a i^2)≤(w+1)^2 := (coefficient_energy a).trans (by dsimp only [w] at *; nlinarith)
  have hpos : 0<(2*(w+1))^2 := by positivity
  change (n/(2*(w+1)))^2*(∑i,a i^2)≤n^2/4
  rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ hpos]
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg n)
  nlinarith

lemma reserve_nonneg (n w : ℝ) {k : ℕ} (a : Fin k → ℝ) : 0≤reserve n w a :=
  Real.sqrt_nonneg _

lemma reserve_variance {k : ℕ} (n : ℝ) (a : Fin k → ℝ) :
    (reserve n (∑i,|a i|) a)^2+(childNoise n (∑i,|a i|))^2*(∑i,a i^2)=n^2 := by
  have h := childNoise_energy n a
  rw [reserve,Real.sq_sqrt (by nlinarith [sq_nonneg n])]
  ring

lemma reserve_positive {k : ℕ} {n : ℝ} (hn : 0<n) (a : Fin k → ℝ) :
    0<reserve n (∑i,|a i|) a := by
  apply Real.sqrt_pos.mpr
  have h := childNoise_energy n a
  nlinarith [sq_pos_of_pos hn]

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem weighted_gaussian_law (a : ι → ℝ) (n : ℝ) (ha : (∑i,a i^2)=n^2) :
    (Measure.pi fun _ : ι => stdGaussian E).map (fun g => ∑i,a i • g i)=
      (stdGaussian E).map (fun z => n • z) := by
  let S : (ι → E) →L[ℝ] E := ∑i,a i • ContinuousLinearMap.proj i
  let T : E →L[ℝ] E := n • ContinuousLinearMap.id ℝ E
  have hS (g : ι → E) : S g=∑i,a i • g i := by simp [S]
  have hT0 (z : E) : T z=n • z := by simp [T]
  simp_rw [←hS,←hT0]
  change (Measure.pi fun _ : ι => stdGaussian E).map S=(stdGaussian E).map T
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_map,charFunDual_pi]
  have hL (i : ι) : (L.comp S).comp (ContinuousLinearMap.single ℝ (fun _ : ι => E) i)=a i • L := by
    ext z
    simp only [ContinuousLinearMap.comp_apply, hS, map_sum, map_smul, ContinuousLinearMap.single_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [Pi.single_eq_of_ne hji]
    · simp
  have hT : L.comp T=n • L := by ext z; simp [T]
  simp_rw [hL,hT,charFunDual_stdGaussian]
  rw [←Complex.exp_sum]
  simp only [norm_smul,Real.norm_eq_abs]
  congr 1
  norm_cast
  simp only [mul_pow,sq_abs,←Finset.sum_div,Finset.sum_neg_distrib,←Finset.sum_mul,ha]

theorem reserve_gaussian_law {k : ℕ} (n : ℝ) (a : Fin k → ℝ) :
    (Measure.pi fun _ : Fin (k+1) => stdGaussian E).map
      (fun g => reserve n (∑i,|a i|) a • g 0+
        ∑i,a i • (childNoise n (∑j,|a j|) • g i.succ))=
      (stdGaussian E).map (fun z => n • z) := by
  let c : Fin (k+1) → ℝ := Fin.cons (reserve n (∑i,|a i|) a)
    (fun i => a i*childNoise n (∑j,|a j|))
  have hc : (∑i,c i^2)=n^2 := by
    simp only [c,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_pow,←Finset.sum_mul]
    rw [mul_comm (∑i,a i^2)]
    exact reserve_variance n a
  have he (g : Fin (k+1) → E) : (∑i,c i • g i)=
      reserve n (∑i,|a i|) a • g 0+∑i,a i • (childNoise n (∑j,|a j|) • g i.succ) := by
    simp only [c,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_smul]
  simpa only [he] using weighted_gaussian_law (E:=E) c n hc
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def declaredNoise (n A : ℝ) : ℝ := n/(2*A)
def declaredReserve (n A : ℝ) {k : ℕ} (a : Fin k → ℝ) : ℝ :=
  Real.sqrt (n^2-(declaredNoise n A)^2*∑i,a i^2)

def compileDeclared (D A : ℝ) (M : ℝ → ℝ → SeedProgram d) :
    MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    compileTerms D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))

def compileDeclaredRoot (D A Af : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d) :
    MeanTree X d → ℝ → Expression X d
  | .node k b hb a r C,n =>
    compileTerms D k a (fun i => compileDeclared D A Mi (C i) (r i/(2*D)))
      (fun i => Mf (r i) (declaredNoise n Af)) (.noise b hb (declaredReserve n Af a))

lemma declaredNoise_energy {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) : (declaredNoise n A)^2*(∑i,a i^2)≤n^2/4 := by
  have hw : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have he := (coefficient_energy a).trans (pow_le_pow_left₀ hw ha 2)
  change (n/(2*A))^2*(∑i,a i^2)≤n^2/4
  rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ (by positivity : 0<(2*A)^2)]
  have hm := mul_le_mul_of_nonneg_left he (sq_nonneg n)
  nlinarith

lemma declaredReserve_variance {k : ℕ} {A : ℝ} (hA : 0<A) (n : ℝ) (a : Fin k → ℝ)
    (ha : (∑i,|a i|)≤A) :
    (declaredReserve n A a)^2+(declaredNoise n A)^2*(∑i,a i^2)=n^2 := by
  have he := declaredNoise_energy hA n a ha
  rw [declaredReserve,Real.sq_sqrt (by nlinarith [sq_nonneg n])]
  ring

lemma declaredReserve_positive {k : ℕ} {A n : ℝ} (hA : 0<A) (hn : 0<n)
    (a : Fin k → ℝ) (ha : (∑i,|a i|)≤A) : 0<declaredReserve n A a := by
  apply Real.sqrt_pos.mpr
  have he := declaredNoise_energy hA n a ha
  nlinarith [sq_pos_of_pos hn]

lemma calls_compileDeclared (D A : ℝ) (M : ℝ → ℝ → SeedProgram d)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) :
    (compileDeclared D A M (.node k b hb a r C) n).calls=
      ∑i,((compileDeclared D A M (C i) (r i/(2*D))).calls+(M (r i) (declaredNoise n A)).calls) := by
  simp only [compileDeclared,calls_compileTerms,Expression.calls,zero_add]

theorem compileDeclared_program (D A Af : ℝ) (Mf Mi : ℝ → ℝ → SeedProgram d)
    (E : MeanTree X d) (n : ℝ) :
    ∃q : ℕ,∃P : Program (X × (Fin (compileDeclaredRoot D A Af Mf Mi E n).slots → Point d)) d q (Point d),
      ∀V x z,P.run V (x,z)=(compileDeclaredRoot D A Af Mf Mi E n).eval V x z := by
  exact ⟨_,(compileDeclaredRoot D A Af Mf Mi E n).compile,
    (compileDeclaredRoot D A Af Mf Mi E n).compile_run⟩
end LogConcaveSampling.MeanTree

end

end

end OAI
