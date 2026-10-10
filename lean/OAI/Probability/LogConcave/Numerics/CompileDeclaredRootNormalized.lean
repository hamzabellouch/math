import Mathlib
import OAI.Probability.LogConcave.Numerics.CentersBoundPicard
import OAI.Probability.LogConcave.Numerics.CompileDeclaredRootShift
import OAI.Probability.LogConcave.OraclePrograms.TerminalMeanProgram

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

theorem compileDeclaredRoot_normalized (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hLi : 0≤Li) (hLf : 0≤Lf)
    (hcon : 4*A^2*Li^2≤1)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift
      (fun c g => (M s r τ).program.run V (c,g)))
    (henergy : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hLipi : ∀r τ,P false r τ → ∀u v g,
      ‖(M false r τ).program.run V (u,g)-(M false r τ).program.run V (v,g)‖≤Li*‖u-v‖)
    (hLipf : ∀r τ,P true r τ → ∀u v g,
      ‖(M true r τ).program.run V (u,g)-(M true r τ).program.run V (v,g)‖≤Lf*‖u-v‖)
    (hMi : ∀r τ,P false r τ → ∀c,SquaredAt (gaussianTape d (M false r τ).slots)
      (stdGaussian (Point d)) (fun g => (M false r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ei^2*(circuitD F c)^2))
    (hMf : ∀r τ,P true r τ → ∀c,SquaredAt (gaussianTape d (M true r τ).slots)
      (stdGaussian (Point d)) (fun g => (M true r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (τ^2*ef^2*(circuitD F c)^2))
    (E : MeanTree X d) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n)
    (hc : centersBound A E) (hs : centers (fun r _ => 0≤r ∧ r≤hi) E)
    (hv : centerValues F Q E x) :
    SquaredAt (gaussianTape d (compileDeclaredRoot D A Af (M true) (M false) E n).slots)
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g)
      ((2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2) := by
  let K : Bool → ℝ → ℝ → ℝ := fun s _ _ => if s then Lf else Li
  let B : Bool → ℝ → ℝ → Point d → ℝ := fun s _ τ c =>
    τ^2*(if s then ef else ei)^2*(circuitD F c)^2
  have hK : ∀s r τ,P s r τ → 0≤K s r τ := by
    intro s r τ _; cases s <;> assumption
  have hLip : ∀s r τ,P s r τ → ∀u v g,
      ‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖ := by
    intro s; cases s; exact hLipi; exact hLipf
  have hM : ∀s r τ,P s r τ → ∀c,SquaredAt (gaussianTape d (M s r τ).slots)
      (stdGaussian (Point d)) (fun g => (M s r τ).program.run V (c,g))
      (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c) := by
    intro s; cases s; exact hMi; exact hMf
  have hh := compileDeclaredRoot_squared F V hV hD hA hAf P M K B
    hK henergy hshift hLip hM E n x hE
  apply hh.mono
  cases E with | node k b hb a r C =>
    exact declaredRootError_normalized F hD hA hAf hcon (K false) (K true)
      (fun _ _ _ _ _ _ => le_rfl) k b hb a r C x hE.2.1 hc hs hv (fun _ => le_rfl)
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma forward_weights {r T h P A : ℝ} (hr : 0≤r) (hP : 0≤P) (n N : ℕ)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|probabilityWeight T h n i j|≤P)
    (x y : MeanTree X d) (hxw : weight x=0)
    (hx : centersBound A x) (hy : centersBound A y)
    (hA : r*(weight y+P*r)≤A) (i : ProbabilityNode T h n) :
    weight (forward r T h n N x y i)≤weight y+P*r ∧
      centersBound A (forward r T h n N x y i) := by
  have hc (j : ProbabilityNode T h n) (E : MeanTree X d) :
      weight (scale (-r) (conditional r (probabilityNodeTime T h n j) x E))≤r := by
    simp [abs_of_nonneg hr]
  constructor
  · exact weight_picard _ _ _ hr hw hc N i
  · apply centersBound_picard _ _ _ hP hr hw hc (fun _ => le_rfl) (fun _ => hy) ?_ N i
    intro j E hE hEb
    apply (centersBound_scale _ _ _).2
    apply centersBound_conditional hx hEb
    rw [hxw,zero_add,abs_mul,abs_of_nonneg hr]
    calc
      r*|probabilityNodeTime T h n j| * weight E≤r*weight E := by
        nlinarith [weight_nonneg E,mul_le_mul_of_nonneg_left (ht j) hr]
      _≤r*(weight y+P*r) := mul_le_mul_of_nonneg_left hE hr
      _≤A := hA

lemma literalSample_weights {r T h P A Af : ℝ} (hr : 0<r) (hP : 0≤P)
    (hT : 1/2≤T) (n N : ℕ) (e : ProbabilityNode T h n)
    (ht : ∀j : ProbabilityNode T h n,|probabilityNodeTime T h n j|≤1)
    (hw : ∀i,∑j,|probabilityWeight T h n i j|≤P)
    (hPA : P≤A) (hPf : 2*P≤Af) :
    weight (literalSample (d:=d) r T h n N e)≤Af*r ∧
      centersBound (A*r^2) (literalSample (d:=d) r T h n N e) := by
  have hT0 : 0<T := by linarith
  have hTi : |T⁻¹|≤2 := by
    rw [abs_of_pos (inv_pos.mpr hT0)]
    exact (inv_le_comm₀ hT0 (by norm_num)).mpr (by simpa using hT)
  have hf := forward_weights (d:=d) (X:=SampleInput d) hr.le hP n N ht hw
    (anchor Prod.fst (by fun_prop)) (anchor Prod.snd (by fun_prop)) (by simp) (by simp) (by simp)
    (show r*(weight (anchor (Prod.snd : SampleInput d → Point d) (by fun_prop))+P*r)≤A*r^2 by
      simp only [weight_anchor,zero_add]
      nlinarith [mul_le_mul_of_nonneg_right hPA (sq_nonneg r)]) e
  constructor
  · dsimp only [literalSample]
    rw [weight_scale]
    have h0 := weight_nonneg (forward r T h n N (anchor (Prod.fst : SampleInput d → Point d) (by fun_prop)) (anchor Prod.snd (by fun_prop)) e)
    simp only [weight_anchor,zero_add] at hf
    nlinarith [mul_le_mul_of_nonneg_right hPf hr.le]
  · exact (centersBound_scale _ _ _).2 hf.2

lemma literalMean_weights {r T h ψ σ P H Q S B A Af : ℝ}
    (hr : 0<r) (hσ : 0<σ) (hT : |T|≤1)
    (hP : 0≤P) (hH : 0≤H) (hQ : 0≤Q) (hS : 0≤S) (hB : 0≤B)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (ht : ∀j : ProbabilityNode T h (n+1),|probabilityNodeTime T h (n+1) j|≤1)
    (hpw : ∀a i,∑j,|reanchorWeight (probabilityWeight T h (n+1)) a i j|≤P)
    (hhw : ∀k : Fin (m+1),∀i,∑j,|harmonicWeight (n+1) (ψ*angleNodes m k) i j|≤H)
    (hqw : ∑j,|terminalQuadratureWeight T h n j|≤Q)
    (hsw : (∑j : Fin (m+1),|derivativeWeight (angleNodes m) j/ψ|)≤S)
    (hcw : ∀i,∑j,|centeringWeight nc i j|≤B)
    (hout : ∑j,|Quadrature.weight (probabilityNodes nc) j 0 1|≤B)
    (hA₁ : 2*B*(Q*S*P+2)≤A) (hA₂ : 2*P+H≤A) (hAf : B≤Af) :
    weight (literalMean (d:=d) r T h ψ σ n m N nc Nc e)≤Af ∧
      centersBound (A*(r/σ+r^2)) (literalMean (d:=d) r T h ψ σ n m N nc Nc e) := by
  have hbound : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)≤A*(r/σ+r^2) := by
    have h₁ := mul_le_mul_of_nonneg_right hA₁ (show 0≤r/σ by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hA₂ (sq_nonneg r)
    have he : r*(B*((Q*S*P+2)/(σ/2))+(2*P+H)*r)=
        (2*B*(Q*S*P+2))*(r/σ)+(2*P+H)*r^2 := by field_simp
    rw [he]
    nlinarith
  have hh := meanCircuit_weights (d:=d) (X:=MeanInput d) hr (by positivity : 0<σ/2) hT
    hP hH hQ hS hB n m N nc Nc e ht hpw hhw hqw hsw hcw hout
    (anchor Prod.fst (by fun_prop)) (anchor (fun z => z.2.1) (by fun_prop))
    (anchor (fun z => z.2.2) (by fun_prop)) (by simp) (by simp) (by simp) (by simp)
    (by simpa only [weight_anchor,zero_add] using hbound)
  simp only [weight_anchor,mul_zero,zero_add] at hh
  exact ⟨hh.1.trans hAf,hh.2⟩
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma DeclaredValid.shiftReady {D A : ℝ} (P : ℝ → ℝ → Prop)
    (hp : ∀r τ,P r τ → r≠0) (E : MeanTree X d) (n : ℝ)
    (he : DeclaredValid D A P E n) : ShiftReady D A P E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro i
    exact ⟨hp _ _ (he.2.2 i).1,(he.2.2 i).1,ih i _ (he.2.2 i).2⟩

lemma DeclaredRootValid.shiftReady {D A Af : ℝ} (Pf Pi : ℝ → ℝ → Prop)
    (hpf : ∀r τ,Pf r τ → r≠0) (hpi : ∀r τ,Pi r τ → r≠0)
    (E : MeanTree X d) (n : ℝ) (he : DeclaredRootValid D A Af Pf Pi E n) :
    RootShiftReady D A Af Pf Pi E n := by
  cases E with | node k b hb a r C =>
    intro i
    exact ⟨hpf _ _ (he.2.2 i).1,(he.2.2 i).1,
      (he.2.2 i).2.shiftReady Pi hpi (C i) (r i/(2*D))⟩

lemma declaredRootValid_of_radius_bounds {D A Af lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (Pf Pi : ℝ → ℝ → Prop) (E : MeanTree X d) (hn : 0<n)
    (hw : weight E≤Af) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo≤r ∧ r≤hi) E)
    (hfinal : rootScales (fun r => Pf r (declaredNoise n Af)) E)
    (hPi : ∀r q,lo≤r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → Pi r (declaredNoise q A)) :
    DeclaredRootValid D A Af Pf Pi E n := by
  cases E with | node k b hb a r C =>
    refine ⟨hn,hw,?_⟩
    intro i
    refine ⟨hfinal i,?_⟩
    exact declaredValid_of_radius_bounds hD hlo Pi (C i) (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩ hPi
end LogConcaveSampling.MeanTree

end

end

end OAI
