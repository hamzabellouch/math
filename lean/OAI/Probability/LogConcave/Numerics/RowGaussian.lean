import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.SlotTransformAddShift
import OAI.Probability.LogConcave.Numerics.Forward
import OAI.Probability.LogConcave.Numerics.RowTape
import OAI.Probability.LogConcave.Dynamics.AbsorbFixed

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler
open scoped Classical BigOperators

variable {d k : ℕ}

def rowGaussian (a : Fin k → ℝ) (τ ρ n : ℝ) :
    (Fin k → Point d) × (Fin 1 → Point d) → Point d :=
  fun z => n⁻¹ • ((∑i,a i • (τ • z.1 i))+ρ • z.2 0)

lemma measurable_rowGaussian (a : Fin k → ℝ) (τ ρ n : ℝ) :
    Measurable (rowGaussian (d:=d) a τ ρ n) := by
  unfold rowGaussian; fun_prop

theorem rowGaussian_law (a : Fin k → ℝ) (τ ρ n : ℝ) (hn : n≠0)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2) :
    ((Measure.pi fun _ : Fin k => stdGaussian (Point d)).prod
      (Measure.pi fun _ : Fin 1 => stdGaussian (Point d))).map (rowGaussian a τ ρ n)=
      stdGaussian (Point d) := by
  let w : Fin (k+1) → ℝ := Fin.append (fun i => a i*τ) (fun _ => ρ)
  have hw : (∑i,w i^2)=n^2 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_pow,←Finset.sum_mul,
      Fin.sum_univ_one]
    nlinarith only [hv]
  have hsum := weighted_gaussian_law (E:=Point d) w n hw
  have he (z : (Fin k → Point d) × (Fin 1 → Point d)) :
      (∑i,w i • Fin.append z.1 z.2 i)=(∑i,a i • (τ • z.1 i))+ρ • z.2 0 := by
    simp only [w,Fin.sum_univ_add,Fin.append_left,Fin.append_right,mul_smul,Fin.sum_univ_one]
  have hh := congrArg (Measure.map (fun z : Point d => n⁻¹ • z)) hsum
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at hh
  have hright : (fun z : Point d => n⁻¹ • z) ∘ (fun z => n • z)=id := by
    funext z; simp [smul_smul,hn]
  rw [hright,Measure.map_id] at hh
  rw [←(appendSlots_preserving (stdGaussian (Point d)) k 1).map_eq,
    Measure.map_map (by fun_prop) (appendSlots_preserving (stdGaussian (Point d)) k 1).measurable] at hh
  simp only [Function.comp_def,he] at hh
  exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d k : ℕ}

theorem compileTerms_squared (V : Point d → ℝ) (hV : Measurable (firstOrderReply V))
    {D τ ρ n : ℝ} (hD : 0<D) (hn : n≠0) (a r K S B : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d)
    (b : X → Point d) (hb : Measurable b) (x : X) (c m : Fin k → Point d)
    (hv : ρ^2+τ^2*(∑i,a i^2)=n^2)
    (hK : ∀i,0≤K i) (hvshift : ∀i,(∑j,(M i).shift j^2)≤D^2)
    (hshift : ∀i,ShiftInvariant (r i) (M i).shift (fun c g => (M i).program.run V (c,g)))
    (hLip : ∀i u v g,‖(M i).program.run V (u,g)-(M i).program.run V (v,g)‖≤K i*‖u-v‖)
    (hC : ∀i,SquaredAt (Measure.pi fun _ : Fin (C i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((C i).eval V x) (fun g => c i+(r i/(2*D)) • g) (S i))
    (hM : ∀i,SquaredAt (Measure.pi fun _ : Fin (M i).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) (fun g => (M i).program.run V (c i,g)) (fun g => m i+τ • g) (B i)) :
    SquaredAt (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileTerms D k a C M (.noise b hb ρ)).eval V x)
      (fun g => (∑i,a i • m i)+b x+n • g)
      ((∑i,|a i|)*(∑i,|a i| * (2*(K i)^2*S i+2*B i))) := by
  let γ := stdGaussian (Point d)
  let A i := fun z : (Fin (C i).slots → Point d) × (Fin (M i).slots → Point d) =>
    (M i).program.run V ((C i).eval V x z.1,(M i).damping D z.2)
  have hcmeas (i) : Measurable ((C i).eval V x) :=
    ((C i).measurable_eval V hV).comp (measurable_const.prodMk measurable_id)
  have hameas (i) : Measurable (A i) :=
    ((M i).program.measurable_run V hV).comp
      (((hcmeas i).comp measurable_fst).prodMk ((M i).measurable_damping D |>.comp measurable_snd))
  have ha (i) : SquaredAt
      ((Measure.pi fun _ : Fin (C i).slots => γ).prod (Measure.pi fun _ : Fin (M i).slots => γ)) γ
      (A i) (fun g => m i+τ • g) (2*(K i)^2*S i+2*B i) :=
    SquaredAt.absorb_fixed _ _ (hcmeas i) (c i) (m i) hD (hK i) (M i).shift (hvshift i)
      (fun c g => (M i).program.run V (c,g)) ((M i).program.measurable_run V hV)
      (hshift i) (hLip i) (hC i) (hM i)
  have hrow := SquaredAt.weighted_pi _ _ A (fun i g => m i+τ • g) hameas
    (by intro; fun_prop) a (fun i => 2*(K i)^2*S i+2*B i) ha
  have hfrow : Measurable (fun z : RowTape C M => ∑i,a i • A i (z i)) := by fun_prop
  have hgrow : Measurable (fun z : Fin k → Point d => ∑i,a i • (m i+τ • z i)) := by fun_prop
  have hext := hrow.common_noise hfrow hgrow (Measure.pi fun _ : Fin 1 => γ)
    (fun z => b x+ρ • z 0) (by fun_prop)
  have hout : Measurable ((compileTerms D k a C M (.noise b hb ρ)).eval V x) :=
    ((compileTerms D k a C M (.noise b hb ρ)).measurable_eval V hV).comp
      (measurable_const.prodMk measurable_id)
  have hfin := hext.reindex (concatTerms D k a C M (.noise b hb ρ)) (rowGaussian a τ ρ n)
    (concatTerms_preserving D k a C M (.noise b hb ρ)).measurable
    (measurable_rowGaussian a τ ρ n) _ (fun g => (∑i,a i • m i)+b x+n • g) hout (by fun_prop)
    (by intro z; exact eval_concatTerms V D k a C M (.noise b hb ρ) x z)
    (by
      intro z
      dsimp only [rowGaussian]
      rw [smul_smul,mul_inv_cancel₀ hn,one_smul]
      simp only [smul_add,Finset.sum_add_distrib]
      abel)
  have hcmap : Measure.map (concatTerms D k a C M (.noise b hb ρ))
      ((Measure.pi fun i => (Measure.pi fun _ : Fin (C i).slots => γ).prod
        (Measure.pi fun _ : Fin (M i).slots => γ)).prod (Measure.pi fun _ : Fin 1 => γ))=
      (Measure.pi fun _ : Fin (compileTerms D k a C M (.noise b hb ρ)).slots => γ) :=
    (concatTerms_preserving D k a C M (.noise b hb ρ)).map_eq
  have hgmap : Measure.map (rowGaussian a τ ρ n)
      ((Measure.pi fun _ : Fin k => γ).prod (Measure.pi fun _ : Fin 1 => γ))=γ :=
    rowGaussian_law a τ ρ n hn hv
  rw [hcmap,hgmap] at hfin
  exact hfin
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DeclaredValid (D A : ℝ) (P : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ a r C,n => 0<n ∧ (∑i,|a i|)≤A ∧
      ∀i,P (r i) (declaredNoise n A) ∧ DeclaredValid D A P (C i) (r i/(2*D))

def declaredError (F : Point d → ℝ) (D A : ℝ) (K : ℝ → ℝ → ℝ)
    (B : ℝ → ℝ → Point d → ℝ) : MeanTree X d → ℝ → X → ℝ
  | .node _ _ _ a r C,n,x => (∑i,|a i|)*(∑i,|a i| *
      (2*(K (r i) (declaredNoise n A))^2 * declaredError F D A K B (C i) (r i/(2*D)) x+
       2*B (r i) (declaredNoise n A) ((C i).eval F x)))

theorem compileDeclared_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A : ℝ} (hD : 0<D) (hA : 0<A)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (hK : ∀r τ,P r τ → 0≤K r τ)
    (hvshift : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hshift : ∀r τ,P r τ → ShiftInvariant r (M r τ).shift (fun c g => (M r τ).program.run V (c,g)))
    (hLip : ∀r τ,P r τ → ∀u v g,‖(M r τ).program.run V (u,g)-(M r τ).program.run V (v,g)‖≤K r τ*‖u-v‖)
    (hM : ∀r τ,P r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredValid D A P E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclared D A M E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclared D A M E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredError F D A K B E n x) := by
  induction E generalizing n with
  | node k b hb a r C ih =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := ih i (r i/(2*D)) (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K (r i) (declaredNoise n A))
      (fun i => declaredError F D A K B (C i) (r i/(2*D)) x)
      (fun i => B (r i) (declaredNoise n A) ((C i).eval F x))
      (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hA n a hw)
      (fun i => hK _ _ (hc i).1) (fun i => hvshift _ _ (hc i).1)
      (fun i => hshift _ _ (hc i).1) (fun i => hLip _ _ (hc i).1) hi
      (fun i => hM _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory ProbabilityTheory OracleCompiler Coupling SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DeclaredRootValid (D A Af : ℝ) (Pf Pi : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ a r C,n => 0<n ∧ (∑i,|a i|)≤Af ∧
      ∀i,Pf (r i) (declaredNoise n Af) ∧ DeclaredValid D A Pi (C i) (r i/(2*D))

def declaredRootError (F : Point d → ℝ) (D A Af : ℝ) (Kf Ki : ℝ → ℝ → ℝ)
    (Bf Bi : ℝ → ℝ → Point d → ℝ) : MeanTree X d → ℝ → X → ℝ
  | .node _ _ _ a r C,n,x => (∑i,|a i|)*(∑i,|a i| *
      (2*(Kf (r i) (declaredNoise n Af))^2 * declaredError F D A Ki Bi (C i) (r i/(2*D)) x+
       2*Bf (r i) (declaredNoise n Af) ((C i).eval F x)))

theorem compileDeclaredRoot_squared (F V : Point d → ℝ)
    (hV : Measurable (firstOrderReply V)) {D A Af : ℝ} (hD : 0<D) (hA : 0<A) (hAf : 0<Af)
    (P : Bool → ℝ → ℝ → Prop) (M : Bool → ℝ → ℝ → SeedProgram d)
    (K : Bool → ℝ → ℝ → ℝ) (B : Bool → ℝ → ℝ → Point d → ℝ)
    (hK : ∀s r τ,P s r τ → 0≤K s r τ)
    (hvshift : ∀s r τ,P s r τ → (∑j,(M s r τ).shift j^2)≤D^2)
    (hshift : ∀s r τ,P s r τ → ShiftInvariant r (M s r τ).shift (fun c g => (M s r τ).program.run V (c,g)))
    (hLip : ∀s r τ,P s r τ → ∀u v g,‖(M s r τ).program.run V (u,g)-(M s r τ).program.run V (v,g)‖≤K s r τ*‖u-v‖)
    (hM : ∀s r τ,P s r τ → ∀c,SquaredAt
      (Measure.pi fun _ : Fin (M s r τ).slots => stdGaussian (Point d)) (stdGaussian (Point d))
      (fun g => (M s r τ).program.run V (c,g)) (fun g => primitiveExpectedField F c r+τ • g) (B s r τ c))
    (E : MeanTree X d) (n : ℝ) (x : X) (hE : DeclaredRootValid D A Af (P true) (P false) E n) :
    SquaredAt (Measure.pi fun _ : Fin (compileDeclaredRoot D A Af (M true) (M false) E n).slots => stdGaussian (Point d))
      (stdGaussian (Point d)) ((compileDeclaredRoot D A Af (M true) (M false) E n).eval V x)
      (fun g => E.eval F x+n • g) (declaredRootError F D A Af (K true) (K false) (B true) (B false) E n x) := by
  cases E with | node k b hb a r C =>
    obtain ⟨hn,hw,hc⟩ := hE
    have hi (i) := compileDeclared_squared F V hV hD hA (P false) (M false) (K false) (B false)
      (hK false) (hvshift false) (hshift false) (hLip false) (hM false) (C i) (r i/(2*D)) x (hc i).2
    have hh := compileTerms_squared V hV hD hn.ne' a r
      (fun i => K true (r i) (declaredNoise n Af))
      (fun i => declaredError F D A (K false) (B false) (C i) (r i/(2*D)) x)
      (fun i => B true (r i) (declaredNoise n Af) ((C i).eval F x))
      (fun i => compileDeclared D A (M false) (C i) (r i/(2*D)))
      (fun i => M true (r i) (declaredNoise n Af)) b hb x
      (fun i => (C i).eval F x) (fun i => primitiveExpectedField F ((C i).eval F x) (r i))
      (declaredReserve_variance hAf n a hw)
      (fun i => hK _ _ _ (hc i).1) (fun i => hvshift _ _ _ (hc i).1)
      (fun i => hshift _ _ _ (hc i).1) (fun i => hLip _ _ _ (hc i).1) hi
      (fun i => hM _ _ _ (hc i).1 _)
    have he : (fun g => (node k b hb a r C).eval F x+n • g)=
        (fun g => (∑i,a i • primitiveExpectedField F ((C i).eval F x) (r i))+b x+n • g) := by
      funext g
      simp only [eval,add_comm (b x)]
    rw [he]
    exact hh
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma centers_mono {P Q : ℝ → (X → Point d) → Prop} (E : MeanTree X d)
    (h : ∀r b,P r b → Q r b) (hE : centers P E) : centers Q E := by
  induction E with | node k b hb a r C ih =>
    intro i
    exact ⟨h _ _ (hE i).1,ih i (hE i).2⟩

omit [MeasurableSpace X] in
lemma DirectCenter.radius {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0≤r) (_hT0 : 0≤T) (_hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) :
    r*Real.sqrt (1-T^2)≤r' ∧ r'≤r := by
  obtain ⟨ρ,hρ,θ,hθ,rfl,hb⟩ := hb
  have hρsq : ρ^2≤T^2 := pow_le_pow_left₀ hρ.1 hρ.2 2
  have hlo := Real.sqrt_le_sqrt (show 1-T^2≤1-ρ^2 by linarith)
  have hhi : Real.sqrt (1-ρ^2)≤1 := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by norm_num,by nlinarith [sq_nonneg ρ]⟩
  exact ⟨mul_le_mul_of_nonneg_left hlo hr,(mul_le_mul_of_nonneg_left hhi hr).trans_eq (mul_one r)⟩

omit [MeasurableSpace X] in
lemma DirectCenter.radius_pos {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0<r) (hT0 : 0≤T) (hT1 : T<1)
    (hb : DirectCenter r T v x Y G r' b) : 0<r' := by
  have ht : 0<1-T^2 := by nlinarith
  exact lt_of_lt_of_le (mul_pos hr (Real.sqrt_pos.mpr ht)) (hb.radius hr.le hT0 hT1).1

omit [MeasurableSpace X] in
lemma oriented_norm (Y G : X → Point d) (θ : ℝ) (z : X) :
    ‖oriented Y G θ z‖≤‖Y z‖+|θ| *‖G z‖ := by
  apply (norm_add_le _ _).trans
  simp only [norm_smul,Real.norm_eq_abs]
  have hc := mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg (Y z))
  have hs := mul_le_mul_of_nonneg_right (Real.abs_sin_le_abs (x:=θ)) (norm_nonneg (G z))
  linarith

omit [MeasurableSpace X] in
lemma DirectCenter.norm_displacement {r T v r' : ℝ} {x Y G b : X → Point d}
    (hr : 0≤r) (_hT0 : 0≤T) (hT1 : T≤1)
    (hb : DirectCenter r T v x Y G r' b) (z : X) :
    ‖b z-x z‖≤r*(‖Y z‖+v*‖G z‖) := by
  obtain ⟨ρ,hρ,θ,hθ,hr',rfl⟩ := hb
  simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_mul,
    abs_of_nonneg hr,abs_of_nonneg hρ.1]
  have hY : ‖oriented Y G θ z‖≤‖Y z‖+v*‖G z‖ :=
    by
      have h := oriented_norm Y G θ z
      have hmul := mul_le_mul_of_nonneg_right hθ (norm_nonneg (G z))
      linarith
  have hρ1 := hρ.2.trans hT1
  exact (mul_le_mul_of_nonneg_left hY (mul_nonneg hr hρ.1)).trans
    (by nlinarith [mul_nonneg hr (show 0≤‖Y z‖+v*‖G z‖ by
      have hv := (abs_nonneg θ).trans hθ
      positivity)])

def rootScales (P : ℝ → Prop) : MeanTree X d → Prop
  | .node _ _ _ _ r _ => ∀i,P (r i)

@[simp] lemma rootScales_anchor (P : ℝ → Prop) (b : X → Point d) (hb : Measurable b) :
    rootScales P (anchor b hb) := by intro i; exact Fin.elim0 i
@[simp] lemma rootScales_scale (P : ℝ → Prop) (c : ℝ) (E : MeanTree X d) :
    rootScales P (scale c E) ↔ rootScales P E := by cases E; rfl
lemma rootScales_add (P : ℝ → Prop) (E B : MeanTree X d)
    (hE : rootScales P E) (hB : rootScales P B) : rootScales P (add E B) := by
  cases E with | node k b hb a r C =>
    cases B with | node l c hc v s D =>
      intro i
      exact Fin.addCases (fun j => by simpa [add] using hE j)
        (fun j => by simpa [add] using hB j) i
lemma rootScales_sumFin (P : ℝ → Prop) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,rootScales P (E i)) : rootScales P (sumFin k E) := by
  induction k with
  | zero => exact rootScales_anchor _ _ _
  | succ k ih => exact rootScales_add P _ _ (hE 0) (ih _ (fun i => hE i.succ))
lemma rootScales_sumFamily {I : Type*} [Fintype I] (P : ℝ → Prop)
    (E : I → MeanTree X d) (hE : ∀i,rootScales P (E i)) : rootScales P (sumFamily E) :=
  rootScales_sumFin P _ _ (fun _ => hE _)

lemma meanCircuit_final_radius (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (xE yE : MeanTree X d)
    (G : X → Point d) (hG : Measurable G) :
    rootScales (fun r' => r'=r*Real.sqrt (1-T^2))
      (meanCircuit r T h ψ s n m N nc Nc e xE yE (anchor G hG)) := by
  apply rootScales_add
  · exact (rootScales_scale _ _ _).2 (rootScales_anchor _ _ _)
  · apply rootScales_sumFamily
    intro j
    apply (rootScales_scale _ _ _).2
    intro i
    rfl

lemma declaredValid_of_radius_bounds {D A lo hi n : ℝ} (hD : 0<D) (hlo : 0<lo)
    (P : ℝ → ℝ → Prop) (E : MeanTree X d) (hw : weight E≤A) (hC : centersBound A E)
    (hscale : centers (fun r _ => lo≤r ∧ r≤hi) E)
    (hn : lo/(2*D)≤n ∧ n≤hi/(2*D))
    (hP : ∀r q,lo≤r → r≤hi → lo/(2*D)≤q → q≤hi/(2*D) → P r (declaredNoise q A)) :
    DeclaredValid D A P E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    refine ⟨lt_of_lt_of_le (div_pos hlo (by positivity)) hn.1,hw,?_⟩
    intro i
    refine ⟨hP _ _ (hscale i).1.1 (hscale i).1.2 hn.1 hn.2,?_⟩
    exact ih i (hC i).1 (hC i).2 (hscale i).2
      ⟨div_le_div_of_nonneg_right (hscale i).1.1 (by positivity),
       div_le_div_of_nonneg_right (hscale i).1.2 (by positivity)⟩

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def centerValues (F : Point d → ℝ) (Q : ℝ) : MeanTree X d → X → Prop
  | .node _ _ _ _ _ C,z => ∀i,circuitD F ((C i).eval F z)≤Q ∧ centerValues F Q (C i) z

lemma child_depth_le (k : ℕ) (b : X → Point d) (hb : Measurable b)
    (a r : Fin k → ℝ) (C : Fin k → MeanTree X d) (i : Fin k) :
    depth (C i)+1≤depth (.node k b hb a r C) :=
  Finset.le_sup (f:=fun j => depth (C j)+1) (Finset.mem_univ i)

lemma centerValues_of_bounds {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (z : X) {A B : ℝ} (hB : 0≤B)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1) (M : ℕ)
    (E : MeanTree X d) (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (fun r b => 0≤r ∧ (lam:ℝ)*r^2≤1/2 ∧ (lam:ℝ)*r≤1 ∧
      circuitD F x+(lam:ℝ)*‖b z-x‖≤B) E) :
    centerValues F ((M:ℝ)*B) E z := by
  induction E with | node k b hm a r C ih =>
    intro i
    have hdi := (child_depth_le k b hm a r C i).trans hd
    have hdi' : ((depth (C i):ℝ)+1)≤(M:ℝ) := by exact_mod_cast hdi
    refine ⟨?_,ih i (hweights i).2 (by omega) (hc i).2⟩
    apply (eval_circuitD_bound hF x z hB hsmall (C i) (hweights i).1
      (hweights i).2 (hc i).1.2.2.2 (hc i).2).trans
    exact mul_le_mul_of_nonneg_right hdi' hB

omit [MeasurableSpace X] in
lemma directCenter_scalar_bounds {r T v r' : ℝ} {x Y G b : X → Point d}
    {lam : ℝ≥0} (hr : 0≤r) (hT : 0≤T) (hT1 : T<1)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hb : DirectCenter r T v x Y G r' b) :
    0≤r' ∧ (lam:ℝ)*r'^2≤1/2 ∧ (lam:ℝ)*r'≤1 := by
  have hrad := hb.radius hr hT hT1
  have hr' : 0≤r' := (mul_nonneg hr (Real.sqrt_nonneg _)).trans hrad.1
  exact ⟨hr',(mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr' hrad.2 2) lam.coe_nonneg).trans hl,
    (mul_le_mul_of_nonneg_left hrad.2 lam.coe_nonneg).trans hL⟩

theorem centerValues_of_direct {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T v A : ℝ} (hr : 0≤r) (hT : 0≤T) (hT1 : T<1) (hv : 0≤v)
    (hl : (lam:ℝ)*r^2≤1/2) (hL : (lam:ℝ)*r≤1)
    (hsmall : (lam:ℝ)*A*(2*Real.pi+2)≤1)
    (x Y G : X → Point d) (z : X) (M : ℕ) (E : MeanTree X d)
    (hweights : centersBound A E) (hd : depth E≤M)
    (hc : centers (DirectCenter r T v x Y G) E) :
    centerValues F ((M:ℝ)*(circuitD F (x z)+(lam:ℝ)*r*(‖Y z‖+v*‖G z‖))) E z := by
  apply centerValues_of_bounds hF (x z) z (by positivity [circuitD_nonneg F (x z)])
    hsmall M E hweights hd
  apply centers_mono E (fun r' b hb => ?_) hc
  have hs := directCenter_scalar_bounds hr hT hT1 hl hL hb
  refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
  have hdisp := mul_le_mul_of_nonneg_left (hb.norm_displacement hr hT hT1.le z) lam.coe_nonneg
  linarith
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def ErrorLimits (F : Point d → ℝ) (D A : ℝ) (K : ℝ → ℝ → ℝ)
    (B : ℝ → ℝ → Point d → ℝ) (L R : ℝ) : MeanTree X d → ℝ → X → Prop
  | .node _ _ _ _ r C,n,x => ∀i,
      (K (r i) (declaredNoise n A))^2≤L^2 ∧
      B (r i) (declaredNoise n A) ((C i).eval F x)≤R ∧
      ErrorLimits F D A K B L R (C i) (r i/(2*D)) x

theorem declaredError_uniform (F : Point d → ℝ) (D : ℝ) {A L R : ℝ}
    (_hA : 0≤A) (hR : 0≤R) (hc : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (B : ℝ → ℝ → Point d → ℝ)
    (E : MeanTree X d) (n : ℝ) (x : X) (hw : weight E≤A) (hweights : centersBound A E)
    (hE : ErrorLimits F D A K B L R E n x) :
    declaredError F D A K B E n x≤4*A^2*R := by
  induction E generalizing n with | node k b hb a r C ih =>
    have hchild (i : Fin k) := ih i (r i/(2*D)) (hweights i).1 (hweights i).2 (hE i).2.2
    have hterm (i : Fin k) :
        2*(K (r i) (declaredNoise n A))^2*declaredError F D A K B (C i) (r i/(2*D)) x+
          2*B (r i) (declaredNoise n A) ((C i).eval F x)≤2*L^2*(4*A^2*R)+2*R := by
      have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(K (r i) (declaredNoise n A))^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right (hE i).1 (show 0≤2*(4*A^2*R) by positivity)
      linarith [(hE i).2.1]
    have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
    rw [←Finset.sum_mul] at hsum
    have htot := mul_le_mul_of_nonneg_left hsum hs0
    change (∑i,|a i|)≤A at hw
    have hs := pow_le_pow_left₀ hs0 hw 2
    have hsq := mul_le_mul_of_nonneg_right hs (show 0≤2*L^2*(4*A^2*R)+2*R by positivity)
    have hcon := mul_le_mul_of_nonneg_right hc (show 0≤2*A^2*R by positivity)
    change (∑i,|a i|)*(∑i,|a i| *_)≤_
    nlinarith

theorem declaredRootError_bound (F : Point d → ℝ) (D A : ℝ) {Af L H e Q : ℝ}
    (hAf : 0<Af) (hH : 0≤H)
    (Kf Ki : ℝ → ℝ → ℝ) (Bf Bi : ℝ → ℝ → Point d → ℝ)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (n : ℝ) (x : X) (hw : (∑i,|a i|)≤Af)
    (hK : ∀i,(Kf (r i) (declaredNoise n Af))^2≤L^2)
    (hB : ∀i,Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤(declaredNoise n Af)^2*e^2*Q^2)
    (hchild : ∀i,declaredError F D A Ki Bi (C i) (r i/(2*D)) x≤H) :
    declaredRootError F D A Af Kf Ki Bf Bi (.node k b hb a r C) n x≤
      2*Af^2*L^2*H+n^2*e^2*Q^2/2 := by
  have hterm (i : Fin k) :
      2*(Kf (r i) (declaredNoise n Af))^2*declaredError F D A Ki Bi (C i) (r i/(2*D)) x+
        2*Bf (r i) (declaredNoise n Af) ((C i).eval F x)≤
      2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 := by
    have h₁ := mul_le_mul_of_nonneg_left (hchild i) (show 0≤2*(Kf (r i) (declaredNoise n Af))^2 by positivity)
    have h₂ := mul_le_mul_of_nonneg_right (hK i) (show 0≤2*H by positivity)
    linarith [hB i]
  have hs0 : 0≤∑i,|a i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hsum := Finset.sum_le_sum (s:=Finset.univ) (fun (i : Fin k) _ => mul_le_mul_of_nonneg_left (hterm i) (abs_nonneg (a i)))
  rw [←Finset.sum_mul] at hsum
  have htot := mul_le_mul_of_nonneg_left hsum hs0
  have hs := pow_le_pow_left₀ hs0 hw 2
  have hsq := mul_le_mul_of_nonneg_right hs
    (show 0≤2*L^2*H+2*(declaredNoise n Af)^2*e^2*Q^2 by positivity)
  have hid : Af^2*(declaredNoise n Af)^2=n^2/4 := by
    unfold declaredNoise
    field_simp [ne_of_gt hAf]
    ring
  change (∑i,|a i|)*(∑i,|a i| *_)≤_
  nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg Q)]
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma normalizedErrorLimits (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0≤r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X)
    (hs : centers (fun r _ => 0≤r ∧ r≤hi) E) (hc : centerValues F Q E x) :
    ErrorLimits F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2)
      L ((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2) E n x := by
  induction E generalizing n with | node k b hb a r C ih =>
    have ht0 : 0≤declaredNoise n A := by unfold declaredNoise; positivity
    have ht : declaredNoise n A≤declaredNoise (hi/(2*D)) A :=
      div_le_div_of_nonneg_right hhi (by positivity)
    intro i
    refine ⟨hK _ _ (hs i).1.1 (hs i).1.2 ht0 ht,?_,?_⟩
    · have hnoise := pow_le_pow_left₀ ht0 ht 2
      have hvalue := pow_le_pow_left₀ (circuitD_nonneg F _) (hc i).1 2
      exact mul_le_mul (mul_le_mul_of_nonneg_right hnoise (sq_nonneg e)) hvalue
        (sq_nonneg _) (by positivity)
    · exact ih i (div_nonneg (hs i).1.1 (by positivity))
        (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) (hs i).2 (hc i).2

theorem declaredError_normalized (F : Point d → ℝ) {D A hi n L e Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hn : 0≤n) (hhi : n≤hi/(2*D))
    (hcon : 4*A^2*L^2≤1)
    (K : ℝ → ℝ → ℝ) (hK : ∀r τ,0≤r → r≤hi → 0≤τ →
      τ≤declaredNoise (hi/(2*D)) A → (K r τ)^2≤L^2)
    (E : MeanTree X d) (x : X) (hw : weight E≤A) (hc : centersBound A E)
    (hs : centers (fun r _ => 0≤r ∧ r≤hi) E) (hv : centerValues F Q E x) :
    declaredError F D A K (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x≤
      (hi/(2*D))^2*e^2*Q^2 := by
  have he := declaredError_uniform F D hA.le (by positivity) hcon K
    (fun _ τ c => τ^2*e^2*(circuitD F c)^2) E n x hw hc
    (normalizedErrorLimits F hD hA hn hhi K hK E x hs hv)
  have hid : 4*A^2*((declaredNoise (hi/(2*D)) A)^2*e^2*Q^2)=
      (hi/(2*D))^2*e^2*Q^2 := by
    unfold declaredNoise
    field_simp [hA.ne',hD.ne']
    ring
  rwa [hid] at he

theorem declaredRootError_normalized (F : Point d → ℝ) {D A Af hi n Li Lf ei ef Q : ℝ}
    (hD : 0<D) (hA : 0<A) (hAf : 0<Af) (hcon : 4*A^2*Li^2≤1)
    (Ki Kf : ℝ → ℝ → ℝ)
    (hKi : ∀r τ,0≤r → r≤hi → 0≤τ → τ≤declaredNoise (hi/(2*D)) A → (Ki r τ)^2≤Li^2)
    (k : ℕ) (b : X → Point d) (hb : Measurable b) (a r : Fin k → ℝ)
    (C : Fin k → MeanTree X d) (x : X) (hw : (∑i,|a i|)≤Af)
    (hc : centersBound A (.node k b hb a r C))
    (hs : centers (fun r _ => 0≤r ∧ r≤hi) (.node k b hb a r C))
    (hv : centerValues F Q (.node k b hb a r C) x)
    (hKf : ∀i,(Kf (r i) (declaredNoise n Af))^2≤Lf^2) :
    declaredRootError F D A Af Kf Ki
      (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
      (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) (.node k b hb a r C) n x≤
      (2*Af^2*Lf^2*(hi/(2*D))^2*ei^2+n^2*ef^2/2)*Q^2 := by
  have hierr (i : Fin k) := declaredError_normalized F (e := ei) hD hA
    (div_nonneg (hs i).1.1 (by positivity))
    (div_le_div_of_nonneg_right (hs i).1.2 (by positivity)) hcon Ki hKi (C i) x
    (hc i).1 (hc i).2 (hs i).2 (hv i).2
  have he := declaredRootError_bound F D A hAf (by positivity) Kf Ki
    (fun _ τ c => τ^2*ef^2*(circuitD F c)^2)
    (fun _ τ c => τ^2*ei^2*(circuitD F c)^2) k b hb a r C n x hw hKf
    (fun i => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (circuitD_nonneg F _) (hv i).1 2) (by positivity)) hierr
  convert he using 1
  ring
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory OracleCompiler OracleCompiler.Expression SeedCompiler
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def DriftData : MeanTree X d → Type
  | .node k _ _ _ _ C => ℝ × ((i : Fin k) → DriftData (C i))

def DriftData.root : (E : MeanTree X d) → DriftData E → ℝ
  | .node ..,p => p.1

def DriftValid (f : Point d → X → X) : (E : MeanTree X d) → DriftData E → Prop
  | .node _ b _ _ _ C,p => (∀Δ x,b (f Δ x)=b x+p.1 • Δ) ∧ ∀i,DriftValid f (C i) (p.2 i)

def compileTermsShift (D : ℝ) : (k : ℕ) → (a : Fin k → ℝ) →
    (C : Fin k → Expression X d) → (M : Fin k → SeedProgram d) → (E : Expression X d) →
    ((i : Fin k) → Fin (C i).slots → ℝ) → ((i : Fin k) → Fin (M i).slots → ℝ) →
    (Fin E.slots → ℝ) → Fin (compileTerms D k a C M E).slots → ℝ
  | 0,_,_,_,_,_,_,w => w
  | k+1,a,C,M,E,u,v,w => Fin.append (u 0) (Fin.append (v 0)
      (compileTermsShift D k (fun i => a i.succ) (fun i => C i.succ) (fun i => M i.succ) E
        (fun i => u i.succ) (fun i => v i.succ) w))

lemma compileTerms_equivariant (D : ℝ) (k : ℕ) (a c : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (u : (i : Fin k) → Fin (C i).slots → ℝ) (v : (i : Fin k) → Fin (M i).slots → ℝ)
    (w : Fin E.slots → ℝ) (t : ℝ) (f : X → X) (Δ : Point d)
    (hC : ∀i,(C i).compile.Equivariant (moveSeed f (u i) Δ) (fun y => y+c i • Δ))
    (hM : ∀i,((M i).program.seedMap (fun z => (z.1,(M i).damping D z.2))
      (measurable_fst.prodMk (((M i).measurable_damping D).comp measurable_snd))).Equivariant
      (moveSeed (fun y => y+c i • Δ) (v i) Δ) id)
    (hE : E.compile.Equivariant (moveSeed f w Δ) (fun y => y+t • Δ)) :
    (compileTerms D k a C M E).compile.Equivariant
      (moveSeed f (compileTermsShift D k a C M E u v w) Δ) (fun y => y+t • Δ) := by
  induction k with
  | zero => exact hE
  | succ k ih =>
    exact add_equivariant (a 0) (C 0) _ (M 0).program _ _ f Δ (u 0) (v 0) _ (c 0) t
      (hC 0) (hM 0) (ih _ _ _ _ _ _ (fun i => hC i.succ) (fun i => hM i.succ))

lemma compileTermsShift_energy (D : ℝ) (k : ℕ) (a : Fin k → ℝ)
    (C : Fin k → Expression X d) (M : Fin k → SeedProgram d) (E : Expression X d)
    (u : (i : Fin k) → Fin (C i).slots → ℝ) (v : (i : Fin k) → Fin (M i).slots → ℝ)
    (w : Fin E.slots → ℝ) :
    (∑j,compileTermsShift D k a C M E u v w j^2)=
      (∑j,w j^2)+∑i,((∑j,u i j^2)+(∑j,v i j^2)) := by
  induction k with
  | zero =>
    change (∑j,w j^2)=(∑j,w j^2)+∑i : Fin 0,_
    simp
  | succ k ih =>
    change (∑j : Fin ((C 0).slots+((M 0).slots+(compileTerms D k (fun i => a i.succ)
      (fun i => C i.succ) (fun i => M i.succ) E).slots)),
      (Fin.append (u 0) (Fin.append (v 0) (compileTermsShift D k (fun i => a i.succ)
        (fun i => C i.succ) (fun i => M i.succ) E (fun i => u i.succ) (fun i => v i.succ) w)) j)^2)=_
    simp only [Fin.sum_univ_add,Fin.append_left,Fin.append_right,ih,Fin.sum_univ_succ]
    ring

def inverseChildShift (D r c : ℝ) (M : SeedProgram d) : Fin M.slots → ℝ :=
  fun i => (c/r)*slotTransform (inverseCoefficient (fun j => M.shift j/(2*D)))
    (fun j => M.shift j/(2*D)) M.shift i

def compileDeclaredShift (D A : ℝ) (M : ℝ → ℝ → SeedProgram d) :
    (E : MeanTree X d) → (n : ℝ) → DriftData E → Fin (compileDeclared D A M E n).slots → ℝ
  | .node k b hb a r C,n,p =>
    compileTermsShift D k a (fun i => compileDeclared D A M (C i) (r i/(2*D)))
      (fun i => M (r i) (declaredNoise n A)) (.noise b hb (declaredReserve n A a))
      (fun i => compileDeclaredShift D A M (C i) (r i/(2*D)) (p.2 i))
      (fun i => inverseChildShift D (r i) ((p.2 i).root (C i)) (M (r i) (declaredNoise n A)))
      (fun _ => 0)

def ShiftReady (D A : ℝ) (P : ℝ → ℝ → Prop) : MeanTree X d → ℝ → Prop
  | .node _ _ _ _ r C,n => ∀i,r i≠0 ∧ P (r i) (declaredNoise n A) ∧ ShiftReady D A P (C i) (r i/(2*D))

theorem compileDeclared_equivariant (D A : ℝ) (hD : 0<D)
    (P : ℝ → ℝ → Prop) (M : ℝ → ℝ → SeedProgram d)
    (hv : ∀r τ,P r τ → (∑j,(M r τ).shift j^2)≤D^2)
    (hM : ∀r τ,P r τ → ∀Δ,(M r τ).program.Equivariant
      (moveSeed (fun x => x+r • Δ) (M r τ).shift Δ) id)
    (f : Point d → X → X) (E : MeanTree X d) (n : ℝ) (p : DriftData E)
    (hp : DriftValid f E p)
    (hready : ShiftReady D A P E n) :
    ∀Δ,(compileDeclared D A M E n).compile.Equivariant
      (moveSeed (f Δ) (compileDeclaredShift D A M E n p) Δ) (fun y => y+p.root E • Δ) := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro Δ
    apply compileTerms_equivariant
    · intro i
      exact ih i (r i/(2*D)) (p.2 i) (hp.2 i) (hready i).2.2 Δ
    · intro i
      exact transformed_mean_equivariant (M (r i) (declaredNoise n A)).program
        (hready i).1 _ _
        ((normalized_shift_bound hD _ (hv _ _ (hready i).2.1)).trans_lt (by norm_num))
        (hM _ _ (hready i).2.1) ((p.2 i).root (C i)) Δ
    · exact noise_equivariant b hb _ p.1 (f Δ) Δ (hp.1 Δ)
end LogConcaveSampling.MeanTree

end

end

end OAI
