import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.TerminalMeanEquivariant
import OAI.Probability.LogConcave.OraclePrograms.SampleParentEquivariant
import OAI.Probability.LogConcave.OraclePrograms.CircuitParameters

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def scalarPicard (k : ℕ) (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => a
  | N+1 => a+k*f (scalarPicard k f a N)

def vectorPicard (k : ℕ) (f : ℕ × ℕ → ℕ × ℕ) (a : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => a
  | N+1 => (a.1+k*(f (vectorPicard k f a N)).1,a.2+k*(f (vectorPicard k f a N)).2)

lemma cost_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    (f : ℕ → ℕ) (a₀ : ℕ) (hφ : ∀i E,cost (φ i E)=f (cost E))
    (ha : ∀i,cost (a i)=a₀) (N : ℕ) (i : I) :
    cost (picard w φ a N i)=scalarPicard (Fintype.card I) f a₀ N := by
  induction N generalizing i with
  | zero => exact ha i
  | succ N ih => simp only [picard,cost_add,cost_sumFamily,cost_scale,hφ,ih,ha,
      Finset.sum_const,Finset.card_univ,smul_eq_mul,scalarPicard]

lemma cost_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) (f : ℕ × ℕ → ℕ × ℕ)
    (hφ : ∀p,(cost (φ p).1,cost (φ p).2)=f (cost p.1,cost p.2)) (N : ℕ) (i : I) :
    (cost (pairPicard w φ a N i).1,cost (pairPicard w φ a N i).2)=
      vectorPicard (Fintype.card I) f (cost a.1,cost a.2) N := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    have hp (j : I) := hφ (pairPicard w φ a N j)
    simp_rw [ih] at hp
    have hp₁ j := congrArg Prod.fst (hp j)
    have hp₂ j := congrArg Prod.snd (hp j)
    dsimp only at hp₁ hp₂
    apply Prod.ext <;> simp only [pairPicard,cost_add,cost_sumFamily,cost_scale,
      hp₁,hp₂,Finset.sum_const,
      Finset.card_univ,smul_eq_mul,vectorPicard]

def flowWork (k N x y : ℕ) : ℕ := scalarPicard k (fun z => 1+x+z) y N

def kernelWork (p q N x y g : ℕ) : ℕ :=
  p*(1+x+flowWork p N x (flowWork q N x (flowWork p N x y+g)))

def velocityWork (p q m N x : ℕ) (z : ℕ × ℕ) : ℕ × ℕ :=
  (p*(m+1)*kernelWork p q N x z.1 z.2,2+2*x+z.1)

def meanWork (p q m N nc Nc x y g : ℕ) : ℕ :=
  g+(nc+1)*(1+x+(vectorPicard (nc+1) (velocityWork p q m N x) (y,g) Nc).1)

lemma cost_probability (r T h : ℝ) (n N : ℕ) (s i : ProbabilityNode T h n) (x y : MeanTree X d) :
    cost (probability r T h n N s x y i)=flowWork (Fintype.card (ProbabilityNode T h n)) N (cost x) (cost y) := by
  exact cost_picard _ _ _ _ _ (fun _ _ => by simp) (fun _ => rfl) N i

lemma cost_forward (r T h : ℝ) (n N : ℕ) (i : ProbabilityNode T h n) (x y : MeanTree X d) :
    cost (forward r T h n N x y i)=flowWork (Fintype.card (ProbabilityNode T h n)) N (cost x) (cost y) := by
  exact cost_picard _ _ _ _ _ (fun _ _ => by simp) (fun _ => rfl) N i

lemma cost_harmonic (r ρ θ : ℝ) (n N : ℕ) (i : Fin (n+1)) (x y g : MeanTree X d) :
    cost (harmonic r ρ θ n N x y g i)=flowWork (n+1) N (cost x) (cost y+cost g) := by
  simpa only [Fintype.card_fin,harmonic,flowWork] using cost_picard (harmonicWeight n θ) _ _ (fun z => 1+cost x+z)
    (cost y+cost g) (fun _ _ => by simp) (fun _ => by simp) N i

lemma cost_kernelCorrection (r T h θ : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) :
    cost (kernelCorrection r T h θ n N s e x y g)=
      kernelWork (Fintype.card (ProbabilityNode T h n)) (n+1) N (cost x) (cost y) (cost g) := by
  simp only [kernelCorrection,cost_sumFamily,cost_scale,cost_conditional,cost_probability,
    cost_harmonic,Finset.sum_const,Finset.card_univ,smul_eq_mul,kernelWork]

lemma cost_kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) :
    cost (kernelQuadrature r T h ψ n m N e w x y g)=
      Fintype.card (ProbabilityNode T h n)*(m+1)*
        kernelWork (Fintype.card (ProbabilityNode T h n)) (n+1) N (cost x) (cost y) (cost g) := by
  simp only [kernelQuadrature,kernelAction,cost_sumFamily,cost_scale,cost_kernelCorrection,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_assoc]

lemma cost_velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) :
    (cost (velocity r T h ψ s n m N e x p).1,cost (velocity r T h ψ s n m N e x p).2)=
      velocityWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N (cost x) (cost p.1,cost p.2) := by
  simp only [velocity,cost_scale,cost_add,cost_conditional,cost_mean,cost_kernelQuadrature,velocityWork]
  congr 1
  omega

lemma cost_meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1))
    (x y g : MeanTree X d) :
    cost (meanCircuit r T h ψ s n m N nc Nc e x y g)=
      meanWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N nc Nc (cost x) (cost y) (cost g) := by
  have hp (i : Fin (nc+1)) := cost_pairPicard (centeringWeight nc) _ (y,g)
    _ (fun p => cost_velocity r T h ψ s n m N e x p) Nc i
  have hy (i : Fin (nc+1)) := congrArg Prod.fst (hp i)
  simp only [Fintype.card_fin] at hy
  simp only [meanCircuit,cost_add,cost_scale,cost_sumFamily,cost_conditional,centeringStates,hy,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,meanWork]

lemma cost_literalMean (r T h ψ σ : ℝ) (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) :
    cost (literalMean (d:=d) r T h ψ σ n m N nc Nc e)=
      meanWork (Fintype.card (ProbabilityNode T h (n+1))) (n+2) m N nc Nc 0 0 0 := by
  simp only [literalMean,cost_meanCircuit,cost_anchor]

lemma cost_literalSample (r T h : ℝ) (n N : ℕ) (e : ProbabilityNode T h n) :
    cost (literalSample (d:=d) r T h n N e)=flowWork (Fintype.card (ProbabilityNode T h n)) N 0 0 := by
  simp only [literalSample,cost_scale,cost_forward,cost_anchor]
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeanTree OracleCompiler MeasureTheory OracleCompiler.Expression OracleCompiler.Program
open scoped Classical BigOperators

variable {d : ℕ}

namespace MeanTree
lemma shiftReady_of_positive {X : Type*} [MeasurableSpace X] (D A : ℝ)
    (E : MeanTree X d) (hE : centers (fun r _ => 0<r) E) (n : ℝ) :
    ShiftReady D A (fun r _ => 0<r) E n := by
  induction E generalizing n with | node k b hb a r C ih =>
    intro i
    exact ⟨(hE i).1.ne',(hE i).1,ih i (hE i).2 _⟩
lemma rootShiftReady_of_positive {X : Type*} [MeasurableSpace X] (D A Af : ℝ)
    (E : MeanTree X d) (hE : centers (fun r _ => 0<r) E) (n : ℝ) :
    RootShiftReady D A Af (fun r _ => 0<r) (fun r _ => 0<r) E n := by
  cases E with | node k b hb a r C =>
    intro i
    exact ⟨(hE i).1.ne',(hE i).1,shiftReady_of_positive D A _ (hE i).2 _⟩
end MeanTree

namespace OracleCompiler
structure MeanBudget (B : ℕ) (r : ℝ) (S : SeedProgram d) : Prop where
  slots : S.slots≤B
  calls : S.calls≤B
  energy : (∑j,S.shift j^2)≤(B:ℝ)
  equiv : ∀Δ,S.program.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) id
structure SampleBudget (B : ℕ) (r η : ℝ) (S : ReservedProgram d) : Prop where
  slots : S.slots≤B
  calls : S.calls≤B
  energy : (∑j,S.shift j^2)≤(B:ℝ)
  equiv : ∀Δ,S.pre.Equivariant (moveSeed (fun x => x+r • Δ) S.shift Δ) (fun y => y-Δ)
  reserve : S.reserve=η/2

lemma MeanBudget.mono {B C : ℕ} {r : ℝ} {S : SeedProgram d} (h : MeanBudget B r S) (hBC : B≤C) : MeanBudget C r S :=
  ⟨h.slots.trans hBC,h.calls.trans hBC,h.energy.trans (by exact_mod_cast hBC),h.equiv⟩
lemma SampleBudget.mono {B C : ℕ} {r η : ℝ} {S : ReservedProgram d} (h : SampleBudget B r η S) (hBC : B≤C) : SampleBudget C r η S :=
  ⟨h.slots.trans hBC,h.calls.trans hBC,h.energy.trans (by exact_mod_cast hBC),h.equiv,h.reserve⟩

lemma terminalMeanProgram_budget (r σ : ℝ) : MeanBudget 2 r (terminalMeanProgram d r σ) := by
  refine ⟨le_rfl,by norm_num [terminalMeanProgram],?_,fun Δ => SeedCompiler.terminalMean_equivariant r σ Δ⟩
  change (∑j : Fin 2,(if j=0 then (-1:ℝ) else 0)^2)≤2
  norm_num [Fin.sum_univ_two]
lemma terminalReservedProgram_budget (r η : ℝ) : SampleBudget 2 r η (terminalReservedProgram d r η) := by
  refine ⟨le_rfl,by norm_num [terminalReservedProgram],?_,fun Δ => terminalReservedProgram_equivariant r η Δ,rfl⟩
  change (∑j : Fin 2,(if j=0 then (-1:ℝ) else 0)^2)≤2
  norm_num [Fin.sum_univ_two]

namespace CircuitParameters
variable (C : CircuitParameters)
lemma mean_positive {r σ : ℝ} (hr : 0<r) : centers (fun r _ => 0<r) (C.meanTree (d:=d) r σ) := by
  exact centers_mono _ (fun _ _ h => DirectCenter.radius_pos hr (by linarith [C.T_lower]) C.T_upper h)
    (literalMean_geometry (by linarith [C.T_lower]) C.T_upper C.h_pos C.v_nonneg C.angle_bound C.meanEndpoint).2
lemma sample_positive {r η : ℝ} (hr : 0<r) (hη : 0<η) (hη1 : η≤1) :
    centers (fun r _ => 0<r) (C.sampleTree (d:=d) r η hη hη1) := by
  have ht := sampleCorrelation_properties hη hη1
  exact centers_mono _ (fun _ _ h => DirectCenter.radius_pos hr (by linarith [ht.1]) ht.2.1 h)
    (literalSample_geometry (Nat.succ_pos C.n) (by linarith [ht.1]) ht.2.1 C.h_pos (C.sampleEndpoint η hη hη1)).2
lemma sampleDrift_spec (r η : ℝ) (hr : 0<r) (hη : 0<η) (hη1 : η≤1) :
    DriftValid (sampleInputMove r (sampleCorrelation η)) (C.sampleTree (d:=d) r η hη hη1) (C.sampleDrift r η hr hη hη1) ∧
      (C.sampleDrift (d:=d) r η hr hη hη1).root _ = -1 ∧ DriftBound 2 _ (C.sampleDrift (d:=d) r η hr hη hη1) := by
  exact (literalSample_drift hr (Nat.succ_pos C.n)
    (by linarith [(sampleCorrelation_properties hη hη1).1])
    (sampleCorrelation_properties hη hη1).2.1 C.h_pos (C.sampleEndpoint η hη hη1)).choose_spec

lemma sampleFrom_budget {B c : ℕ} (hB : 1≤B) (hD : 0<C.D) (hBD : (B:ℝ)≤C.D^2)
    (Mf Mi : ℝ → ℝ → SeedProgram d)
    (hM : ∀(s : Bool) r σ,0<r → MeanBudget B r ((if s then Mf else Mi) r σ))
    (r η : ℝ)
    (hc : 0<r → ∀hη : 0<η, ∀hη1 : η≤1,cost (C.sampleTree (d:=d) r η hη hη1)≤c) :
    SampleBudget ((40*c+40)*B) r η (C.sampleFrom Mf Mi r η) := by
  by_cases hv : 0<r ∧ 0<η ∧ η≤1
  · rw [sampleFrom,dite_eq_left hv]
    let E := C.sampleTree (d:=d) r η hv.2.1 hv.2.2
    let p := C.sampleDrift (d:=d) r η hv.1 hv.2.1 hv.2.2
    let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
    have hready := rootShiftReady_of_positive C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) E (C.sample_positive hv.1 hv.2.1 hv.2.2) (η/Real.sqrt 2)
    have hvD : ∀s r σ,0<r → (∑j,(M s r σ).shift j^2)≤C.D^2 := fun s r σ hr => (hM s r σ hr).energy.trans hBD
    have hsize := compileDeclaredRoot_size C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) (fun _ r _ => 0<r) M B B
      (fun s r σ hr => ⟨(hM s r σ hr).slots,(hM s r σ hr).calls⟩) E _ hready
    have he := compileDeclaredRootShift_energy_bound hD (by norm_num : (0:ℝ)≤2)
      (by positivity : (0:ℝ)≤B) (fun _ r _ => 0<r) M hvD (fun s r σ hr => (hM s r σ hr).energy)
      E _ p hready (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).2.2
    simp only [M,ite_true,ite_false,Bool.false_eq_true] at hsize he
    have hproot : p.root E = -1 := (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).2.1
    have hcost := hc hv.1 hv.2.1 hv.2.2
    have hc' : (cost E:ℝ)≤c := by exact_mod_cast hcost
    have hB' : (1:ℝ)≤B := by exact_mod_cast hB
    have ht := sampleCorrelation_properties hv.2.1 hv.2.2
    refine ⟨?_,?_,?_,?_,rfl⟩
    · change 1+(compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E _).slots≤_
      nlinarith [hsize.1]
    · change (compileDeclaredRoot C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E _).calls≤_
      nlinarith [hsize.2]
    · rw [sampleParent_shift_energy]
      have htsq : (sampleCorrelation η)^2≤1 := by nlinarith [ht.1,ht.2.1]
      push_cast
      change (∑j,compileDeclaredRootShift C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) Mf Mi E (η/Real.sqrt 2) p j^2)≤_ at he
      nlinarith
    · intro Δ
      apply sampleParent_equivariant
      have hh := compileDeclaredRoot_equivariant C.D (C.sampleCenterBudget r) (C.sampleFinalBudget r) hD (fun _ r _ => 0<r) M hvD
        (fun s r σ hr => (hM s r σ hr).equiv) (sampleInputMove r (sampleCorrelation η)) E _ p
        (C.sampleDrift_spec r η hv.1 hv.2.1 hv.2.2).1 hready Δ
      rw [hproot] at hh
      have hout : (fun y : Point d => y+(-1:ℝ) • Δ)=(fun y=>y-Δ) := by
        funext y; simp [sub_eq_add_neg]
      rw [hout] at hh
      exact hh
  · rw [sampleFrom,dite_eq_right hv]
    exact (terminalReservedProgram_budget r η).mono (by nlinarith)
lemma meanFrom_budget {B c : ℕ} (hB : 1≤B) (hD : 0<C.D) (hBD : (B:ℝ)≤C.D^2)
    (Mf Mi : ℝ → ℝ → SeedProgram d) (S : ℝ → ℝ → ReservedProgram d)
    (hM : ∀(s : Bool) r σ,0<r → MeanBudget B r ((if s then Mf else Mi) r σ))
    (hS : ∀r,0<r → SampleBudget B r (Real.sqrt (1-C.T^2)/C.T) (S r (Real.sqrt (1-C.T^2)/C.T)))
    (r σ : ℝ) (hc : cost (C.meanTree (d:=d) r σ)≤c) :
    MeanBudget ((40*c+40)*B) r (C.meanFrom Mf Mi S r σ) := by
  by_cases hr : 0<r
  · rw [meanFrom,dite_eq_left hr]
    let E := C.meanTree (d:=d) r σ
    let p := C.meanDrift (d:=d) r σ hr
    let M : Bool → ℝ → ℝ → SeedProgram d := fun s => if s then Mf else Mi
    let R := Real.sqrt (1-C.T^2)
    let anc := S r (R/C.T)
    have hs : SampleBudget B r (R/C.T) anc := hS r hr
    have hT : 0<C.T := by linarith [C.T_lower]
    have hT2 : 0≤1-C.T^2 := by nlinarith [C.T_upper]
    have hR : 0≤R := Real.sqrt_nonneg _
    have hR2 : R^2=1-C.T^2 := Real.sq_sqrt hT2
    have hR1 : R≤1 := by nlinarith [sq_nonneg C.T]
    have hRT : R/C.T≤2 := (div_le_iff₀ hT).mpr (by linarith [C.T_lower])
    have hsquare : (-2*R/C.T)^2≤16 := by
      have hn : 0≤R/C.T := div_nonneg hR hT.le
      rw [mul_div_assoc]
      nlinarith
    have hready := rootShiftReady_of_positive C.D (C.meanCenterBudget r σ) C.Af E (C.mean_positive hr) (Real.sqrt 3*σ/2)
    have hvD : ∀s r σ,0<r → (∑j,(M s r σ).shift j^2)≤C.D^2 := fun s r σ hr => (hM s r σ hr).energy.trans hBD
    have hsize := compileDeclaredRoot_size C.D (C.meanCenterBudget r σ) C.Af (fun _ r _ => 0<r) M B B
      (fun s r σ hr => ⟨(hM s r σ hr).slots,(hM s r σ hr).calls⟩) E _ hready
    have he := compileDeclaredRootShift_energy_bound hD (by norm_num : (0:ℝ)≤3)
      (by positivity : (0:ℝ)≤B) (fun _ r _ => 0<r) M hvD (fun s r σ hr => (hM s r σ hr).energy)
      E _ p hready (C.meanDrift_spec r σ hr).2.2
    simp only [M,ite_true,ite_false,Bool.false_eq_true] at hsize he
    have hproot : p.root E = 0 := (C.meanDrift_spec r σ hr).2.1
    have hc' : (cost E:ℝ)≤c := by exact_mod_cast hc
    have hB' : (1:ℝ)≤B := by exact_mod_cast hB
    refine ⟨?_,?_,?_,?_⟩
    · change anc.slots+1+(1+(compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E _).slots)≤_
      nlinarith [hsize.1,hs.slots]
    · change anc.calls+(compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E _).calls≤_
      nlinarith [hsize.2,hs.calls]
    · change (∑j,(meanParent anc.full (compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2))
        (anc.extraShift (-2*R/C.T)) (compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p) C.T).shift j^2)≤_
      have henergy := meanParent_shift_energy anc.full (compileDeclaredRoot C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2))
        (anc.extraShift (-2*R/C.T)) (compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p) C.T
      change _ = _ at henergy
      rw [henergy]
      change (∑i : Fin (anc.slots+1),anc.extraShift (-2*R/C.T) i^2)+_≤_
      rw [ReservedProgram.extraShift_energy]
      push_cast
      change (∑j,compileDeclaredRootShift C.D (C.meanCenterBudget r σ) C.Af Mf Mi E (Real.sqrt 3*σ/2) p j^2)≤_ at he
      have ha := hs.energy
      change (∑j,anc.shift j^2)+(-2*R/C.T)^2+_≤_
      nlinarith
    · intro Δ
      apply meanParent_equivariant _ _ _ _ hT.ne'
      · have hx := anc.full_equivariant r (-2*R/C.T) Δ (hs.equiv Δ)
        have hid : (fun y : Point d => y-Δ+(anc.reserve*(-2*R/C.T)) • Δ)=
            (fun y => y-(C.T⁻¹)^2 • Δ) := by
          rw [hs.reserve]
          funext y
          have heq : 1-(R/C.T/2)*(-2*R/C.T)=(C.T⁻¹)^2 := by
            field_simp
            nlinarith [hR2]
          calc
            _ = y-(1-(R/C.T/2)*(-2*R/C.T)) • Δ := by module
            _ = _ := by rw [heq]
        rw [hid] at hx
        exact hx
      · have hh := compileDeclaredRoot_equivariant C.D (C.meanCenterBudget r σ) C.Af hD (fun _ r _ => 0<r) M hvD
          (fun s r σ hr => (hM s r σ hr).equiv) (meanInputMove r C.T) E _ p
          (C.meanDrift_spec r σ hr).1 hready Δ
        rw [hproot] at hh
        have hout : (fun y : Point d => y+(0:ℝ) • Δ)=id := by
          funext y; simp
        rw [hout] at hh
        exact hh
  · rw [meanFrom,dite_eq_right hr]
    exact (terminalMeanProgram_budget r σ).mono (by nlinarith)
end CircuitParameters
end OracleCompiler
end LogConcaveSampling

end

end

end OAI
