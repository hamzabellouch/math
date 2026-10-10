import Mathlib
import OAI.Probability.LogConcave.Complexity.KernelAnalyticNormalizedBudget

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators NNReal

namespace MeanTree
variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def forward (r T h : ℝ) (n N : ℕ) (x y : MeanTree X d)
    (i : ProbabilityNode T h n) : MeanTree X d :=
  picard (probabilityWeight T h n)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) N i

lemma eval_forward {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (x y : MeanTree X d) (z : X) (i : ProbabilityNode T h n) :
    eval F (forward r T h n N x y i) z=
      probabilityPicard F (eval F x z) r T h n N (eval F y z) i := by
  unfold forward probabilityPicard
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  have he := eval_picard F (probabilityWeight T h n)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) (fun z j => probabilityMeanVelocity F (eval F x z) r (probabilityNodeTime T h n j))
    (fun j E z => by simp only [eval_scale,eval_conditional hF r _ x E z (ha j),probabilityMeanVelocity]) N z i
  simpa only [FinitePicard.nodes_eq_iterate] using he

lemma depth_forward (r T h : ℝ) (n N : ℕ) (x y : MeanTree X d)
    (i : ProbabilityNode T h n) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) :
    depth (forward r T h n N x y i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun _ => hy) ?_ N i).trans (by omega)
  intro j E
  rw [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)
end MeanTree

def sampleMeanCircuit {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T h : ℝ)
    (n N : ℕ) (e : ProbabilityNode T h n) (z : Point d) : Point d :=
  T⁻¹ • probabilityPicard F x r T h n N z e

def samplingEnvelope (d k n N : ℕ) (C q h : ℝ) : ℝ :=
  4*(2*C*dimensionLog d^k*(2*h)^(n+1)+circuitGrowthConstant*q^N)^2

theorem sampleMeanCircuit_rms (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      r≤1 → 0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,(lam:ℝ)*r≤1 → 1≤d →
      ∀{T h : ℝ},1/2≤T → T<1 → 0<h → h≤Real.log 2 →
      A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,∀e : ProbabilityNode T h n,
      Integrable (fun z => ‖sampleMeanCircuit F x r T h n N e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T h n N e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
        (circuitD F x)^2*samplingEnvelope d k n N C (A*probabilityMeanLipschitz lam r) h := by
  obtain ⟨A,C,hC,k,h⟩ := probabilityPicard_forward_rms n hn
  refine ⟨A,C,hC,k,?_⟩
  intro d F lam hF x r hr hr1 hlam hl hL hd T hmesh hT hT1 hh hhsmall hq N e
  have he := h hF x hr hlam hl hd (by linarith) hT1 hh hhsmall hq N e
  have hT0 : 0<T := by linarith
  have hTin : 0≤T⁻¹ := inv_nonneg.mpr hT0.le
  have hTi : T⁻¹≤2 := (inv_le_comm₀ hT0 (by norm_num)).mpr (by simpa using hT)
  have hi := probabilityInitialRms_growth F x lam hr.le hL
  have hi' : probabilityInitialRms F x lam r≤circuitGrowthConstant*circuitD F x := by
    apply hi.trans
    nlinarith [mul_le_mul_of_nonneg_left hr1
      (mul_nonneg circuitGrowthConstant_pos.le (circuitD_nonneg F x))]
  have hD := sqrt_le_circuitD F x
  have hD0 := circuitD_nonneg F x
  have hlo : 0≤(lam:ℝ)*r^2 := by positivity
  have hlog := dimensionLog_nonneg d
  let q : ℝ := A*probabilityMeanLipschitz lam r
  let B : ℝ := 2*C*dimensionLog d^k*(2*hmesh)^(n+1)+circuitGrowthConstant*q^N
  have heq : (fun z => ‖sampleMeanCircuit F x r T hmesh n N e z-
      T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T hmesh n e) z‖^2)=
      (fun z => (T⁻¹)^2*‖probabilityPicard F x r T hmesh n N z e-
        fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T hmesh n e) z‖^2) := by
    funext z
    simp only [sampleMeanCircuit,←smul_sub,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [heq]
  refine ⟨he.1.const_mul _,?_⟩
  rw [integral_const_mul]
  have hb : 2*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*hmesh)^(n+1)+
      q^N*probabilityInitialRms F x lam r≤circuitD F x*B := by
    have hls : (lam:ℝ)*r^2*Real.sqrt d≤circuitD F x := by
      exact (mul_le_of_le_one_left (Real.sqrt_nonneg _) (by linarith)).trans hD
    have h₁ := mul_le_mul_of_nonneg_left hls
      (show 0≤2*C*dimensionLog d^k*(2*hmesh)^(n+1) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hi' (show 0≤q^N by dsimp [q]; positivity)
    dsimp [B,dimensionLog] at *
    nlinarith
  have hp := pow_le_pow_left₀ (show 0≤2*C*((lam:ℝ)*r^2)*Real.sqrt d*(1+Real.log ((d:ℝ)+1))^k*(2*hmesh)^(n+1)+
      q^N*probabilityInitialRms F x lam r by
        change 0≤2*C*((lam:ℝ)*r^2)*Real.sqrt d*dimensionLog d^k*(2*hmesh)^(n+1)+q^N*probabilityInitialRms F x lam r
        positivity [probabilityInitialRms_nonneg F x lam r]) hb 2
  have hti := pow_le_pow_left₀ hTin hTi 2
  calc
    _ ≤ (T⁻¹)^2*(circuitD F x*B)^2 := mul_le_mul_of_nonneg_left (he.2.trans hp) (sq_nonneg _)
    _ ≤ 4*(circuitD F x*B)^2 := by nlinarith [mul_le_mul_of_nonneg_right hti (sq_nonneg (circuitD F x*B))]
    _ = _ := by dsimp [samplingEnvelope,B,q]; ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def oriented (Y G : X → Point d) (θ : ℝ) : X → Point d :=
  fun z => Real.cos θ • Y z+Real.sin θ • G z

omit [MeasurableSpace X] in
@[simp] lemma oriented_zero (Y G : X → Point d) : oriented Y G 0=Y := by
  funext z; simp [oriented]

def DirectCenter (r T v : ℝ) (x Y G : X → Point d) (r' : ℝ) (b : X → Point d) : Prop :=
  ∃ρ∈Icc (0:ℝ) T,∃θ,|θ|≤v ∧ r'=r*Real.sqrt (1-ρ^2) ∧
    b=fun z => x z+(r*ρ) • oriented Y G θ z

lemma conditional_centers_direct {r T v ρ θ : ℝ} {x Y G : X → Point d}
    (xE yE : MeanTree X d) (hx : base xE=x) (hy : base yE=oriented Y G θ)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE) :
    centers (DirectCenter r T v x Y G) (conditional r ρ xE yE) := by
  apply centers_conditional _ _ _ _ _ _ hxc hyc
  exact ⟨ρ,hρ,θ,hθ,rfl,by rw [hx,hy]⟩

lemma probability_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=oriented Y G θ) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (s i : ProbabilityNode T h n) :
    base (probability r T h n N s xE yE i)=base yE ∧
      centers (DirectCenter r T v x Y G) (probability r T h n N s xE yE i) := by
  apply picard_shape _ _ _ _ (fun _ => hyc)
  intro j k E he hc
  refine ⟨by simp,?_⟩
  apply (centers_scale _ _ _).2
  exact conditional_centers_direct xE E hx (he.trans hy)
    (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hc

lemma forward_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=oriented Y G θ) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (i : ProbabilityNode T h n) :
    base (forward r T h n N xE yE i)=base yE ∧
      centers (DirectCenter r T v x Y G) (forward r T h n N xE yE i) := by
  apply picard_shape _ _ _ _ (fun _ => hyc)
  intro j k E he hc
  refine ⟨by simp,?_⟩
  apply (centers_scale _ _ _).2
  exact conditional_centers_direct xE E hx (he.trans hy)
    (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hc

lemma harmonic_centers_direct {r T v ρ θ : ℝ} {n N : ℕ} (hn : 0<n)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hρ : ρ∈Icc (0:ℝ) T) (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE) (i : Fin (n+1)) :
    base (harmonic r ρ θ n N xE yE gE i)=oriented Y G (θ*probabilityNodes n i) ∧
      centers (DirectCenter r T v x Y G) (harmonic r ρ θ n N xE yE gE i) := by
  have ha : ∀j : Fin (n+1), base (add (scale (Real.cos (θ*probabilityNodes n j)) yE)
      (scale (Real.sin (θ*probabilityNodes n j)) gE))=oriented Y G (θ*probabilityNodes n j) := by
    intro j; simp only [base_add,base_scale,hy,hg]; rfl
  have hp := picard_shape (DirectCenter r T v x Y G) (harmonicWeight n θ)
    (fun _ E => scale ρ (scale (-r) (conditional r ρ xE E)))
    (fun j => add (scale (Real.cos (θ*probabilityNodes n j)) yE)
      (scale (Real.sin (θ*probabilityNodes n j)) gE))
    (fun _ => (centers_add _ _ _).2 ⟨(centers_scale _ _ _).2 hyc,(centers_scale _ _ _).2 hgc⟩) ?_ N i
  · exact ⟨hp.1.trans (ha i),hp.2⟩
  · intro j k E he hc
    refine ⟨by simp,?_⟩
    apply (centers_scale _ _ _).2
    apply (centers_scale _ _ _).2
    apply conditional_centers_direct xE E hx (he.trans (ha k)) hρ _ hxc hc
    rw [abs_mul,abs_of_nonneg (probabilityNodes_mem hn k).1]
    exact (mul_le_mul_of_nonneg_left (probabilityNodes_mem hn k).2 (abs_nonneg θ)).trans (by simpa using hθ)

lemma kernelCorrection_centers_direct {r T h v θ : ℝ} {n N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hθ : |θ|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE) (s e : ProbabilityNode T h n) :
    base (kernelCorrection r T h θ n N s e xE yE gE)=(fun _ => 0) ∧
      centers (DirectCenter r T v x Y G) (kernelCorrection r T h θ n N s e xE yE gE) := by
  have hv : 0≤v := (abs_nonneg _).trans hθ
  have hb := probability_centers_direct (N:=N) hn hT hT1 hh xE yE hx
    (by simpa using hy : base yE=oriented Y G 0) (by simpa using hv) hxc hyc e s
  have hw := harmonic_centers_direct (N:=N) hn xE (probability r T h n N e xE yE s) gE hx
    (hb.1.trans hy) hg (probabilityNodeTime_mem hT hT1 hh hn s) hθ hxc hb.2 hgc (Fin.last n)
  have vlast : probabilityNodes n (Fin.last n)=1 := by
    simp [probabilityNodes,hn.ne']
  rw [vlast,mul_one] at hw
  constructor
  · funext z
    simp only [kernelCorrection,base_sumFamily,base_scale,base_conditional,smul_zero,Finset.sum_const_zero]
  · unfold kernelCorrection
    apply centers_sumFamily
    intro j
    apply (centers_scale _ _ _).2
    apply (centers_scale _ _ _).2
    have hp := probability_centers_direct (N:=N) hn hT hT1 hh xE
      (harmonic r (probabilityNodeTime T h n s) θ n N xE (probability r T h n N e xE yE s) gE (Fin.last n))
      hx hw.1 hθ hxc hw.2 s j
    exact conditional_centers_direct _ _ hx (hp.1.trans hw.1)
      (probabilityNodeTime_mem hT hT1 hh hn j) hθ hxc hp.2

lemma kernelQuadrature_centers_direct {r T h ψ v : ℝ} {n m N : ℕ}
    (hn : 0<n) (hT : 0<T) (hT1 : T<1) (hh : 0<h)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ) :
    base (kernelQuadrature r T h ψ n m N e w xE yE gE)=(fun _ => 0) ∧
      centers (DirectCenter r T v x Y G) (kernelQuadrature r T h ψ n m N e w xE yE gE) := by
  have hk (i : ProbabilityNode T h n) (j : Fin (m+1)) :=
    kernelCorrection_centers_direct (N:=N) hn hT hT1 hh xE yE gE hx hy hg (hψ j) hxc hyc hgc i e
  constructor
  · funext z
    simp only [kernelQuadrature,kernelAction,base_sumFamily,base_scale,(hk _ _).1,smul_zero,Finset.sum_const_zero]
  · apply centers_sumFamily
    intro i
    apply (centers_scale _ _ _).2
    apply centers_sumFamily
    intro j
    exact (centers_scale _ _ _).2 (hk i j).2
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

lemma pairPicard_shape {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (w : I → I → ℝ) (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d)
    (ha : centers P a.1 ∧ centers P a.2)
    (hφ : ∀p,base p.1=base a.1 → base p.2=base a.2 → centers P p.1 → centers P p.2 →
      base (φ p).1=(fun _ => 0) ∧ base (φ p).2=(fun _ => 0) ∧
      centers P (φ p).1 ∧ centers P (φ p).2)
    (N : ℕ) (i : I) :
    base (pairPicard w φ a N i).1=base a.1 ∧ base (pairPicard w φ a N i).2=base a.2 ∧
      centers P (pairPicard w φ a N i).1 ∧ centers P (pairPicard w φ a N i).2 := by
  induction N generalizing i with
  | zero => exact ⟨rfl,rfl,ha⟩
  | succ N ih =>
    have hp (j : I) := hφ (pairPicard w φ a N j) (ih j).1 (ih j).2.1 (ih j).2.2.1 (ih j).2.2.2
    refine ⟨?_,?_,?_,?_⟩
    · funext z
      simp only [pairPicard,base_add,base_sumFamily,base_scale,(hp _).1,smul_zero,Finset.sum_const_zero,add_zero]
    · funext z
      simp only [pairPicard,base_add,base_sumFamily,base_scale,(hp _).2.1,smul_zero,Finset.sum_const_zero,add_zero]
    · exact (centers_add _ _ _).2 ⟨ha.1,centers_sumFamily _ _ (fun j => (centers_scale _ _ _).2 (hp j).2.2.1)⟩
    · exact (centers_add _ _ _).2 ⟨ha.2,centers_sumFamily _ _ (fun j => (centers_scale _ _ _).2 (hp j).2.2.2)⟩

lemma velocity_centers_direct {r T h ψ v s : ℝ} {n m N : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) :
    base (velocity r T h ψ s n m N e xE (yE,gE)).1=(fun _ => 0) ∧
    base (velocity r T h ψ s n m N e xE (yE,gE)).2=(fun _ => 0) ∧
    centers (DirectCenter r T v x Y G) (velocity r T h ψ s n m N e xE (yE,gE)).1 ∧
    centers (DirectCenter r T v x Y G) (velocity r T h ψ s n m N e xE (yE,gE)).2 := by
  have hk := kernelQuadrature_centers_direct (N:=N) (Nat.succ_pos n) hT hT1 hh xE yE gE hx hy hg hψ hxc hyc hgc e (terminalQuadratureWeight T h n)
  have hm : centers (DirectCenter r T v x Y G) (mean r xE) := by
    apply centers_mean _ _ _ _ hxc
    refine ⟨0,⟨by norm_num,hT.le⟩,0,by simpa using hv,?_,?_⟩
    · simp
    · simpa only [mul_zero,zero_smul,add_zero] using hx
  have hc := conditional_centers_direct xE yE hx (by simpa using hy : base yE=oriented Y G 0)
    ⟨hT.le,le_rfl⟩ (by simpa using hv : |(0:ℝ)|≤v) hxc hyc
  refine ⟨?_,?_,?_,?_⟩
  · funext z; simp only [velocity,base_scale,hk.1,smul_zero]
  · funext z; simp only [velocity,base_scale,base_add,base_conditional,base_mean,smul_zero,add_zero]
  · exact (centers_scale _ _ _).2 hk.2
  · exact (centers_scale _ _ _).2 ((centers_add _ _ _).2 ⟨hc,(centers_scale _ _ _).2 hm⟩)

lemma centeringStates_centers_direct {r T h ψ v s : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) (i : Fin (nc+1)) :
    base (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).1=Y ∧
    base (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).2=G ∧
    centers (DirectCenter r T v x Y G) (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).1 ∧
    centers (DirectCenter r T v x Y G) (centeringStates r T h ψ s n m N nc Nc e xE yE gE i).2 := by
  have hp := pairPicard_shape (DirectCenter r T v x Y G) (centeringWeight nc)
    (velocity r T h ψ s n m N e xE) (yE,gE) ⟨hyc,hgc⟩
    (fun p hp hq hpc hqc => velocity_centers_direct hT hT1 hh hv xE p.1 p.2 hx
      (hp.trans hy) (hq.trans hg) hψ hxc hpc hqc e) Nc i
  exact ⟨hp.1.trans hy,hp.2.1.trans hg,hp.2.2⟩

lemma meanCircuit_centers_direct {r T h ψ v s : ℝ} {n m N nc Nc : ℕ}
    (hT : 0<T) (hT1 : T<1) (hh : 0<h) (hv : 0≤v)
    {x Y G : X → Point d} (xE yE gE : MeanTree X d)
    (hx : base xE=x) (hy : base yE=Y) (hg : base gE=G)
    (hψ : ∀j : Fin (m+1),|ψ*angleNodes m j|≤v)
    (hxc : centers (DirectCenter r T v x Y G) xE)
    (hyc : centers (DirectCenter r T v x Y G) yE)
    (hgc : centers (DirectCenter r T v x Y G) gE)
    (e : ProbabilityNode T h (n+1)) :
    base (meanCircuit r T h ψ s n m N nc Nc e xE yE gE)=(fun z => s • G z) ∧
    centers (DirectCenter r T v x Y G) (meanCircuit r T h ψ s n m N nc Nc e xE yE gE) := by
  have hp (i : Fin (nc+1)) := centeringStates_centers_direct (N:=N) (Nc:=Nc) (s:=s) hT hT1 hh hv xE yE gE hx hy hg hψ hxc hyc hgc e i
  constructor
  · funext z
    simp only [meanCircuit,base_add,base_scale,base_sumFamily,base_conditional,hg,
      smul_zero,Finset.sum_const_zero,add_zero]
  · apply (centers_add _ _ _).2
    refine ⟨(centers_scale _ _ _).2 hgc,centers_sumFamily _ _ ?_⟩
    intro j
    apply (centers_scale _ _ _).2
    exact conditional_centers_direct xE _ hx (by simpa using (hp j).1 : base _=oriented Y G 0)
      ⟨hT.le,le_rfl⟩ (by simpa using hv : |(0:ℝ)|≤v) hxc (hp j).2.2.1
end LogConcaveSampling.MeanTree

end

end

end OAI
