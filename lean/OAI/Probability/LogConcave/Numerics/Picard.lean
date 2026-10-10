import Mathlib
import OAI.Probability.LogConcave.Numerics.MeanTree
import OAI.Probability.LogConcave.OraclePrograms.CenteringMeanCircuit

namespace OAI

section
noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d) :
    ℕ → I → MeanTree X d
  | 0 => a
  | k+1 => fun i => add (a i) (sumFamily (fun j => scale (w i j) (φ j (picard w φ a k j))))

lemma eval_picard {I : Type*} [Fintype I] (F : Point d → ℝ)
    (w : I → I → ℝ) (φ : I → MeanTree X d → MeanTree X d)
    (a : I → MeanTree X d) (V : X → I → Point d → Point d)
    (hφ : ∀j E z,eval F (φ j E) z=V z j (eval F E z)) (N : ℕ) (z : X) (i : I) :
    eval F (picard w φ a N i) z=
      nodes w (V z) (fun (_ : Unit) j => eval F (a j) z) N () i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    simp only [picard,eval_add,eval_sumFamily,eval_scale,hφ,ih,nodes,step,correction,Pi.add_apply]

lemma depth_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d) {b D : ℕ}
    (ha : ∀i,depth (a i)≤b)
    (hφ : ∀i E,depth (φ i E)≤ max b (depth E)+D) (N : ℕ) (i : I) :
    depth (picard w φ a N i)≤b+N*D := by
  induction N generalizing i with
  | zero => simpa [picard] using ha i
  | succ N ih =>
    apply depth_add_le
    · exact (ha i).trans (by omega)
    · apply depth_sumFamily_le
      intro j
      rw [depth_scale]
      have he := hφ j (picard w φ a N j)
      have hi := ih j
      simp only [Nat.succ_mul] at *
      omega

def probability (r T h : ℝ) (n N : ℕ) (s : ProbabilityNode T h n)
    (x y : MeanTree X d) (i : ProbabilityNode T h n) : MeanTree X d :=
  picard (reanchorWeight (probabilityWeight T h n) s)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) N i

lemma eval_probability {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s i : ProbabilityNode T h n) (x y : MeanTree X d) (z : X) :
    eval F (probability r T h n N s x y i) z=
      probabilityAnchoredPicard F (eval F x z) r T h n N s (eval F y z) i := by
  unfold probability probabilityAnchoredPicard
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  have he := eval_picard F (reanchorWeight (probabilityWeight T h n) s)
    (fun j E => scale (-r) (conditional r (probabilityNodeTime T h n j) x E))
    (fun _ => y) (fun z j => probabilityMeanVelocity F (eval F x z) r (probabilityNodeTime T h n j))
    (fun j E z => by simp only [eval_scale,eval_conditional hF r _ x E z (ha j),probabilityMeanVelocity]) N z i
  simpa only [nodes_eq_iterate] using he

lemma depth_probability (r T h : ℝ) (n N : ℕ) (s i : ProbabilityNode T h n)
    (x y : MeanTree X d) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) :
    depth (probability r T h n N s x y i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun _ => hy) ?_ N i).trans (by omega)
  intro j E
  rw [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)

def harmonic (r ρ z : ℝ) (n N : ℕ) (x y g : MeanTree X d) (i : Fin (n+1)) : MeanTree X d :=
  picard (harmonicWeight n z) (fun _ E => scale ρ (scale (-r) (conditional r ρ x E)))
    (fun j => add (scale (Real.cos (z*probabilityNodes n j)) y)
      (scale (Real.sin (z*probabilityNodes n j)) g)) N i

lemma eval_harmonic {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (r ρ v : ℝ) (ha : 0<1-ρ^2) (n N : ℕ) (x y g : MeanTree X d)
    (z : X) (i : Fin (n+1)) :
    eval F (harmonic r ρ v n N x y g i) z=
      harmonicPicard F (eval F x z) r ρ v n N (eval F y z,eval F g z) i := by
  unfold harmonic harmonicPicard
  have he := eval_picard F (harmonicWeight n v)
    (fun _ E => scale ρ (scale (-r) (conditional r ρ x E)))
    (fun j => add (scale (Real.cos (v*probabilityNodes n j)) y)
      (scale (Real.sin (v*probabilityNodes n j)) g))
    (fun z _ => harmonicMeanVelocity F (eval F x z) r ρ)
    (fun j E z => by simp only [eval_scale,eval_conditional hF r ρ x E z ha,
      harmonicMeanVelocity,probabilityMeanVelocity]) N z i
  simp only [nodes_eq_iterate,eval_add,eval_scale] at he ⊢
  change _ = _ at he
  exact he

lemma depth_harmonic (r ρ v : ℝ) (n N : ℕ) (x y g : MeanTree X d) (i : Fin (n+1))
    {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (harmonic r ρ v n N x y g i)≤b+N := by
  apply (depth_picard _ _ _ (D:=1) (fun j => depth_add_le _ _ (by simpa using hy) (by simpa using hg)) ?_ N i).trans (by omega)
  intro j E
  simp only [depth_scale]
  exact depth_conditional_le _ _ _ _ (hx.trans (le_max_left _ _)) (le_max_right _ _)

def kernelCorrection (r T h v : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) : MeanTree X d :=
  let b := probability r T h n N e x y s
  let w := harmonic r (probabilityNodeTime T h n s) v n N x b g (Fin.last n)
  sumFamily (fun j => scale (reanchorWeight (probabilityWeight T h n) s e j)
    (scale (-r) (conditional r (probabilityNodeTime T h n j) x
      (probability r T h n N s x w j))))

lemma eval_kernelCorrection {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h v : ℝ} {n N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s e : ProbabilityNode T h n) (x y g : MeanTree X d) (z : X) :
    eval F (kernelCorrection r T h v n N s e x y g) z=
      kernelCorrectionPicard F (eval F x z) r T h v n N s e (eval F y z,eval F g z) := by
  have ha (j : ProbabilityNode T h n) : 0<1-(probabilityNodeTime T h n j)^2 := by
    have hj := probabilityNodeTime_mem hT0 hT1 hh hn j
    have ht := hj.2.trans_lt hT1
    nlinarith [hj.1]
  simp only [kernelCorrection,eval_sumFamily,eval_scale,eval_conditional hF _ _ _ _ z (ha _),
    eval_probability hF hn hT0 hT1 hh,eval_harmonic hF _ _ _ (ha s)]
  simp only [kernelCorrectionPicard,probabilityAnchoredPicard,nodes,step,correction,Pi.add_apply,
    add_sub_cancel_left,probabilityMeanVelocity]

lemma depth_kernelCorrection (r T h v : ℝ) (n N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) {b : ℕ} (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (kernelCorrection r T h v n N s e x y g)≤b+3*N+1 := by
  have hb := depth_probability r T h n N e s x y hx hy
  have hw := depth_harmonic r (probabilityNodeTime T h n s) v n N x
    (probability r T h n N e x y s) g (Fin.last n)
    (b:=b+N) (hx.trans (by omega)) hb (hg.trans (by omega))
  unfold kernelCorrection
  apply depth_sumFamily_le
  intro j
  simp only [depth_scale]
  apply depth_conditional_le
  · exact hx.trans (by omega)
  · exact (depth_probability r T h n N s j x _ (b:=b+N+N)
      (hx.trans (by omega)) hw).trans (by omega)

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def kernelAction (r T h ψ : ℝ) (n m N : ℕ) (s e : ProbabilityNode T h n)
    (x y g : MeanTree X d) : MeanTree X d :=
  sumFamily (fun j : Fin (m+1) => scale (derivativeWeight (angleNodes m) j/ψ)
    (kernelCorrection r T h (ψ*angleNodes m j) n N s e x y g))

def kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) : MeanTree X d :=
  sumFamily (fun j => scale (w j) (kernelAction r T h ψ n m N j e x y g))

lemma eval_kernelAction {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ : ℝ} {n m N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (s e : ProbabilityNode T h n) (x y g : MeanTree X d) (z : X) :
    eval F (kernelAction r T h ψ n m N s e x y g) z=
      kernelActionPicard F (eval F x z) r T h ψ n m N s e (eval F y z,eval F g z) := by
  simp only [kernelAction,eval_sumFamily,eval_scale,eval_kernelCorrection hF hn hT0 hT1 hh]
  rfl

lemma eval_kernelQuadrature {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ : ℝ} {n m N : ℕ} (hn : 0<n) (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (e : ProbabilityNode T h n) (w : ProbabilityNode T h n → ℝ)
    (x y g : MeanTree X d) (z : X) :
    eval F (kernelQuadrature r T h ψ n m N e w x y g) z=
      kernelQuadraturePicard F (eval F x z) r T h ψ n m N e w (eval F y z,eval F g z) := by
  simp only [kernelQuadrature,eval_sumFamily,eval_scale,eval_kernelAction hF hn hT0 hT1 hh]
  rfl

lemma depth_kernelQuadrature (r T h ψ : ℝ) (n m N : ℕ) (e : ProbabilityNode T h n)
    (w : ProbabilityNode T h n → ℝ) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (kernelQuadrature r T h ψ n m N e w x y g)≤b+3*N+1 := by
  apply depth_sumFamily_le
  intro j
  rw [depth_scale]
  apply depth_sumFamily_le
  intro k
  rw [depth_scale]
  exact depth_kernelCorrection _ _ _ _ _ _ _ _ _ _ _ hx hy hg

def velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) : MeanTree X d × MeanTree X d :=
  (scale (-(r*s)⁻¹) (kernelQuadrature r T h ψ (n+1) m N e (terminalQuadratureWeight T h n) x p.1 p.2),
    scale s⁻¹ (add (conditional r T x p.1) (scale (-1) (mean r x))))

def pairEval (F : Point d → ℝ) (p : MeanTree X d × MeanTree X d) (z : X) : Point d × Point d :=
  (eval F p.1 z,eval F p.2 z)

lemma eval_velocity {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N : ℕ) (e : ProbabilityNode T h (n+1)) (x : MeanTree X d)
    (p : MeanTree X d × MeanTree X d) (z : X) :
    pairEval F (velocity r T h ψ s n m N e x p) z=
      centeringVelocityPicard F (eval F x z) r T h ψ s n m N e (pairEval F p z) := by
  have ha : 0<1-T^2 := by nlinarith
  simp only [pairEval,velocity,eval_scale,eval_kernelQuadrature hF (Nat.succ_pos n) hT0 hT1 hh,
    eval_add,eval_conditional hF _ _ _ _ z ha,eval_mean,neg_one_smul,←sub_eq_add_neg]
  rfl

lemma depth_velocity (r T h ψ s : ℝ) (n m N : ℕ) (e : ProbabilityNode T h (n+1))
    (x : MeanTree X d) (p : MeanTree X d × MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth p.1≤b) (hg : depth p.2≤b) :
    depth (velocity r T h ψ s n m N e x p).1≤b+(3*N+1) ∧
    depth (velocity r T h ψ s n m N e x p).2≤b+(3*N+1) := by
  constructor
  · simpa only [velocity,depth_scale,Nat.add_assoc] using
      depth_kernelQuadrature r T h ψ (n+1) m N e (terminalQuadratureWeight T h n) x p.1 p.2 hx hy hg
  · simp only [velocity,depth_scale]
    apply depth_add_le
    · exact (depth_conditional_le _ _ _ _ hx hy).trans (by omega)
    · simp only [depth_scale,depth_mean]; omega

def pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) : ℕ → I → MeanTree X d × MeanTree X d
  | 0 => fun _ => a
  | k+1 => fun i =>
    (add a.1 (sumFamily (fun j => scale (w i j) (φ (pairPicard w φ a k j)).1)),
     add a.2 (sumFamily (fun j => scale (w i j) (φ (pairPicard w φ a k j)).2)))

lemma eval_pairPicard {I : Type*} [Fintype I] (F : Point d → ℝ) (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) (V : X → (Point d × Point d) → Point d × Point d)
    (hφ : ∀p z,pairEval F (φ p) z=V z (pairEval F p z))
    (N : ℕ) (z : X) (i : I) :
    pairEval F (pairPicard w φ a N i) z=
      nodes w (fun _ => V z) (fun p : Point d × Point d => fun _ => p) N (pairEval F a z) i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    have hsum (j : I) := hφ (pairPicard w φ a N j) z
    simp only [ih] at hsum
    apply Prod.ext
    · simp only [pairPicard,pairEval,eval_add,eval_sumFamily,eval_scale,nodes,step,correction,
        Pi.add_apply,Prod.fst_add,Prod.fst_sum,Prod.smul_fst]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simpa only [pairEval] using congrArg (fun p : Point d × Point d => w i j • p.1) (hsum j)
    · simp only [pairPicard,pairEval,eval_add,eval_sumFamily,eval_scale,nodes,step,correction,
        Pi.add_apply,Prod.snd_add,Prod.snd_sum,Prod.smul_snd]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      simpa only [pairEval] using congrArg (fun p : Point d × Point d => w i j • p.2) (hsum j)

lemma depth_pairPicard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : MeanTree X d × MeanTree X d → MeanTree X d × MeanTree X d)
    (a : MeanTree X d × MeanTree X d) {b D : ℕ}
    (ha : depth a.1≤b ∧ depth a.2≤b)
    (hφ : ∀p k,b≤k → depth p.1≤k → depth p.2≤k →
      depth (φ p).1≤k+D ∧ depth (φ p).2≤k+D) (N : ℕ) (i : I) :
    depth (pairPicard w φ a N i).1≤b+N*D ∧ depth (pairPicard w φ a N i).2≤b+N*D := by
  induction N generalizing i with
  | zero => simpa [pairPicard] using ha
  | succ N ih =>
    have hstep (j : I) := hφ (pairPicard w φ a N j) (b+N*D) (by omega) (ih j).1 (ih j).2
    constructor
    · apply depth_add_le
      · exact ha.1.trans (by omega)
      · apply depth_sumFamily_le
        intro j
        rw [depth_scale]
        simpa only [Nat.succ_mul,Nat.add_assoc] using (hstep j).1
    · apply depth_add_le
      · exact ha.2.trans (by omega)
      · apply depth_sumFamily_le
        intro j
        rw [depth_scale]
        simpa only [Nat.succ_mul,Nat.add_assoc] using (hstep j).2

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def centeringStates (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) (i : Fin (nc+1)) :
    MeanTree X d × MeanTree X d :=
  pairPicard (centeringWeight nc) (velocity r T h ψ s n m N e x) (y,g) Nc i

def meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) : MeanTree X d :=
  add (scale s g) (sumFamily (fun j => scale (Quadrature.weight (probabilityNodes nc) j 0 1)
    (conditional r T x (centeringStates r T h ψ s n m N nc Nc e x y g j).1)))

lemma nodes_productPointEquiv {I : Type*} [Fintype I] (w : I → I → ℝ)
    (V : Point d × Point d → Point d × Point d) (y : Point (d+d)) (N : ℕ) (i : I) :
    productPointEquiv d d
      (nodes w (fun _ z => (productPointEquiv d d).symm (V (productPointEquiv d d z)))
        (fun z _ => z) N y i)=
      nodes w (fun _ => V) (fun p : Point d × Point d => fun _ => p) N (productPointEquiv d d y) i := by
  induction N generalizing i with
  | zero => rfl
  | succ N ih =>
    simp only [nodes,step,correction,Pi.add_apply,map_add,map_sum,map_smul,
      ContinuousLinearEquiv.apply_symm_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [ih]

lemma eval_centeringStates {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d)
    (z : X) (i : Fin (nc+1)) :
    pairEval F (centeringStates r T h ψ s n m N nc Nc e x y g i) z=
      productPointEquiv d d (stationaryPicard nc Nc
        (centeringVelocityJoint F (eval F x z) r T h ψ s n m N e)
        ((productPointEquiv d d).symm (eval F y z,eval F g z)) i) := by
  rw [centeringStates,eval_pairPicard F _ _ _ _ (fun p z => eval_velocity hF hT0 hT1 hh n m N e x p z)]
  unfold stationaryPicard centeringVelocityJoint
  rw [nodes_productPointEquiv]
  simp only [ContinuousLinearEquiv.apply_symm_apply,pairEval]

lemma eval_meanCircuit {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    {r T h ψ s : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (n m N nc Nc : ℕ) (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) (z : X) :
    eval F (meanCircuit r T h ψ s n m N nc Nc e x y g) z=
      centeringMeanCircuit F (eval F x z) r T h ψ s n m N nc Nc e
        ((productPointEquiv d d).symm (eval F y z,eval F g z)) := by
  have ha : 0<1-T^2 := by nlinarith
  simp only [meanCircuit,eval_add,eval_scale,eval_sumFamily,
    eval_conditional hF _ _ _ _ z ha,centeringMeanCircuit,ContinuousLinearEquiv.apply_symm_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have he := congrArg Prod.fst (eval_centeringStates hF (r:=r) (ψ:=ψ) (s:=s) hT0 hT1 hh n m N nc Nc e x y g z j)
  change eval F (centeringStates r T h ψ s n m N nc Nc e x y g j).1 z=_ at he
  rw [he]

lemma depth_centeringStates (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) (i : Fin (nc+1)) :
    depth (centeringStates r T h ψ s n m N nc Nc e x y g i).1≤b+Nc*(3*N+1) ∧
    depth (centeringStates r T h ψ s n m N nc Nc e x y g i).2≤b+Nc*(3*N+1) := by
  apply depth_pairPicard _ _ _ ⟨hy,hg⟩
  intro p k hk hp hq
  exact depth_velocity r T h ψ s n m N e x p (hx.trans hk) hp hq

lemma depth_meanCircuit (r T h ψ s : ℝ) (n m N nc Nc : ℕ)
    (e : ProbabilityNode T h (n+1)) (x y g : MeanTree X d) {b : ℕ}
    (hx : depth x≤b) (hy : depth y≤b) (hg : depth g≤b) :
    depth (meanCircuit r T h ψ s n m N nc Nc e x y g)≤b+Nc*(3*N+1)+1 := by
  apply depth_add_le
  · simpa only [depth_scale] using hg.trans (by omega)
  · apply depth_sumFamily_le
    intro j
    rw [depth_scale]
    exact depth_conditional_le _ _ _ _ (hx.trans (by omega))
      (depth_centeringStates r T h ψ s n m N nc Nc e x y g hx hy hg j).1

theorem meanCircuit_fixed_depth (r T h ψ s : ℝ) (n m N nc Nc : ℕ) (hNc : Nc≤N)
    (e : ProbabilityNode T h (n+1)) (x y g : X → Point d)
    (hx : Measurable x) (hy : Measurable y) (hg : Measurable g) :
    depth (meanCircuit r T h ψ s n m N nc Nc e (anchor x hx) (anchor y hy) (anchor g hg))≤
      4*(N+1)^2 := by
  have he := depth_meanCircuit r T h ψ s n m N nc Nc e (anchor x hx) (anchor y hy) (anchor g hg)
    (b:=0) (by simp) (by simp) (by simp)
  have hh := Nat.mul_le_mul_right (3*N+1) hNc
  nlinarith

end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

def base : MeanTree X d → X → Point d
  | .node _ b .. => b

@[simp] lemma base_anchor (b : X → Point d) (hb : Measurable b) : base (anchor b hb)=b := rfl
@[simp] lemma base_zero : base (zero : MeanTree X d)=fun _ => 0 := rfl
@[simp] lemma base_scale (s : ℝ) (E : MeanTree X d) : base (scale s E)=fun z => s • base E z := by cases E; rfl
@[simp] lemma base_add (E D : MeanTree X d) : base (add E D)=fun z => base E z+base D z := by cases E; cases D; rfl
@[simp] lemma base_mean (r : ℝ) (E : MeanTree X d) : base (mean r E)=fun _ => 0 := rfl
@[simp] lemma base_conditional (r ρ : ℝ) (x y : MeanTree X d) : base (conditional r ρ x y)=fun _ => 0 := rfl

@[simp] lemma base_sumFin (k : ℕ) (E : Fin k → MeanTree X d) :
    base (sumFin k E)=fun z => ∑i,base (E i) z := by
  induction k with
  | zero => funext z; simp [sumFin]
  | succ k ih => funext z; simp [sumFin,ih,Fin.sum_univ_succ]

@[simp] lemma base_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    base (sumFamily E)=fun z => ∑i,base (E i) z := by
  funext z
  simp only [sumFamily,base_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)

def centers (P : ℝ → (X → Point d) → Prop) : MeanTree X d → Prop
  | .node _ _ _ _ r C => ∀i,P (r i) (base (C i)) ∧ centers P (C i)

@[simp] lemma centers_anchor (P : ℝ → (X → Point d) → Prop) (b : X → Point d) (hb : Measurable b) :
    centers P (anchor b hb) := by intro i; exact Fin.elim0 i
@[simp] lemma centers_zero (P : ℝ → (X → Point d) → Prop) : centers P (zero : MeanTree X d) := centers_anchor _ _ _
@[simp] lemma centers_scale (P : ℝ → (X → Point d) → Prop) (s : ℝ) (E : MeanTree X d) :
    centers P (scale s E)↔centers P E := by cases E; rfl
@[simp] lemma centers_add (P : ℝ → (X → Point d) → Prop) (E D : MeanTree X d) :
    centers P (add E D)↔centers P E ∧ centers P D := by
  cases E with | node k b hb a r C =>
    cases D with | node l c hc v t B =>
      simp only [centers,add]
      constructor
      · intro h
        constructor
        · intro i
          simpa only [Fin.addCases_left] using h (Fin.castAdd l i)
        · intro i
          simpa only [Fin.addCases_right] using h (Fin.natAdd k i)
      · rintro ⟨h₁,h₂⟩ i
        exact Fin.addCases (fun j => by simpa only [Fin.addCases_left] using h₁ j)
          (fun j => by simpa only [Fin.addCases_right] using h₂ j) i

lemma centers_mean (P : ℝ → (X → Point d) → Prop) (r : ℝ) (E : MeanTree X d)
    (hr : P r (base E)) (hE : centers P E) : centers P (mean r E) := by
  intro i
  exact ⟨hr,hE⟩

lemma centers_conditional (P : ℝ → (X → Point d) → Prop) (r ρ : ℝ) (x y : MeanTree X d)
    (hr : P (r*Real.sqrt (1-ρ^2)) (fun z => base x z+(r*ρ) • base y z))
    (hx : centers P x) (hy : centers P y) : centers P (conditional r ρ x y) := by
  apply centers_mean
  · simpa only [base_add,base_scale] using hr
  · exact (centers_add _ _ _).2 ⟨hx,(centers_scale _ _ _).2 hy⟩

lemma centers_sumFin (P : ℝ → (X → Point d) → Prop) (k : ℕ) (E : Fin k → MeanTree X d)
    (h : ∀i,centers P (E i)) : centers P (sumFin k E) := by
  induction k with
  | zero => exact centers_zero _
  | succ k ih => exact (centers_add _ _ _).2 ⟨h 0,ih _ (fun i => h i.succ)⟩

lemma centers_sumFamily {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (E : I → MeanTree X d) (h : ∀i,centers P (E i)) : centers P (sumFamily E) :=
  centers_sumFin P _ _ (fun _ => h _)

lemma picard_shape {I : Type*} [Fintype I] (P : ℝ → (X → Point d) → Prop)
    (w : I → I → ℝ) (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    (ha : ∀i,centers P (a i))
    (hφ : ∀i j E,base E=base (a j) → centers P E →
      base (φ i E)=(fun _ => 0) ∧ centers P (φ i E)) (N : ℕ) (i : I) :
    base (picard w φ a N i)=base (a i) ∧ centers P (picard w φ a N i) := by
  induction N generalizing i with
  | zero => exact ⟨rfl,ha i⟩
  | succ N ih =>
    have hc (j : I) := hφ j j (picard w φ a N j) (ih j).1 (ih j).2
    constructor
    · funext z
      simp only [picard,base_add,base_sumFamily,base_scale,(hc _).1,smul_zero,Finset.sum_const_zero,add_zero]
    · apply (centers_add _ _ _).2
      refine ⟨ha i,centers_sumFamily _ _ ?_⟩
      intro j
      exact (centers_scale _ _ _).2 (hc j).2
end LogConcaveSampling.MeanTree

end

end

section

noncomputable section
namespace LogConcaveSampling.MeanTree
open MeasureTheory Quadrature
open scoped Classical BigOperators

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

@[simp] lemma weight_anchor (b : X → Point d) (hb : Measurable b) : weight (anchor b hb)=0 := by
  simp [anchor,weight]
@[simp] lemma weight_zero : weight (zero : MeanTree X d)=0 := by simp [zero]
@[simp] lemma weight_scale (s : ℝ) (E : MeanTree X d) : weight (scale s E)=|s| * weight E := by
  cases E
  simp only [weight,scale,abs_mul,Finset.mul_sum]
@[simp] lemma weight_add (E D : MeanTree X d) : weight (add E D)=weight E+weight D := by
  cases E; cases D
  simp [weight,add,Fin.sum_univ_add]
@[simp] lemma weight_mean (r : ℝ) (E : MeanTree X d) : weight (mean r E)=1 := by
  simp [weight,mean]
lemma weight_nonneg (E : MeanTree X d) : 0≤weight E := by
  cases E
  exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
@[simp] lemma weight_sumFin (k : ℕ) (E : Fin k → MeanTree X d) :
    weight (sumFin k E)=∑i,weight (E i) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => simp [sumFin,ih,Fin.sum_univ_succ]
@[simp] lemma weight_sumFamily {I : Type*} [Fintype I] (E : I → MeanTree X d) :
    weight (sumFamily E)=∑i,weight (E i) := by
  simp only [sumFamily,weight_sumFin]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun _ => rfl)
@[simp] lemma weight_conditional (r t : ℝ) (x y : MeanTree X d) :
    weight (conditional r t x y)=1 := by simp [conditional]

def centersBound (A : ℝ) : MeanTree X d → Prop
  | .node _ _ _ _ _ E => ∀i,weight (E i)≤A ∧ centersBound A (E i)

lemma centersBound_mono {A B : ℝ} (hAB : A≤B) {E : MeanTree X d}
    (hE : centersBound A E) : centersBound B E := by
  induction E with
  | node k b hb a r E ih =>
    intro i
    exact ⟨(hE i).1.trans hAB,ih i (hE i).2⟩
@[simp] lemma centersBound_anchor (A : ℝ) (b : X → Point d) (hb : Measurable b) :
    centersBound A (anchor b hb) := by
  intro i
  exact Fin.elim0 i
@[simp] lemma centersBound_zero (A : ℝ) : centersBound A (zero : MeanTree X d) := by simp [zero]
@[simp] lemma centersBound_scale (A s : ℝ) (E : MeanTree X d) :
    centersBound A (scale s E) ↔ centersBound A E := by cases E; rfl
@[simp] lemma centersBound_add (A : ℝ) (E D : MeanTree X d) :
    centersBound A (add E D) ↔ centersBound A E ∧ centersBound A D := by
  cases E with | node k b hb a r C =>
    cases D with | node l e he c s B =>
      simp only [add,centersBound,Fin.forall_fin_add]
      simp
@[simp] lemma centersBound_mean (A r : ℝ) (E : MeanTree X d) :
    centersBound A (mean r E) ↔ weight E≤A ∧ centersBound A E := by
  simp [mean,centersBound]
lemma centersBound_sumFin (A : ℝ) (k : ℕ) (E : Fin k → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFin k E) := by
  induction k with
  | zero => simp [sumFin]
  | succ k ih => exact (centersBound_add _ _ _).2 ⟨hE 0,ih _ (fun i => hE i.succ)⟩
lemma centersBound_sumFamily {I : Type*} [Fintype I] (A : ℝ) (E : I → MeanTree X d)
    (hE : ∀i,centersBound A (E i)) : centersBound A (sumFamily E) := by
  exact centersBound_sumFin A _ _ (fun i => hE _)
lemma centersBound_conditional {A r t : ℝ} {x y : MeanTree X d}
    (hx : centersBound A x) (hy : centersBound A y)
    (hw : weight x+|r*t| * weight y≤A) : centersBound A (conditional r t x y) := by
  simp only [conditional,centersBound_mean,weight_add,weight_scale,centersBound_add,centersBound_scale]
  exact ⟨hw,hx,hy⟩

lemma weight_picard {I : Type*} [Fintype I] (w : I → I → ℝ)
    (φ : I → MeanTree X d → MeanTree X d) (a : I → MeanTree X d)
    {B C : ℝ} (hC : 0≤C) (hw : ∀i,∑j,|w i j|≤B)
    (hφ : ∀i E,weight (φ i E)≤C) (N : ℕ) (i : I) :
    weight (picard w φ a N i)≤weight (a i)+B*C := by
  have hB : 0≤B := (Finset.sum_nonneg (fun _ _ => abs_nonneg _)).trans (hw i)
  cases N with
  | zero => simpa only [picard] using (le_add_of_nonneg_right (a:=weight (a i)) (mul_nonneg hB hC))
  | succ N =>
    simp only [picard,weight_add,weight_sumFamily,weight_scale]
    apply add_le_add_right
    calc
      _≤∑j,|w i j| * C := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hφ j _) (abs_nonneg _))
      _=(∑j,|w i j|)*C := (Finset.sum_mul _ _ _).symm
      _≤B*C := mul_le_mul_of_nonneg_right (hw i) hC

end LogConcaveSampling.MeanTree

end

end

end OAI
