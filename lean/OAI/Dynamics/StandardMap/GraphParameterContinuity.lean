import OAI.Dynamics.StandardMap.ScaledContraction

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma continuous_liftedOrbit_pair (k : ℝ) (n : ℕ) :
    Continuous (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n) :=
  continuous_iff_continuousAt.mpr (fun z =>
    (hasStrictFDerivAt_liftedOrbit k z.1 z.2 n).continuousAt)
lemma continuousOn_linearSolution_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (a b : α → ℝ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ha : ContinuousOn a s) (hb : ContinuousOn b s) (n : ℕ) :
    ContinuousOn (fun x => linearSolution (v x) (a x) (b x) n) s := by
  induction n using Nat.twoStepInduction with
  | zero => exact ha
  | one => exact hb
  | more n h0 h1 => exact ((hv (n+1)).mul h1).sub h0
lemma continuousOn_dirichlet_params {α : Type*} [TopologicalSpace α]
    (s : Set α) (v : α → ℕ → ℝ) (j p : ℕ)
    (hv : ∀ n, ContinuousOn (fun x => v x n) s)
    (ht : ∀ x ∈ s, tSolution (v x) j ≠ 0) :
    ContinuousOn (fun x => dirichletSolution (v x) j p) s := by
  have hb : ContinuousOn (fun x => boundaryValue (v x) j) s :=
    (continuousOn_linearSolution_params s v (fun _ => 1) (fun _ => 0) hv
      continuousOn_const continuousOn_const j).neg.div
      (continuousOn_linearSolution_params s v (fun _ => 0) (fun _ => 1) hv
        continuousOn_const continuousOn_const j) ht
  exact continuousOn_linearSolution_params s v (fun _ => 1) _ hv continuousOn_const hb p

lemma continuousOn_nonlinear_dirichlet_corrections (k : ℝ) (n : ℕ) (hk : 0 ≤ k)
    (hq : growthBase k^(-(3/5:ℝ)) ≤ 1/2)
    (hsmall : (384*Real.pi)*growthBase k^(-(7/10:ℝ)) ≤ 1/2)
    (s : Set ((ℝ × ℝ) × ℝ)) (ξ : ((ℝ × ℝ) × ℝ) → Fin n → ℝ)
    (ht : ∀ z ∈ s, tSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) ≠ 0)
    (hU : ∀ z ∈ s, ∀ p, 1 ≤ p → p ≤ n →
      |dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) p| ≤
        12*growthBase k^(-(9/10:ℝ)*(p:ℝ)))
    (hξb : ∀ z ∈ s, ∀ i, |ξ z i| ≤ 8/growthBase k^((4/5:ℝ)*((i:ℝ)+1)))
    (hξ : ∀ z ∈ s, ∀ i, ξ z i=
      dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)*z.2+
        ∑ j, greenMatrix (orbitCoefficient k z.1.1 z.1.2) n i j *
          (-(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+ξ z j)-
            phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
            potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*ξ z j))) :
    ContinuousOn ξ s := by
  let M := growthBase k
  have hp : 0 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  let w : Fin n → ℝ := fun i => M^((4/5:ℝ)*((i:ℝ)+1))
  let U : ((ℝ × ℝ) × ℝ) → Fin n → ℝ := fun z i =>
    dirichletSolution (orbitCoefficient k z.1.1 z.1.2) (n+1) (i+1)
  let G : ((ℝ × ℝ) × ℝ) → Fin n → Fin n → ℝ := fun z =>
    greenMatrix (orbitCoefficient k z.1.1 z.1.2) n
  let F : ((ℝ × ℝ) × ℝ) → Fin n → ℝ → ℝ := fun z j u =>
    -(phi k (liftedOrbit k z.1.1 z.1.2 (j+1)+u)-
      phi k (liftedOrbit k z.1.1 z.1.2 (j+1))-
      potential k (liftedOrbit k z.1.1 z.1.2 (j+1))*u)
  let L : Fin n → ℝ := fun i => (2*Real.pi*M)*8/w i
  have ho (p : ℕ) : Continuous (fun z : ((ℝ × ℝ) × ℝ) => liftedOrbit k z.1.1 z.1.2 p) :=
    (continuous_liftedOrbit_pair k p).comp continuous_fst
  have hpot : Continuous (potential k) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_potential k x).continuousAt)
  have hphi : Continuous (phi k) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_phi k x).continuousAt)
  have hv (p : ℕ) : ContinuousOn
      (fun z : ((ℝ × ℝ) × ℝ) => orbitCoefficient k z.1.1 z.1.2 p) s :=
    (hpot.comp (ho p)).continuousOn
  apply continuousOn_weighted_fixedPoints s w U G F L Prod.snd 8 ξ
    (fun i => Real.rpow_pos_of_pos hp _) (by norm_num)
    (fun i => by dsimp only [L,w]; positivity) hξb hξ
  · intro z hz i x y hx hy
    dsimp only [F]
    rw [← neg_sub,abs_neg]
    have hh:=phi_remainder_lipschitz k (liftedOrbit k z.1.1 z.1.2 (i+1)) x y (8/w i) hk hx hy
    dsimp only [L,M]
    convert hh using 1 <;> ring_nf
  · intro z hz i
    exact bridge_green_row k z.1.1 z.1.2 n hk hq hsmall (hU z hz) i
  · intro i
    exact continuousOn_dirichlet_params s _ (n+1) (i+1) hv ht
  · intro i j
    exact (continuousOn_linearSolution_params s _ (fun _ => 0) (fun _ => 1) hv
      continuousOn_const continuousOn_const (min ((i:ℕ)+1) ((j:ℕ)+1))).mul
      (continuousOn_dirichlet_params s _ (n+1) (max ((i:ℕ)+1) ((j:ℕ)+1)) hv ht)
  · intro i x
    exact (((hphi.comp ((ho (i+1)).add_const x)).sub
      (hphi.comp (ho (i+1)))).sub ((hpot.comp (ho (i+1))).mul_const x)).neg.continuousOn
  · exact continuous_snd.continuousOn
end StandardMapEntropy

end OAI
