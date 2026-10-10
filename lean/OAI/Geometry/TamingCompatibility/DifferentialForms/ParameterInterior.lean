import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.QuantitativeLocalStep
import OAI.Geometry.TamingCompatibility.DifferentialForms.UniformInterior

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertSobolev
open MeasureTheory TemperedDistribution EuclideanSobolevOperators Filter
open scoped SchwartzMap LineDeriv Topology ContDiff
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {P : Type*} [TopologicalSpace P]
lemma parameter_matrixLowerH_eventually_bounded {ι κ : Type*} [Fintype ι] [Fintype κ] (p₀ : P) (n : ℕ)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (v : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀, ‖matrixLowerH n (b r) L v (c r) K‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : P → ℝ := fun r =>
      (∑ i, (A * coefficientSize n (b r i)) * ‖fiberOperator (E := E) n (L i)‖ *
        ‖derivative (F := F) ((n:ℝ)+1) (v i)‖) +
      ∑ i, (A * coefficientSize n (c r i)) * ‖fiberOperator (E := E) n (K i)‖ *
        ‖inclusion (E := E) (F := F) (s := (n:ℝ)+1) (t := (n:ℝ)) (by linarith : (n:ℝ) ≤ n+1)‖
  have hS : ContinuousAt S p₀ := by
    apply ContinuousAt.add <;> apply tendsto_finsetSum <;> intro i _
    · exact (((hb i).const_mul A).mul_const _).mul_const _
    · exact (((hc i).const_mul A).mul_const _).mul_const _
  have hbnd (r : P) : ‖matrixLowerH n (b r) L v (c r) K‖ ≤ S r := by
    apply (matrixLowerH_norm_le n (b r) L v (c r) K).trans
    dsimp only [S]
    gcongr
    · exact hprod _
    · exact hprod _
  refine ⟨|S p₀|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, S r < |S p₀|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S p₀)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le

lemma parameter_localizationErrorH_eventually_bounded (p₀ : P) (n : ℕ)
    (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ)) (g : 𝓢(E,ℂ))
    (ha : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀, ‖localizationErrorH (F := F) n (a r) g‖ ≤ C := by
  obtain ⟨A,hA,hprod⟩ := product_operator_estimate (E := E) (F := F) n
  let S : P → ℝ := fun r =>
      |((2*Real.pi)^2)⁻¹| * ∑ i, ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E i)‖ +
      ∑ i, ∑ j, (A * coefficientSize n (a r i j)) * ‖secondCommutatorH (F := F) n g
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j)‖
  have hS : ContinuousAt S p₀ := by
    apply ContinuousAt.add continuousAt_const
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact ((ha i j).const_mul A).mul_const _
  have hbnd (r : P) : ‖localizationErrorH (F := F) n (a r) g‖ ≤ S r := by
    apply (localizationErrorH_norm_le n (a r) g).trans
    dsimp only [S]
    gcongr
    exact hprod _
  refine ⟨|S p₀|+1, by positivity, ?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, S r < |S p₀|+1 :=
    hS.eventually (gt_mem_nhds (by linarith [le_abs_self (S p₀)]))
  exact he.mono fun r hr => (hbnd r).trans hr.le

theorem parameter_uniform_local_step {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p₀ : P) (n : ℕ) (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ η : 𝓢(E,ℂ)) (hη : ∀ x ∈ tsupport χ, η =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀,
      ∀ (u : 𝓢'(E,F)) (f : H E F n) (v : H E F ((n:ℝ)+2)) (w : H E F ((n:ℝ)+1)),
      toDistribution E F ((n:ℝ)+2) v = smulLeftCLM F χ u →
      toDistribution E F ((n:ℝ)+1) w = smulLeftCLM F η u →
      smulLeftCLM F χ (perturbedHelmholtz (a r) u + matrixLowerOrder (b r) L d (c r) K u) =
        smulLeftCLM F χ (toDistribution E F n f) →
      ‖v‖ ≤ C * (‖f‖ + ‖w‖) := by
  obtain ⟨B,hB,hboundB⟩ := parameter_matrixLowerH_eventually_bounded p₀ n b L d c K hb hc
  obtain ⟨D,hD,hboundD⟩ := parameter_localizationErrorH_eventually_bounded (F := F) p₀ n a χ hac
  let P := ‖product (F := F) n χ‖
  have hP : 0 ≤ P := norm_nonneg _
  refine ⟨2*(P+P*B+D+1),by positivity,?_⟩
  have hhalf : ∀ᶠ r in 𝓝 p₀, ‖perturbation (F := F) n (a r)‖ < 1/2 :=
    ha.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hhalf,hboundB,hboundD] with r hr hrB hrD
  intro u f v w hv hw heq
  have h := small_principal_local_step n (a r) hr.le (b r) L d (c r) K χ η hη
    u f v w hv hw heq
  apply h.trans
  change 2*(P*‖f‖+(P*‖matrixLowerH n (b r) L d (c r) K‖+
    ‖localizationErrorH (F := F) n (a r) χ‖)*‖w‖) ≤ _
  calc
    _ ≤ 2*(P*‖f‖+(P*B+D)*‖w‖) := by gcongr
    _ ≤ 2*(P+P*B+D+1)*(‖f‖+‖w‖) := by
      have hpb : 0 ≤ P*B := mul_nonneg hP hB.le
      nlinarith [norm_nonneg f,norm_nonneg w,mul_nonneg (by positivity : 0 ≤ P*B+D+1)
        (norm_nonneg f),mul_nonneg (by positivity : 0 ≤ P+1) (norm_nonneg w)]

private lemma parameter_finite_step_bound (N : ℕ) (a : ℕ → ℝ) {B f : ℝ}
    (hB : 1 ≤ B) (hf : 0 ≤ f) (ha : 0 ≤ a 0)
    (hstep : ∀ n ≤ N, a (n+1) ≤ B*(f+a n)) :
    a (N+1) ≤ (2*B)^(N+1)*(f+a 0) := by
  have hpow (n : ℕ) : 1 ≤ (2*B)^n := one_le_pow₀ (by linarith)
  have hi : ∀ n ≤ N+1, a n ≤ (2*B)^n*(f+a 0) := by
    intro n
    induction n with
    | zero => intro _; simp; linarith
    | succ n ih =>
      intro hn
      have hn' : n ≤ N := by omega
      have hi' := ih (by omega)
      calc
        a (n+1) ≤ B*(f+a n) := hstep n hn'
        _ ≤ B*(f+(2*B)^n*(f+a 0)) := by gcongr
        _ ≤ B*((2*B)^n*(f+a 0)+(2*B)^n*(f+a 0)) := by
          gcongr
          calc f ≤ f+a 0 := le_add_of_nonneg_right ha
               _ ≤ (2*B)^n*(f+a 0) := le_mul_of_one_le_left (add_nonneg hf ha) (hpow n)
        _ = (2*B)^(n+1)*(f+a 0) := by rw [pow_succ]; ring
  exact hi _ le_rfl

theorem parameter_uniform_finite_bootstrap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p₀ : P) (N : ℕ) (a : P → basisIndex E → basisIndex E → 𝓢(E,ℂ))
    (ha : ∀ n ≤ N, Tendsto (fun r => ‖perturbation (F := F) n (a r)‖) (𝓝 p₀) (𝓝 0))
    (hac : ∀ n ≤ N, ∀ i j, ContinuousAt (fun r => coefficientSize n (a r i j)) p₀)
    (b : P → ι → 𝓢(E,ℂ)) (L : ι → F →L[ℂ] F) (d : ι → E)
    (c : P → κ → 𝓢(E,ℂ)) (K : κ → F →L[ℂ] F)
    (hb : ∀ n ≤ N, ∀ i, ContinuousAt (fun r => coefficientSize n (b r i)) p₀)
    (hc : ∀ n ≤ N, ∀ i, ContinuousAt (fun r => coefficientSize n (c r i)) p₀)
    (χ : ℕ → 𝓢(E,ℂ))
    (hχ : ∀ n ≤ N, ∀ x ∈ tsupport (χ (n+1)), χ n =ᶠ[𝓝 x] fun _ => 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r in 𝓝 p₀,
      ∀ (u : 𝓢'(E,F)) (f : H E F N) (v : (n : ℕ) → H E F ((n:ℝ)+1)),
      (∀ n ≤ N+1, toDistribution E F ((n:ℝ)+1) (v n) = smulLeftCLM F (χ n) u) →
      (∀ n ≤ N, smulLeftCLM F (χ (n+1))
          (perturbedHelmholtz (a r) u + matrixLowerOrder (b r) L d (c r) K u) =
        smulLeftCLM F (χ (n+1)) (toDistribution E F N f)) →
      ‖v (N+1)‖ ≤ C * (‖f‖ + ‖v 0‖) := by
  classical
  have hi (i : Fin (N+1)) := parameter_uniform_local_step p₀ i.val a (ha i.val (by omega))
    (hac i.val (by omega)) b L d c K (hb i.val (by omega)) (hc i.val (by omega))
    (χ (i.val+1)) (χ i.val) (hχ i.val (by omega))
  choose B hB hbound using hi
  let C := 1 + ∑ i : Fin (N+1), B i
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hB i).le))
  have hBC (i : Fin (N+1)) : B i ≤ C := by
    have h := Finset.single_le_sum (fun j _ => (hB j).le) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  refine ⟨(2*C)^(N+1),by positivity,?_⟩
  have he : ∀ᶠ r in 𝓝 p₀, ∀ i : Fin (N+1), _ := Filter.eventually_all.mpr hbound
  filter_upwards [he] with r hr
  intro u f v hv heq
  apply parameter_finite_step_bound N (fun n => ‖v n‖) hC (norm_nonneg f) (norm_nonneg (v 0))
  intro n hn
  let i : Fin (N+1) := ⟨n,by omega⟩
  let fn : H E F n := inclusion (s := (N:ℝ)) (t := (n:ℝ)) (by exact_mod_cast hn) f
  have hfn : toDistribution E F n fn = toDistribution E F N f :=
    toDistribution_inclusion (by exact_mod_cast hn) f
  have hvn : toDistribution E F ((n:ℝ)+2) (v (n+1)) = smulLeftCLM F (χ (n+1)) u := by
    have h := hv (n+1) (by omega)
    have he : (((n+1:ℕ):ℝ)+1) = (n:ℝ)+2 := by push_cast; ring
    rw [← he]
    exact h
  have ht := hr i u fn (v (n+1)) (v n) hvn (hv n (by omega))
    (by
      change smulLeftCLM F (χ (n+1)) _ = smulLeftCLM F (χ (n+1)) (toDistribution E F n fn)
      rw [hfn]
      exact heq n hn)
  apply ht.trans
  calc
    B i * (‖fn‖+‖v n‖) ≤ C * (‖fn‖+‖v n‖) := by gcongr; exact hBC i
    _ ≤ C * (‖f‖+‖v n‖) := by
      gcongr
      exact inclusion_norm_le (by exact_mod_cast hn) f

end TamingCompatibility.HilbertSobolev

end

end OAI
