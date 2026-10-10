import Mathlib
import OAI.Analysis.Conductivity.Flux.AntisymmetricFlux
import OAI.Analysis.Conductivity.Branching.CascadeLocality

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory

def cascadePotentialTerm (L K k A : ℝ) (n : ℕ) (i j : Fin 3) (x : Coord3) : ℝ :=
  (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j
    ((k*2^n) • (x-cascadeCenter (cascadeLength L K) k n))

lemma cascadePotentialTerm_inactive {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) {m n : ℕ}
    (hm₁ : -L/8 < cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K+L/8)
    (hn : n≠m) (hn' : n≠m+1) (i j : Fin 3) :
    cascadePotentialTerm L K k A n i j x = 0 := by
  obtain ⟨_,hb,hc⟩ := cascadeMother_inactive_wide hL hK hk x hm₁ hm₂ hn hn'
  simp [cascadePotentialTerm,cascadePotentialMother,hb,hc]

lemma cascadePotential_two_terms {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) {m : ℕ}
    (hm₁ : -L/8 < cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) < cascadeLength L K+L/8)
    (i j : Fin 3) : cascadePotential L K k A i j x =
      cascadePotentialTerm L K k A m i j x + cascadePotentialTerm L K k A (m+1) i j x := by
  have he : (∑' n : ℕ, cascadePotentialTerm L K k A n i j x) =
      ∑ n ∈ ({m,m+1} : Finset ℕ), cascadePotentialTerm L K k A n i j x :=
    tsum_eq_sum (s := ({m,m+1} : Finset ℕ)) (fun n hn =>
      cascadePotentialTerm_inactive hL hK hk A x hm₁ hm₂
        (by simpa using fun h => hn (by simp [h]))
        (by simpa using fun h => hn (by simp [h])) i j)
  simpa [cascadePotential,cascadePotentialTerm,Finset.sum_pair (show m≠m+1 by omega)] using he

lemma cascade_stage_nhds {L K k : ℝ} (hL : 0 < L) (x : Coord3) {m : ℕ}
    (hm₁ : 0 ≤ cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) ≤ cascadeLength L K) :
    {y : Coord3 | -L/8 < cascadePhase (cascadeLength L K) k m (y 0) ∧
      cascadePhase (cascadeLength L K) k m (y 0) < cascadeLength L K+L/8} ∈ 𝓝 x := by
  have hc : Continuous (fun y : Coord3 => cascadePhase (cascadeLength L K) k m (y 0)) := by
    unfold cascadePhase
    fun_prop
  exact (hc.isOpen_preimage _ isOpen_Ioo).mem_nhds ⟨by linarith,by linarith⟩

lemma cascadePotential_eventually_two_terms {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) {m : ℕ}
    (hm₁ : 0 ≤ cascadePhase (cascadeLength L K) k m (x 0))
    (hm₂ : cascadePhase (cascadeLength L K) k m (x 0) ≤ cascadeLength L K)
    (i j : Fin 3) : cascadePotential L K k A i j =ᶠ[𝓝 x]
      fun y => cascadePotentialTerm L K k A m i j y + cascadePotentialTerm L K k A (m+1) i j y := by
  filter_upwards [cascade_stage_nhds hL x hm₁ hm₂] with y hy
  exact cascadePotential_two_terms hL hK hk A y hy.1 hy.2 i j

lemma cascadePotential_terminal {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K ≤ k*x 0) (i j : Fin 3) :
    cascadePotential L K k A i j x = 0 := by
  have hh (n : ℕ) : cascadePotentialTerm L K k A n i j x = 0 := by
    let y := (k*2^n) • (x-cascadeCenter (cascadeLength L K) k n)
    have hy : K+2+7*L/4 < y 0 := by
      dsimp only [y]
      rw [cascade_dilation_time hk,cascadePhase]
      have hp : 0 ≤ (2:ℝ)^n*(k*x 0-2*cascadeLength L K) := mul_nonneg (by positivity) (by linarith)
      unfold cascadeLength at *
      linarith
    have hb := cascadeBaseStream_zero hL (cascadeAxis n) y (Or.inr hy)
    have hc := cascadeCrossStream_zero_right hL (cascadeAxis n) (cascadeAxis (n+1)) y hy
    change (A*cascadeRatio L K^n)*cascadePotentialMother L K (cascadeAxis n) (cascadeAxis (n+1)) i j y=0
    simp [cascadePotentialMother,hb,hc]
  change (∑' n : ℕ, cascadePotentialTerm L K k A n i j x)=0
  simp only [hh,tsum_zero]

lemma cascadeFlux_terminal_strict {L K k : ℝ} (hL : 0 < L) (hK : 0 < K) (hk : k≠0)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K < k*x 0) (i : Fin 3) :
    cascadeFlux L K k A x i = 0 := by
  have hn : {y : Coord3 | 2*cascadeLength L K < k*y 0} ∈ 𝓝 x :=
    (isOpen_lt continuous_const (continuous_const.mul (continuous_apply 0))).mem_nhds ht
  unfold cascadeFlux
  apply Finset.sum_eq_zero
  intro j _
  have he : cascadePotential L K k A i j =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [hn] with y hy
    exact cascadePotential_terminal hL hK hk A y hy.le i j
  simp [direction,he.fderiv_eq]

lemma cascadeFlux_terminal {L K k : ℝ} (hL : 1 ≤ L) (hK : 0 < K) (hk : 0 < k)
    (A : ℝ) (x : Coord3) (ht : 2*cascadeLength L K ≤ k*x 0) (i : Fin 3) :
    cascadeFlux L K k A x i = 0 := by
  have hcont : Continuous (fun r : ℝ => cascadeFlux L K k A (x+r • Pi.single 0 1) i) :=
    (cascadeFlux_C1 hL hK k A i).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hlim : Tendsto (fun r : ℝ => cascadeFlux L K k A (x+r • Pi.single 0 1) i)
      (𝓝[>] (0:ℝ)) (𝓝 (cascadeFlux L K k A x i)) := by
    simpa only [ContinuousWithinAt,zero_smul,add_zero] using (hcont.continuousAt (x := (0:ℝ))).continuousWithinAt (s := Ioi (0:ℝ))
  have he : (fun r : ℝ => cascadeFlux L K k A (x+r • Pi.single 0 1) i) =ᶠ[𝓝[>] (0:ℝ)]
      fun _ => (0:ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    apply cascadeFlux_terminal_strict (lt_of_lt_of_le (by norm_num) hL) hK hk.ne' A
    simp only [Pi.add_apply,Pi.smul_apply,Pi.single_eq_same,smul_eq_mul,mul_one]
    have hp : 0 < k*r := mul_pos hk hr
    nlinarith
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

end ScalarConductivity

end

end OAI
