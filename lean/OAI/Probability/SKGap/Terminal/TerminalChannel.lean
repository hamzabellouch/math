import Mathlib
import OAI.Probability.SKGap.Terminal.TerminalProbability
import OAI.Probability.SKGap.Terminal.TerminalHighProbability
import OAI.Probability.SKGap.Posterior.ChannelTranslation

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal
variable {n : ℕ}

lemma channel_field_shift {T : ℝ} (hT : 0 ≤ T) (x : Spin n) (z : Fin n→ℝ) :
    (fun i=>sqrt T*(z i+sqrt T*spinValue (x i)))=observationField T x z := by
  funext i
  simp only [observationField]
  calc
    _ = sqrt T*z i+(sqrt T)^2*spinValue (x i) := by ring
    _ = _ := by rw [sq_sqrt hT];ring

lemma gaussianChannel_terminal_bad (g : Disorder n) {T c : ℝ} (hT : 0 ≤ T)
    (hh : ∀ x : Spin n,(channelReference n).real {z | ¬∀ f : Spin n→ℝ,
      variance g (observationField T x z) f ≤ 2*dirichlet g (observationField T x z) f} ≤ exp (-c*(n:ℝ))) :
    (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-c*(n:ℝ)) := by
  let B : Set (Fin n→ℝ) := {z | ¬∀ f : Spin n→ℝ,
    variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f}
  have hB : MeasurableSet B :=
    ((terminal_goodSet_closed g 2).measurableSet.compl).preimage (by fun_prop)
  have he := gaussianChannel_event g hT B hB
  have hx (x : Spin n) : channelReference n
      ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B) ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    have hb : ((fun z : Fin n→ℝ=>fun i=>z i+sqrt T*spinValue (x i)) ⁻¹' B)=
        {z | ¬∀ f : Spin n→ℝ,variance g (observationField T x z) f ≤
          2*dirichlet g (observationField T x z) f} := by
      ext z
      simp only [Set.mem_preimage,B,Set.mem_ofPred_eq,channel_field_shift hT]
    rw [hb]
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
      (by simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hh x)
  have hs : (∑ x : Spin n,ENNReal.ofReal (mass g 0 x))=1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _=>mass_nonneg g 0 x),sum_mass]
    exact ENNReal.ofReal_one
  have hb : gaussianChannelLaw g T B ≤ ENNReal.ofReal (exp (-c*(n:ℝ))) := by
    rw [he]
    calc
      _ ≤ ∑ x,ENNReal.ofReal (mass g 0 x)*ENNReal.ofReal (exp (-c*(n:ℝ))) :=
        Finset.sum_le_sum (fun x _=>by gcongr;exact hx x)
      _ = _ := by rw [← Finset.sum_mul,hs,one_mul]
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simpa only [measureReal_def,ENNReal.toReal_ofReal (exp_pos _).le] using hr
end SKGap

end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators Topology Matrix.Norms.L2Operator
variable {n : ℕ}

lemma terminalMatrixBound_nonneg {j : ℝ} (hj : 0 ≤ j) : 0 ≤ terminalMatrixBound j := by
  unfold terminalMatrixBound terminalRowBound
  have hlog : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  positivity

lemma terminal_endpoint_from_data {M α ε T : ℝ} (hM : 0 ≤ M) (hT : 0 < T) (hε : 0 ≤ ε)
    (hsmall : M^2 ≤ (T/4)^2*α/2)
    (hnum : 400001*(ε+M*(2*sqrt (1/cosh (T/4)^2)+1/cosh (T/4)^2)) ≤ 1/4)
    (hp : exp (-T/8)*(exp 1-1) ≤ α/4)
    (hn₁ : terminalEntryScale n ≤ 1/1000) (hn₂ : 800000*(M*terminalEntryScale n^2) ≤ 1/4)
    (g : Disorder n) (hg : terminalMatrixData M α ε g) :
    (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
      variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-(α/4)*(n:ℝ)) := by
  apply gaussianChannel_terminal_bad g hT.le
  intro x
  have hc (i k : Fin n) : |tanh (coupling g i k)| ≤ 1/1000 :=
    (abs_tanh_le_abs _).trans ((hg.1 i k).trans hn₁)
  have hh := terminal_probability_fixedSpin g hM hT hε hg.2.1 hg.2.2.1 hg.2.2.2.1 hc hg.2.2.2.2.1
    (terminalMatrixData_forms g hg) hsmall (by linarith only [hnum,hn₂]) hp x
  convert hh using 1
  congr 1
  ring

lemma terminal_numeric_eventually (M : ℝ) : ∀ᶠ n : ℕ in atTop,
    terminalEntryScale n ≤ 1/1000 ∧ 800000*(M*terminalEntryScale n^2) ≤ 1/4 := by
  have ht := (terminalEntryScale_tendsto.pow 2).const_mul M |>.const_mul 800000
  simp only [zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] at ht
  exact (terminalEntryScale_tendsto.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/1000))).and
    (ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1/4)))

theorem terminal_gap_high_probability {β : ℝ} (hβ : 0 < β) :
    ∃ T a : ℝ,0 < T ∧ 0 < a ∧ ∃ Ω : (n : ℕ)→Set (Disorder n),
      (∀ n,MeasurableSet (Ω n)) ∧
      Tendsto (fun n=>(disorderLaw β n).real (Ω n)) atTop (𝓝 1) ∧
      ∀ (n : ℕ) (g : Disorder n),g ∈ Ω n →
        (gaussianChannelLaw g T).real {z | ¬∀ f : Spin n→ℝ,
          variance g (fun i=>sqrt T*z i) f ≤ 2*dirichlet g (fun i=>sqrt T*z i) f} ≤ exp (-a*(n:ℝ)) := by
  let ε : ℝ := 1/(16*400001)
  have hε : 0 < ε := by norm_num [ε]
  obtain ⟨α,l,hα,hαhalf,hl,hedge,h₅,h₆⟩ := sparse_parameters (sq_pos_of_pos hβ) hε
  let M := terminalMatrixBound (β^2)
  have hM : 0 ≤ M := terminalMatrixBound_nonneg (sq_nonneg β)
  obtain ⟨T,hT,hsmall,hnum,hp⟩ := terminalTime_exists hM hα (show 400001*ε < 1/4 by norm_num [ε])
  obtain ⟨N,hN⟩ := eventually_atTop.mp (terminal_numeric_eventually M)
  let Ω : (n : ℕ)→Set (Disorder n) := fun n=>if N ≤ n then {g | terminalMatrixData M α ε g} else ∅
  have hΩ (n : ℕ) : MeasurableSet (Ω n) := by
    dsimp [Ω]
    split_ifs
    · exact terminalMatrixData_measurable M α ε
    · exact MeasurableSet.empty
  refine ⟨T,α/4,hT,(by positivity),Ω,hΩ,?_,?_⟩
  · apply Tendsto.congr' _ (terminalMatrixData_actual_whp hβ hα.le hε hl hedge h₅ h₆)
    filter_upwards [eventually_ge_atTop N] with n hn
    simp only [Ω,ite_eq_left hn]
    rfl
  · intro n g hg
    have hn : N ≤ n := by
      by_contra hn
      simp only [Ω,ite_eq_right hn,Set.mem_empty_iff_false] at hg
    have hd : terminalMatrixData M α ε g := by simpa only [Ω,ite_eq_left hn,Set.mem_ofPred_eq] using hg
    exact terminal_endpoint_from_data hM hT hε.le hsmall hnum hp (hN n hn).1 (hN n hn).2 g hd
end SKGap

end
end

end OAI
