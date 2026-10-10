import Mathlib
import OAI.Analysis.BoundedHochschild.Ultrapowers

namespace OAI

/-! Hilbert-valued martingale limits and random-walk mean-square convergence. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
namespace HochschildMartingale

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
 
lemma energy_identity (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0) {k n : ℕ} (hkn : k ≤ n) :
    ‖Z n - Z k‖ ^ 2 = ‖Z n‖ ^ 2 - ‖Z k‖ ^ 2 := by
  have h := horth k n hkn
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at h
  rw [norm_sub_sq_real]
  linarith

 

theorem exists_limit_of_bounded_orthogonal_increments (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0)
    (C : ℝ) (hb : ∀ n, ‖Z n‖ ≤ C) :
    ∃ z : H, Tendsto Z atTop (𝓝 z) ∧
      ∀ k n, k ≤ n → ‖Z n - Z k‖ ^ 2 = ‖z - Z k‖ ^ 2 - ‖z - Z n‖ ^ 2 := by
  have hmono : Monotone (fun n => ‖Z n‖ ^ 2) := by
    intro k n hkn
    have := sq_nonneg ‖Z n-Z k‖
    rw [energy_identity Z horth hkn] at this
    linarith
  have hbd : BddAbove (Set.range (fun n => ‖Z n‖^2)) := by
    refine ⟨C^2, ?_⟩
    rintro x ⟨n,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (hb n) _
  let L : ℝ := ⨆ n, ‖Z n‖^2
  have hlim : Tendsto (fun n => ‖Z n‖^2) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbd
  have hc : CauchySeq Z := by
    apply cauchySeq_of_le_tendsto_0' (fun n => Real.sqrt (L-‖Z n‖^2))
    · intro n m hnm
      rw [dist_eq_norm, norm_sub_rev]
      apply Real.le_sqrt_of_sq_le
      rw [energy_identity Z horth hnm]
      exact sub_le_sub_right (le_ciSup hbd m) _
    · simpa only [sub_self, Real.sqrt_zero] using ((tendsto_const_nhds (x := L)).sub hlim).sqrt
  obtain ⟨z,hz⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨z,hz,?_⟩
  intro k n hkn
  have he (i : ℕ) : ‖z-Z i‖^2 = ‖z‖^2-‖Z i‖^2 := by
    have ha : Tendsto (fun m => ‖Z m-Z i‖^2) atTop (𝓝 (‖z-Z i‖^2)) :=
      (hz.sub_const _).norm.pow 2
    have hb' : Tendsto (fun m => ‖Z m‖^2-‖Z i‖^2) atTop (𝓝 (‖z‖^2-‖Z i‖^2)) :=
      (hz.norm.pow 2).sub_const _
    exact tendsto_nhds_unique ha (hb'.congr' (eventually_atTop.2
      ⟨i,fun m hm => (energy_identity Z horth hm).symm⟩))
  rw [he k,he n,energy_identity Z horth hkn]
  ring

 
theorem uniform_cauchy_error (Z : ℕ → H)
    (horth : ∀ k n, k ≤ n → inner ℝ (Z n - Z k) (Z k) = 0)
    (C : ℝ) (hb : ∀ n, ‖Z n‖ ≤ C) :
    ∃ z : H, Tendsto Z atTop (𝓝 z) ∧
      Tendsto (fun k => ‖z-Z k‖^2) atTop (𝓝 0) ∧
      ∀ k n, k ≤ n → ‖Z n-Z k‖^2 ≤ ‖z-Z k‖^2 := by
  obtain ⟨z,hz,he⟩ := exists_limit_of_bounded_orthogonal_increments Z horth C hb
  refine ⟨z,hz,?_,fun k n hkn => ?_⟩
  · simpa using ((tendsto_const_nhds (x := z)).sub hz).norm.pow 2
  · rw [he k n hkn]
    exact sub_le_self _ (sq_nonneg _)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {f : ℕ → Ω → H}

 
lemma martingale_L2_orthogonal (hm : Martingale f ℱ μ) (h2 : ∀ n, MemLp (f n) 2 μ)
    {k n : ℕ} (hkn : k ≤ n) :
    inner ℝ ((h2 n).toLp (f n) - (h2 k).toLp (f k)) ((h2 k).toLp (f k)) = 0 := by
  have hcond : (condExpL2 H ℝ (ℱ.le k) ((h2 n).toLp (f n)) : Lp H 2 μ) =
      (h2 k).toLp (f k) := by
    apply Lp.ext
    exact ((h2 n).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le k)).trans
      ((hm.2 k n hkn).trans (h2 k).coeFn_toLp.symm)
  have hinner := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (ℱ.le k) ((h2 n).toLp (f n))
    ((h2 k).toLp (f k))
    (((hm.stronglyMeasurable k).aestronglyMeasurable).congr (h2 k).coeFn_toLp.symm)
  rw [hcond] at hinner
  rw [inner_sub_left, ← hinner, sub_self]

 
theorem martingale_L2_convergence (hm : Martingale f ℱ μ) (h2 : ∀ n, MemLp (f n) 2 μ)
    (C : ℝ) (hb : ∀ n, ‖(h2 n).toLp (f n)‖ ≤ C) :
    ∃ z : Lp H 2 μ, Tendsto (fun n => (h2 n).toLp (f n)) atTop (𝓝 z) ∧
      Tendsto (fun k => ‖z-(h2 k).toLp (f k)‖^2) atTop (𝓝 0) ∧
      ∀ k n, k ≤ n → ‖(h2 n).toLp (f n)-(h2 k).toLp (f k)‖^2 ≤
        ‖z-(h2 k).toLp (f k)‖^2 :=
  uniform_cauchy_error _ (fun _ _ hkn => martingale_L2_orthogonal hm h2 hkn) C hb

end HochschildMartingale

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
namespace HochschildWalk
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

 
def pathMeasure : Measure (ℕ → G) := Measure.infinitePi (fun _ : ℕ => μ)
instance : IsProbabilityMeasure (pathMeasure μ) := by unfold pathMeasure; infer_instance

def takePath (n : ℕ) (ω : ℕ → G) : Fin n → G := fun i => ω i

def word {n : ℕ} (ω : Fin n → G) : G := (List.ofFn ω).prod

def walk (n : ℕ) (ω : ℕ → G) : G := word (takePath n ω)

omit [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] in
lemma walk_succ (n : ℕ) (ω : ℕ → G) : walk (n+1) ω = walk n ω * ω n := by
  unfold walk word
  rw [List.ofFn_succ', List.prod_concat]
  rfl

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
lemma takePath_measurable (n : ℕ) : Measurable (takePath (G := G) n) := by
  exact Measurable.of_eval (fun index : Fin n => measurable_pi_apply (index : ℕ))

omit [Group G] [Countable G] [MeasurableSingletonClass G] in
lemma takePath_law (n : ℕ) : (pathMeasure μ).map (takePath n) = Measure.pi (fun _ : Fin n => μ) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ)
    (f := (Fin.val : Fin n → ℕ)) Fin.val_injective
  change (Measure.infinitePi (fun _ : ℕ => μ)).map (fun ω (i : Fin n) => ω (i : ℕ)) = _
  rw [h, Measure.infinitePi_eq_pi]

lemma walk_measurable (n : ℕ) : Measurable (walk (G := G) n) :=
  (measurable_of_countable (word (G := G) (n := n))).comp (takePath_measurable n)

omit [CompleteSpace H] [Group G] in
lemma takePath_integral (n : ℕ) (F : (Fin n → G) → H) :
    ∫ ω, F (takePath n ω) ∂pathMeasure μ = ∫ w, F w ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [← takePath_law μ n]
  exact (integral_map (takePath_measurable n).aemeasurable
    (StronglyMeasurable.of_discrete (f := F)).aestronglyMeasurable).symm

omit [Group G] [MeasurableSingletonClass G] [CompleteSpace H] in
 
lemma last_integral (n : ℕ) (F : (Fin n → G) → G → H)
    (hF : Integrable (fun p : (Fin n → G) × G => F p.1 p.2)
      ((Measure.pi (fun _ : Fin n => μ)).prod μ)) :
    ∫ v : Fin (n+1) → G, F (fun i => v i.castSucc) (v (Fin.last n))
      ∂Measure.pi (fun _ : Fin (n+1) => μ) =
    ∫ w : Fin n → G, ∫ u, F w u ∂μ ∂Measure.pi (fun _ : Fin n => μ) := by
  have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) (Fin.last n)).integral_comp'
    (fun p => F p.2 p.1)
  have he : ∀ v : Fin (n+1) → G,
      (fun p : G × (Fin n → G) => F p.2 p.1)
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => G) (Fin.last n)) v) =
      F (fun i => v i.castSucc) (v (Fin.last n)) := by
    intro v
    simp [MeasurableEquiv.piFinSuccAbove]
    rfl
  simp only [he] at h
  rw [h]
  calc
    _ = ∫ p : (Fin n → G) × G, F p.1 p.2 ∂(Measure.pi (fun _ : Fin n => μ)).prod μ :=
      integral_prod_swap (fun p : (Fin n → G) × G => F p.1 p.2)
    _ = _ := integral_prod _ hF

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
 
lemma integrable_of_countable_bound {S : Type*} [Countable S] [MeasurableSpace S]
    [MeasurableSingletonClass S] (ν : Measure S) [IsFiniteMeasure ν]
    (f : S → H) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f ν :=
  Integrable.of_bound (StronglyMeasurable.of_discrete (f := f)).aestronglyMeasurable C
    (Filter.Eventually.of_forall hb)

 
lemma increment_inner_integral (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) (n : ℕ)
    (Y : (Fin n → G) → H) (B : ℝ) (hY : ∀ w, ‖Y w‖ ≤ B) :
    ∫ ω, inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω)) ∂pathMeasure μ = 0 := by
  let F (w : Fin n → G) (u : G) := inner ℝ (D (word w*u)-D (word w)) (Y w)
  have hF : ∀ w u, ‖F w u‖ ≤ (C+C)*B := by
    intro w u
    calc
      _ ≤ ‖D (word w*u)-D (word w)‖ * ‖Y w‖ := norm_inner_le_norm _ _
      _ ≤ (C+C)*B := mul_le_mul
        ((norm_sub_le _ _).trans (add_le_add (hD _) (hD _))) (hY _) (norm_nonneg _)
        (add_nonneg ((norm_nonneg (D 1)).trans (hD 1)) ((norm_nonneg (D 1)).trans (hD 1)))
  have hstep : ∀ w, ∫ u, F w u ∂μ = 0 := by
    intro w
    have hi : Integrable (fun u => D (word w*u)) μ := integrable_of_countable_bound μ _ C (fun _ => hD _)
    simp_rw [show F w = fun u => inner ℝ (D (word w*u)-D (word w)) (Y w) from rfl,
      real_inner_comm]
    have he := integral_inner (𝕜 := ℝ) (hi.sub (integrable_const (D (word w)))) (Y w)
    simp only [Pi.sub_apply] at he
    rw [he, integral_sub hi (integrable_const _), hh, integral_const]
    simp
  have hhF := integrable_of_countable_bound
    ((Measure.pi (fun _ : Fin n => μ)).prod μ) (fun p => F p.1 p.2) ((C+C)*B)
    (fun p => hF p.1 p.2)
  have hm : (fun ω => inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω))) =
      fun ω => (fun v : Fin (n+1) → G => F (fun i => v i.castSucc) (v (Fin.last n)))
        (takePath (n+1) ω) := by
    funext ω
    rw [walk_succ]
    rfl
  rw [hm, takePath_integral μ (n+1) (fun v => F (fun i => v i.castSucc) (v (Fin.last n))),
    last_integral μ n F hhF]
  simp [hstep]

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma process_memLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    MemLp (fun ω => D (walk n ω)) 2 (pathMeasure μ) :=
  MemLp.of_bound ((StronglyMeasurable.of_discrete (f := D)).comp_measurable
    (walk_measurable n)).aestronglyMeasurable C (Filter.Eventually.of_forall (fun _ => hD _))

 
def processLp (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    Lp H 2 (pathMeasure μ) := (process_memLp μ D C hD n).toLp (fun ω => D (walk n ω))

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma processLp_ae (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    processLp μ D C hD n =ᵐ[pathMeasure μ] fun ω => D (walk n ω) :=
  (process_memLp μ D C hD n).coeFn_toLp

omit [CompleteSpace H] [InnerProductSpace ℝ H] in
lemma processLp_norm_le (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (n : ℕ) :
    ‖processLp μ D C hD n‖ ≤ C := by
  have hC : 0 ≤ C := (norm_nonneg (D 1)).trans (hD 1)
  have ha : ∀ᵐ ω ∂pathMeasure μ, ‖processLp μ D C hD n ω‖ ≤ C := by
    filter_upwards [processLp_ae μ D C hD n] with ω hω
    rw [hω]
    exact hD _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hC ha

lemma processLp_step_orthogonal (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) {k n : ℕ} (hkn : k ≤ n) :
    inner ℝ (processLp μ D C hD (n+1)-processLp μ D C hD n) (processLp μ D C hD k) = 0 := by
  let Y (w : Fin n → G) : H := D (word (fun i : Fin k => w (Fin.castLE hkn i)))
  have he := increment_inner_integral μ D C hD hh n Y C (fun _ => hD _)
  rw [L2.inner_def]
  calc
    _ = ∫ ω, inner ℝ (D (walk (n+1) ω)-D (walk n ω)) (Y (takePath n ω)) ∂pathMeasure μ := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (processLp μ D C hD (n+1)) (processLp μ D C hD n),
        processLp_ae μ D C hD (n+1), processLp_ae μ D C hD n,
        processLp_ae μ D C hD k] with ω hs hn hn' hk
      rw [hs,Pi.sub_apply,hn,hn',hk]
      rfl
    _ = 0 := he

lemma processLp_orthogonal (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) {k n : ℕ} (hkn : k ≤ n) :
    inner ℝ (processLp μ D C hD n-processLp μ D C hD k) (processLp μ D C hD k) = 0 := by
  induction n, hkn using Nat.le_induction with
  | base => simp
  | succ n hkn ih =>
    have hs := processLp_step_orthogonal μ D C hD hh hkn
    have he : processLp μ D C hD (n+1)-processLp μ D C hD k =
        (processLp μ D C hD (n+1)-processLp μ D C hD n) +
        (processLp μ D C hD n-processLp μ D C hD k) := by abel
    rw [he,inner_add_left,hs,ih,add_zero]

end HochschildWalk

namespace HochschildWalk
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
variable (μ : Measure G) [IsProbabilityMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
lemma processLp_sq_error (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C) (k n : ℕ) :
    ‖processLp μ D C hD n-processLp μ D C hD k‖ ^ 2 =
      ∫ ω, ‖D (walk n ω)-D (walk k ω)‖ ^ 2 ∂pathMeasure μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (processLp μ D C hD n) (processLp μ D C hD k),
    processLp_ae μ D C hD n, processLp_ae μ D C hD k] with ω hs hn hk
  rw [hs, Pi.sub_apply, hn, hk, real_inner_self_eq_norm_sq]

omit [CompleteSpace H] in
lemma limitLp_sq_error (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (z : Lp H 2 (pathMeasure μ)) (n : ℕ) :
    ‖z-processLp μ D C hD n‖ ^ 2 =
      ∫ ω, ‖z ω-D (walk n ω)‖ ^ 2 ∂pathMeasure μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub z (processLp μ D C hD n),
    processLp_ae μ D C hD n] with ω hs hn
  rw [hs, Pi.sub_apply, hn, real_inner_self_eq_norm_sq]

 

theorem harmonic_mean_square_convergence (D : G → H) (C : ℝ) (hD : ∀ g, ‖D g‖ ≤ C)
    (hh : ∀ g, ∫ u, D (g*u) ∂μ = D g) :
    ∃ z : Lp H 2 (pathMeasure μ),
      Tendsto (fun n => processLp μ D C hD n) atTop (𝓝 z) ∧
      Tendsto (fun n => ∫ ω, ‖z ω-D (walk n ω)‖^2 ∂pathMeasure μ) atTop (𝓝 0) ∧
      ∀ k n, k ≤ n →
        ∫ ω, ‖D (walk n ω)-D (walk k ω)‖^2 ∂pathMeasure μ ≤
          ∫ ω, ‖z ω-D (walk k ω)‖^2 ∂pathMeasure μ := by
  obtain ⟨z,hz,he,hb⟩ := HochschildMartingale.uniform_cauchy_error (processLp μ D C hD)
    (fun _ _ hkn => processLp_orthogonal μ D C hD hh hkn) C (processLp_norm_le μ D C hD)
  refine ⟨z,hz,?_,?_⟩
  · simpa only [limitLp_sq_error] using he
  · intro k n hkn
    rw [← processLp_sq_error μ D C hD k n, ← limitLp_sq_error μ D C hD z k]
    exact hb k n hkn

end HochschildWalk
end

end OAI
