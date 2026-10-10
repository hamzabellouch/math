import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.BoundedL1PoissonBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.PuncturedGreenBarrier

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_LocalArzelaAscoli_barrier_scope

open Filter Set Topology

theorem local_arzela_ascoli {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SigmaCompactSpace X] [T2Space X]
    (f : ℕ → C(X,ℝ))
    (he : Equicontinuous (fun n x => f n x))
    (hb : ∀ x, ∃ M : ℝ, ∀ n, |f n x| ≤ M) :
    ∃ u : C(X,ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → TendstoUniformlyOn (fun n x => f (φ n) x) u atTop K := by
  let : T2Space (UniformOnFun X ℝ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have hce := (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact
    (α := X) (β := ℝ)).isClosedEmbedding
  have heq (K : Set X) : EquicontinuousOn
      (fun g : range f => fun x => (g.val : C(X,ℝ)) x) K := by
    have hh := (he.comp (fun g : range f => Classical.choose g.property)).equicontinuousOn K
    convert hh using 1
    funext g x
    exact (congrArg (fun F : C(X,ℝ) => F x) (Classical.choose_spec g.property)).symm
  have hc : IsCompact (closure (range f)) :=
    ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (𝔖 := {K : Set X | IsCompact K}) (fun _ hK => hK)
      (F := fun g : C(X,ℝ) => (g : X → ℝ)) hce
      (fun K _ => heq K) (fun _ _ x _ => by
        obtain ⟨M,hM⟩ := hb x
        refine ⟨Icc (-M) M,isCompact_Icc,?_⟩
        rintro g ⟨n,rfl⟩
        exact abs_le.mp (hM n))
  obtain ⟨u,_hu,φ,hφ,ht⟩ := hc.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  exact ⟨u,φ,hφ,ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht⟩

end Work_LocalArzelaAscoli_barrier_scope

section Work_LocalLipschitzAscoli_barrier_scope

open Filter Set Metric
open scoped Topology

theorem equicontinuous_of_local_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    {f : ι → X → ℝ}
    (hl : ∀ x, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ i y, dist y x < r → |f i x-f i y| ≤ L*dist y x) : Equicontinuous f := by
  intro x
  obtain ⟨r,L,hr,hL,h⟩ := hl x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  refine ⟨min r (ε/(L+1)),lt_min hr (div_pos hε (by linarith)),?_⟩
  intro y hy i
  rw [lt_min_iff] at hy
  rw [Real.dist_eq]
  calc
    _ ≤ L*dist y x := h i y hy.1
    _ ≤ (L+1)*dist y x := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hh := (lt_div_iff₀ (show 0 < L+1 by linarith)).mp hy.2
      linarith only [hh]

theorem local_lipschitz_arzela_ascoli
    {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) (f : ℕ → X → ℝ) (hf : ∀ n, ContinuousOn (f n) U)
    (hb : ∀ x ∈ U, ∃ M : ℝ, ∀ n, |f n x| ≤ M)
    (hl : ∀ x ∈ U, ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧
      ∀ n y, y ∈ U → dist y x < r → |f n x-f n y| ≤ L*dist y x) :
    ∃ u : X → ℝ, ContinuousOn u U ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ U → TendstoUniformlyOn (fun n => f (φ n)) u atTop K := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let F : ℕ → C(U,ℝ) := fun n => ⟨fun x => f n x,(hf n).domRestrict⟩
  have he : Equicontinuous (fun n x => F n x) := by
    apply equicontinuous_of_local_lipschitz
    intro x
    obtain ⟨r,L,hr,hL,h⟩ := hl x x.property
    exact ⟨r,L,hr,hL,fun n y hy => h n y y.property hy⟩
  obtain ⟨v,φ,hφ,hv⟩ := local_arzela_ascoli F he (fun x => hb x x.property)
  let u : X → ℝ := fun x => if hx : x ∈ U then v ⟨x,hx⟩ else 0
  have heq (x : U) : u x = v x := by simp only [u,dite_eq_left x.property]
  refine ⟨u,?_,φ,hφ,?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    convert v.continuous using 1
    exact funext heq
  · intro K hK hKU
    let K' : Set U := Subtype.val ⁻¹' K
    have hK' : IsCompact K' := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      convert hK using 1
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x,hKU hx⟩,hx,rfl⟩
    have hh := hv K' hK'
    rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
    intro ε hε
    filter_upwards [hh ε hε] with n hn x hx
    have hs := hn ⟨x,hKU hx⟩ hx
    change dist (v ⟨x,hKU hx⟩) (f (φ n) x) < ε at hs
    rw [show u x = v ⟨x,hKU hx⟩ from heq ⟨x,hKU hx⟩]
    exact hs

end Work_LocalLipschitzAscoli_barrier_scope

open MeasureTheory Filter Set Metric Laplacian
open scoped Topology

open CoulombAtom

lemma nonnegative_density_restrict_integrable {ρ : Space → ℝ} {K : Set Space} {M : ℝ}
    (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hb : ∀ z ∈ K, ρ z ≤ M) : Integrable (K.indicator ρ) := by
  apply IntegrableOn.integrable_indicator _ hK
  apply IntegrableOn.of_bound hfin.lt_top hm.aestronglyMeasurable.restrict M
  exact ae_restrict_of_forall_mem hK (fun z hz => by rw [Real.norm_of_nonneg (hn z)]; exact hb z hz)

lemma nonnegative_density_restrict_mass {ρ : Space → ℝ} {K : Set Space} {M : ℝ}
    (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) (hK : MeasurableSet K)
    (hfin : volume K ≠ ⊤) (hb : ∀ z ∈ K, ρ z ≤ M) :
    (∫ z, K.indicator ρ z) ≤ M*(volume K).toReal := by
  rw [integral_indicator hK]
  have hi := (integrable_indicator_iff hK).mp (nonnegative_density_restrict_integrable hm hn hK hfin hb)
  have hc : IntegrableOn (fun _ : Space => M) K := integrableOn_const hfin
  have hh := integral_mono_ae hi hc (ae_restrict_of_forall_mem hK hb)
  simpa only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hh

theorem punctured_poisson_normal_family {f ρ : ℕ → Space → ℝ}
    (hf : ∀ n, ContinuousOn (f n) {0}ᶜ) (hρ : ∀ n, Measurable (ρ n))
    (hn : ∀ n z, 0 ≤ ρ n z)
    (he : ∀ n, PuncturedPoisson (f n) (fun z => 4*Real.pi*ρ n z))
    (hb : ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ M A : ℝ, 0 ≤ M ∧ 0 ≤ A ∧ (∀ n z, z ∈ K → ρ n z ≤ M) ∧
        ∀ n, (∫ z in K, |f n z|) ≤ A) :
    ∃ u : Space → ℝ, ContinuousOn u {0}ᶜ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ K, IsCompact K → K ⊆ {0}ᶜ → TendstoUniformlyOn (fun n => f (φ n)) u atTop K := by
  obtain ⟨P,L,hP,hL,hest⟩ := exists_weak_poisson_L1_constants
  have hlocal : ∀ c : Space, c ≠ 0 → ∃ r b l : ℝ, 0 < r ∧ 0 ≤ l ∧
      (∀ n, |f n c| ≤ b) ∧ ∀ n y, dist y c < r → |f n c-f n y| ≤ l*dist y c := by
    intro c hc
    let r := ‖c‖/8
    have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
    have hr : 0 < r := by dsimp [r]; positivity
    let K := closedBall c (3*r)
    have hK : IsCompact K := isCompact_closedBall c (3*r)
    have hK0 : K ⊆ {0}ᶜ := by
      intro z hz hzero
      have hez : z = 0 := hzero
      rw [hez] at hz
      change dist 0 c ≤ 3*r at hz
      rw [dist_zero_left] at hz
      dsimp [r] at hz
      linarith
    obtain ⟨M,A,hM,hA,hρM,hfA⟩ := hb K hK hK0
    let B := M*(volume K).toReal
    have hB : 0 ≤ B := mul_nonneg hM ENNReal.toReal_nonneg
    let C := A+(2*Real.pi*M+B)*(volume K).toReal
    have hC : 0 ≤ C := by dsimp [C]; positivity
    let b := P/r^3*C+(2*Real.pi*M+B)
    let l := L/r^4*C+4*Real.pi*M+B
    have hl : 0 ≤ l := by dsimp [l]; positivity
    have hi (n : ℕ) : Integrable (K.indicator (ρ n)) :=
      nonnegative_density_restrict_integrable (hρ n) (hn n) hK.measurableSet hK.measure_lt_top.ne (hρM n)
    have hm (n : ℕ) : Measurable (K.indicator (ρ n)) := (hρ n).indicator hK.measurableSet
    have hnon (n : ℕ) (z : Space) : 0 ≤ K.indicator (ρ n) z := indicator_nonneg (fun x _ => hn n x) z
    have hbound (n : ℕ) (z : Space) : K.indicator (ρ n) z ≤ M := by
      by_cases hz : z ∈ K
      · rw [indicator_of_mem hz]; exact hρM n z hz
      · rw [indicator_of_notMem hz]; exact hM
    have hmass (n : ℕ) : (∫ z, K.indicator (ρ n) z) ≤ B :=
      nonnegative_density_restrict_mass (hρ n) (hn n) hK.measurableSet hK.measure_lt_top.ne (hρM n)
    have hw (n : ℕ) : ∀ g : Space → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
        tsupport g ⊆ ball c (3*r) →
        (∫ z, f n z*Δ g z) = 4*Real.pi*∫ z, K.indicator (ρ n) z*g z := by
      intro g hg hcg hs
      rw [he n g hg hcg (hs.trans (ball_subset_closedBall.trans hK0)),←integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun z => by
        by_cases hz : g z = 0
        · simp only [hz,mul_zero]
        · have hzK : z ∈ K := ball_subset_closedBall (hs (subset_tsupport g hz))
          change 4*Real.pi*ρ n z*g z = 4*Real.pi*(K.indicator (ρ n) z*g z)
          rw [indicator_of_mem hzK]
          ring)
    have hx : c ∈ closedBall c r := mem_closedBall_self hr.le
    have hh (n : ℕ) (y : Space) (hy : y ∈ closedBall c r) :=
      hest (f n) (K.indicator (ρ n)) c r M A B hr hM (hm n) (hi n) (hnon n)
        (hbound n) (hmass n) ((hf n).mono hK0) (hfA n) (hw n) c hx y hy
    refine ⟨r,b,l,hr,hl,fun n => (hh n c hx).1,?_⟩
    intro n y hy
    have hd := (hh n y hy.le).2
    simpa only [dist_eq_norm,norm_sub_rev] using hd
  apply local_lipschitz_arzela_ascoli isOpen_compl_singleton f hf
  · intro c hc
    obtain ⟨r,b,l,_hr,_hl,hb',_hd⟩ := hlocal c hc
    exact ⟨b,hb'⟩
  · intro c hc
    obtain ⟨r,b,l,hr,hl,_hb,hd⟩ := hlocal c hc
    exact ⟨r,l,hr,hl,fun n y _hy hy => hd n y hy⟩

end CoulombAnalysis

end

end OAI
